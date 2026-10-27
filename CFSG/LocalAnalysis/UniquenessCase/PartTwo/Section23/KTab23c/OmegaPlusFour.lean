module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open CFSG.Open Matrix

local notation "ιP" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def e1P (K : Type) [Field K] : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inl 0) 1

@[expose] def e2P (K : Type) [Field K] : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inl 1) 1

private def e4P (K : Type) [Field K] : ιP → K :=
  Pi.single (Sum.inr 1) 1

private lemma quadP_apply (v : ιP → K) :
    StatedQuadPlus 2 K v = v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

private def polarP (u v : ιP → K) : K :=
  StatedQuadPlus 2 K (u + v) - StatedQuadPlus 2 K u - StatedQuadPlus 2 K v

private lemma polarP_apply (u v : ιP → K) :
    polarP u v = u (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 0) * u (Sum.inr 0) +
      u (Sum.inl 1) * v (Sum.inr 1) + v (Sum.inl 1) * u (Sum.inr 1) := by
  rw [polarP, quadP_apply, quadP_apply, quadP_apply]
  simp only [Pi.add_apply]
  ring

private lemma polarP_e1 (z : ιP → K) : polarP z (e1P K) = z (Sum.inr 0) := by
  rw [polarP_apply]
  simp [e1P]

private lemma polarP_e2 (z : ιP → K) : polarP z (e2P K) = z (Sum.inr 1) := by
  rw [polarP_apply]
  simp [e2P]

private lemma polarP_e2_e4 : polarP (e2P K) (e4P K) = 1 := by
  rw [polarP_apply]
  simp [e2P, e4P]

private lemma quadP_e2 : StatedQuadPlus 2 K (e2P K) = 0 := by
  rw [quadP_apply]
  simp [e2P]

private lemma quadP_e4 : StatedQuadPlus 2 K (e4P K) = 0 := by
  rw [quadP_apply]
  simp [e4P]

private lemma polarP_mulVec {g : GL ιP K}
    (hg : ∀ v, StatedQuadPlus 2 K ((g : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v)
    (u v : ιP → K) :
    polarP ((g : Matrix ιP ιP K) *ᵥ u) ((g : Matrix ιP ιP K) *ᵥ v) = polarP u v := by
  unfold polarP
  rw [← Matrix.mulVec_add, hg, hg, hg]

private lemma polarP_sub_left (u v w : ιP → K) :
    polarP (u - v) w = polarP u w - polarP v w := by
  rw [polarP_apply, polarP_apply, polarP_apply]
  simp only [Pi.sub_apply]
  ring

private lemma eq_smul_e1_e2_of (z : ιP → K) (h0 : z (Sum.inr 0) = 0)
    (h1 : z (Sum.inr 1) = 0) :
    z = z (Sum.inl 0) • e1P K + z (Sum.inl 1) • e2P K := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [e1P, e2P, h0, h1]

private lemma eq_smul_e1_e4_of (z : ιP → K) (h0 : z (Sum.inr 0) = 0)
    (h2 : z (Sum.inl 1) = 0) :
    z = z (Sum.inl 0) • e1P K + z (Sum.inr 1) • e4P K := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [e1P, e4P, h0, h2]

theorem sq_eq_one_of_fix_plane [CharP K 2] {g : GL ιP K}
    (hg : ∀ v, StatedQuadPlus 2 K ((g : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v)
    (h1 : (g : Matrix ιP ιP K) *ᵥ e1P K = e1P K) (h2 : (g : Matrix ιP ιP K) *ᵥ e2P K = e2P K) :
    g ^ 2 = 1 := by
  have hP := polarP_mulVec hg
  have hstep1 : ∀ z, polarP ((g : Matrix ιP ιP K) *ᵥ z) (e1P K) = polarP z (e1P K) := by
    intro z
    simpa [h1] using hP z (e1P K)
  have hstep2 : ∀ z, polarP ((g : Matrix ιP ιP K) *ᵥ z) (e2P K) = polarP z (e2P K) := by
    intro z
    simpa [h2] using hP z (e2P K)
  have hdz : ∀ z, ((g : Matrix ιP ιP K) *ᵥ z - z) (Sum.inr 0) = 0 ∧
      ((g : Matrix ιP ιP K) *ᵥ z - z) (Sum.inr 1) = 0 := by
    intro z
    constructor
    · have h : polarP ((g : Matrix ιP ιP K) *ᵥ z - z) (e1P K) = 0 := by
        rw [polarP_sub_left, hstep1 z, sub_self]
      rwa [polarP_e1] at h
    · have h : polarP ((g : Matrix ιP ιP K) *ᵥ z - z) (e2P K) = 0 := by
        rw [polarP_sub_left, hstep2 z, sub_self]
      rwa [polarP_e2] at h
  have hgfix : ∀ z, (g : Matrix ιP ιP K) *ᵥ ((g : Matrix ιP ιP K) *ᵥ z - z) =
      ((g : Matrix ιP ιP K) *ᵥ z - z) := by
    intro z
    obtain ⟨h0, h1'⟩ := hdz z
    rw [eq_smul_e1_e2_of _ h0 h1', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      h1, h2]
  have hsq : ∀ z, ((g : Matrix ιP ιP K) ^ 2) *ᵥ z = z := by
    intro z
    set d : ιP → K := (g : Matrix ιP ιP K) *ᵥ z - z with hd
    have hgz : (g : Matrix ιP ιP K) *ᵥ z = z + d := by rw [hd]; abel
    have hgd : (g : Matrix ιP ιP K) *ᵥ d = d := by rw [hd]; exact hgfix z
    calc ((g : Matrix ιP ιP K) ^ 2) *ᵥ z
        = (g : Matrix ιP ιP K) *ᵥ ((g : Matrix ιP ιP K) *ᵥ z) := by
          rw [pow_two, Matrix.mulVec_mulVec]
      _ = (g : Matrix ιP ιP K) *ᵥ (z + d) := by rw [hgz]
      _ = (g : Matrix ιP ιP K) *ᵥ z + (g : Matrix ιP ιP K) *ᵥ d := by rw [Matrix.mulVec_add]
      _ = (z + d) + d := by rw [hgz, hgd]
      _ = z := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [Matrix.one_mulVec]
  exact hsq (Pi.single i 1)

theorem exists_mulVec_e2P_eq [CharP K 2] {g : GL ιP K}
    (hg : ∀ v, StatedQuadPlus 2 K ((g : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v)
    (hodd : Odd (orderOf g)) (h1 : (g : Matrix ιP ιP K) *ᵥ e1P K = e1P K) :
    ∃ α β : K, (g : Matrix ιP ιP K) *ᵥ e2P K = α • e1P K + β • e2P K := by
  classical
  set f : ιP → K := (g : Matrix ιP ιP K) *ᵥ e2P K with hf
  set h4 : ιP → K := (g : Matrix ιP ιP K) *ᵥ e4P K with hh4
  have hf0 : f (Sum.inr 0) = 0 := by
    have hp := polarP_mulVec hg (e2P K) (e1P K)
    rw [h1, ← hf, polarP_e1, polarP_e1] at hp
    simpa [e2P] using hp
  have hh0 : h4 (Sum.inr 0) = 0 := by
    have hp := polarP_mulVec hg (e4P K) (e1P K)
    rw [h1, ← hh4, polarP_e1, polarP_e1] at hp
    simpa [e4P] using hp
  have hQf : StatedQuadPlus 2 K f = 0 := by
    have h := hg (e2P K)
    rw [← hf, quadP_e2] at h
    exact h
  have hQh : StatedQuadPlus 2 K h4 = 0 := by
    have h := hg (e4P K)
    rw [← hh4, quadP_e4] at h
    exact h
  have hfprod : f (Sum.inl 1) * f (Sum.inr 1) = 0 := by
    have h := hQf
    rw [quadP_apply, hf0] at h
    simpa using h
  have hhprod : h4 (Sum.inl 1) * h4 (Sum.inr 1) = 0 := by
    have h := hQh
    rw [quadP_apply, hh0] at h
    simpa using h
  have hpfh : polarP f h4 = 1 := by
    have hp := polarP_mulVec hg (e2P K) (e4P K)
    rw [polarP_e2_e4, ← hf, ← hh4] at hp
    exact hp
  have hcross : f (Sum.inl 1) * h4 (Sum.inr 1) + h4 (Sum.inl 1) * f (Sum.inr 1) = 1 := by
    have h := hpfh
    rw [polarP_apply, hf0, hh0] at h
    simpa using h
  have hfy1 : f (Sum.inr 1) = 0 := by
    by_contra hfy1
    have hfx1 : f (Sum.inl 1) = 0 := by
      rcases mul_eq_zero.mp hfprod with h' | h'
      · exact h'
      · exact absurd h' hfy1
    have hhx1fy1 : h4 (Sum.inl 1) * f (Sum.inr 1) = 1 := by
      rw [hfx1, zero_mul, zero_add] at hcross
      exact hcross
    have hhx1 : h4 (Sum.inl 1) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hhx1fy1
      exact zero_ne_one hhx1fy1
    have hhy1 : h4 (Sum.inr 1) = 0 := by
      rcases mul_eq_zero.mp hhprod with h' | h'
      · exact absurd h' hhx1
      · exact h'
    have hgzP1 : ∀ z : ιP → K, z (Sum.inr 0) = 0 → z (Sum.inr 1) = 0 →
        (g : Matrix ιP ιP K) *ᵥ z = z (Sum.inl 0) • e1P K + z (Sum.inl 1) • f := by
      intro z hz0 hz1
      rw [eq_smul_e1_e2_of z hz0 hz1, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, h1, ← hf]
      simp [e1P, e2P]
    have stepA : ∀ z : ιP → K, z (Sum.inr 0) = 0 → z (Sum.inr 1) = 0 →
        ((g : Matrix ιP ιP K) *ᵥ z) (Sum.inr 0) = 0 ∧
        ((g : Matrix ιP ιP K) *ᵥ z) (Sum.inl 1) = 0 := by
      intro z hz0 hz1
      rw [hgzP1 z hz0 hz1]
      constructor <;> simp [e1P, hf0, hfx1]
    have hgzP2 : ∀ z : ιP → K, z (Sum.inr 0) = 0 → z (Sum.inl 1) = 0 →
        (g : Matrix ιP ιP K) *ᵥ z = z (Sum.inl 0) • e1P K + z (Sum.inr 1) • h4 := by
      intro z hz0 hz1
      rw [eq_smul_e1_e4_of z hz0 hz1, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, h1, ← hh4]
      simp [e1P, e4P]
    have stepB : ∀ z : ιP → K, z (Sum.inr 0) = 0 → z (Sum.inl 1) = 0 →
        ((g : Matrix ιP ιP K) *ᵥ z) (Sum.inr 0) = 0 ∧
        ((g : Matrix ιP ιP K) *ᵥ z) (Sum.inr 1) = 0 := by
      intro z hz0 hz1
      rw [hgzP2 z hz0 hz1]
      constructor <;> simp [e1P, hh0, hhy1]
    have stepB2 : ∀ z : ιP → K, z (Sum.inr 0) = 0 → z (Sum.inl 1) = 0 →
        (((g : Matrix ιP ιP K) ^ 2) *ᵥ z) (Sum.inr 0) = 0 ∧
        (((g : Matrix ιP ιP K) ^ 2) *ᵥ z) (Sum.inl 1) = 0 := by
      intro z hz0 hz1
      obtain ⟨hb0, hb1⟩ := stepB z hz0 hz1
      have := stepA ((g : Matrix ιP ιP K) *ᵥ z) hb0 hb1
      rwa [pow_two, ← Matrix.mulVec_mulVec]
    have key : ∀ k : ℕ,
        (((g : Matrix ιP ιP K) ^ (2 * k + 1)) *ᵥ e2P K) (Sum.inr 0) = 0 ∧
        (((g : Matrix ιP ιP K) ^ (2 * k + 1)) *ᵥ e2P K) (Sum.inl 1) = 0 := by
      intro k
      induction k with
      | zero => simpa using stepA (e2P K) (by simp [e2P]) (by simp [e2P])
      | succ k ih =>
        have hpow : 2 * (k + 1) + 1 = 2 + (2 * k + 1) := by ring
        rw [hpow, pow_add, ← Matrix.mulVec_mulVec]
        exact stepB2 _ ih.1 ih.2
    obtain ⟨k, hk⟩ := hodd
    have hgpow : (g : Matrix ιP ιP K) ^ orderOf g = 1 := by
      conv_lhs => rw [← Units.val_pow_eq_pow_val]
      rw [pow_orderOf_eq_one g, Units.val_one]
    have hmem := key k
    have he2 : e2P K (Sum.inl 1) = 0 := by
      have hm : (g : Matrix ιP ιP K) ^ (2 * k + 1) *ᵥ e2P K = e2P K := by
        rw [← hk, hgpow, Matrix.one_mulVec]
      rw [← hm]
      exact hmem.2
    rw [show e2P K (Sum.inl 1) = 1 by simp [e2P]] at he2
    exact one_ne_zero he2
  exact ⟨f (Sum.inl 0), f (Sum.inl 1), eq_smul_e1_e2_of f hf0 hfy1⟩

private def e2Coord (g : GL ιP K) : K :=
  ((g : Matrix ιP ιP K) *ᵥ e2P K) (Sum.inl 0)

private def e2Char (g : GL ιP K) : K :=
  ((g : Matrix ιP ιP K) *ᵥ e2P K) (Sum.inl 1)

private lemma e2Char_one : e2Char (1 : GL ιP K) = 1 := by
  rw [e2Char, Units.val_one, Matrix.one_mulVec]
  simp [e2P]

theorem isCyclic_of_odd_of_fix [Finite K] [CharP K 2] {E : Subgroup (GL ιP K)}
    (hE : ∀ g ∈ E, ∀ v, StatedQuadPlus 2 K ((g : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v)
    (hodd : Odd (Nat.card ↥E)) (hfix : ∀ g ∈ E, (g : Matrix ιP ιP K) *ᵥ e1P K = e1P K) :
    IsCyclic ↥E := by
  classical
  haveI hfinGL : Finite (GL ιP K) :=
    Finite.of_injective (fun u : GL ιP K => (u : Matrix ιP ιP K)) (fun a b h => Units.ext h)
  haveI hfinE : Finite ↥E :=
    Finite.of_injective (fun g : ↥E => (g : GL ιP K)) Subtype.coe_injective
  have hodd' : ∀ g : ↥E, Odd (orderOf (g : GL ιP K)) := fun g =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard E g.2)
  have hdec : ∀ g : ↥E, ((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K =
      e2Coord (g : GL ιP K) • e1P K + e2Char (g : GL ιP K) • e2P K := by
    intro g
    obtain ⟨α, β, hαβ⟩ := exists_mulVec_e2P_eq (hE g g.2) (hodd' g) (hfix g g.2)
    have hα : α = e2Coord (g : GL ιP K) := by
      rw [e2Coord, hαβ]
      simp [e1P, e2P]
    have hβ : β = e2Char (g : GL ιP K) := by
      rw [e2Char, hαβ]
      simp [e1P, e2P]
    rw [hα, hβ] at hαβ
    exact hαβ
  have hβne : ∀ g : ↥E, e2Char (g : GL ιP K) ≠ 0 := by
    intro g hzero
    have hdecg : ((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K =
        e2Coord (g : GL ιP K) • e1P K := by
      rw [hdec g, hzero, zero_smul, add_zero]
    have hfixinv : ((g⁻¹ : GL ιP K) : Matrix ιP ιP K) *ᵥ e1P K = e1P K := by
      have h := congrArg (fun v => ((g⁻¹ : GL ιP K) : Matrix ιP ιP K) *ᵥ v) (hfix g g.2)
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] using h.symm
    have hga : ((g⁻¹ : GL ιP K) : Matrix ιP ιP K) *ᵥ (e2Coord (g : GL ιP K) • e1P K) =
        e2Coord (g : GL ιP K) • e1P K := by
      rw [Matrix.mulVec_smul, hfixinv]
    have hvec : e2P K = e2Coord (g : GL ιP K) • e1P K := by
      calc e2P K = ((g⁻¹ : GL ιP K) : Matrix ιP ιP K) *ᵥ
            (((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K) := by
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.one_mulVec]
        _ = ((g⁻¹ : GL ιP K) : Matrix ιP ιP K) *ᵥ (e2Coord (g : GL ιP K) • e1P K) := by
            rw [hdecg]
        _ = e2Coord (g : GL ιP K) • e1P K := by rw [hga]
    have hx := congrFun hvec (Sum.inl 1)
    have hx' : (1 : K) = 0 := by simpa [e1P, e2P] using hx
    exact one_ne_zero hx'
  have hβmul : ∀ g h : ↥E, e2Char ((g * h : ↥E) : GL ιP K) =
      e2Char (g : GL ιP K) * e2Char (h : GL ιP K) := by
    intro g h
    have hmain : (((↑(g * h) : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K) (Sum.inl 1) =
        (((h : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K) (Sum.inl 1) *
        (((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K) (Sum.inl 1) := by
      rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hdec h, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hfix g g.2, hdec g]
      simp [e1P, e2P]
    simp only [e2Char]
    rw [hmain, mul_comm]
  have hβeq_one : ∀ g : ↥E, e2Char (g : GL ιP K) = 1 → g = 1 := by
    intro g hg1
    have hge2 : ((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K =
        e2P K + e2Coord (g : GL ιP K) • e1P K := by
      rw [hdec g, hg1, one_smul, add_comm]
    have hge1 : ((g : GL ιP K) : Matrix ιP ιP K) *ᵥ (e2Coord (g : GL ιP K) • e1P K) =
        e2Coord (g : GL ιP K) • e1P K := by
      rw [Matrix.mulVec_smul, hfix g g.2]
    have hge1pow : ∀ k : ℕ, ((g : GL ιP K) : Matrix ιP ιP K) ^ k *ᵥ e1P K = e1P K := by
      intro k
      induction k with
      | zero => rw [pow_zero, Matrix.one_mulVec]
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hfix g g.2, ih]
    have hpow : ∀ k : ℕ, ((g : GL ιP K) : Matrix ιP ιP K) ^ k *ᵥ e2P K =
        e2P K + (k : K) • (e2Coord (g : GL ιP K) • e1P K) := by
      intro k
      induction k with
      | zero => rw [pow_zero, Matrix.one_mulVec, Nat.cast_zero, zero_smul, add_zero]
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hge2, Matrix.mulVec_add, Matrix.mulVec_smul,
          hge1pow k, ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_assoc]
    have hgm : ((g : GL ιP K) : Matrix ιP ιP K) ^ orderOf (g : GL ιP K) = 1 := by
      conv_lhs => rw [← Units.val_pow_eq_pow_val]
      rw [pow_orderOf_eq_one (g : GL ιP K), Units.val_one]
    have hαzero : e2Coord (g : GL ιP K) = 0 := by
      have h := hpow (orderOf (g : GL ιP K))
      rw [hgm, Matrix.one_mulVec] at h
      have hcast : (orderOf (g : GL ιP K) : K) = 1 :=
        natCast_eq_one_of_odd_of_two_eq_zero (hodd' g) (by simpa using CharP.cast_eq_zero K 2)
      rw [hcast, one_smul] at h
      have hzero : e2Coord (g : GL ιP K) • e1P K = 0 := by
        have h2 : e2P K + e2Coord (g : GL ιP K) • e1P K = e2P K + 0 := by rw [← h, add_zero]
        exact add_left_cancel h2
      have hx := congrFun hzero (Sum.inl 0)
      simpa [e1P] using hx
    have hge2' : ((g : GL ιP K) : Matrix ιP ιP K) *ᵥ e2P K = e2P K := by
      rw [hge2, hαzero, zero_smul, add_zero]
    have hgsq : (g : GL ιP K) ^ 2 = 1 :=
      sq_eq_one_of_fix_plane (hE g g.2) (hfix g g.2) hge2'
    have hdvd : orderOf (g : GL ιP K) ∣ 2 := orderOf_dvd_of_pow_eq_one hgsq
    obtain ⟨k, hk⟩ := hodd' g
    have hone : orderOf (g : GL ιP K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hk
        omega
    exact Subtype.ext (orderOf_eq_one_iff.mp hone)
  let ψ : ↥E →* Kˣ :=
  { toFun := fun g => Units.mk0 (e2Char (g : GL ιP K)) (hβne g)
    map_one' := by
      ext
      rw [Units.val_mk0, Units.val_one]
      rw [show ((1 : ↥E) : GL ιP K) = 1 from Subgroup.coe_one E, e2Char_one]
    map_mul' := by
      intro g h
      ext
      rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hβmul g h }
  have hψval : ∀ g : ↥E, (ψ g : K) = e2Char (g : GL ιP K) := fun g => rfl
  have hψinj : Function.Injective ψ := by
    intro g h hgh
    have hβeq : e2Char (g : GL ιP K) = e2Char (h : GL ιP K) := by
      have h' := congrArg (fun u : Kˣ => (u : K)) hgh
      rwa [hψval g, hψval h] at h'
    have hinv : e2Char ((h⁻¹ : ↥E) : GL ιP K) = (e2Char (h : GL ιP K))⁻¹ := by
      have hh : e2Char ((h⁻¹ : ↥E) : GL ιP K) * e2Char (h : GL ιP K) = 1 := by
        rw [← hβmul, inv_mul_cancel, Subgroup.coe_one, e2Char_one]
      exact eq_inv_of_mul_eq_one_left hh
    have hprod : e2Char ((g * h⁻¹ : ↥E) : GL ιP K) = 1 := by
      rw [hβmul, hβeq, hinv, mul_inv_cancel₀ (hβne h)]
    have hgh1 : g * h⁻¹ = 1 := hβeq_one (g * h⁻¹) hprod
    calc g = g * h⁻¹ * h := by group
      _ = 1 * h := by rw [hgh1]
      _ = h := one_mul h
  have hcoe_inj : Function.Injective ((Units.coeHom K).comp ψ) :=
    Units.coeHom_injective.comp hψinj
  exact isCyclic_of_subgroup_isDomain ((Units.coeHom K).comp ψ) hcoe_inj

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
