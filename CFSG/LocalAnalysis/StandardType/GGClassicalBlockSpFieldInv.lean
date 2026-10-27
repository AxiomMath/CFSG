module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDescent
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpTwoPart
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix

private lemma ggJSa1_conj_scalar {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (A : GL (Fin n ⊕ Fin n) K) (c : Kˣ) :
    A * (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c).map σ.toRingHom * A⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (Units.map σ.toRingHom c) := by
  rw [Matrix.GeneralLinearGroup.map_scalar, ← Matrix.GeneralLinearGroup.scalar_commute,
    mul_assoc, mul_inv_cancel, mul_one]

private lemma ggJSa1_scalar_injective {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    (a b : Kˣ) (hab : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) a =
      Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) b) : a = b := by
  apply Units.ext
  have hmat := congrArg (fun w : GL (Fin n ⊕ Fin n) K =>
    (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hab
  let i : Fin n ⊕ Fin n := Sum.inl ⟨0, hn⟩
  have hi := congrFun (congrFun hmat i) i
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hi

private lemma ggJSa1_sigma_sq {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (A : GL (Fin n ⊕ Fin n) K)
    (hinv : ∀ g : GL (Fin n ⊕ Fin n) K,
      A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g) (hn : 0 < n) :
    ∀ x : K, σ (σ x) = x := by
  intro x
  by_cases hx : x = 0
  · subst hx
    simp
  · let u : Kˣ := Units.mk0 x hx
    have hinner : A * (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) u).map σ.toRingHom *
        A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (Units.map σ.toRingHom u) :=
      ggJSa1_conj_scalar σ A u
    have h := hinv (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) u)
    rw [hinner] at h
    rw [ggJSa1_conj_scalar σ A (Units.map σ.toRingHom u)] at h
    let σu : Kˣ →* Kˣ := Units.map (σ.toRingHom : K →* K)
    have h2 : σu (σu u) = u := ggJSa1_scalar_injective hn (σu (σu u)) u h
    have hx' : σ (σ x) = x := by
      have hval := congrArg (fun w : Kˣ => (w : K)) h2
      simpa [u, σu, Units.coe_map] using hval
    exact hx'

private lemma ggJSa1_central {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (A : GL (Fin n ⊕ Fin n) K)
    (hinv : ∀ g : GL (Fin n ⊕ Fin n) K,
      A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (hσ2 : ∀ x, σ (σ x) = x) (g : GL (Fin n ⊕ Fin n) K) :
    (A * A.map σ.toRingHom) * g = g * (A * A.map σ.toRingHom) := by
  have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id K := by
    ext x
    exact hσ2 x
  have hmap2 : (g.map σ.toRingHom).map σ.toRingHom = g := by
    have h := congrArg (fun f : GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) K => f g)
      (Matrix.GeneralLinearGroup.map_comp σ.toRingHom σ.toRingHom)
    rw [hcomp, Matrix.GeneralLinearGroup.map_id] at h
    simpa using h.symm
  have h1 : (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom =
      A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹ := by
    simp only [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_inv, hmap2]
  have h2 : A * (A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹) * A⁻¹ =
      (A * A.map σ.toRingHom) * g * (A * A.map σ.toRingHom)⁻¹ := by
    group
  have h := hinv g
  rw [h1, h2] at h
  calc (A * A.map σ.toRingHom) * g
      = ((A * A.map σ.toRingHom) * g * (A * A.map σ.toRingHom)⁻¹) *
          (A * A.map σ.toRingHom) := by group
    _ = g * (A * A.map σ.toRingHom) := by rw [h]

private lemma ggJSa1_AA {n : ℕ} {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)
    (A : GL (Fin n ⊕ Fin n) K) (hA : A ∈ StatedSp n K)
    (hinv : ∀ g : GL (Fin n ⊕ Fin n) K,
      A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (hσ2 : ∀ x, σ (σ x) = x) (hn : 0 < n) :
    A * A.map σ.toRingHom = 1 := by
  have hcentral := ggJSa1_central σ A hinv hσ2
  have hCsp : A * A.map σ.toRingHom ∈ StatedSp n K :=
    mul_mem hA (CFSG.Open.StatedAPI.map_mem_statedSp σ.toRingHom hA)
  have hcenter : A * A.map σ.toRingHom ∈ Subgroup.center (GL (Fin n ⊕ Fin n) K) :=
    Subgroup.mem_center_iff.mpr (fun g => (hcentral g).symm)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  have hscalarSp : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K := by
    rw [hc]
    exact hCsp
  have hc2 : c ^ 2 = 1 :=
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (by omega : 1 ≤ n) c).mp hscalarSp
  have hc1 : c = 1 := by
    apply Units.ext
    have h2 : (c : K) ^ 2 = 1 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hc2
    have h3 : (c : K) * (c : K) = 1 := by simpa [sq] using h2
    rcases mul_self_eq_one_iff.mp h3 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
      simp
  rw [← hc, hc1, map_one]

private lemma ggJSa1_arith {f f₀ N : ℕ} (hf : f = 2 * f₀) (hf₀ : 0 < f₀)
    (h : f * N = f₀ * N) : N = 0 := by
  have h1 : f₀ * N = 0 := by
    have h2 : f₀ * N + f₀ * N = f₀ * N + 0 := by
      rw [← two_mul, ← mul_assoc, add_zero, ← hf]
      exact h
    exact Nat.add_left_cancel h2
  rcases Nat.mul_eq_zero.mp h1 with h' | h'
  · exact absurd h' (Nat.ne_of_gt hf₀)
  · exact h'

theorem isMulCommutative_centralizer_of_fieldInv_Sp {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n : ℕ} (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K) (A : GL (Fin n ⊕ Fin n) K)
    (hA : A ∈ StatedSp n K)
    (hinv : ∀ g : GL (Fin n ⊕ Fin n) K,
      A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    (hfix : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedSp n K,
      A * g.map σ.toRingHom * A⁻¹ = g) :
    ∀ x ∈ Subgroup.centralizer {b} ⊓ StatedSp n K,
      ∀ y ∈ Subgroup.centralizer {b} ⊓ StatedSp n K, x * y = y * x := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    intro x _ y _
    apply Units.ext
    exact Subsingleton.elim _ _
  · letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    have hσ2 : ∀ x : K, σ (σ x) = x := ggJSa1_sigma_sq σ A hinv hn
    have hAA : A * A.map σ.toRingHom = 1 := ggJSa1_AA σ A hA hinv hσ2 hn
    have hfix' : ∀ g ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype,
        A * (g : GL (Fin n ⊕ Fin n) K).map σ.toRingHom * A⁻¹ = g := by
      intro g hg
      have hgGL : (g : GL (Fin n ⊕ Fin n) K) ∈
          Subgroup.centralizer {b} ⊓ StatedSp n K :=
        ⟨Subgroup.mem_comap.mp hg, g.2⟩
      exact hfix (g : GL (Fin n ⊕ Fin n) K) hgGL
    obtain ⟨K₀, hK₀field, hK₀fin, hK₀char, b₀, hb₀, hodd₀, hcard, hIso, hblockExp⟩ :=
      descent_centralizer_Sp σ hσ hσ2 A hA hAA b hb hodd hfix'
    letI : Field K₀ := hK₀field
    letI : Fintype K₀ := hK₀fin
    letI : CharP K₀ 2 := hK₀char
    letI : Algebra (ZMod 2) K₀ := ZMod.algebra K₀ 2
    obtain ⟨e⟩ := hIso
    have hfK : Fintype.card K = 2 ^ Module.finrank (ZMod 2) K :=
      (FiniteField.pow_finrank_eq_card 2 K).symm
    have hfK₀ : Fintype.card K₀ = 2 ^ Module.finrank (ZMod 2) K₀ :=
      (FiniteField.pow_finrank_eq_card 2 K₀).symm
    have hf_eq : Module.finrank (ZMod 2) K = 2 * Module.finrank (ZMod 2) K₀ := by
      have h : 2 ^ Module.finrank (ZMod 2) K =
          2 ^ (2 * Module.finrank (ZMod 2) K₀) := by
        have hc' := hcard
        rw [hfK, hfK₀] at hc'
        rw [hc', pow_mul']
      exact Nat.pow_right_injective (le_refl 2) h
    have hf₀pos : 0 < Module.finrank (ZMod 2) K₀ := by
      by_contra h
      have h0 : Module.finrank (ZMod 2) K₀ = 0 := Nat.eq_zero_of_not_pos h
      rw [h0] at hfK₀
      simp at hfK₀
      exact absurd hfK₀.symm (ne_of_lt Fintype.one_lt_card)
    have h2C := two_part_centralizer_Sp (K := K) hfK b hb hodd
    have h2C₀ := two_part_centralizer_Sp (K := K₀) hfK₀ b₀ hb₀ hodd₀
    let C : Subgroup ↥(StatedSp n K) := (Subgroup.centralizer {b}).comap (StatedSp n K).subtype
    let C₀ : Subgroup ↥(StatedSp n K₀) :=
      (Subgroup.centralizer {b₀}).comap (StatedSp n K₀).subtype
    have hcardC : Nat.card ↥C = Nat.card ↥C₀ := Nat.card_congr e.toEquiv
    have hfac : (Nat.card ↥C).factorization 2 = (Nat.card ↥C₀).factorization 2 := by
      rw [hcardC]
    have heq : Module.finrank (ZMod 2) K *
          blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Module.finrank (ZMod 2) K₀ *
          blockExp false (b₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀) := by
      rw [← h2C, ← h2C₀]
      exact hfac
    have heq' : Module.finrank (ZMod 2) K *
          blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Module.finrank (ZMod 2) K₀ *
          blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      rw [← hblockExp] at heq
      exact heq
    have hN : blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 0 :=
      ggJSa1_arith hf_eq hf₀pos heq'
    have hcomm := commutative_centralizer_of_blockExp_eq_zero_Sp b hb hodd hN
    intro x hx y hy
    have hx' : (⟨x, hx.2⟩ : ↥(StatedSp n K)) ∈
        (Subgroup.centralizer {b}).comap (StatedSp n K).subtype := by
      rw [Subgroup.mem_comap]
      exact hx.1
    have hy' : (⟨y, hy.2⟩ : ↥(StatedSp n K)) ∈
        (Subgroup.centralizer {b}).comap (StatedSp n K).subtype := by
      rw [Subgroup.mem_comap]
      exact hy.1
    have hc := hcomm ⟨x, hx.2⟩ hx' ⟨y, hy.2⟩ hy'
    simpa using congrArg (fun z : ↥(StatedSp n K) => (z : GL (Fin n ⊕ Fin n) K)) hc

end CFSG.StandardType.ClassicalBlocks
