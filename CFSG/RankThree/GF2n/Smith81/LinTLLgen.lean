module

public import CFSG.RankThree.GF2n.Smith81.LinTLConj
public import CFSG.RankThree.GF2n.Stroth80.Sec37Bridge
public import CFSG.LieType.SeitzGeneration.HyperIrrBlock

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

private theorem charP_two_of_card_two_pow {K : Type} [Field K] [Finite K] {k : ℕ}
    (h : Nat.card K = 2 ^ k) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact _root_.charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, h])

private theorem scalar_eq_one_of_sq_eq_one {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (hn : 0 < n) {r : K} (hr : Matrix.scalar (Fin n) r * Matrix.scalar (Fin n) r = 1) :
    Matrix.scalar (Fin n) r = 1 := by
  have hrr : r * r = 1 := by
    have h := congrFun (congrFun hr ⟨0, hn⟩) ⟨0, hn⟩
    simpa [Matrix.scalar_apply] using h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (r - 1) * (r - 1) = 0 := by linear_combination hrr - (r - 1) * h2
  have hr1 : r = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  rw [hr1, map_one]

theorem LinSetup.Lgen_eq_of_le_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A) (hAV : A ≤ V₁) :
    Lgen M (LB M Q A) = Lgen M (LB M Q B) := by
  have hLA : LB M Q A ≤ Lgen M (LB M Q B) := LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hA hAV
  have hw : Width Q Z n := LinSetup.width hc.hyp hS
  have hLM : Lgen M (LB M Q B) ≤ M := Br37.Lgen_le_of fun m hm => conj_le_M hc.LB_le_M hm
  have hle : Lgen M (LB M Q A) ≤ Lgen M (LB M Q B) := by
    refine Br37.Lgen_le_of fun m hm => ?_
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 : m⁻¹ * x * m ∈ Lgen M (LB M Q B) := hLA hx
    have h2 := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q B) hm) _).mp h1
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2
  have hQL : Q ≤ Lgen M (LB M Q A) :=
    (le_sup_left : Q ≤ LB M Q A).trans (le_Lgen_self M (LB M Q A))
  have hnorm : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ Lgen M (LB M Q A),
      s * x * s⁻¹ ∈ Lgen M (LB M Q A) := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M (LB M Q A) (hLM hs)) x).mp hx
  have hcardA : Nat.card Q * Nat.card Z ^ (n - 1) ≤ Nat.card (LB M Q A) :=
    hA.card_LB_ge hw (by omega)
  obtain ⟨t, ht, htQ⟩ : ∃ t ∈ LB M Q A, t ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hleQ : LB M Q A ≤ Q := fun x hx => hcon x hx
    have hle' : Nat.card (LB M Q A) ≤ Nat.card Q := Subgroup.card_le_of_le hleQ
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hpow : Nat.card Z ≤ Nat.card Z ^ (n - 1) := by
      calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
        _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 4 ≤ Nat.card Z ^ (n - 1) := le_trans hq4 hpow
    have hmul := Nat.mul_le_mul_left (Nat.card Q) h4
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    linarith
  have htL : t ∈ Lgen M (LB M Q B) := hLA ht
  have ht' : t ∈ Lgen M (LB M Q A) := le_Lgen_self M (LB M Q A) ht
  have htt : t * t ∈ Q := by
    have h2 := hA.sq_mem_Q_of_mem_LB ht
    rwa [pow_two] at h2
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, -, -, -, -, -, -, -, -, -, -⟩ := hS
  haveI : CharP K 2 := by
    obtain ⟨m, -, hZ2, -⟩ := hc.hyp.cp
    exact charP_two_of_card_two_pow (hcard.trans hZ2)
  have hsurj : ∀ g : GL (Fin n) K, g ∈ φ.range →
      ∃ a : Matrix.SpecialLinearGroup (Fin n) K, Matrix.SpecialLinearGroup.toGL a = g := by
    intro g hg
    rw [hrange, CFSG.Open.StatedAPI.statedSL_eq_range_toGL, MonoidHom.mem_range] at hg
    exact hg
  have hgen : ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
      Matrix.SpecialLinearGroup.toGL g ∈ φ.range := by
    intro g
    rw [hrange, CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (GL (Fin n) K),
      N = Subgroup.map φ ((Lgen M (LB M Q A)).subgroupOf (Lgen M (LB M Q B))) := ⟨_, rfl⟩
  have hmemN : ∀ g : GL (Fin n) K, g ∈ N ↔
      ∃ y : Lgen M (LB M Q B), (y : G) ∈ Lgen M (LB M Q A) ∧ φ y = g := by
    intro g
    rw [hN, Subgroup.mem_map]
    exact ⟨fun ⟨y, hy, hyg⟩ => ⟨y, Subgroup.mem_subgroupOf.mp hy, hyg⟩,
      fun ⟨y, hy, hyg⟩ => ⟨y, Subgroup.mem_subgroupOf.mpr hy, hyg⟩⟩
  obtain ⟨NS, hNS⟩ : ∃ NS : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      NS = N.comap Matrix.SpecialLinearGroup.toGL := ⟨_, rfl⟩
  have hmemNS : ∀ a : Matrix.SpecialLinearGroup (Fin n) K,
      a ∈ NS ↔ Matrix.SpecialLinearGroup.toGL a ∈ N := by
    intro a
    rw [hNS, Subgroup.mem_comap]
  have hNSn : NS.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hmemNS] at hx ⊢
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hgen g)
    obtain ⟨y, hy, hyx⟩ := (hmemN _).mp hx
    have key : φ (s * y * s⁻¹) = φ s * φ y * (φ s)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [map_mul, map_mul, map_inv, ← hs, ← hyx, ← key, hmemN]
    exact ⟨s * y * s⁻¹, hnorm _ s.2 _ hy, rfl⟩
  have htL' : φ ⟨t, htL⟩ ≠ 1 := by
    intro h1
    apply htQ
    have h2 : (⟨t, htL⟩ : ↥(Lgen M (LB M Q B))) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have htsq : φ ⟨t, htL⟩ * φ ⟨t, htL⟩ = 1 := by
    rw [← map_mul]
    have h2 : (⟨t, htL⟩ * ⟨t, htL⟩ : ↥(Lgen M (LB M Q B))) ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact htt
    exact MonoidHom.mem_ker.mp h2
  obtain ⟨a, ha⟩ := hsurj (φ ⟨t, htL⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have haNS : a ∈ NS := by
    rw [hmemNS, ha]
    exact (hmemN _).mpr ⟨⟨t, htL⟩, ht', rfl⟩
  have hncent : a ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro hac
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hac
    have ha2 : a * a = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_mul, ha, map_one]
      exact htsq
    have hmat : (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) = 1 :=
      congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) ha2
    rw [← hr] at hmat
    have hone : Matrix.scalar (Fin n) r = 1 := scalar_eq_one_of_sq_eq_one (by omega) hmat
    apply htL'
    rw [← ha]
    apply Units.ext
    show (a : Matrix (Fin n) (Fin n) K) = 1
    exact hr.symm.trans hone
  have hNStop : NS = ⊤ := by
    haveI := hNSn
    exact CFSG.LieType.SeitzGeneration.eq_top_of_normal_of_not_mem_center hn haNS hncent
  refine le_antisymm hle ?_
  intro g hg
  obtain ⟨h, hh⟩ := hsurj (φ ⟨g, hg⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hhN : h ∈ NS := by
    rw [hNStop]
    exact Subgroup.mem_top h
  have hhN' : Matrix.SpecialLinearGroup.toGL h ∈ N := (hmemNS h).mp hhN
  rw [hh, hmemN] at hhN'
  obtain ⟨y, hyA, hy⟩ := hhN'
  have hk : y⁻¹ * (⟨g, hg⟩ : ↥(Lgen M (LB M Q B))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hmul : (y : G) * ((y⁻¹ * (⟨g, hg⟩ : ↥(Lgen M (LB M Q B))) : ↥(Lgen M (LB M Q B))) : G)
      ∈ Lgen M (LB M Q A) :=
    (Lgen M (LB M Q A)).mul_mem hyA (hQL hk)
  simpa using hmul

private theorem linSetup_of_Lgen_eq {A : Subgroup G} (hS : LinSetup M Q Z B n V₁ V₂)
    (h : Lgen M (LB M Q A) = Lgen M (LB M Q B)) : LinSetup M Q Z A n V₁ V₂ := by
  unfold LinSetup at hS ⊢
  rw [h]
  exact hS

theorem LinSetup.of_conj_of_le (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A) (hAV : A ≤ V₁ ∨ A ≤ V₂) :
    LinSetup M Q Z A n V₁ V₂ := by
  rcases hAV with hAV | hAV
  · exact linSetup_of_Lgen_eq hS (LinSetup.Lgen_eq_of_le_V₁ hc hS hn hA hAV)
  · exact (linSetup_of_Lgen_eq hS.symm (LinSetup.Lgen_eq_of_le_V₁ hc hS.symm hn hA hAV)).symm

end CFSG.RankThree.GF2n.Smith81
