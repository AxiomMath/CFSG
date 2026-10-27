module

public import CFSG.RankThree.Holt.Basic
public import CFSG.Timmesfeld.Closure.MinCex
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.Holt

open CFSG.RankThree.PartTwo.Sec21 CFSG.Timmesfeld.Connectivity

variable {G : Type*} [Group G]

theorem isNormalSet_conjugatesOf (z : G) : IsNormalSet (conjugatesOf z) := fun g x hx =>
  (show IsConj z x from hx).trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem mem_compStab_of_reach {z t : G} (ht : Reach (conjugatesOf z) z t) :
    t ∈ compStab (isNormalSet_conjugatesOf z) z := by
  rw [mem_compStab_iff]
  have h1 := reach_conj (isNormalSet_conjugatesOf z) t ht
  rw [show t * t * t⁻¹ = t by group] at h1
  exact reach_trans ht (reach_symm h1)

theorem reach_of_mem_compStab_of_twoCentral [Finite G] {z : G} (hz : orderOf z = 2)
    (hS : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Subgroup.centralizer {z})
    {t : G} (hzt : IsConj z t) (htM : t ∈ compStab (isNormalSet_conjugatesOf z) z) :
    Reach (conjugatesOf z) z t := by
  obtain ⟨S, -, hSc⟩ := hS
  set M := compStab (isNormalSet_conjugatesOf z) z
  have hSM : (S : Subgroup G) ≤ M := by
    intro s hs
    rw [mem_compStab_iff]
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hSc hs)
    rw [hsz, mul_inv_cancel_right]
    exact reach_refl z
  let t' : M := ⟨t, htM⟩
  have htord : orderOf t' = 2 := by
    rw [Subgroup.orderOf_mk, ← hz]
    obtain ⟨c, rfl⟩ := isConj_iff.mp hzt
    simpa [MulAut.conj_apply] using (MulAut.conj c).orderOf_eq z
  have hP0 : IsPGroup 2 (Subgroup.zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord, pow_one])
  obtain ⟨P, hP⟩ := hP0.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P (S.subtype hSM)
  have htP : t' ∈ (P : Subgroup M) := hP (Subgroup.mem_zpowers t')
  have hmt : MulAut.conj m • t' ∈ ((S.subtype hSM : Sylow 2 M) : Subgroup M) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul t' (MulAut.conj m) _ htP
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmt
  have hmt' : (m : G) * t * (m : G)⁻¹ ∈ (S : Subgroup G) := by
    simpa [MulAut.smul_def, MulAut.conj_apply, t'] using hmt
  have hreach : Reach (conjugatesOf z) z ((m : G) * t * (m : G)⁻¹) :=
    reach_of_commute (mem_conjugatesOf_self) (isNormalSet_conjugatesOf z m t hzt)
      (Subgroup.mem_centralizer_singleton_iff.mp (hSc hmt')).symm
  have hm' : (m : G)⁻¹ ∈ M := M.inv_mem m.2
  have h1 := reach_conj (isNormalSet_conjugatesOf z) (m : G)⁻¹ hreach
  rw [show (m : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) * (m : G)⁻¹⁻¹ = t by group] at h1
  exact reach_trans ((mem_compStab_iff _).mp hm') h1

theorem conj_mem_compStab_iff [Finite G] {z : G} (hz : orderOf z = 2)
    (hS : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (g : G) : g⁻¹ * z * g ∈ compStab (isNormalSet_conjugatesOf z) z ↔
      g ∈ compStab (isNormalSet_conjugatesOf z) z := by
  have hconj : IsConj z (g⁻¹ * z * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  constructor
  · intro ht
    have h := reach_of_mem_compStab_of_twoCentral hz hS hconj ht
    have hinv : g⁻¹ ∈ compStab (isNormalSet_conjugatesOf z) z := by
      rw [mem_compStab_iff, inv_inv]
      exact h
    simpa using Subgroup.inv_mem _ hinv
  · intro hg
    apply mem_compStab_of_reach
    have hinv := Subgroup.inv_mem _ hg
    rw [mem_compStab_iff, inv_inv] at hinv
    exact hinv

theorem holt_commutingComponent (hHolt : HoltUniqueFixedPointSimple) {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) {z : X}
    (hz : orderOf z = 2)
    (hS : ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Subgroup.centralizer {z})
    (hdis : ∃ t : X, IsConj z t ∧ ¬ Reach (conjugatesOf z) z t) :
    (∃ M : Subgroup X, CFSG.IsStronglyEmbedded M) ∨
      ∃ n : ℕ, Odd n ∧ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  have hM : compStab (isNormalSet_conjugatesOf z) z ≠ ⊤ := by
    obtain ⟨t, hzt, htD⟩ := hdis
    obtain ⟨c, rfl⟩ := isConj_iff.mp hzt
    intro htop
    have hmem : c ∈ compStab (isNormalSet_conjugatesOf z) z := htop ▸ Subgroup.mem_top c
    exact htD ((mem_compStab_iff _).mp hmem)
  have hfix := uniqueFixed_iff.mpr (conj_mem_compStab_iff hz hS)
  exact hHolt X hnonab _ hM z hz hS (existsUnique_fixed_of_uniqueFixed hfix)

end CFSG.RankThree.Holt
