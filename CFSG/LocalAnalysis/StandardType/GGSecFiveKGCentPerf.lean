module

public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Steinberg.PartB
public import CFSG.Assembly.Defs
import CFSG.LieType.CurtisTits.Perfect
import CFSG.LocalAnalysis.StandardType.GGPresentation
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggKGCent_le_of_le_normalizer {G : Type*} [Group G] {J S : Subgroup G}
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hSJ : S ≤ J)
    (hN : J ≤ Subgroup.normalizer (S : Set G)) {a a' : G} (ha : a ∈ S) (ha' : a' ∈ S)
    (hne : a * a' ≠ a' * a) : J ≤ S := by
  have hnorm : (S.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hN g.2) n).mp hn⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups_assembly hJ hnorm with
    h | h
  · exact Subgroup.subgroupOf_eq_top.mp h
  · have hc := Subgroup.mem_center_iff.mp
      (h (show (⟨a, hSJ ha⟩ : ↥J) ∈ S.subgroupOf J from Subgroup.mem_subgroupOf.mpr ha))
      ⟨a', hSJ ha'⟩
    exact absurd (congrArg Subtype.val hc).symm hne

theorem ggKGCent_commutator_eq_top {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    commutator K = ⊤ := by
  refine Group.isPerfect_def.mp
    (CFSG.LieType.CurtisTits.isPerfect_of_rootGroup_single_le_commutator hct ?_ fun i => ?_)
  · intro γ _ h2γ
    exfalso
    rcases (show 2 • γ ∈ roots D.isFiniteType ∅ from hdiv ▸ h2γ) with ⟨w, j, hw⟩ |
      ⟨w, j, hj, -⟩
    · have h : weylAction D.isFiniteType w⁻¹ (2 • γ) = Pi.single j 1 := by
        rw [hw, weylAction_inv_apply_apply]
      rw [map_nsmul] at h
      have hj := congrFun h j
      rw [Pi.smul_apply, Pi.single_eq_same, two_nsmul] at hj
      omega
    · simp at hj
  · intro z hz
    obtain ⟨c, rfl⟩ := ((hE.param _ (single_mem_roots i)).1 z).mp hz
    obtain ⟨φ, -, hφu, -⟩ := hE.rankOne i
    have hle : (commutator (Matrix.SpecialLinearGroup (Fin 2) F)).map φ ≤ commutator K := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rw [← hφu]
    refine hle (Subgroup.mem_map_of_mem φ ?_)
    rw [Matrix.SL2.commutator_eq_top ha hasq]
    exact Subgroup.mem_top _

theorem ggKGCent_eq_one_of_mem_center {K : Type*} [Group K] (hK : commutator K = ⊤)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {y : G} (hy : y ∈ ψ.range)
    (hyc : ∀ g ∈ ψ.range, g * y = y * g) (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨k, rfl⟩ := hy
  have hcen := CFSG.LocalCores.comap_center_eq_of_perfect ⟨hK⟩ ψ.rangeRestrict
    ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  have hk : k ∈ Subgroup.center K := by
    rw [← hcen, Subgroup.mem_comap, Subgroup.mem_center_iff]
    rintro ⟨_, g, rfl⟩
    exact Subtype.ext (hyc _ ⟨g, rfl⟩)
  have hZk : ψ k ^ Nat.card (Subgroup.center K) = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := Subgroup.center K) (x := ⟨k, hk⟩))
    have h' : k ^ Nat.card (Subgroup.center K) = 1 := by
      simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h
    rw [← map_pow, h', map_one]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center K)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
  have h1 := pow_gcd_eq_one.mpr ⟨hyp, hZk⟩
  rwa [hcop.gcd_eq_one, pow_one] at h1

end CFSG.StandardType

end
