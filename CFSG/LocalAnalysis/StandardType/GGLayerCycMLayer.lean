module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycMLie
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicCover

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace LayerCycM

@[expose] def GGLayerLieTwo (p : ℕ) {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  α ≠ 1 → α ^ p = 1 → IsComponentOf (LargeEvenLayer (ggFix α)) (ggFix α) →
    LieTwoModel (↥(LargeEvenLayer (ggFix α)) ⧸ Subgroup.center ↥(LargeEvenLayer (ggFix α)))

theorem ggModelLayerCyclic_of_layerLieTwo (hG : CFSG.Open.GriessAllModelsStatement) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] {α : MulAut Y}
    (h : GGLayerLieTwo p α) : GGModelLayerCyclic p α := by
  intro hα1 hαp hcomp S hSE hSC hSp
  have hX := h hα1 hαp hcomp
  have hEq : CFSG.IsQuasisimple (LargeEvenLayer (ggFix α)) :=
    (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hperf : commutator ↥(LargeEvenLayer (ggFix α)) = ⊤ := by
    haveI := hEq.1
    exact Group.IsPerfect.commutator_eq_top
  have hS' : S.subgroupOf (LargeEvenLayer (ggFix α)) ≤
      Subgroup.center ↥(LargeEvenLayer (ggFix α)) := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hSC hs) (g : Y) g.2
  have hSp' : IsPGroup p (S.subgroupOf (LargeEvenLayer (ggFix α))) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSE).symm
  haveI : IsCyclic (S.subgroupOf (LargeEvenLayer (ggFix α))) :=
    isCyclic_of_le_center_of_lieTwoModel hG hperf hp hp2 hX hS' hSp'
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSE)
    (Subgroup.subgroupOfEquivOfLe hSE).surjective

section CenterQuot

variable {K G : Type*} [Group K] [Group G]

theorem center_eq_map_center_of_perfect (ψ : K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) (hperf : commutator K = ⊤) :
    Subgroup.center G = (Subgroup.center K).map ψ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, rfl⟩ := hsurj g
    refine ⟨x, ?_, rfl⟩
    show x ∈ Subgroup.center K
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 : ∀ y ∈ (⊤ : Subgroup K), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K := by
      intro y _
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h2 := Subgroup.mem_center_iff.mp hg (ψ y)
      calc ψ x * ψ y * (ψ x)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ x) * (ψ x)⁻¹ * (ψ y)⁻¹ := by rw [h2]
        _ = 1 := by group
    have hk : k ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
      rw [← _root_.commutator_def, hperf]
      exact Subgroup.mem_top k
    exact (TableBSymp.commute_of_mem_commutator h1 hk).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := hsurj y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']

noncomputable def centerQuotientEquiv (ψ : K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K)
    (hZ : Subgroup.center G = (Subgroup.center K).map ψ) :
    K ⧸ Subgroup.center K ≃* G ⧸ Subgroup.center G := by
  have hcomp : Function.Surjective ((QuotientGroup.mk' (Subgroup.center G)).comp ψ) :=
    (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerc : ((QuotientGroup.mk' (Subgroup.center G)).comp ψ).ker = Subgroup.center K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ,
      Subgroup.comap_map_eq_self (by simpa using hker)]
  exact (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)

end CenterQuot

theorem GGLayerLieTwo.of_central_surjective {p : ℕ} {L R : Type} [Group L] [Group R]
    (ψ : L →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    {a : MulAut L} {φ : MulAut R} (hφ : ∀ l, ψ (a l) = φ (ψ l)) (hne : a ≠ 1 → φ ≠ 1)
    (h : GGLayerLieTwo p φ) : GGLayerLieTwo p a := by
  intro ha1 hap hcomp
  have hφp : φ ^ p = 1 := LayerCC.eq_one_of_comp_eq hψ fun l => by
    rw [← LayerCC.map_pow_apply hφ p l, hap, MulAut.one_apply]
  have hEmap := LayerCC.map_largeEvenLayer_ggFix hψ hker hφ
  have hcompR : IsComponentOf (LargeEvenLayer (ggFix φ)) (ggFix φ) := by
    have := LayerCC.isComponentOf_map_ggFix hψ hker hφ hcomp
    rwa [hEmap] at this
  have hX := h (hne ha1) hφp hcompR
  have hEq : CFSG.IsQuasisimple (LargeEvenLayer (ggFix a)) :=
    (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hperfE : commutator ↥(LargeEvenLayer (ggFix a)) = ⊤ := by
    haveI := hEq.1
    exact Group.IsPerfect.commutator_eq_top
  let ψE : ↥(LargeEvenLayer (ggFix a)) →* ↥(LargeEvenLayer (ggFix φ)) :=
    (MulEquiv.subgroupCongr hEmap).toMonoidHom.comp (ψ.subgroupMap (LargeEvenLayer (ggFix a)))
  have hψE : Function.Surjective ψE :=
    (MulEquiv.surjective (MulEquiv.subgroupCongr hEmap)).comp
      (ψ.subgroupMap_surjective (LargeEvenLayer (ggFix a)))
  have hkerE : ψE.ker ≤ Subgroup.center ↥(LargeEvenLayer (ggFix a)) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : ψ (x : L) = 1 := by simpa [ψE] using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx1)) y)
  exact LieTwoModel.of_mulEquiv
    (centerQuotientEquiv ψE hψE hkerE
      (center_eq_map_center_of_perfect ψE hψE hkerE hperfE)).symm hX

theorem ne_one_of_injective {L R : Type} [Group L] [Group R] {ψ : L →* R}
    (hψ : Function.Injective ψ) {a : MulAut L} {φ : MulAut R} (hφ : ∀ l, ψ (a l) = φ (ψ l)) :
    a ≠ 1 → φ ≠ 1 := by
  intro ha hφ1
  apply ha
  ext l
  apply hψ
  rw [hφ, hφ1, MulAut.one_apply, MulAut.one_apply]

theorem ggLayerCenterCyclic_of_layerLieTwo (hG : CFSG.Open.GriessAllModelsStatement) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ φ ∈ I, GGLayerLieTwo p φ) : GGLayerCenterCyclic p R I := by
  intro L' _ _ ψ hψ hker hperf _ a ha1 hap hind hcomp S hSK hSC hSp
  obtain ⟨φ, hφI, hφ⟩ := hind
  have hne : a ≠ 1 → φ ≠ 1 := fun ha hφ1 =>
    ha (LayerCC.eq_one_of_map_eq hker hperf fun l => by rw [← hφ, hφ1, MulAut.one_apply])
  have hlie := GGLayerLieTwo.of_central_surjective ψ hψ hker (fun l => (hφ l).symm) hne
    (h φ hφI)
  exact ggModelLayerCyclic_of_layerLieTwo hG hp hp2 hlie ha1 hap hcomp S hSK hSC hSp

end LayerCycM

end CFSG.StandardType

end
