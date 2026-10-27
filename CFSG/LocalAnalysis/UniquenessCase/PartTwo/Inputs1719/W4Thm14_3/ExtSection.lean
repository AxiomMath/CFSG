module

public import CFSG.Quasithin.Background.SmithB45L2Class
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Cohom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Bridge
public import CFSG.Quasithin.Background.D216Restrict
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Bridge.Rep
public import CFSG.Quasithin.Background.B15P4Layer2Trans
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.QuasithinUnique.Setup.Layer
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

@[expose] def dualSectionMap {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {M : Type} [AddCommGroup M]
    (θ : Sec I (I ⊓ fixV L) ≃* Multiplicative M) : ↥I →* Multiplicative M :=
  θ.toMonoidHom.comp (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I))

theorem dualSectionMap_surjective {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {M : Type} [AddCommGroup M]
    (θ : Sec I (I ⊓ fixV L) ≃* Multiplicative M) :
    Function.Surjective (dualSectionMap θ) := by
  intro x
  obtain ⟨y, hy⟩ := θ.surjective x
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective ((I ⊓ fixV L).subgroupOf I) y
  refine ⟨w, ?_⟩
  show θ (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I) w) = x
  rw [hw, hy]

theorem dualSectionMap_eq_one_iff {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {M : Type} [AddCommGroup M]
    (θ : Sec I (I ⊓ fixV L) ≃* Multiplicative M) (w : ↥I) :
    dualSectionMap θ w = 1 ↔ (w : W) ∈ I ⊓ fixV L := by
  constructor
  · intro h
    have hθ : θ (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I) w) = 1 := h
    have h1 : QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I) w = 1 :=
      θ.injective (by rw [hθ, map_one])
    rw [← Subgroup.mem_subgroupOf, ← QuotientGroup.ker_mk' ((I ⊓ fixV L).subgroupOf I)]
    exact MonoidHom.mem_ker.mpr h1
  · intro h
    have h1 : w ∈ (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I)).ker := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.mem_subgroupOf.mpr h
    show θ (QuotientGroup.mk' ((I ⊓ fixV L).subgroupOf I) w) = 1
    rw [MonoidHom.mem_ker.mp h1, map_one]

theorem exists_dual_cocycle_section_of_mulEquiv {X : Type} [Group X] {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : I ∈ irrSet L) (hIC : I ⊓ fixV L ≠ ⊥) (hLW : L ≤ stabSub I)
    (hLC : L ≤ stabSub (I ⊓ fixV L)) (hfaith : L ⊓ centSec I (I ⊓ fixV L) = ⊥)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (θ : Sec I (I ⊓ fixV L) ≃* Multiplicative M)
    (θL : ↥(autSec L I (I ⊓ fixV L)) ≃* X) :
    ∃ c : X → Module.Dual (ZMod 2) M,
      c ∈ Z1 (CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ
        θL.symm.toMonoidHom).dual ∧
      c ∉ B1 (CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ
        θL.symm.toMonoidHom).dual := by
  classical
  let I₀ : Subgroup W := I ⊓ fixV L
  let Z : Subgroup ↥I := I₀.subgroupOf I
  let ρQ : Representation (ZMod 2) X M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ θL.symm.toMonoidHom
  let φ : X ≃* ↥L := θL.symm.trans (B5.secEquiv L hLW hLC hfaith).symm
  let H : Subgroup (MulAut ↥I) := autSub L I
  let π : X →* ↥H :=
    { toFun := fun g => ⟨(resHom I) (Subgroup.inclusion hLW (φ g)),
        mem_autSub.mpr ⟨Subgroup.inclusion hLW (φ g), (φ g).2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        simp [map_mul] }
  have hπ : Function.Surjective π := by
    rintro ⟨h, hh⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.mp hh
    let l : ↥L := ⟨(g : MulAut W), hgL⟩
    refine ⟨φ.symm l, ?_⟩
    apply Subtype.ext
    change (resHom I) (Subgroup.inclusion hLW (φ (φ.symm l))) = h
    rw [MulEquiv.apply_symm_apply]
    have hgl : Subgroup.inclusion hLW l = g := Subtype.ext rfl
    rw [hgl, hg]
  have hZH : Z ≤ fixV H := by
    intro z hz
    change z ∈ fixV (autSub L I)
    rw [mem_fixV_autSub]
    intro g hg _
    have hz' : (z : W) ∈ I₀ := Subgroup.mem_subgroupOf.mp hz
    exact mem_fixV.mp hz'.2 g hg
  have hcommH : commV H = ⊤ := by
    change commV (autSub L I) = ⊤
    apply Subgroup.map_injective (f := I.subtype) I.subtype_injective
    rw [← commSub_eq_map_commV hLW, hI.1, Subgroup.map_top, Subgroup.range_subtype]
  let β : ↥I →* Multiplicative M := dualSectionMap θ
  have hβs : Function.Surjective β := dualSectionMap_surjective θ
  have hβk : ∀ w : ↥I, β w = 1 ↔ w ∈ Z := by
    intro w
    rw [dualSectionMap_eq_one_iff θ]
    exact Subgroup.mem_subgroupOf.symm
  have hβe : ∀ (γ : X) (w : ↥I),
      β ((π γ : MulAut ↥I) w) =
        Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β w))) := by
    intro γ w
    have hsymm : (((θL.symm.toMonoidHom γ : ↥(autSec L I I₀))) : MulAut (Sec I I₀)) =
        B5.secHom L hLW hLC (φ γ) := by
      have h1 : (B5.secEquiv L hLW hLC hfaith) (φ γ) = θL.symm γ := by
        show (B5.secEquiv L hLW hLC hfaith)
          ((B5.secEquiv L hLW hLC hfaith).symm (θL.symm γ)) = θL.symm γ
        rw [MulEquiv.apply_symm_apply]
      calc ↑(θL.symm.toMonoidHom γ)
          = ↑(θL.symm γ) := rfl
        _ = ↑((B5.secEquiv L hLW hLC hfaith) (φ γ)) := by rw [h1]
        _ = B5.secHom L hLW hLC (φ γ) :=
          B5.secEquiv_apply L hLW hLC hfaith (φ γ)
    have hsec : B5.secHom L hLW hLC (φ γ) (QuotientGroup.mk' Z w) =
        QuotientGroup.mk' Z ((resHom I) (Subgroup.inclusion hLW (φ γ)) w) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, B5.secHom_mk]
      rfl
    have hR : ρQ γ (Multiplicative.toAdd (β w)) =
        Multiplicative.toAdd
          (θ (B5.secHom L hLW hLC (φ γ) (QuotientGroup.mk' Z w))) := by
      rw [show ρQ = CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ
          θL.symm.toMonoidHom from rfl,
        CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf_apply, hsymm]
      rw [show β w = θ (QuotientGroup.mk' Z w) from rfl]
      exact B15P4.binPsi_apply_toAdd θ (B5.secHom L hLW hLC (φ γ)) (QuotientGroup.mk' Z w)
    show θ (QuotientGroup.mk' Z ((resHom I) (Subgroup.inclusion hLW (φ γ)) w)) =
      Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β w)))
    rw [hR]
    show θ (QuotientGroup.mk' Z ((resHom I) (Subgroup.inclusion hLW (φ γ)) w)) =
      θ (B5.secHom L hLW hLC (φ γ) (QuotientGroup.mk' Z w))
    rw [hsec]
  have hexp : ∀ w : ↥I, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW (w : W))
  obtain ⟨M', hM'add, hM'mod, hM'fin, θM, ρM, q, hqsurj, hqρ, hqZ, hperf, hθM, hqker⟩ :=
    s16sp_module_data_of_cover hexp hZH hcommH π hπ ρQ β hβs hβk hβe
  letI : AddCommGroup M' := hM'add
  letI : Module (ZMod 2) M' := hM'mod
  letI : Finite M' := hM'fin
  obtain ⟨⟨zW, hzI0⟩, hzWne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIC
  let z : ↥I := ⟨zW, hzI0.1⟩
  have hzZ : z ∈ Z := Subgroup.mem_subgroupOf.mpr hzI0
  have hzMne : Multiplicative.toAdd (θM z) ≠ 0 := by
    intro h
    have h1 : θM z = 1 := by
      have := congrArg Multiplicative.ofAdd h
      simpa using this
    have h2 : z = 1 := θM.injective (by simpa using h1)
    exact hzWne (Subtype.ext (congrArg (fun x : ↥I => (x : W)) h2))
  have hzmod : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hex : ∃ ψ : M' →ₗ[ZMod 2] ZMod 2, ψ (Multiplicative.toAdd (θM z)) = 1 := by
    by_contra h
    have h0 : ∀ ψ : M' →ₗ[ZMod 2] ZMod 2, ψ (Multiplicative.toAdd (θM z)) = 0 := by
      intro ψ
      rcases hzmod (ψ (Multiplicative.toAdd (θM z))) with hz' | hz'
      · exact hz'
      · exact absurd ⟨ψ, hz'⟩ h
    exact hzMne ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp h0)
  obtain ⟨ψ, hψz⟩ := hex
  haveI : Module.Free (ZMod 2) M' := Module.Free.of_divisionRing _ _
  obtain ⟨s, hs⟩ :=
    LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.mpr hqsurj)
  have hsq : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  refine ⟨extCocycle ρM ρQ s ψ, ?_, ?_⟩
  · exact s16sp_extCocycle_mem ρM ρQ q s hqρ hsq hqZ ψ
  · exact s16sp_extCocycle_not_mem_B1 ρM ρQ q s hqρ hsq hqZ hperf ψ
      ((hqker z).mpr hzZ) hψz

theorem exists_dual_cocycle_section {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet L)
    (hIC : I ⊓ fixV L ≠ ⊥) (hLW : L ≤ stabSub I) (hLC : L ≤ stabSub (I ⊓ fixV L))
    (hfaith : L ⊓ centSec I (I ⊓ fixV L) = ⊥) {F : Type} [Field F] (φ : ↥L ≃* SL(2, F))
    {Wb : Type} [AddCommGroup Wb] [Module (ZMod 2) Wb]
    (θ : Sec I (I ⊓ fixV L) ≃* Multiplicative Wb) :
    ∃ c : SL(2, F) → Module.Dual (ZMod 2) Wb,
      c ∈ Z1 (B45L2.repOf θ ((B5.secEquiv L hLW hLC hfaith).symm.trans φ)).dual ∧
      c ∉ B1 (B45L2.repOf θ ((B5.secEquiv L hLW hLC hfaith).symm.trans φ)).dual := by
  classical
  let θL : ↥(autSec L I (I ⊓ fixV L)) ≃* SL(2, F) :=
    (B5.secEquiv L hLW hLC hfaith).symm.trans φ
  obtain ⟨c, hc, hnc⟩ :=
    exists_dual_cocycle_section_of_mulEquiv hW hI hIC hLW hLC hfaith θ θL
  have hrep : CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.repOf θ θL.symm.toMonoidHom =
      B45L2.repOf θ θL := by
    refine DFunLike.ext _ _ fun g => ?_
    ext w
    rfl
  exact ⟨c, by rwa [hrep] at hc, by rwa [hrep] at hnc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
