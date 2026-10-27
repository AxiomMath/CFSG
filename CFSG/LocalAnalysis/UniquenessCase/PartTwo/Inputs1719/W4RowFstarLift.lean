module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.SmithB45ExcHSRuLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.B45Exc.HSRu
  CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem mem_of_mem_centralizer_of_fstar_eq {G : Type} [Group G] [Finite G] {Y L : Subgroup G}
    (hLY : L ≤ Y) (hF : Fstar Y = L) {y : G} (hy : y ∈ Y)
    (hc : y ∈ Subgroup.centralizer (L : Set G)) : y ∈ L := by
  let yY : ↥Y := ⟨y, hy⟩
  have hsub : L.subgroupOf Y = CFSG.Open.genFittingFStar ↥Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hLY]
    exact hF.symm
  have hcY : yY ∈ Subgroup.centralizer (L.subgroupOf Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hc (z : G) (Subgroup.mem_subgroupOf.mp hz)
  rw [hsub] at hcY
  have hgF : yY ∈ CFSG.Open.genFittingFStar ↥Y :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le ↥Y hcY
  have hg' : y ∈ Fstar Y := Subgroup.mem_map_of_mem Y.subtype hgF
  simpa [hF] using hg'

variable {W : Type} [CommGroup W] [Finite W]

theorem actS_injective_of_fstar {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L)
    (hperf : Group.IsPerfect ↥L) (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {S : Type} [Group S] (e : CQ L ≃* S) (hcent : Subgroup.center ↥L = ⊥) :
    Function.Injective (actS hY e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ Y)
      (normal_sup_of_le_normalizer hY) x = 1 := by
    rw [actS_apply] at hx
    exact (MulAut.congr e).injective (by rw [hx, map_one])
  have h2 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y)
    (normal_sup_of_le_normalizer hY) hperf x).1 h1
  have hxY : (x : MulAut W) ∈ Y := le_of_eq (sup_eq_right.mpr hLY) x.2
  have hxL : (x : MulAut W) ∈ L := mem_of_mem_centralizer_of_fstar_eq hLY hF hxY h2
  have h4 : (⟨(x : MulAut W), hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)
  rw [hcent, Subgroup.mem_bot] at h4
  have h5 : (x : MulAut W) = 1 := Subtype.ext_iff.1 h4
  exact Subtype.ext h5

noncomputable def liftOfFstar {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L)
    (hperf : Group.IsPerfect ↥L) (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {S : Type} [Group S] (e : CQ L ≃* S) (hcent : Subgroup.center ↥L = ⊥) {G : Type*} [Group G]
    {R P : Subgroup G} (hPR : P ≤ R) (Φ : ↥R ≃* MulAut S) (θ : S ≃* ↥P)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hPR (θ s).2⟩ = MulAut.conj s) : Lift L Y R P where
  hom := Φ.symm.toMonoidHom.comp (actS hY e)
  inj := Φ.symm.injective.comp (actS_injective_of_fstar hLY hF hperf hY e hcent)
  mem_iff := by
    have hact := actS_injective_of_fstar hLY hF hperf hY e hcent
    have hval : ∀ l : ↥L, Φ.symm (actS hY e ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩) =
        ⟨(θ (redHom L e l) : G), hPR (θ (redHom L e l)).2⟩ := by
      intro l
      rw [actS_of_mem hY e l, MulEquiv.symm_apply_eq, hΦ]
    intro x
    constructor
    · intro hx
      set s := θ.symm ⟨_, hx⟩ with hs
      obtain ⟨l, hl⟩ := redHom_surjective L e s
      have h1 : Φ.symm (actS hY e x) = Φ.symm (actS hY e ⟨(l : MulAut W),
          Subgroup.mem_sup_left l.2⟩) := by
        rw [hval, hl, hs, MulEquiv.apply_symm_apply]
        rfl
      have h2 := hact (Φ.symm.injective h1)
      rw [h2]
      exact l.2
    · intro hx
      have := hval ⟨_, hx⟩
      show ((Φ.symm (actS hY e x) : ↥R) : G) ∈ P
      have hxe : x = ⟨((⟨_, hx⟩ : ↥L) : MulAut W), Subgroup.mem_sup_left hx⟩ := rfl
      rw [hxe, this]
      exact (θ _).2
  surj := by
    intro p hp
    obtain ⟨l, hl⟩ := redHom_surjective L e (θ.symm ⟨p, hp⟩)
    refine ⟨⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩, l.2, ?_⟩
    show ((Φ.symm (actS hY e ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩) : ↥R) : G) = p
    rw [actS_of_mem hY e l, hl]
    have : Φ.symm (MulAut.conj (θ.symm ⟨p, hp⟩)) = ⟨p, hPR hp⟩ := by
      rw [MulEquiv.symm_apply_eq, ← hΦ]
      congr 1
      apply Subtype.ext
      simp
    rw [this]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
