module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S34

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

section Frame

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.semisimpleAction
    (d : Data h E f) : SemisimpleAction p A (kOf (θ f)) := by
  have := (Sec6S31.hyp h d.zpowers_mem_rSet).semisimpleAction
  rwa [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one] at this

theorem Data.dZero_eq
    (d : Data h E f) : dZero p A θ = cenIn (kOf (θ f)) A := by
  have := Sec6S31.cenIn_kOf_eq h d.zpowers_mem_rSet
  rw [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one] at this
  exact this.symm

theorem Data.permutes (d : Data h E f) {a : G} (ha : a ∈ A) {J : Subgroup G}
    (hJ : J ∈ lcal (θ f)) : J.map (MulAut.conj a).toMonoidHom ∈ lcal (θ f) :=
  map_conj_mem_lcal hJ (h.hyp.nearFunctor.isFunctor.normalized f d.mem d.ne_one ha)

theorem Data.exists_conj_A
    (d : Data h E f) {J L : Subgroup G} (hJ : J ∈ lcal (θ f))
    (hL : L ∈ lcal (θ f)) : ∃ a ∈ A, L = J.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨e, he, hen⟩ := d.exists_mem_sdiff
  obtain ⟨k, hk⟩ := d.exists_zpow_conj he hen hJ hL
  exact ⟨e ^ k, zpow_mem he k, hk⟩

theorem Data.smear_eq
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    smear L A = dZero p A θ := by
  rw [d.dZero_eq]
  exact smear_eq_centralizer_of_transitive d.isDirectProduct (fun _ ha _ hJ => d.permutes ha hJ)
    hL fun _ hK => d.exists_conj_A hL hK

theorem Data.projIn_dZero
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    projIn (lcal (θ f)) L (dZero p A θ) = cenIn L (norIn A L) := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  have := d.semisimpleAction.projIn_cenIn hL'
  rw [d.lcal_kOf, ← d.dZero_eq] at this
  exact this

theorem Data.projIn_dOne
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    projIn (lcal (θ f)) L (dOne p A θ) = CFSG.fittingSubgroupOf (cenIn L (norIn A L)) := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  have := d.semisimpleAction.projIn_fittingSubgroupOf_smear hL'
  rw [d.lcal_kOf, d.smear_eq hL] at this
  exact this

theorem Data.dZero_inf_sSup
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    dZero p A θ ⊓ sSup (lcal (θ f) \ {L}) = ⊥ := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  have := d.semisimpleAction.smear_inf_sSup hL'
  rw [d.lcal_kOf, d.smear_eq hL] at this
  exact this

end Frame

theorem mem_normalizer_of_conj_mem {P : Subgroup G} {x : G} (h : ∀ y ∈ P, x * y * x⁻¹ ∈ P) :
    x ∈ Subgroup.normalizer (P : Set G) := by
  have hle : P.map (MulAut.conj x).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : P.map (MulAut.conj x).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

section S3

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.mem_sThree_of_mem (d : Data h E f) {x : G} (hx : x ∈ θ f)
    (hxs : x ∈ sectionCentralizer (sOne p A θ) (dZero p A θ ⊔ sOne p A θ)) :
    x ∈ sThree p A θ := by
  have hθ := h.hyp.nearFunctor
  refine ⟨?_, hxs⟩
  set Y : Subgroup G := θ f ⊓ sectionCentralizer (sOne p A θ) (dZero p A θ ⊔ sOne p A θ)
    with hY
  have hAY : Admits A Y :=
    Admits.inf (hθ.isFunctor.normalized f d.mem d.ne_one)
      (Sec6S33.admits_sectionCentralizer (Sec6S33.admits_sOne hθ)
        ((Sec6S33.admits_of_le_dsub hθ Sec6S33.dZero_le_dsub).sup (Sec6S33.admits_sOne hθ)))
  have hYm : Y ∈ assoc p A θ := mem_assoc_of_le hθ.prime d.mtil.1 inf_le_left hAY
  have hYN : Y ≤ Subgroup.normalizer ((dZero p A θ ⊔ sOne p A θ : Subgroup G) : Set G) :=
    fun y hy => (mem_sectionCentralizer_iff.mp hy.2).2.1
  exact (le_iSup₂ (f := fun Y (_ : Y ∈ {Y : Subgroup G | Y ∈ assoc p A θ ∧
    Y ≤ Subgroup.normalizer ((dZero p A θ ⊔ sOne p A θ : Subgroup G) : Set G)}) => Y) Y
    ⟨hYm, hYN⟩ : Y ≤ thetaN p A θ (dZero p A θ ⊔ sOne p A θ)) ⟨hx, hxs⟩


theorem Data.fitting_eq
    (d : Data h E f) :
    CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (θ f)) = sOne p A θ ⊓ θ f := by
  have := h.lemma611 d.zpowers_mem_rSet
  rw [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one, inf_comm (kOf (θ f))] at this
  exact this.symm

theorem Data.sThree_inf_le
    (d : Data h E f) :
    sThree p A θ ⊓ θ f ≤ ssol p A θ ⊓ kOf (θ f) := by
  rintro x ⟨hxS, hxH⟩
  have h67 := h.lemma67c d.zpowers_mem_rSet
  rw [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one, d.fitting_eq] at h67
  obtain ⟨hxN1, hxN2, hxc⟩ := mem_sectionCentralizer_iff.mp hxS.2
  have hxθ : ∀ y ∈ θ f, x * y * x⁻¹ ∈ θ f := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH) y).mp hy
  have hΦ : ∀ y ∈ sOne p A θ ⊓ θ f, x * y * x⁻¹ ∈ sOne p A θ ⊓ θ f := fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hxN1 y).mp hy.1, hxθ y hy.2⟩
  have hDθ : dZero p A θ ≤ θ f := by
    rw [d.dZero_eq]
    exact inf_le_left.trans (kOf_le (θ f))
  have hcomm : ∀ y ∈ dZero p A θ ⊔ (sOne p A θ ⊓ θ f), ⁅x, y⁆ ∈ sOne p A θ ⊓ θ f := by
    intro y hy
    have hy1 : y ∈ dZero p A θ ⊔ sOne p A θ :=
      (sup_le_sup_left (inf_le_left : sOne p A θ ⊓ θ f ≤ sOne p A θ) (dZero p A θ)) hy
    have hy2 : y ∈ θ f := _root_.sup_le hDθ inf_le_right hy
    refine ⟨hxc y hy1, ?_⟩
    simp only [commutatorElement_def]
    exact (θ f).mul_mem ((θ f).mul_mem ((θ f).mul_mem hxH hy2) ((θ f).inv_mem hxH))
      ((θ f).inv_mem hy2)
  have hmem : x ∈ θ f ⊓ sectionCentralizer (sOne p A θ ⊓ θ f)
      (dZero p A θ ⊔ (sOne p A θ ⊓ θ f)) := by
    refine ⟨hxH, mem_sectionCentralizer_iff.mpr ⟨mem_normalizer_of_conj_mem hΦ, ?_, hcomm⟩⟩
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right (hcomm y hy)) hy
  exact h67 hmem


theorem Data.kProd_eq
    (d : Data h E f) :
    kProd A (kOf (θ f)) = ssol p A θ ⊓ kOf (θ f) := by
  have := Sec6S31.mOf_eq h d.zpowers_mem_rSet
  rw [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one] at this
  rw [← d.semisimpleAction.mOf_eq_kProd]
  exact this

theorem Data.fProd_eq
    (d : Data h E f) : fProd A (kOf (θ f)) = sOne p A θ ⊓ θ f := by
  rw [← d.semisimpleAction.fittingSubgroupOf_kProd, d.kProd_eq, d.fitting_eq]

theorem Data.kJ_le
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    kJ A L ≤ ssol p A θ ⊓ kOf (θ f) := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  rw [← d.kProd_eq, ← d.semisimpleAction.kProd_inf hL']
  exact inf_le_left

theorem Data.fitting_kJ_le
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    CFSG.fittingSubgroupOf (kJ A L) ≤ sOne p A θ ⊓ θ f := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  rw [← d.fProd_eq, ← d.semisimpleAction.fProd_inf hL']
  exact inf_le_left

theorem Data.dsub_le_normalizer_dZero
    (d : Data h E f) :
    dsub A θ ≤ Subgroup.normalizer (dZero p A θ : Set G) := by
  have hθ := h.hyp.nearFunctor
  rw [d.dZero_eq]
  have h1 : Admits (dsub A θ) (kOf (θ f)) :=
    (dsub_le_apply d.mem d.ne_one).trans (Thm41Aux.le_normalizer_kOf (θ f))
  have h2 : Admits (dsub A θ) (Subgroup.centralizer (A : Set G)) :=
    (dsub_le_centralizer hθ).trans Subgroup.le_normalizer
  exact Admits.inf h1 h2

theorem Data.dsub_le_normalizer_dOne
    (d : Data h E f) :
    dsub A θ ≤ Subgroup.normalizer (dOne p A θ : Set G) := fun _ hx =>
  mem_normalizer_of_conj_mem fun _ hy =>
    Thm210.fittingSubgroupOf_conj_mem_of_mem_normalizer (d.dsub_le_normalizer_dZero hx) hy

theorem Data.dsub_le_normalizer_sOne
    (d : Data h E f) :
    dsub A θ ≤ Subgroup.normalizer (sOne p A θ : Set G) := by
  have hθ := h.hyp.nearFunctor
  have hD1 := d.dsub_le_normalizer_dOne
  have hmem : dsub A θ ≤ thetaN p A θ (dOne p A θ) :=
    (le_iSup₂ (f := fun Y (_ : Y ∈ {Y : Subgroup G | Y ∈ assoc p A θ ∧
      Y ≤ Subgroup.normalizer (dOne p A θ : Set G)}) => Y) (dsub A θ)
      ⟨dsub_mem_assoc hθ, hD1⟩ : dsub A θ ≤ thetaN p A θ (dOne p A θ))
  exact Admits.inf
    (hmem.trans Subgroup.le_normalizer : Admits (dsub A θ) (thetaN p A θ (dOne p A θ)))
    (Sec6S33.admits_centralizer hD1)


theorem centralizer_fixedFitting_inf_le
    {X : Type*} [Group X] [Finite X] (hp : NearSimple p X)
    {φ : MulAut X} (hφ : orderOf φ = p) :
    Subgroup.centralizer (fixedFitting φ : Set X) ⊓ signalizerFixedSubgroup φ ≤ fixedFitting φ := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple hp hφ
  rintro c ⟨hcZ, hcC⟩
  by_contra hc0
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF.C0_ne_bot
  have hz' : (z : X) ∈ Subgroup.centralizer (fixedFitting φ : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hF.C0_comm.is_comm.comm (⟨y, hy⟩ : fixedFitting φ) z)
  apply hz
  refine Subtype.ext ?_
  have hcz : (c : X) * z = z * c := (Subgroup.mem_centralizer_iff.mp hcZ z z.2).symm
  exact hF.fpf c hcC hc0 z hz' hcz

section Local

variable {Γ : Type u} [Group Γ] [Finite Γ] {A' G' J : Subgroup Γ}

theorem cenIn_fitting_inf_le
    (hK : SemisimpleAction p A' G') (hJ : J ∈ lcal G') :
    cenIn J (CFSG.fittingSubgroupOf (cenIn J (norIn A' J)) : Set Γ) ⊓ cenIn J (norIn A' J) ≤
      CFSG.fittingSubgroupOf (cenIn J (norIn A' J)) := by
  obtain ⟨φ, hφ, hC, hC₀, -, -⟩ := hK.exists_frame_data hJ
  have hNS := hK.nearSimple hJ
  rintro x ⟨⟨hxJ, hxc⟩, hxC⟩
  obtain ⟨c, hc, rfl⟩ : x ∈ (signalizerFixedSubgroup φ).map J.subtype := hC ▸ hxC
  have hcZ : c ∈ Subgroup.centralizer (fixedFitting φ : Set ↥J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : Γ) ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A' J)) := hC₀ ▸ ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (y : Γ) hy')
  have := centralizer_fixedFitting_inf_le hNS hφ ⟨hcZ, hc⟩
  rw [← hC₀]
  exact ⟨c, this, rfl⟩

end Local


theorem Data.cenIn_norIn_eq
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    cenIn L (norIn A L) = L ⊓ thetaOf θ E := by
  have hθ := h.hyp.nearFunctor
  have hEA : E ≤ A := d.distE.mem.1
  have hnor : norIn A L = E ⊔ Subgroup.zpowers f := d.inf_normalizer_eq hL
  have hLθ : L ≤ θ f := lcal_le hL
  ext x
  constructor
  · rintro ⟨hxL, hxc⟩
    refine ⟨hxL, ?_⟩
    rw [hnor] at hxc
    have hxE : x ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hxc
    have hx1 : x ∈ θ f ⊓ Subgroup.centralizer (E : Set G) := ⟨hLθ hxL, hxE⟩
    rw [hθ.isFunctor.inf_centralizer_eq_thetaOf d.mem d.ne_one hEA] at hx1
    exact thetaOf_anti (le_sup_right : E ≤ Subgroup.zpowers f ⊔ E) hx1
  · rintro ⟨hxL, hxE⟩
    refine ⟨hxL, ?_⟩
    rw [hnor, centralizer_sup]
    refine ⟨hθ.isFunctor.thetaOf_le_centralizer hEA hxE, ?_⟩
    rw [centralizer_zpowers_eq_singleton]
    exact hθ.isFunctor.le_centralizer f d.mem d.ne_one (hLθ hxL)


theorem Data.coord_comm
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) {x : G}
    (hxK : x ∈ kOf (θ f)) {a : G} (ha : a ∈ norIn A L) (hax : a * x = x * a) :
    a * ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) =
      ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) * a := by
  have hD := d.isDirectProduct
  have hconj : ∀ J ∈ lcal (θ f), J.map (MulAut.conj a).toMonoidHom ∈ lcal (θ f) :=
    fun J hJ => d.permutes ha.1 hJ
  have hLa : L.map (MulAut.conj a).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ha.2
  have h1 := hD.coord_conj hconj hL hxK
  have hmem : a * x * a⁻¹ ∈ kOf (θ f) := hD.conj_mem hconj hxK
  have h2 := hD.coord_val_congr (hconj L hL) hL hLa ⟨a * x * a⁻¹, hmem⟩
  have h3 : (⟨a * x * a⁻¹, hmem⟩ : ↥(kOf (θ f))) = ⟨x, hxK⟩ :=
    Subtype.ext (show a * x * a⁻¹ = x by rw [hax]; group)
  rw [h3] at h1 h2
  set X : G := ((hD.coord hL ⟨x, hxK⟩ : L) : G) with hX
  have h4 : X = a * X * a⁻¹ := h2.symm.trans h1
  calc a * X = (a * X * a⁻¹) * a := by group
    _ = X * a := by rw [← h4]

theorem Data.commutator_coord_mem
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f))
    {x : G} (hxK : x ∈ kOf (θ f))
    (hxs : x ∈ sectionCentralizer (sOne p A θ) (dZero p A θ ⊔ sOne p A θ))
    (hxC : ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) ∈ cenIn L (norIn A L)) {y : G}
    (hy : y ∈ cenIn L (norIn A L)) :
    ⁅((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G), y⁆ ∈
      CFSG.fittingSubgroupOf (cenIn L (norIn A L)) := by
  have hK := d.semisimpleAction
  have hD := d.isDirectProduct
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  set xL : G := ((hD.coord hL ⟨x, hxK⟩ : L) : G) with hxL
  have hy' : y ∈ projIn (lcal (θ f)) L (dZero p A θ) := by
    rw [d.projIn_dZero hL]
    exact hy
  obtain ⟨d₀, hd₀, hd₀y⟩ := (hD.mem_projIn_iff hL).mp hy'
  have hxs' := (mem_sectionCentralizer_iff.mp hxs).2.2 (d₀ : G) (Subgroup.mem_sup_left hd₀)
  have hzK : ⁅x, (d₀ : G)⁆ ∈ kOf (θ f) :=
    (kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem hxK d₀.2)
      ((kOf (θ f)).inv_mem hxK)) ((kOf (θ f)).inv_mem d₀.2)
  have hzF : ⁅x, (d₀ : G)⁆ ∈ fProd A (kOf (θ f)) := by
    rw [d.fProd_eq]
    exact ⟨hxs', kOf_le _ hzK⟩
  have hc : ((hD.coord hL ⟨⁅x, (d₀ : G)⁆, hzK⟩ : L) : G) = ⁅xL, y⁆ := by
    have : (⟨⁅x, (d₀ : G)⁆, hzK⟩ : ↥(kOf (θ f))) = ⁅(⟨x, hxK⟩ : ↥(kOf (θ f))), d₀⁆ := rfl
    rw [this, map_commutatorElement, ← hd₀y]
    rfl
  have hproj : ((hD.coord hL ⟨⁅x, (d₀ : G)⁆, hzK⟩ : L) : G) ∈
      projIn (lcal (θ f)) L (fProd A (kOf (θ f))) :=
    (hD.mem_projIn_iff hL).mpr ⟨⟨_, hzK⟩, hzF, rfl⟩
  rw [hc] at hproj
  have hle := (hK.le_fProd_iff.mp le_rfl).2 L hL'
  rw [d.lcal_kOf] at hle
  have hz1 : ⁅xL, y⁆ ∈ CFSG.fittingSubgroupOf (kJ A L) := hle hproj
  rw [hK.fittingSubgroupOf_kJ_eq hL'] at hz1
  have hxyC : ⁅xL, y⁆ ∈ cenIn L (norIn A L) := by
    simp only [commutatorElement_def]
    exact (cenIn L (norIn A L)).mul_mem ((cenIn L (norIn A L)).mul_mem
      ((cenIn L (norIn A L)).mul_mem hxC hy) ((cenIn L (norIn A L)).inv_mem hxC))
      ((cenIn L (norIn A L)).inv_mem hy)
  exact cenIn_fitting_inf_le hK hL' ⟨hz1, hxyC⟩

theorem Data.inf_sThree_eq
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    L ⊓ sThree p A θ ⊓ thetaOf θ E =
      cenIn L (norIn A L) ⊓ sectionCentralizer (CFSG.fittingSubgroupOf (cenIn L (norIn A L)))
        (cenIn L (norIn A L)) := by
  have hθ := h.hyp.nearFunctor
  have hK := d.semisimpleAction
  have hD := d.isDirectProduct
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  have hCL := d.cenIn_norIn_eq hL
  apply le_antisymm
  · rintro x ⟨⟨hxL, hxS⟩, hxE⟩
    have hxC : x ∈ cenIn L (norIn A L) := by
      rw [hCL]
      exact ⟨hxL, hxE⟩
    have hxK : x ∈ kOf (θ f) := hD.le hL hxL
    refine ⟨hxC, mem_sectionCentralizer_iff.mpr ⟨Thm210.le_normalizer_fittingSubgroupOf _ hxC,
      Subgroup.le_normalizer hxC, fun y hy => ?_⟩⟩
    have hy' : y ∈ projIn (lcal (θ f)) L (dZero p A θ) := by
      rw [d.projIn_dZero hL]
      exact hy
    obtain ⟨d₀, hd₀, hd₀y⟩ := (hD.mem_projIn_iff hL).mp hy'
    have hxs := (mem_sectionCentralizer_iff.mp hxS.2).2.2 (d₀ : G) (Subgroup.mem_sup_left hd₀)
    have hzK : ⁅x, (d₀ : G)⁆ ∈ kOf (θ f) :=
      (kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem hxK d₀.2)
        ((kOf (θ f)).inv_mem hxK)) ((kOf (θ f)).inv_mem d₀.2)
    have hzF : ⁅x, (d₀ : G)⁆ ∈ fProd A (kOf (θ f)) := by
      rw [d.fProd_eq]
      exact ⟨hxs, kOf_le _ hzK⟩
    have hc : ((hD.coord hL ⟨⁅x, (d₀ : G)⁆, hzK⟩ : L) : G) = ⁅x, y⁆ := by
      have : (⟨⁅x, (d₀ : G)⁆, hzK⟩ : ↥(kOf (θ f))) = ⁅(⟨x, hxK⟩ : ↥(kOf (θ f))), d₀⁆ := rfl
      rw [this, map_commutatorElement]
      have hx1 : hD.coord hL ⟨x, hxK⟩ = ⟨x, hxL⟩ := Subtype.ext (hD.coord_of_mem hL hxL)
      rw [hx1, ← hd₀y]
      rfl
    have hproj : ((hD.coord hL ⟨⁅x, (d₀ : G)⁆, hzK⟩ : L) : G) ∈
        projIn (lcal (θ f)) L (fProd A (kOf (θ f))) :=
      (hD.mem_projIn_iff hL).mpr ⟨⟨_, hzK⟩, hzF, rfl⟩
    rw [hc] at hproj
    have hle := (hK.le_fProd_iff.mp le_rfl).2 L hL'
    rw [d.lcal_kOf] at hle
    have hz1 : ⁅x, y⁆ ∈ CFSG.fittingSubgroupOf (kJ A L) := hle hproj
    rw [hK.fittingSubgroupOf_kJ_eq hL'] at hz1
    have hxyC : ⁅x, y⁆ ∈ cenIn L (norIn A L) := by
      simp only [commutatorElement_def]
      exact (cenIn L (norIn A L)).mul_mem ((cenIn L (norIn A L)).mul_mem
        ((cenIn L (norIn A L)).mul_mem hxC hy) ((cenIn L (norIn A L)).inv_mem hxC))
        ((cenIn L (norIn A L)).inv_mem hy)
    exact cenIn_fitting_inf_le hK hL' ⟨hz1, hxyC⟩
  · rintro x ⟨hxC, hxs'⟩
    have hxHE : x ∈ L ⊓ thetaOf θ E := hCL ▸ hxC
    have hxL : x ∈ L := hxHE.1
    have hxθ : x ∈ θ f := lcal_le hL hxL
    refine ⟨⟨hxL, ?_⟩, hxHE.2⟩
    apply d.mem_sThree_of_mem hxθ
    have hxM : x ∈ ssol p A θ ⊓ kOf (θ f) := d.kJ_le hL (hK.cenIn_norIn_le_kJ hL' hxC)
    have hxN : x ∈ Subgroup.normalizer (sOne p A θ : Set G) := by
      have := h.lemma613 d.zpowers_mem_rSet
      rw [h.hyp.isFunctor.thetaOf_zpowers d.mem d.ne_one] at this
      exact this ⟨hxM.2, hxM.1⟩
    let Y₀ : Subgroup G :=
      { carrier := {y | y ∈ Subgroup.normalizer (sOne p A θ : Set G) ∧ ⁅x, y⁆ ∈ sOne p A θ}
        one_mem' := ⟨one_mem _, by simp [commutatorElement_def]⟩
        mul_mem' := by
          rintro y y' ⟨hy, hxy⟩ ⟨hy', hxy'⟩
          refine ⟨mul_mem hy hy', ?_⟩
          have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (sOne p A θ).mul_mem hxy ((Subgroup.mem_normalizer_iff.mp hy _).mp hxy')
        inv_mem' := by
          rintro y ⟨hy, hxy⟩
          refine ⟨inv_mem hy, ?_⟩
          have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            simp only [commutatorElement_def]
            group
          rw [e]
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) _).mp ((sOne p A θ).inv_mem hxy)
          simpa [mul_assoc] using this }
    have hdZ : dZero p A θ ≤ Y₀ := by
      intro y hy
      have hyK : y ∈ kOf (θ f) := by
        rw [d.dZero_eq] at hy
        exact hy.1
      have hyD : y ∈ dsub A θ := Sec6S33.dZero_le_dsub hy
      refine ⟨d.dsub_le_normalizer_sOne hyD, ?_⟩
      obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute (hD.commute_sSup_diff hL)).mp
        ((hD.isDirectPair hL).sup_eq ▸ hyK)
      have hjC : j ∈ cenIn L (norIn A L) := by
        rw [← d.projIn_dZero hL]
        exact (hD.mem_projIn_iff hL).mpr ⟨⟨j * l, hyK⟩, hy, hD.coord_mul hL hj hl⟩
      have hxl : ⁅x, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (hD.commute_sSup_diff hL x hxL l hl).eq
      have e : ⁅x, j * l⁆ = ⁅x, j⁆ := by
        have : ⁅x, j * l⁆ = ⁅x, j⁆ * (j * ⁅x, l⁆ * j⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this, hxl]
        simp
      show ⁅x, j * l⁆ ∈ sOne p A θ
      rw [e]
      have h1 : ⁅x, j⁆ ∈ CFSG.fittingSubgroupOf (cenIn L (norIn A L)) :=
        (mem_sectionCentralizer_iff.mp hxs').2.2 j hjC
      exact (d.fitting_kJ_le hL (hK.fittingSubgroupOf_cenIn_le_kJ hL' h1)).1
    have hsO : sOne p A θ ≤ Y₀ := fun s hs => by
      refine ⟨Subgroup.le_normalizer hs, ?_⟩
      have : ⁅x, s⁆ = (x * s * x⁻¹) * s⁻¹ := rfl
      rw [this]
      exact (sOne p A θ).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN s).mp hs)
        ((sOne p A θ).inv_mem hs)
    have hle : dZero p A θ ⊔ sOne p A θ ≤ Y₀ := _root_.sup_le hdZ hsO
    refine mem_sectionCentralizer_iff.mpr ⟨hxN, mem_normalizer_of_conj_mem ?_,
      fun y hy => (hle hy).2⟩
    intro y hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (hle hy).2) hy


theorem Data.E_le_norIn
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    E ≤ norIn A L := by
  have : norIn A L = E ⊔ Subgroup.zpowers f := d.inf_normalizer_eq hL
  rw [this]
  exact le_sup_left

theorem Data.coord_mem_cenIn
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) {x : G}
    (hxK : x ∈ kOf (θ f)) (hxE : x ∈ Subgroup.centralizer (E : Set G)) :
    ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) ∈ cenIn L (norIn A L) := by
  have hθ := h.hyp.nearFunctor
  rw [d.cenIn_norIn_eq hL]
  refine ⟨(d.isDirectProduct.coord hL ⟨x, hxK⟩).2, ?_⟩
  have hc : ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) ∈
      Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact d.coord_comm hL hxK (d.E_le_norIn hL he) (Subgroup.mem_centralizer_iff.mp hxE e he)
  have hx1 : ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) ∈
      θ f ⊓ Subgroup.centralizer (E : Set G) :=
    ⟨lcal_le hL (d.isDirectProduct.coord hL ⟨x, hxK⟩).2, hc⟩
  rw [hθ.isFunctor.inf_centralizer_eq_thetaOf d.mem d.ne_one d.distE.mem.1] at hx1
  exact thetaOf_anti (le_sup_right : E ≤ Subgroup.zpowers f ⊔ E) hx1

theorem Data.coord_mem_T
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) {x : G}
    (hxK : x ∈ kOf (θ f)) (hxE : x ∈ Subgroup.centralizer (E : Set G))
    (hxs : x ∈ sectionCentralizer (sOne p A θ) (dZero p A θ ⊔ sOne p A θ)) :
    ((d.isDirectProduct.coord hL ⟨x, hxK⟩ : L) : G) ∈ L ⊓ sThree p A θ ⊓ thetaOf θ E := by
  rw [d.inf_sThree_eq hL]
  have hC := d.coord_mem_cenIn hL hxK hxE
  exact ⟨hC, mem_sectionCentralizer_iff.mpr ⟨Thm210.le_normalizer_fittingSubgroupOf _ hC,
    Subgroup.le_normalizer hC, fun y hy => d.commutator_coord_mem hL hxK hxs hC hy⟩⟩

theorem Data.isDirectProduct_T
    (d : Data h E f) :
    IsDirectProduct {S | ∃ L ∈ lcal (θ f), S = L ⊓ sThree p A θ ⊓ thetaOf θ E}
      (sThree p A θ ⊓ (θ f ⊓ Subgroup.centralizer (E : Set G))) := by
  have hθ := h.hyp.nearFunctor
  have hD := d.isDirectProduct
  have hle : ∀ L : Subgroup G, L ⊓ sThree p A θ ⊓ thetaOf θ E ≤ L := fun L =>
    inf_le_left.trans inf_le_left
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hne x hx y hy
    have hLL : L ≠ L' := fun hh => hne (by rw [hh])
    exact hD.commute L hL L' hL' hLL x (hle L hx) y (hle L' hy)
  · rintro _ ⟨L, hL, rfl⟩
    refine (hD.indep hL).mono_left (hle L) |>.mono_right ?_
    refine sSup_le ?_
    rintro _ ⟨⟨L', hL', rfl⟩, hne⟩
    have hLL : L' ≠ L := fun hh => hne (by rw [hh]; rfl)
    exact (hle L').trans (le_sSup ⟨hL', hLL⟩)
  · apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨L, hL, rfl⟩
      refine le_inf (inf_le_left.trans inf_le_right) (le_inf ((hle L).trans (lcal_le hL)) ?_)
      exact inf_le_right.trans (hθ.isFunctor.thetaOf_le_centralizer d.distE.mem.1)
    · rintro x ⟨hxS, hxθ, hxE⟩
      have hxK : x ∈ kOf (θ f) := (d.sThree_inf_le ⟨hxS, hxθ⟩).2
      refine hD.mem_of_coord_mem hxK fun L hL => ?_
      have hmem : L ⊓ sThree p A θ ⊓ thetaOf θ E ∈
          {S | ∃ L ∈ lcal (θ f), S = L ⊓ sThree p A θ ⊓ thetaOf θ E} := ⟨L, hL, rfl⟩
      exact le_sSup hmem (d.coord_mem_T hL hxK hxE hxS.2)


omit [Finite G] in
theorem fitting_le_c1 (C : Subgroup G) :
    CFSG.fittingSubgroupOf C ≤ C ⊓ sectionCentralizer (CFSG.fittingSubgroupOf C) C := by
  intro x hx
  have hxC : x ∈ C := Subgroup.map_subtype_le _ hx
  refine ⟨hxC, mem_sectionCentralizer_iff.mpr ⟨Thm210.le_normalizer_fittingSubgroupOf C hxC,
    Subgroup.le_normalizer hxC, fun y hy => ?_⟩⟩
  have h1 : y * x⁻¹ * y⁻¹ ∈ CFSG.fittingSubgroupOf C :=
    Thm210.fittingSubgroupOf_conj_mem hy ((CFSG.fittingSubgroupOf C).inv_mem hx)
  have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact (CFSG.fittingSubgroupOf C).mul_mem hx h1

theorem Data.coord_injOn
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) {x y : G}
    (hx : x ∈ dZero p A θ) (hy : y ∈ dZero p A θ) (hxK : x ∈ kOf (θ f)) (hyK : y ∈ kOf (θ f))
    (hxy : d.isDirectProduct.coord hL ⟨x, hxK⟩ = d.isDirectProduct.coord hL ⟨y, hyK⟩) :
    x = y := by
  have hD := d.isDirectProduct
  have h1 : hD.coord hL ⟨x⁻¹ * y, (kOf (θ f)).mul_mem ((kOf (θ f)).inv_mem hxK) hyK⟩ = 1 := by
    have : (⟨x⁻¹ * y, (kOf (θ f)).mul_mem ((kOf (θ f)).inv_mem hxK) hyK⟩ : ↥(kOf (θ f))) =
        (⟨x, hxK⟩ : ↥(kOf (θ f)))⁻¹ * ⟨y, hyK⟩ := rfl
    rw [this, map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 := (hD.coord_eq_one_iff hL _).mp h1
  have h3 : x⁻¹ * y ∈ dZero p A θ ⊓ sSup (lcal (θ f) \ {L}) :=
    ⟨(dZero p A θ).mul_mem ((dZero p A θ).inv_mem hx) hy, h2⟩
  rw [d.dZero_inf_sSup hL, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact h3


theorem Data.dZero_le_kOf
    (d : Data h E f) : dZero p A θ ≤ kOf (θ f) := by
  rw [d.dZero_eq]
  exact inf_le_left

omit [Finite G] in
theorem dOne_le_dZero : dOne p A θ ≤ dZero p A θ := Subgroup.map_subtype_le _

omit [Finite G] in
theorem dTwo_le_dZero : dTwo p A θ ≤ dZero p A θ := inf_le_left

theorem Data.nonempty_mulEquiv_dTwo
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) :
    Nonempty (↥(dTwo p A θ) ≃* ↥(L ⊓ sThree p A θ ⊓ thetaOf θ E)) := by
  have hD := d.isDirectProduct
  have hD2K : dTwo p A θ ≤ kOf (θ f) := dTwo_le_dZero.trans d.dZero_le_kOf
  have hD0K : dZero p A θ ≤ kOf (θ f) := d.dZero_le_kOf
  let ψ : ↥(dTwo p A θ) →* ↥L := (hD.coord hL).comp (Subgroup.inclusion hD2K)
  have hψC : ∀ x : ↥(dTwo p A θ), (ψ x : G) ∈ cenIn L (norIn A L) := by
    intro x
    rw [← d.projIn_dZero hL]
    exact (hD.mem_projIn_iff hL).mpr ⟨⟨x, hD2K x.2⟩, dTwo_le_dZero x.2, rfl⟩
  have hψ : ∀ x : ↥(dTwo p A θ), (ψ x : G) ∈ L ⊓ sThree p A θ ⊓ thetaOf θ E := by
    intro x
    rw [d.inf_sThree_eq hL]
    refine ⟨hψC x, mem_sectionCentralizer_iff.mpr ⟨Thm210.le_normalizer_fittingSubgroupOf _ (hψC x),
      Subgroup.le_normalizer (hψC x), fun y hy => ?_⟩⟩
    have hy' : y ∈ projIn (lcal (θ f)) L (dZero p A θ) := by
      rw [d.projIn_dZero hL]
      exact hy
    obtain ⟨d₀, hd₀, hd₀y⟩ := (hD.mem_projIn_iff hL).mp hy'
    have hxs := (mem_sectionCentralizer_iff.mp x.2.2).2.2 (d₀ : G) hd₀
    have hzK : ⁅(x : G), (d₀ : G)⁆ ∈ kOf (θ f) :=
      (kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem (hD2K x.2) d₀.2)
        ((kOf (θ f)).inv_mem (hD2K x.2))) ((kOf (θ f)).inv_mem d₀.2)
    have hc : ((hD.coord hL ⟨⁅(x : G), (d₀ : G)⁆, hzK⟩ : L) : G) = ⁅(ψ x : G), y⁆ := by
      have : (⟨⁅(x : G), (d₀ : G)⁆, hzK⟩ : ↥(kOf (θ f))) =
          ⁅(⟨x, hD2K x.2⟩ : ↥(kOf (θ f))), d₀⁆ := rfl
      rw [this, map_commutatorElement, ← hd₀y]
      rfl
    have hproj : ((hD.coord hL ⟨⁅(x : G), (d₀ : G)⁆, hzK⟩ : L) : G) ∈
        projIn (lcal (θ f)) L (dOne p A θ) :=
      (hD.mem_projIn_iff hL).mpr ⟨⟨_, hzK⟩, hxs, rfl⟩
    rw [hc, d.projIn_dOne hL] at hproj
    exact hproj
  let Ψ : ↥(dTwo p A θ) →* ↥(L ⊓ sThree p A θ ⊓ thetaOf θ E) :=
    (L.subtype.comp ψ).codRestrict _ hψ
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have h0 := congrArg Subtype.val hxy
    have h1 : ψ x = ψ y := Subtype.ext h0
    exact Subtype.ext (d.coord_injOn hL (dTwo_le_dZero x.2) (dTwo_le_dZero y.2)
      (hD2K x.2) (hD2K y.2) h1)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨c, hc⟩
    have hc' := hc
    rw [d.inf_sThree_eq hL] at hc'
    have hcC : c ∈ projIn (lcal (θ f)) L (dZero p A θ) := by
      rw [d.projIn_dZero hL]
      exact hc'.1
    obtain ⟨d₀, hd₀, hd₀c⟩ := (hD.mem_projIn_iff hL).mp hcC
    have hd₀2 : (d₀ : G) ∈ dTwo p A θ := by
      refine ⟨hd₀, mem_sectionCentralizer_iff.mpr ⟨
        Thm210.le_normalizer_fittingSubgroupOf (dZero p A θ) hd₀,
        Subgroup.le_normalizer hd₀, fun y hy => ?_⟩⟩
      have hyK : y ∈ kOf (θ f) := hD0K hy
      have hyC : ((hD.coord hL ⟨y, hyK⟩ : L) : G) ∈ cenIn L (norIn A L) := by
        rw [← d.projIn_dZero hL]
        exact (hD.mem_projIn_iff hL).mpr ⟨⟨y, hyK⟩, hy, rfl⟩
      have hcom := (mem_sectionCentralizer_iff.mp hc'.2).2.2 _ hyC
      have hzK : ⁅(d₀ : G), y⁆ ∈ kOf (θ f) :=
        (kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem d₀.2 hyK)
          ((kOf (θ f)).inv_mem d₀.2)) ((kOf (θ f)).inv_mem hyK)
      have hzD : ⁅(d₀ : G), y⁆ ∈ dZero p A θ :=
        (dZero p A θ).mul_mem ((dZero p A θ).mul_mem ((dZero p A θ).mul_mem hd₀ hy)
          ((dZero p A θ).inv_mem hd₀)) ((dZero p A θ).inv_mem hy)
      have hc2 : ((hD.coord hL ⟨⁅(d₀ : G), y⁆, hzK⟩ : L) : G) =
          ⁅c, ((hD.coord hL ⟨y, hyK⟩ : L) : G)⁆ := by
        have : (⟨⁅(d₀ : G), y⁆, hzK⟩ : ↥(kOf (θ f))) = ⁅d₀, ⟨y, hyK⟩⁆ := rfl
        rw [this, map_commutatorElement, ← hd₀c]
        rfl
      have hproj : ((hD.coord hL ⟨⁅(d₀ : G), y⁆, hzK⟩ : L) : G) ∈
          projIn (lcal (θ f)) L (dOne p A θ) := by
        rw [hc2, d.projIn_dOne hL]
        exact hcom
      obtain ⟨w, hw, hwc⟩ := (hD.mem_projIn_iff hL).mp hproj
      have hweq : (w : G) = ⁅(d₀ : G), y⁆ := d.coord_injOn hL (dOne_le_dZero hw) hzD w.2 hzK
        (Subtype.ext hwc)
      rw [← hweq]
      exact hw
    exact ⟨⟨(d₀ : G), hd₀2⟩, Subtype.ext hd₀c⟩
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩⟩

theorem Data.dTwo_ne_bot
    (d : Data h E f) : dTwo p A θ ≠ ⊥ := by
  intro hbot
  have hF := d.frobenius.2
  exact hF.1 (le_bot_iff.mp (hF.2.1.trans hbot.le))

theorem Data.nonempty_mulEquiv_pi_dTwo
    (d : Data h E f) :
    Nonempty (↥(sThree p A θ ⊓ (θ f ⊓ Subgroup.centralizer (E : Set G))) ≃*
      (Fin p → ↥(dTwo p A θ))) := by
  classical
  have hT := d.isDirectProduct_T
  have hD := d.isDirectProduct
  obtain ⟨σ⟩ := d.nonempty_equiv_fin
  set 𝒯 : Set (Subgroup G) :=
    {S | ∃ L ∈ lcal (θ f), S = L ⊓ sThree p A θ ⊓ thetaOf θ E} with h𝒯
  let τ : ↥(lcal (θ f)) → ↥𝒯 := fun L => ⟨L.1 ⊓ sThree p A θ ⊓ thetaOf θ E, L.1, L.2, rfl⟩
  have hne : ∀ L : ↥(lcal (θ f)), L.1 ⊓ sThree p A θ ⊓ thetaOf θ E ≠ ⊥ := by
    intro L hbot
    obtain ⟨φ⟩ := d.nonempty_mulEquiv_dTwo L.2
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp d.dTwo_ne_bot
    have hmem : ∀ y : G, y ∈ L.1 ⊓ sThree p A θ ⊓ thetaOf θ E → y = 1 := fun y hy => by
      rw [hbot, Subgroup.mem_bot] at hy
      exact hy
    have h1 : φ x = 1 := Subtype.ext (hmem _ (φ x).2)
    exact hx (φ.injective (h1.trans (map_one φ).symm))
  have hτ : Function.Bijective τ := by
    refine ⟨fun L L' hLL' => ?_, ?_⟩
    · by_contra hne'
      have hTT : L.1 ⊓ sThree p A θ ⊓ thetaOf θ E = L'.1 ⊓ sThree p A θ ⊓ thetaOf θ E :=
        congrArg Subtype.val hLL'
      have hle : L.1 ⊓ sThree p A θ ⊓ thetaOf θ E ≤ L.1 := inf_le_left.trans inf_le_left
      have hle' : L.1 ⊓ sThree p A θ ⊓ thetaOf θ E ≤ sSup (lcal (θ f) \ {L.1}) := by
        rw [hTT]
        exact (inf_le_left.trans inf_le_left).trans (le_sSup ⟨L'.2, fun hh => hne'
          (Subtype.ext hh.symm)⟩)
      have := ((hD.indep L.2).mono hle hle')
      exact hne L (disjoint_self.mp this)
    · rintro ⟨S, L, hL, hS⟩
      exact ⟨⟨L, hL⟩, Subtype.ext hS.symm⟩
  let e : Fin p ≃ ↥𝒯 := σ.trans (Equiv.ofBijective τ hτ)
  have hiso : ∀ i : Fin p, Nonempty (↥(dTwo p A θ) ≃* ↥((e i : ↥𝒯) : Subgroup G)) :=
    fun i => d.nonempty_mulEquiv_dTwo (σ i).2
  obtain ⟨e2⟩ := nonempty_mulEquiv_piCongrLeft (fun J : ↥𝒯 => ↥(J : Subgroup G)) e
  exact ⟨((MulEquiv.piCongrRight fun i => (hiso i).some).trans (e2.trans hT.equiv)).symm⟩

end S3

section Summary

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem DistE.directProduct
    (h : Counterexample p A θ) {E : Subgroup G}
    (hE : DistE p A θ E) :
    ∀ B ∈ signalizerFunctorEk p 2 A, E ≤ B → ∀ F : Subgroup G, IsDirectPair E F B →
      IsDirectProduct {S | ∃ L ∈ lcal (thetaOf θ F), S = L ⊓ sThree p A θ ⊓ thetaOf θ E}
          (sThree p A θ ⊓ thetaOf θ B) ∧
        Nonempty (↥(sThree p A θ ⊓ thetaOf θ B) ≃* (Fin p → ↥(dTwo p A θ))) := by
  intro B hB _ F hdp
  have hθ := h.hyp.nearFunctor
  have hcB : Nat.card B = p ^ 2 := hB.2
  have hcE : Nat.card E = p := by rw [hE.mem.2, pow_one]
  have h1 := card_sup_of_commute hdp.commute hdp.inf_eq_bot
  rw [hdp.sup_eq, hcB, hcE, sq] at h1
  have hcF : Nat.card F = p := (Nat.eq_of_mul_eq_mul_left hθ.prime.pos h1).symm
  have hFne : F ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcF
    exact hθ.prime.one_lt.ne hcF
  obtain ⟨⟨f, hfF⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
  have hfA : f ∈ A := hB.1 (hdp.sup_eq ▸ Subgroup.mem_sup_right hfF)
  have hfE : f ∉ E := fun hfE => by
    have : f ∈ E ⊓ F := ⟨hfE, hfF⟩
    rw [hdp.inf_eq_bot, Subgroup.mem_bot] at this
    exact hf1' this
  have d : Data h E f := ⟨hE, hfA, hfE⟩
  have hFeq : F = Subgroup.zpowers f :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfF)
      (hcF.trans d.card_zpowers.symm).le).symm
  have hBeq : B = E ⊔ Subgroup.zpowers f := hFeq ▸ hdp.sup_eq.symm
  subst hFeq
  subst hBeq
  have e1 : thetaOf θ (Subgroup.zpowers f) = θ f := hθ.isFunctor.thetaOf_zpowers hfA hf1'
  have e2 : thetaOf θ (E ⊔ Subgroup.zpowers f) = θ f ⊓ Subgroup.centralizer (E : Set G) := by
    rw [sup_comm]
    exact (hθ.isFunctor.inf_centralizer_eq_thetaOf hfA hf1' hE.mem.1).symm
  rw [e1, e2]
  exact ⟨d.isDirectProduct_T, d.nonempty_mulEquiv_pi_dTwo⟩

end Summary

end Sec6S34

end CFSG.SignalizerFunctorTheorem.McBride.Near
