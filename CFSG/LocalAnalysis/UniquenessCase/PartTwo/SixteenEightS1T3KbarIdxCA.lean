module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3InvA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

abbrev s16t3_U (L : Subgroup (MulAut W)) (J : Subgroup W) : Type :=
  ↥J ⧸ (J ⊓ fixV L).subgroupOf J

@[expose] def s16t3_PreservesFix (L : Subgroup (MulAut W)) {J J' : Subgroup W}
    (φ : ↥J ≃* ↥J') : Prop :=
  ∀ u : ↥J, ((φ u : ↥J') : W) ∈ fixV L ↔ (u : W) ∈ fixV L

@[expose] def s16t3_IsEquivariant (L : Subgroup (MulAut W)) {J J' : Subgroup W}
    (φ : ↥J ≃* ↥J') : Prop :=
  ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
    ((φ ⟨l (u : W), hu⟩ : ↥J') : W) * (l ((φ u : ↥J') : W))⁻¹ ∈ fixV L

@[expose] def s16t3_IsSemiConj (L : Subgroup (MulAut W)) (α : MulAut W) {J J' : Subgroup W}
    (φ : ↥J ≃* ↥J') : Prop :=
  ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
    ((φ ⟨l (u : W), hu⟩ : ↥J') : W) * ((α * l * α⁻¹) ((φ u : ↥J') : W))⁻¹ ∈ fixV L

theorem s16t3_mem_map_fixV_iff {L : Subgroup (MulAut W)} {a : MulAut W}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))) (w : W) :
    a w ∈ fixV L ↔ w ∈ fixV L := by
  have hfix := s16t3_inv_map_fixV_normalizer (E := L) ha
  constructor
  · intro h
    rw [← hfix] at h
    obtain ⟨z, hz, hz'⟩ := Subgroup.mem_map.mp h
    rwa [a.injective hz'] at hz
  · intro hw
    rw [← hfix]
    exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩

theorem s16t3_injective_toMonoidHom (a : MulAut W) :
    Function.Injective (a.toMonoidHom : W → W) :=
  fun x y h => a.injective h

theorem s16t3_PreservesFix.trans {L : Subgroup (MulAut W)} {J J' J'' : Subgroup W}
    {φ : ↥J ≃* ↥J'} {ψ : ↥J' ≃* ↥J''} (hφ : s16t3_PreservesFix L φ)
    (hψ : s16t3_PreservesFix L ψ) : s16t3_PreservesFix L (φ.trans ψ) :=
  fun u => (hψ (φ u)).trans (hφ u)

theorem s16t3_PreservesFix.symm {L : Subgroup (MulAut W)} {J J' : Subgroup W}
    {φ : ↥J ≃* ↥J'} (hφ : s16t3_PreservesFix L φ) : s16t3_PreservesFix L φ.symm :=
  fun u => by simpa [MulEquiv.apply_symm_apply] using (hφ (φ.symm u)).symm

@[expose] noncomputable def s16t3_quotOfEquiv (L : Subgroup (MulAut W)) {J J' : Subgroup W}
    (φ : ↥J ≃* ↥J') (hφ : s16t3_PreservesFix L φ) : s16t3_U L J ≃* s16t3_U L J' :=
  QuotientGroup.congr ((J ⊓ fixV L).subgroupOf J) ((J' ⊓ fixV L).subgroupOf J') φ (by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy ⊢
      exact ⟨(φ y).2, (hφ y).2 hy.2⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      refine Subgroup.mem_map.mpr ⟨φ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨(φ.symm x).2, (hφ (φ.symm x)).1 (by simpa using hx.2)⟩)

@[simp]
theorem s16t3_quotOfEquiv_mk {L : Subgroup (MulAut W)} {J J' : Subgroup W}
    (φ : ↥J ≃* ↥J') (hφ : s16t3_PreservesFix L φ) (u : ↥J) :
    s16t3_quotOfEquiv L φ hφ (QuotientGroup.mk u) = QuotientGroup.mk (φ u) := by
  simp only [s16t3_quotOfEquiv, QuotientGroup.congr_mk]

@[expose] noncomputable def s16t3_transport (L : Subgroup (MulAut W)) {a : MulAut W}
    (ha : ∀ w : W, a w ∈ fixV L ↔ w ∈ fixV L) (J : Subgroup W) :
    s16t3_U L J ≃* s16t3_U L (J.map a.toMonoidHom) :=
  s16t3_quotOfEquiv L (Subgroup.equivMapOfInjective J a.toMonoidHom (s16t3_injective_toMonoidHom a))
    (fun u => ha (u : W))

theorem s16t3_equivMapOfInjective_pres {L : Subgroup (MulAut W)} {a : MulAut W}
    (ha : ∀ w : W, a w ∈ fixV L ↔ w ∈ fixV L) (J : Subgroup W) :
    s16t3_PreservesFix L (Subgroup.equivMapOfInjective J a.toMonoidHom
      (s16t3_injective_toMonoidHom a)) :=
  fun u => ha (u : W)

@[simp]
theorem s16t3_transport_mk {L : Subgroup (MulAut W)} {a : MulAut W}
    (ha : ∀ w : W, a w ∈ fixV L ↔ w ∈ fixV L) (J : Subgroup W) (u : ↥J) :
    s16t3_transport L ha J (QuotientGroup.mk u) =
      (QuotientGroup.mk (⟨a (u : W), Subgroup.mem_map_of_mem a.toMonoidHom u.2⟩ :
        ↥(J.map a.toMonoidHom)) : s16t3_U L (J.map a.toMonoidHom)) := by
  convert s16t3_quotOfEquiv_mk (L := L) (J := J) (J' := J.map a.toMonoidHom)
    (Subgroup.equivMapOfInjective J a.toMonoidHom (s16t3_injective_toMonoidHom a))
    (s16t3_equivMapOfInjective_pres ha J) u using 1
  · rfl
  · rfl

theorem s16t3_equivMapOfInjective_semiConj {L : Subgroup (MulAut W)} (a : MulAut W)
    (J : Subgroup W) :
    s16t3_IsSemiConj L a (Subgroup.equivMapOfInjective J a.toMonoidHom
      (s16t3_injective_toMonoidHom a)) := by
  intro l hl u hu
  have h1 : ((Subgroup.equivMapOfInjective J a.toMonoidHom
      (s16t3_injective_toMonoidHom a) ⟨l (u : W), hu⟩ :
      ↥(J.map a.toMonoidHom)) : W) = a (l (u : W)) := rfl
  have h2 : ((a * l * a⁻¹) ((Subgroup.equivMapOfInjective J a.toMonoidHom
      (s16t3_injective_toMonoidHom a) u : ↥(J.map a.toMonoidHom)) : W)) =
      a (l (u : W)) := by
    simp only [MulAut.mul_apply, Subgroup.coe_equivMapOfInjective_apply]
    change a (l (a⁻¹ (a (u : W)))) = a (l (u : W))
    simp only [MulAut.inv_apply_self]
  rw [h1, h2, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem s16t3_IsSemiConj.trans {L : Subgroup (MulAut W)} {α β : MulAut W}
    (hα : α ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hβ : β ∈ Subgroup.normalizer (L : Set (MulAut W)))
    {J J' J'' : Subgroup W} (hJ' : StableUnder L J') {φ : ↥J ≃* ↥J'} {ψ : ↥J' ≃* ↥J''}
    (hZφ : s16t3_PreservesFix L φ) (hZψ : s16t3_PreservesFix L ψ)
    (hφ : s16t3_IsSemiConj L α φ) (hψ : s16t3_IsSemiConj L β ψ) :
    s16t3_IsSemiConj L (β * α) (φ.trans ψ) := by
  intro l hl u hu
  have hl' : α * l * α⁻¹ ∈ L := conj_mem_of_mem_normalizer hα hl
  have hmem : (α * l * α⁻¹) ((φ u : ↥J') : W) ∈ J' := hJ' _ hl' _ (φ u).2
  have hzJ' : ((φ ⟨l (u : W), hu⟩ : ↥J') : W) *
      ((α * l * α⁻¹) ((φ u : ↥J') : W))⁻¹ ∈ J' :=
    J'.mul_mem (φ ⟨l (u : W), hu⟩).2 (J'.inv_mem hmem)
  have h1 : ((ψ (φ ⟨l (u : W), hu⟩) : ↥J'') : W) *
      ((ψ (⟨(α * l * α⁻¹) ((φ u : ↥J') : W), hmem⟩ : ↥J')) : W)⁻¹ ∈ fixV L := by
    have hzZ := hφ l hl u hu
    have hzψ : ((ψ (⟨_, hzJ'⟩ : ↥J') : ↥J'') : W) ∈ fixV L := (hZψ ⟨_, hzJ'⟩).2 hzZ
    have hz' : (⟨_, hzJ'⟩ : ↥J') = φ ⟨l (u : W), hu⟩ *
        (⟨(α * l * α⁻¹) ((φ u : ↥J') : W), hmem⟩ : ↥J')⁻¹ := by
      ext
      simp [div_eq_mul_inv, mul_assoc]
    rw [hz', map_mul, map_inv] at hzψ
    simpa using hzψ
  have hβl : (β * α) * l * (β * α)⁻¹ = β * (α * l * α⁻¹) * β⁻¹ := by group
  have h2 : ((ψ (⟨(α * l * α⁻¹) ((φ u : ↥J') : W), hmem⟩ : ↥J')) : W) *
      (((β * α) * l * (β * α)⁻¹) ((ψ (φ u) : ↥J'') : W))⁻¹ ∈ fixV L := by
    have := hψ (α * l * α⁻¹) hl' (φ u) hmem
    rw [hβl]
    exact this
  have hcomb : ((ψ (φ ⟨l (u : W), hu⟩) : ↥J'') : W) *
      ((ψ (⟨(α * l * α⁻¹) ((φ u : ↥J') : W), hmem⟩ : ↥J')) : W)⁻¹ *
      (((ψ (⟨(α * l * α⁻¹) ((φ u : ↥J') : W), hmem⟩ : ↥J')) : W) *
        ((((β * α) * l * (β * α)⁻¹) ((ψ (φ u) : ↥J'') : W))⁻¹)) ∈ fixV L :=
    Subgroup.mul_mem _ h1 h2
  have hfinal : ((ψ (φ ⟨l (u : W), hu⟩) : ↥J'') : W) *
      ((((β * α) * l * (β * α)⁻¹) ((ψ (φ u) : ↥J'') : W))⁻¹) ∈ fixV L := by
    convert hcomb using 1
    group
  simpa only [MulEquiv.trans_apply] using hfinal

theorem s16t3_IsSemiConj.symm {L : Subgroup (MulAut W)} {α : MulAut W}
    (hα : α ∈ Subgroup.normalizer (L : Set (MulAut W))) {J J' : Subgroup W}
    (hJ : StableUnder L J) {φ : ↥J ≃* ↥J'} (hZφ : s16t3_PreservesFix L φ)
    (hφ : s16t3_IsSemiConj L α φ) : s16t3_IsSemiConj L α⁻¹ φ.symm := by
  intro l hl v hv
  have hl₀ : α⁻¹ * l * α ∈ L := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hα) hl
  have hmem : (α⁻¹ * l * α) ((φ.symm v : ↥J) : W) ∈ J := hJ _ hl₀ _ (φ.symm v).2
  have hαlα : α * (α⁻¹ * l * α) * α⁻¹ = l := by group
  have hvv : (φ (φ.symm v) : ↥J') = v := by simp
  let z : ↥J' := ⟨((φ ⟨(α⁻¹ * l * α) ((φ.symm v : ↥J) : W), hmem⟩ : ↥J') : W) *
      (l ((φ (φ.symm v) : ↥J') : W))⁻¹,
    J'.mul_mem (φ ⟨_, hmem⟩).2 (J'.inv_mem (by rw [hvv]; exact hv))⟩
  have hzZ : (z : W) ∈ fixV L := by
    have h1 := hφ (α⁻¹ * l * α) hl₀ (φ.symm v) hmem
    rw [hαlα] at h1
    exact h1
  have hzψ : ((φ.symm z : ↥J) : W) ∈ fixV L := (hZφ (φ.symm z)).1 (by simpa using hzZ)
  let A' : ↥J' := φ ⟨(α⁻¹ * l * α) ((φ.symm v : ↥J) : W), hmem⟩
  let B' : ↥J' := ⟨l ((φ (φ.symm v) : ↥J') : W), by rw [hvv]; exact hv⟩
  have hzdef : z = A' * B'⁻¹ := by
    apply Subtype.ext
    simp [z, A', B', div_eq_mul_inv]
  have hsub : (φ.symm z : ↥J) = φ.symm A' * (φ.symm B')⁻¹ := by
    rw [hzdef, map_mul, map_inv]
  have hA : (φ.symm A' : ↥J) = ⟨(α⁻¹ * l * α) ((φ.symm v : ↥J) : W), hmem⟩ := by
    apply φ.injective
    simp only [A', MulEquiv.apply_symm_apply]
  have hB : (φ.symm B' : ↥J) = φ.symm ⟨l (v : W), hv⟩ := by
    apply φ.injective
    simp only [B', MulEquiv.apply_symm_apply, Subtype.coe_mk]
  rw [hsub, hA, hB] at hzψ
  simpa [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ hzψ

theorem s16t3_IsEquivariant.trans {L : Subgroup (MulAut W)} {J J' J'' : Subgroup W}
    (hJ' : StableUnder L J') {φ : ↥J ≃* ↥J'} {ψ : ↥J' ≃* ↥J''}
    (hZφ : s16t3_PreservesFix L φ) (hZψ : s16t3_PreservesFix L ψ)
    (hφ : s16t3_IsEquivariant L φ) (hψ : s16t3_IsEquivariant L ψ) :
    s16t3_IsEquivariant L (φ.trans ψ) := by
  have hφ' : s16t3_IsSemiConj L 1 φ := by
    simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using hφ
  have hψ' : s16t3_IsSemiConj L 1 ψ := by
    simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using hψ
  have := s16t3_IsSemiConj.trans (L := L) (α := 1) (β := 1) (one_mem _) (one_mem _) hJ'
    hZφ hZψ hφ' hψ'
  simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using this

theorem s16t3_IsEquivariant.symm {L : Subgroup (MulAut W)} {J J' : Subgroup W}
    (hJ : StableUnder L J) {φ : ↥J ≃* ↥J'} (hZφ : s16t3_PreservesFix L φ)
    (hφ : s16t3_IsEquivariant L φ) : s16t3_IsEquivariant L φ.symm := by
  have hφ' : s16t3_IsSemiConj L 1 φ := by
    simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using hφ
  have := s16t3_IsSemiConj.symm (L := L) (α := 1) (one_mem _) hJ hZφ hφ'
  simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using this

theorem s16t3_commSub_map_conj {U : Subgroup W} {Y : Subgroup (MulAut W)} (a : MulAut W) :
    commSub (U.map a.toMonoidHom) (Y.map (MulAut.conj a).toMonoidHom) =
      (commSub U Y).map a.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj a x₀, ⟨x₀, hx₀, rfl⟩, a w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

theorem s16t3_stableUnder_map {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : StableUnder L J) {a : MulAut W} (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    StableUnder L (J.map a.toMonoidHom) := by
  intro l hl v hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  refine Subgroup.mem_map.mpr ⟨(a⁻¹ * l * a) w,
    hJ _ (inv_conj_mem_of_mem_normalizer ha hl) _ hw, ?_⟩
  simp [MulAut.mul_apply]

theorem s16t3_subgroupCongr_pres {L : Subgroup (MulAut W)} {H K : Subgroup W} (h : H = K) :
    s16t3_PreservesFix L (MulEquiv.subgroupCongr h) := by
  intro u
  simp

theorem s16t3_subgroupCongr_equiv {L : Subgroup (MulAut W)} {H K : Subgroup W} (h : H = K) :
    s16t3_IsEquivariant L (MulEquiv.subgroupCongr h) := by
  intro l hl u hu
  simp only [MulEquiv.subgroupCongr_apply]
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem s16t3_eq_mod_fixV_of_isEquivariant [Finite W] {A L T : Subgroup (MulAut W)}
    (h : ThreeNat A L T)
    {J : Subgroup W} (hJ : J ∈ irrSet L) {J₀ : Subgroup W} (hJ₀ : J₀ ∈ irrSet L)
    {φ ψ : ↥J ≃* ↥J₀} (hZφ : s16t3_PreservesFix L φ) (hφ : s16t3_IsEquivariant L φ)
    (hZψ : s16t3_PreservesFix L ψ) (hψ : s16t3_IsEquivariant L ψ) :
    ∀ u : ↥J, ((φ u : ↥J₀) : W) * ((ψ u : ↥J₀) : W)⁻¹ ∈ fixV L := by
  have hnat : SumOfNatShape L J (J ⊓ fixV L) 1 := h.natural_of_mem_irrSet hJ
  have hstableJ : StableUnder L J := hJ.2.2.1
  have hstableJ₀ : StableUnder L J₀ := hJ₀.2.2.1
  let ρ : ↥J ≃* ↥J := φ.trans ψ.symm
  have hZρ : s16t3_PreservesFix L ρ := s16t3_PreservesFix.trans hZφ (s16t3_PreservesFix.symm hZψ)
  have hρ : s16t3_IsEquivariant L ρ :=
    s16t3_IsEquivariant.trans hstableJ₀ hZφ (s16t3_PreservesFix.symm hZψ) hφ
      (s16t3_IsEquivariant.symm hstableJ hZψ hψ)
  have hZρ' : ∀ u : ↥J, ((ρ u : ↥J) : W) ∈ J ⊓ fixV L ↔ (u : W) ∈ J ⊓ fixV L := by
    intro u
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_right (ρ u).2, and_iff_right u.2]
    exact hZρ u
  have hρ' : ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
      ((ρ ⟨l (u : W), hu⟩ : ↥J) : W) * (l ((ρ u : ↥J) : W))⁻¹ ∈ J ⊓ fixV L := by
    intro l hl u hu
    refine ⟨J.mul_mem (ρ _).2 (J.inv_mem ?_), hρ l hl u hu⟩
    exact hstableJ l hl (ρ u) (ρ u).2
  have hconcl := SumOfNatShape.eq_of_equivariant h.quasi hnat ρ hZρ' hρ'
  intro u
  have hzu : ((ρ u : ↥J) : W) * (u : W)⁻¹ ∈ fixV L := (Subgroup.mem_inf.mp (hconcl u)).2
  have hzJ : ((ρ u : ↥J) : W) * (u : W)⁻¹ ∈ J :=
    J.mul_mem (ρ u).2 (J.inv_mem u.2)
  have hzψ : ((ψ (⟨_, hzJ⟩ : ↥J) : ↥J₀) : W) ∈ fixV L := (hZψ ⟨_, hzJ⟩).2 hzu
  have hsub : (⟨_, hzJ⟩ : ↥J) = ψ.symm (φ u) * u⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ρ, MulEquiv.trans_apply]
  rw [hsub, map_mul, map_inv] at hzψ
  simpa [ρ, MulEquiv.trans_apply] using hzψ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
