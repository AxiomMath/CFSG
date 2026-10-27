module

public import CFSG.Quasithin.Background.B610TwoOff

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F]

theorem burnsideB610_commutator_cjSub {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (L : Subgroup G) : ⁅V, cjSub g L⁆ = cjSub g ⁅V, L⁆ := by
  have hVg : V.map (MulAut.conj g).toMonoidHom = V := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  unfold cjSub
  rw [Subgroup.map_commutator, hVg]

@[expose] noncomputable def burnsideB610_conjInvHom (g : G) (L : Subgroup G) :
    ↥(cjSub g L) →* ↥L :=
  ((MulAut.conj g⁻¹).toMonoidHom.comp (cjSub g L).subtype).codRestrict L fun x => by
    have h := mem_cjSub.mp x.2
    simpa [MulAut.conj_apply] using h

theorem burnsideB610_coe_conjInvHom (g : G) (L : Subgroup G) (x : ↥(cjSub g L)) :
    ((burnsideB610_conjInvHom g L x : ↥L) : G) = g⁻¹ * x * g := by
  simp [burnsideB610_conjInvHom, MulAut.conj_apply]

theorem burnsideB610_conjInvHom_surjective (g : G) (L : Subgroup G) :
    Function.Surjective (burnsideB610_conjInvHom g L) := by
  intro l
  refine ⟨⟨g * l * g⁻¹, mem_cjSub.mpr (by simpa [mul_assoc] using l.2)⟩, Subtype.ext ?_⟩
  rw [burnsideB610_coe_conjInvHom]
  group

@[expose] noncomputable def burnsideB610_natConj (D : NatData L V F) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) : NatData (cjSub g L) V F where
  α := D.α.comp (burnsideB610_conjInvHom g L)
  surj := D.surj.comp (burnsideB610_conjInvHom_surjective g L)
  ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, D.ker]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, burnsideB610_coe_conjInvHom]
    have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      B6.le_normalizer_centralizer le_rfl hg
    constructor
    · rintro ⟨-, hc⟩
      refine ⟨x.2, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hgC (g⁻¹ * x * g)).mp hc
      simpa [mul_assoc] using this
    · rintro ⟨-, hc⟩
      refine ⟨mem_cjSub.mp x.2, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G)).inv_mem hgC) x).mp hc
      simpa [mul_assoc] using this
  β := D.β.comp
    (((MulAut.conj g⁻¹).toMonoidHom.comp ⁅V, cjSub g L⁆.subtype).codRestrict ⁅V, L⁆ fun w => by
      have h : (w : G) ∈ cjSub g ⁅V, L⁆ := by
        rw [← burnsideB610_commutator_cjSub hg]
        exact w.2
      rw [mem_cjSub] at h
      simpa [MulAut.conj_apply] using h)
  βsurj := by
    refine D.βsurj.comp fun w => ?_
    refine ⟨⟨g * w * g⁻¹, ?_⟩, Subtype.ext ?_⟩
    · rw [burnsideB610_commutator_cjSub hg, mem_cjSub]
      simpa [mul_assoc] using w.2
    · simp [MulAut.conj_apply, mul_assoc]
  βker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, D.βker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨-, hc⟩
      refine ⟨w.2, ?_⟩
      have hc' : g⁻¹ * (w : G) * g ∈ Subgroup.centralizer (L : Set G) := hc
      show (w : G) ∈ Subgroup.centralizer ((cjSub g L : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff] at hc' ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ L := mem_cjSub.mp hy
      have := hc' _ hy'
      have := congrArg (fun z => g * z * g⁻¹) this
      simpa [mul_assoc] using this
    · rintro ⟨-, hc⟩
      refine ⟨by
        have h : (w : G) ∈ cjSub g ⁅V, L⁆ := by
          rw [← burnsideB610_commutator_cjSub hg]
          exact w.2
        exact mem_cjSub.mp h, ?_⟩
      have hc' : (w : G) ∈ Subgroup.centralizer ((cjSub g L : Subgroup G) : Set G) := hc
      show g⁻¹ * (w : G) * g ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff] at hc' ⊢
      intro l hl
      have hl' : g * l * g⁻¹ ∈ cjSub g L := mem_cjSub.mpr (by simpa [mul_assoc] using hl)
      have := hc' _ hl'
      have := congrArg (fun z => g⁻¹ * z * g) this
      simpa [mul_assoc] using this
  βeq := by
    intro a u v huv
    simp only [MonoidHom.comp_apply]
    apply D.βeq
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_inv,
      burnsideB610_coe_conjInvHom]
    rw [huv, Subgroup.coe_inv]
    group


theorem burnsideB610_exists_psi (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ ψ : ↥(StatedSL 2 F) →* MulAut (IntMod V hV), Function.Injective ψ ∧
      ψ.range = autI hV L ∧ ∀ l : ↥L, ψ (D.α l) = convI hV ⟨l, hLV l.2⟩ := by
  set π : ↥L →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hLV) with hπ
  have hker : D.α.ker = π.ker := by
    ext l
    rw [D.ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hπ, MonoidHom.comp_apply,
      convI_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective D.α D.surj
  let ψ : ↥(StatedSL 2 F) →* MulAut (IntMod V hV) :=
    ((QuotientGroup.kerLift π).comp (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom).comp
      e.symm.toMonoidHom
  have hψα : ∀ l, ψ (D.α l) = π l := by
    intro l
    have h1 : e.symm (D.α l) = (QuotientGroup.mk l : ↥L ⧸ D.α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.kerLift π (QuotientGroup.quotientMulEquivOfEq hker (e.symm (D.α l))) = _
    rw [h1]
    rfl
  refine ⟨ψ, ?_, ?_, fun l => hψα l⟩
  · exact (QuotientGroup.kerLift_injective π).comp
      ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp e.symm.injective)
  · ext φ
    rw [mem_autI hV, MonoidHom.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨l, rfl⟩ := D.surj z
      exact ⟨Subgroup.inclusion hLV l, l.2, (hψα l).symm⟩
    · rintro ⟨g, hgL, rfl⟩
      refine ⟨D.α ⟨g, hgL⟩, ?_⟩
      rw [hψα]
      rfl

theorem burnsideB610_commutator_sup_centralizing {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G)) :
    ⁅V, L ⊔ C⁆ = ⁅V, L⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl le_sup_left)
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hx' : x ∈ ((L ⊔ C : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hx'
  obtain ⟨l, hl, c, hc, rfl⟩ := hx'
  have hcv : c * v⁻¹ = v⁻¹ * c :=
    (Subgroup.mem_centralizer_iff.mp (hCV hc) v⁻¹ (V.inv_mem hv)).symm
  have : ⁅v, l * c⁆ = ⁅v, l⁆ := by
    simp only [commutatorElement_def, mul_inv_rev]
    calc v * (l * c) * v⁻¹ * (c⁻¹ * l⁻¹) = v * l * (c * v⁻¹) * c⁻¹ * l⁻¹ := by group
      _ = v * l * (v⁻¹ * c) * c⁻¹ * l⁻¹ := by rw [hcv]
      _ = v * l * v⁻¹ * l⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator hv hl

@[expose] noncomputable def burnsideB610_psi (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ↥(StatedSL 2 F) →* MulAut (IntMod V hV) :=
  (burnsideB610_exists_psi D hV hLV).choose

theorem burnsideB610_psi_injective (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Injective (burnsideB610_psi D hV hLV) :=
  (burnsideB610_exists_psi D hV hLV).choose_spec.1

theorem burnsideB610_psi_range (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    (burnsideB610_psi D hV hLV).range = autI hV L :=
  (burnsideB610_exists_psi D hV hLV).choose_spec.2.1

theorem burnsideB610_psi_apply (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) :
    burnsideB610_psi D hV hLV (D.α l) = convI hV ⟨l, hLV l.2⟩ :=
  (burnsideB610_exists_psi D hV hLV).choose_spec.2.2 l

section Ext

theorem burnsideB610_sup_le_normalizer (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {C : Subgroup G} (hCV : C ≤ Subgroup.centralizer (V : Set G)) :
    L ⊔ C ≤ Subgroup.normalizer (V : Set G) :=
  sup_le hLV (hCV.trans (Subgroup.centralizer_le_normalizer _))

theorem burnsideB610_convI_mem_range (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G))
    (x : ↥(L ⊔ C)) :
    convI hV ⟨x, burnsideB610_sup_le_normalizer hLV hCV x.2⟩ ∈
      (burnsideB610_psi D hV hLV).range := by
  rw [burnsideB610_psi_range]
  have hx' : (x : G) ∈ ((L ⊔ C : Subgroup G) : Set G) := x.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hx'
  obtain ⟨l, hl, c, hc, hlc⟩ := hx'
  refine (mem_autI hV).2 ⟨⟨l, hLV hl⟩, hl, ?_⟩
  have h1 : convI hV ⟨c, hCV.trans (Subgroup.centralizer_le_normalizer _) hc⟩ = 1 :=
    (convI_eq_one_iff hV _).2 (hCV hc)
  have h2 : (⟨x, burnsideB610_sup_le_normalizer hLV hCV x.2⟩ :
      ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hLV hl⟩ * ⟨c, hCV.trans (Subgroup.centralizer_le_normalizer _) hc⟩ :=
    Subtype.ext hlc.symm
  rw [h2, map_mul, h1, mul_one]

@[expose] noncomputable def burnsideB610_extHom (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G)) :
    ↥(L ⊔ C) →* ↥(StatedSL 2 F) :=
  (MonoidHom.ofInjective (burnsideB610_psi_injective D hV hLV)).symm.toMonoidHom.comp
    (((convI hV).comp (Subgroup.inclusion (burnsideB610_sup_le_normalizer hLV hCV))).codRestrict
      (burnsideB610_psi D hV hLV).range (burnsideB610_convI_mem_range D hV hLV hCV hLC))

theorem burnsideB610_psi_extHom (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G))
    (x : ↥(L ⊔ C)) :
    burnsideB610_psi D hV hLV (burnsideB610_extHom D hV hLV hCV hLC x) =
      convI hV ⟨x, burnsideB610_sup_le_normalizer hLV hCV x.2⟩ := by
  have h := (MonoidHom.ofInjective (burnsideB610_psi_injective D hV hLV)).apply_symm_apply
    ⟨_, burnsideB610_convI_mem_range D hV hLV hCV hLC x⟩
  exact congrArg Subtype.val h

theorem burnsideB610_extHom_eq (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G))
    (x : ↥(L ⊔ C)) (l : ↥L) {c : G} (hc : c ∈ C)
    (hx : (x : G) = l * c) : burnsideB610_extHom D hV hLV hCV hLC x = D.α l := by
  apply burnsideB610_psi_injective D hV hLV
  rw [burnsideB610_psi_extHom, burnsideB610_psi_apply]
  have h1 : convI hV ⟨c, hCV.trans (Subgroup.centralizer_le_normalizer _) hc⟩ = 1 :=
    (convI_eq_one_iff hV _).2 (hCV hc)
  have h2 : (⟨x, burnsideB610_sup_le_normalizer hLV hCV x.2⟩ :
      ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hLV l.2⟩ * ⟨c, hCV.trans (Subgroup.centralizer_le_normalizer _) hc⟩ := Subtype.ext hx
  rw [h2, map_mul, h1, mul_one]

@[expose] noncomputable def burnsideB610_natExt (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Subgroup G}
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hLC : L ≤ Subgroup.normalizer (C : Set G)) :
    NatData (L ⊔ C) V F where
  α := burnsideB610_extHom D hV hLV hCV hLC
  surj := by
    intro γ
    obtain ⟨l, rfl⟩ := D.surj γ
    exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, burnsideB610_extHom_eq D hV hLV hCV hLC _ l C.one_mem
      (by simp)⟩
  ker := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 := burnsideB610_psi_extHom D hV hLV hCV hLC x
      rw [h, map_one] at h1
      exact ⟨x.2, (convI_eq_one_iff hV _).1 h1.symm⟩
    · rintro ⟨-, h⟩
      apply burnsideB610_psi_injective D hV hLV
      rw [burnsideB610_psi_extHom, map_one]
      exact (convI_eq_one_iff hV _).2 h
  β := D.β.comp (MulEquiv.subgroupCongr (burnsideB610_commutator_sup_centralizing hCV hLC)).toMonoidHom
  βsurj := D.βsurj.comp
    (MulEquiv.subgroupCongr (burnsideB610_commutator_sup_centralizing hCV hLC)).surjective
  βker := by
    have he1 := burnsideB610_commutator_sup_centralizing (V := V) hCV hLC
    have hL₀V := burnsideB610_sup_le_normalizer hLV hCV
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, D.βker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_apply, Subgroup.mem_inf]
    have hwV : (w : G) ∈ V := (Subgroup.le_normalizer_iff_commutator_le_left.mp hL₀V) w.2
    constructor
    · rintro ⟨-, hc⟩
      refine ⟨w.2, ?_⟩
      have hc' : (w : G) ∈ Subgroup.centralizer (L : Set G) := hc
      show (w : G) ∈ Subgroup.centralizer ((L ⊔ C : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff] at hc' ⊢
      intro x hx
      have hx' : x ∈ ((L ⊔ C : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hx'
      obtain ⟨l, hl, c, hc, rfl⟩ := hx'
      have h1 := hc' l hl
      have h2 : c * (w : G) = w * c :=
        (Subgroup.mem_centralizer_iff.mp (hCV hc) w hwV).symm
      calc l * c * (w : G) = l * (c * w) := by group
        _ = l * (w * c) := by rw [h2]
        _ = (l * w) * c := by group
        _ = (w * l) * c := by rw [h1]
        _ = w * (l * c) := by group
    · rintro ⟨-, hc⟩
      refine ⟨by rw [← he1]; exact w.2, ?_⟩
      have hc' : (w : G) ∈ Subgroup.centralizer ((L ⊔ C : Subgroup G) : Set G) := hc
      exact Subgroup.centralizer_le (le_sup_left : L ≤ L ⊔ C) hc'
  βeq := by
    have he1 := burnsideB610_commutator_sup_centralizing (V := V) hCV hLC
    have hL₀V := burnsideB610_sup_le_normalizer hLV hCV
    intro a u v huv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have ha' : (a : G) ∈ ((L ⊔ C : Subgroup G) : Set G) := a.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at ha'
    obtain ⟨l, hl, c, hc, hlc⟩ := ha'
    have huV : (u : G) ∈ V := (Subgroup.le_normalizer_iff_commutator_le_left.mp hL₀V) u.2
    have hcu : c * (u : G) * c⁻¹ = u := by
      rw [(Subgroup.mem_centralizer_iff.mp (hCV hc) u huV).symm, mul_inv_cancel_right]
    have hv : ((MulEquiv.subgroupCongr he1 v : ↥⁅V, L⁆) : G) =
        (⟨l, hl⟩ : ↥L) * (MulEquiv.subgroupCongr he1 u : ↥⁅V, L⁆) * ((⟨l, hl⟩ : ↥L) : G)⁻¹ := by
      simp only [MulEquiv.subgroupCongr_apply]
      rw [huv]
      have hlc' : (a : G) = l * c := hlc.symm
      rw [Subgroup.coe_inv, hlc']
      calc l * c * (u : G) * (l * c)⁻¹ = l * (c * u * c⁻¹) * l⁻¹ := by group
        _ = l * u * l⁻¹ := by rw [hcu]
    rw [D.βeq ⟨l, hl⟩ _ _ hv, burnsideB610_extHom_eq D hV hLV hCV hLC a ⟨l, hl⟩ hc hlc.symm]

end Ext

end CFSG.Quasithin.B610T
