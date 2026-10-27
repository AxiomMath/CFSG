module

public import CFSG.Quasithin.Vol2.Ch7Table
public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {I : Subgroup G} {t x : G} :
    x ∈ CFSG.conjugate I t ↔ t * x * t⁻¹ ∈ I := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change t * (t⁻¹ * y * t⁻¹⁻¹) * t⁻¹ ∈ I
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨t * x * t⁻¹, h, ?_⟩
    change t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x
    group

@[expose] def intSub {V : Subgroup G} (hV : IsElemAbelian 2 V) (J : Subgroup G) :
    Subgroup (IntMod V hV) where
  carrier := {v | v.val ∈ J}
  mul_mem' := fun {a b} ha hb => by
    change (a * b).val ∈ J
    rw [IntMod.val_mul]
    exact J.mul_mem ha hb
  one_mem' := by
    change (1 : IntMod V hV).val ∈ J
    rw [IntMod.val_one]
    exact J.one_mem
  inv_mem' := fun {a} ha => by
    change (a⁻¹).val ∈ J
    rw [IntMod.val_inv]
    exact J.inv_mem ha

theorem mem_intSub {V : Subgroup G} {hV : IsElemAbelian 2 V} {J : Subgroup G}
    {v : IntMod V hV} : v ∈ intSub hV J ↔ v.val ∈ J := Iff.rfl

@[expose] def valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem valHom_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (valHom hV) := IntMod.val_injective

theorem map_valHom_intSub {V : Subgroup G} (hV : IsElemAbelian 2 V) {J : Subgroup G}
    (hJ : J ≤ V) : (intSub hV J).map (valHom hV) = J := by
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hg
    exact ⟨IntMod.mk hV ⟨g, hJ hg⟩, hg, rfl⟩

theorem map_valHom_top {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    (⊤ : Subgroup (IntMod V hV)).map (valHom hV) = V := by
  ext g
  constructor
  · rintro ⟨v, -, rfl⟩
    exact v.val_mem
  · intro hg
    exact ⟨IntMod.mk hV ⟨g, hg⟩, trivial, rfl⟩

theorem isXSectionIso_of_isoMod {V : Subgroup G} (hV : IsElemAbelian 2 V) {X Y J K : Subgroup G}
    (hJ : J ≤ V) (hK : K ≤ V) (hXY : X ≤ Y) (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (h : Pair.IsoMod (autI hV Y) (intSub hV J) (intSub hV K)) :
    IsXSectionIso X ⊥ J K := by
  obtain ⟨e, he⟩ := h
  let iJ : ↥J ≃* ↥(intSub hV J) :=
    { toFun := fun j => ⟨IntMod.mk hV ⟨j, hJ j.2⟩, j.2⟩
      invFun := fun w => ⟨(w : IntMod V hV).val, w.2⟩
      left_inv := fun j => rfl
      right_inv := fun w => rfl
      map_mul' := fun a b => rfl }
  let iK : ↥K ≃* ↥(intSub hV K) :=
    { toFun := fun k => ⟨IntMod.mk hV ⟨k, hK k.2⟩, k.2⟩
      invFun := fun w => ⟨(w : IntMod V hV).val, w.2⟩
      left_inv := fun k => rfl
      right_inv := fun w => rfl
      map_mul' := fun a b => rfl }
  let f : ↥J ≃* ↥K := (iJ.trans e).trans iK.symm
  have hf : ∀ j : ↥J, ((f j : ↥K) : G) = ((e (iJ j) : ↥(intSub hV K)) : IntMod V hV).val :=
    fun j => rfl
  let qJ : ↥J ⧸ (⊥ : Subgroup G).subgroupOf J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf J)).trans QuotientGroup.quotientBot
  let qK : ↥K ⧸ (⊥ : Subgroup G).subgroupOf K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf K)).trans QuotientGroup.quotientBot
  have hqJ : ∀ j : ↥J, qJ (j : ↥J ⧸ (⊥ : Subgroup G).subgroupOf J) = j := fun j => rfl
  have hqK : ∀ k : ↥K, qK (k : ↥K ⧸ (⊥ : Subgroup G).subgroupOf K) = k := fun k => rfl
  refine ⟨inferInstance, inferInstance, qJ.trans (f.trans qK.symm), fun x hx j k hj hk hjk => ?_⟩
  have hjk' : f j = k := by
    have := congrArg qK hjk
    simpa [hqJ, hqK] using this
  set g := convI hV ⟨x, hXN hx⟩ with hg
  have hgY : g ∈ autI hV Y := convI_mem_autI hV (hXY hx) (hXN hx)
  have hgv : ∀ v : IntMod V hV, (g v).val = x * v.val * x⁻¹ := fun v => convI_apply_val hV _ v
  have hgJ : g ((iJ j : ↥(intSub hV J)) : IntMod V hV) ∈ intSub hV J := by
    rw [mem_intSub, hgv]
    exact hj
  have h1 := he g hgY (iJ j) hgJ
  have h4 : iJ ⟨x * j * x⁻¹, hj⟩ = ⟨g ((iJ j : ↥(intSub hV J)) : IntMod V hV), hgJ⟩ := by
    apply Subtype.ext
    apply IntMod.val_injective
    change x * (j : G) * x⁻¹ = (g ((iJ j : ↥(intSub hV J)) : IntMod V hV)).val
    rw [hgv]
    rfl
  have h2 : f ⟨x * j * x⁻¹, hj⟩ = ⟨x * k * x⁻¹, hk⟩ := by
    apply Subtype.ext
    rw [hf, h4, h1, hgv, ← hf, hjk']
  change qK.symm (f (qJ ((⟨x * j * x⁻¹, hj⟩ : ↥J) : ↥J ⧸ (⊥ : Subgroup G).subgroupOf J))) = _
  rw [hqJ, h2]
  rfl

theorem stmt7_2_1_SL3Pair : Stmt7_2_1_SL3Pair := by
  intro G _ _ T L I hyp hV hN hNM hc n hn2 hrow
  obtain ⟨⟨t, htT, hsup, hinf, hniso⟩, hnat⟩ := hrow
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) y).mp (hIV hy)
    simpa [mul_assoc] using this
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := hTV (T.inv_mem htT)
  set φ := convI hV ⟨t⁻¹, htN⟩ with hφ
  set V₁ : Subgroup (IntMod (fsuV T I) hV) := intSub hV I with hV₁
  have hL : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) V₁ ⊥ 3 n := hnat
  have hmap : V₁.map φ.toMonoidHom = intSub hV (CFSG.conjugate I t) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_intSub]
      change (φ v).val ∈ CFSG.conjugate I t
      rw [hφ, convI_apply_val, mem_conjugate_iff']
      have : t * (t⁻¹ * v.val * t⁻¹⁻¹) * t⁻¹ = v.val := by group
      rw [this]
      exact hv
    · intro hx
      rw [mem_intSub] at hx
      have hx' := mem_conjugate_iff'.mp hx
      refine ⟨IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩, hx', ?_⟩
      apply IntMod.val_injective
      change (φ (IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩)).val = x.val
      rw [hφ, convI_apply_val]
      change t⁻¹ * (t * x.val * t⁻¹) * t⁻¹⁻¹ = x.val
      group
  have hφN : φ ∈ Subgroup.normalizer (autI hV (fsuL0 T L) :
      Set (MulAut (IntMod (fsuV T I) hV))) :=
    autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) htN)
  have hinf' : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥ := by
    rw [hmap, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : x.val ∈ I ⊓ CFSG.conjugate I t := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact IntMod.val_injective this
  have hsup' : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤ := by
    rw [hmap]
    apply Subgroup.map_injective (valHom_injective hV)
    rw [Subgroup.map_sup, hV₁, map_valHom_intSub hV hIV, map_valHom_intSub hV hItV, hsup,
      map_valHom_top]
  have hniso' : ¬ Pair.IsoMod (autI hV (fsuL0 T L)) V₁ (V₁.map φ.toMonoidHom) := by
    rw [hmap]
    intro h
    exact hniso (isXSectionIso_of_isoMod hV hIV hItV (le_fsuL0 T L)
      ((le_fsuL0 T L).trans (le_sup_left.trans hN)) h)
  obtain ⟨h1, -, h3, h4⟩ := SL3Pair.H4_1_SL3Pair hn2 hL hφN hinf' hsup' hniso'
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)
  exact ⟨h1, h4 (hypBang_autI hyp.fsu hV), h3⟩

theorem stmt7_5_2_of_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h734 : Stmt7_3_4) (h741 : Stmt7_4_1)
    (hM22 : Stmt7_2_1_M22Hat) : Stmt7_5_2 :=
  stmt7_5_2_of_rows h37 h38 h39 hmod h711 h734 h741 hM22 stmt7_2_1_SL3Pair

end CFSG.Quasithin.H13
