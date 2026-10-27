module

public import CFSG.Quasithin.Vol2.Ch10SecKITd
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312SL2Native
public import CFSG.Quasithin.Vol2.Ch10SecQ4A11
public import CFSG.Quasithin.Vol2.Ch10SecQ4A12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF

variable {G : Type} [Group G] [Finite G] {M T L X : Subgroup G} {n : ℕ}

theorem xbar_ne_top {X₁ X₂ : Subgroup G} (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M)
    (hX₁ : X₁ ∈ lFamily T) (hne : X₁ ≠ X₂) (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L)
    (h₁ : IsNatBlock X₁ n) (h₂ : IsNatBlock X₂ n) : modO2Image L X₁ ≠ ⊤ := by
  intro htop
  have hLX : L ≤ X₁ ⊔ pCoreOf 2 L := le_sup_of_xbar_le le_rfl (htop ▸ le_top)
  have hLN : L ≤ Subgroup.normalizer (X₁ : Set G) :=
    hLX.trans (sup_le Subgroup.le_normalizer (pCoreOf_le_normalizer hT hL hX₁ hX₁L))
  have hsub : IsSubnormal X₁ M := A3.subnormal_trans
    (A3.subnormal_of_normal hX₁L ((Subgroup.normal_subgroupOf_iff_le_normalizer hX₁L).mpr hLN))
    (subnormal_of_mem_cComp hL)
  have hX₁' : X₁ ∈ cComp (X₁ ⊔ T) := hX₁
  have heq : X₁ = L := by
    by_contra hne'
    exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hX₁L hne') (ne_bot_of_mem_cComp hX₁')
      (perfect_of_mem_cComp hX₁') hsub
  apply hne
  refine (Subgroup.eq_of_le_of_card_ge (heq ▸ hX₂L) ?_).symm
  rw [h₁.card, h₂.card]

theorem isQuasisimple_Y (h36 : A36ForSQTK) (hM : SQTKGroup ↥M) (hT : IsSylowTwoOf T M)
    (hL : L ∈ cComp M) (hX : X ∈ lFamily T) (hXL : X ≤ L) (h : IsNatBlock X n) (hn : 2 ≤ n) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  set Y := ↥L ⧸ CFSG.pCore 2 ↥L
  have hTs := C10E4.isSylowTwoOf_quot hT hL
  have hB := xbar_mem_lFamily hT hL hX hXL
  have hYc := C10E4.sqtkHypCat_quot (le_of_mem_cComp hL) (SQTKGroup.isSQTKCat hM)
  have h36Y := h36 _ (sqtkHyp_of_cat hYc)
  have hTop := C10E4.top_mem_cComp_quot hL
  by_contra hnq
  have hnq' : ¬ CFSG.IsQuasisimple ↥(⊤ : Subgroup Y) := fun h' =>
    hnq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mp h')
  set OL : Subgroup Y := (CFSG.oddCore ↥(⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype with hOL
  have hsurj : Function.Surjective (⊤ : Subgroup Y).subtype := fun y => ⟨⟨y, trivial⟩, rfl⟩
  have hOLn : OL.Normal := Subgroup.Normal.map inferInstance _ hsurj
  have hdec : ∀ y ∈ modO2Image L X ⊔ OL, ∃ x : ↥X, ∃ o ∈ OL, C10E4.fK hXL x * o = y := by
    intro y hy
    obtain ⟨a, ha, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    obtain ⟨x', hx', rfl⟩ := ha
    exact ⟨⟨x', Subgroup.mem_subgroupOf.mp hx'⟩, o, ho, rfl⟩
  rcases A312.nonquasi_of_lFamily Vol2Native.a312SL2Fact hTs hTop le_top hB (h36Y ⊤ hTop) hnq' with
    ⟨-, hsup, p, hp, hp2, ⟨e⟩⟩ | ⟨-, -, N, hN, hNeq, ⟨e⟩⟩
  ·
    let φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.oddCore ↥(⊤ : Subgroup Y))).comp
        ((Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).symm.toMonoidHom.comp (C10E4.fK hXL)))
    refine h.false_of_surj hn hp hp2 φ fun s => ?_
    obtain ⟨q, rfl⟩ := e.surjective s
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have ht : (t : Y) ∈ modO2Image L X ⊔ OL := hsup ▸ Subgroup.mem_top _
    obtain ⟨x, o, ho, hxo⟩ := hdec t ht
    obtain ⟨o', ho', hoo⟩ := ho
    refine ⟨x, ?_⟩
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e1 : t = (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).symm (C10E4.fK hXL x) * o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hxo, ← hoo]
      rfl
    rw [e1, inv_mul_cancel_left]
    exact ho'
  ·
    have hmem : ∀ x : ↥X, C10E4.fK hXL x ∈ modO2Image L X ⊔ OL := fun x =>
      Subgroup.mem_sup_left ⟨⟨x, hXL x.2⟩, x.2, rfl⟩
    let ι : ↥X →* ↥(modO2Image L X ⊔ OL) := (C10E4.fK hXL).codRestrict _ hmem
    let φ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      e.toMonoidHom.comp ((QuotientGroup.mk' N).comp ι)
    refine h.false_of_surj hn Nat.prime_five (by norm_num) φ fun s => ?_
    obtain ⟨q, rfl⟩ := e.surjective s
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨x, o, ho, hxo⟩ := hdec t t.2
    refine ⟨x, ?_⟩
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hNeq,
      Subgroup.mem_subgroupOf]
    have e1 : ((ι x)⁻¹ * t : ↥(modO2Image L X ⊔ OL)) = (o : Y) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ι, MonoidHom.codRestrict_apply]
      rw [← hxo]
      group
    rw [e1]
    exact ho

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
