module

public import CFSG.Quasithin.Background.A1cModuleHomog
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

abbrev onA (A X : Subgroup G) : Subgroup ↥(Subgroup.normalizer (A : Set G)) :=
  X.subgroupOf (Subgroup.normalizer (A : Set G))

theorem XMod.isIrr_of_iso {B : Type*} [Group B] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction B Q] {L L' : Subgroup Q} (hL' : XMod.IsInv B L') (hL : XMod.IsIrr B L)
    (h : XMod.Iso B L' L) : XMod.IsIrr B L' := by
  rw [XMod.isIrr_iff hL']
  have := (XMod.isIrr_iff hL.1).1 hL
  obtain ⟨e⟩ := XMod.nonempty_linearEquiv_of_iso hL' hL.1 h
  exact IsSimpleModule.congr e

variable {A X : Subgroup G}

theorem coe_smul_onA (a : ↥(onA A X)) (v : ↥A) :
    ((a • v : ↥A) : G) = ((a : ↥(Subgroup.normalizer (A : Set G))) : G) * v *
      ((a : ↥(Subgroup.normalizer (A : Set G))) : G)⁻¹ :=
  rfl

abbrev elemOnA (hX : X ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ X) : ↥(onA A X) :=
  ⟨⟨x, hX hx⟩, hx⟩

theorem map_subtype_top (A : Subgroup G) : (⊤ : Subgroup ↥A).map A.subtype = A := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_modFix [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    (W : Subgroup ↥A) :
    (modFix (onA A X) W).map A.subtype =
      W.map A.subtype ⊓ Subgroup.centralizer (X : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hv.1, rfl⟩, fun x hx => ?_⟩
    have h1 : x * (v : G) * x⁻¹ = v := congrArg Subtype.val (hv.2 (elemOnA hX hx))
    calc x * (v : G) = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [h1]
  · rintro ⟨⟨v, hv, rfl⟩, hc⟩
    refine ⟨v, ⟨hv, fun a => Subtype.ext ?_⟩, rfl⟩
    rw [coe_smul_onA, hc _ (Subgroup.mem_subgroupOf.1 a.2), mul_assoc, mul_inv_cancel, mul_one]

theorem map_modComm [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    (W : Subgroup ↥A) :
    (modComm (onA A X) W).map A.subtype = ⁅W.map A.subtype, X⁆ := by
  rw [modComm, XMod.commOf, MonoidHom.map_closure, Subgroup.commutator_comm,
    Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨a, v, hv, rfl⟩, rfl⟩
    refine ⟨((a : ↥(Subgroup.normalizer (A : Set G))) : G), Subgroup.mem_subgroupOf.1 a.2, v,
      ⟨v, hv, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    rfl
  · rintro ⟨x, hx, g₂, hg₂, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hg₂
    refine ⟨_, ⟨elemOnA hX hx, v, hv, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    rfl

theorem isModInv_iff [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    (W : Subgroup ↥A) :
    IsModInv (onA A X) W ↔
      X ≤ Subgroup.normalizer ((W.map A.subtype : Subgroup G) : Set G) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hg
      exact Subgroup.mem_map.2 ⟨_, h (elemOnA hX hx) v hv, rfl⟩
    · intro hg
      obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 hg
      have hx' : x⁻¹ ∈ X := X.inv_mem hx
      refine Subgroup.mem_map.2 ⟨_, h (elemOnA hX hx') v hv, ?_⟩
      change x⁻¹ * (v : G) * x⁻¹⁻¹ = g
      have hve' : (v : G) = x * g * x⁻¹ := hve
      rw [hve']
      group
  · intro h a v hv
    have h1 : ((a : ↥(Subgroup.normalizer (A : Set G))) : G) * v *
        ((a : ↥(Subgroup.normalizer (A : Set G))) : G)⁻¹ ∈ W.map A.subtype :=
      (Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 a.2)) v).1
        (Subgroup.mem_map.2 ⟨v, hv, rfl⟩)
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 h1
    have : w = a • v := Subtype.ext hwe
    rw [← this]
    exact hw

theorem isModInv_subgroupOf [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    {J : Subgroup G} (hJ : J ≤ A) (hXJ : X ≤ Subgroup.normalizer (J : Set G)) :
    IsModInv (onA A X) (J.subgroupOf A) := by
  rw [isModInv_iff hX, Subgroup.map_subgroupOf_eq_of_le hJ]
  exact hXJ

theorem isIrrPlusBase_map_iff [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    (I : Subgroup ↥A) :
    IsIrrPlusBase X A (I.map A.subtype) ↔ I ∈ IrrPlus (onA A X) ⊤ := by
  have hfix := map_modFix hX I
  constructor
  · rintro ⟨-, -, hinv, hcomm, hlt, hirr⟩
    have hinv' : IsModInv (onA A X) I := (isModInv_iff hX I).2 hinv
    refine ⟨le_top, hinv', ?_, ?_, ?_⟩
    · rw [← Subgroup.map_subtype_inj, map_modComm hX, hcomm]
    · rw [← Subgroup.map_subtype_lt_map_subtype, hfix]
      exact hlt
    · intro J hJ hfJ hJI
      have h1 := hirr (J.map A.subtype)
        (by rw [← hfix]; exact Subgroup.map_mono hfJ) (Subgroup.map_mono hJI)
        ((isModInv_iff hX J).1 hJ)
      rw [← hfix, Subgroup.map_subtype_inj, Subgroup.map_subtype_inj] at h1
      exact h1
  · rintro ⟨-, hinv, hcomm, hlt, hirr⟩
    have hinv' := (isModInv_iff hX I).1 hinv
    have hlt' : I.map A.subtype ⊓ Subgroup.centralizer (X : Set G) < I.map A.subtype := by
      rw [← hfix, Subgroup.map_subtype_lt_map_subtype]
      exact hlt
    refine ⟨Subgroup.map_subtype_le I, ?_, hinv', ?_, hlt', ?_⟩
    · intro h
      rw [h] at hlt'
      exact not_lt_bot hlt'
    · have h := map_modComm hX I
      rw [show modComm (onA A X) I = I from hcomm] at h
      exact h.symm
    · intro J hCJ hJI hXJ
      have hJA : J ≤ A := hJI.trans (Subgroup.map_subtype_le I)
      have hJ' := Subgroup.map_subgroupOf_eq_of_le hJA
      have h1 := hirr (J.subgroupOf A) (isModInv_subgroupOf hX hJA hXJ)
        (by rw [← Subgroup.map_subtype_le_map_subtype, hJ', hfix]; exact hCJ)
        (by rw [← Subgroup.map_subtype_le_map_subtype, hJ']; exact hJI)
      rcases h1 with h1 | h1
      · left
        rw [← hJ', h1, hfix]
      · right
        rw [← hJ', h1]

theorem isIrrPlusBase_iff [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    {I : Subgroup G} (hI : I ≤ A) : IsIrrPlusBase X A I ↔ I.subgroupOf A ∈ IrrPlus (onA A X) ⊤ := by
  rw [← isIrrPlusBase_map_iff hX, Subgroup.map_subgroupOf_eq_of_le hI]

theorem isMulCommutative_of_le [IsMulCommutative ↥A] {J : Subgroup G} (hJ : J ≤ A) :
    IsMulCommutative ↥J :=
  ⟨⟨fun a b => Subtype.ext <| by
    have h := congrArg Subtype.val (mul_comm (⟨a, hJ a.2⟩ : ↥A) ⟨b, hJ b.2⟩)
    exact h⟩⟩

theorem normal_of_le [IsMulCommutative ↥A] {J : Subgroup G} (hJ : J ≤ A) (H : Subgroup ↥J) :
    H.Normal := by
  have := isMulCommutative_of_le hJ
  exact Subgroup.normal_of_isMulCommutative H

theorem exists_sectionEquiv [IsMulCommutative ↥A] (hX : X ≤ Subgroup.normalizer (A : Set G))
    (J : Subgroup ↥A)
    [((J.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (J.map A.subtype)).Normal] :
    ∃ ψ : ↥(J.map A.subtype) ⧸ (J.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf
        (J.map A.subtype) ≃* ↥(tilde (onA A X) ⊤ J),
      ∀ j : ↥(J.map A.subtype), ((ψ (QuotientGroup.mk j) : ↥(tilde (onA A X) ⊤ J)) :
        ↥A ⧸ modFix (onA A X) ⊤) =
          QuotientGroup.mk (⟨j, Subgroup.map_subtype_le J j.2⟩ : ↥A) := by
  set f : ↥(J.map A.subtype) →* ↥A ⧸ modFix (onA A X) ⊤ :=
    (QuotientGroup.mk' (modFix (onA A X) ⊤)).comp
      (Subgroup.inclusion (Subgroup.map_subtype_le J)) with hf
  have hrange : f.range = tilde (onA A X) ⊤ J := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
    rfl
  have hker : f.ker =
      (J.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (J.map A.subtype) := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 := map_modFix hX (⊤ : Subgroup ↥A)
    rw [map_subtype_top] at h1
    constructor
    · intro hj
      have h2 : (j : G) ∈ (modFix (onA A X) ⊤).map A.subtype :=
        Subgroup.mem_map.2 ⟨_, hj, rfl⟩
      rw [h1] at h2
      exact ⟨j.2, h2.2⟩
    · intro hj
      have h2 : (j : G) ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
        ⟨Subgroup.map_subtype_le J j.2, hj.2⟩
      rw [← h1] at h2
      obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 h2
      have : v = Subgroup.inclusion (Subgroup.map_subtype_le J) j := Subtype.ext hve
      rw [← this]
      exact hv
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)), ?_⟩
  intro j
  rfl

theorem iso_tilde_of_isXSectionIso₂ [IsMulCommutative ↥A]
    (hX : X ≤ Subgroup.normalizer (A : Set G)) {J₁ J₂ : Subgroup ↥A}
    (hJ₁ : IsModInv (onA A X) J₁) (hJ₂ : IsModInv (onA A X) J₂)
    (h : IsXSectionIso₂ X (J₁.map A.subtype) (J₁.map A.subtype ⊓ Subgroup.centralizer (X : Set G))
      (J₂.map A.subtype) (J₂.map A.subtype ⊓ Subgroup.centralizer (X : Set G))) :
    XMod.Iso ↥(onA A X) (tilde (onA A X) ⊤ J₁) (tilde (onA A X) ⊤ J₂) := by
  obtain ⟨hn₁, hn₂, e, he⟩ := h
  obtain ⟨ψ₁, hψ₁⟩ := exists_sectionEquiv hX J₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_sectionEquiv hX J₂
  have hX₁ := (isModInv_iff hX J₁).1 hJ₁
  have hX₂ := (isModInv_iff hX J₂).1 hJ₂
  refine ⟨ψ₁.symm.trans (e.trans ψ₂), fun a l l' hll' => ?_⟩
  obtain ⟨q, rfl⟩ := ψ₁.surjective l
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨q₂, rfl⟩ := ψ₁.surjective l'
  obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk j))
  set x : G := ((a : ↥(Subgroup.normalizer (A : Set G))) : G) with hxdef
  have hxX : x ∈ X := Subgroup.mem_subgroupOf.1 a.2
  have hj : x * (j : G) * x⁻¹ ∈ J₁.map A.subtype :=
    (Subgroup.mem_normalizer_iff.1 (hX₁ hxX) j).1 j.2
  have hkk : x * (k : G) * x⁻¹ ∈ J₂.map A.subtype :=
    (Subgroup.mem_normalizer_iff.1 (hX₂ hxX) k).1 k.2
  have he' := he x hxX j k hj hkk hk.symm
  have hl' : (QuotientGroup.mk j' : ↥(J₁.map A.subtype) ⧸
      (J₁.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (J₁.map A.subtype)) =
      QuotientGroup.mk ⟨x * (j : G) * x⁻¹, hj⟩ := by
    apply ψ₁.injective
    apply Subtype.ext
    rw [← hll', hψ₁, hψ₁]
    rfl
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hl', he', ← hk, hψ₂, hψ₂]
  rfl

theorem isXSectionIso₂_of_iso_tilde [IsMulCommutative ↥A]
    (hX : X ≤ Subgroup.normalizer (A : Set G)) {J₁ J₂ : Subgroup ↥A}
    (h : XMod.Iso ↥(onA A X) (tilde (onA A X) ⊤ J₁) (tilde (onA A X) ⊤ J₂)) :
    IsXSectionIso₂ X (J₁.map A.subtype) (J₁.map A.subtype ⊓ Subgroup.centralizer (X : Set G))
      (J₂.map A.subtype) (J₂.map A.subtype ⊓ Subgroup.centralizer (X : Set G)) := by
  obtain ⟨φ, hφ⟩ := h
  have hn₁ := normal_of_le (Subgroup.map_subtype_le J₁)
    ((J₁.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (J₁.map A.subtype))
  have hn₂ := normal_of_le (Subgroup.map_subtype_le J₂)
    ((J₂.map A.subtype ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (J₂.map A.subtype))
  obtain ⟨ψ₁, hψ₁⟩ := exists_sectionEquiv hX J₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_sectionEquiv hX J₂
  refine ⟨hn₁, hn₂, ψ₁.trans (φ.trans ψ₂.symm), fun x hx j k hj hk hjk => ?_⟩
  simp only [MulEquiv.trans_apply] at hjk ⊢
  rw [MulEquiv.symm_apply_eq] at hjk ⊢
  apply Subtype.ext
  have h1 := hφ (elemOnA hX hx) (ψ₁ (QuotientGroup.mk j))
    (ψ₁ (QuotientGroup.mk ⟨_, hj⟩)) (by rw [hψ₁, hψ₁]; rfl)
  rw [← h1, hjk, hψ₂, hψ₂]
  rfl

theorem mem_map_smul_iff (t : ↥(Subgroup.normalizer (A : Set G))) (W : Subgroup ↥A) {g : G} :
    g ∈ (t • W).map A.subtype ↔ ∃ w ∈ W, (t : G) * (w : G) * (t : G)⁻¹ = g := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists v t W).1 hv
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨t • w, Subgroup.smul_mem_pointwise_smul w t W hw, rfl⟩

theorem map_biSup_smul {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (A : Set G))
    (W : Subgroup ↥A) :
    (⨆ y ∈ onA A T, y • W).map A.subtype = conjClosure (W.map A.subtype) T := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun y hy v hv => ?_
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists v y W).1 hv
    exact mem_conjClosure (Subgroup.mem_subgroupOf.1 hy) (Subgroup.mem_map.2 ⟨w, hw, rfl⟩)
  · refine conjClosure_le fun t ht z hz => ?_
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    have hmem : (⟨t, hT ht⟩ : ↥(Subgroup.normalizer (A : Set G))) • w ∈
        ⨆ y ∈ onA A T, y • W :=
      (le_iSup₂ (f := fun (y : ↥(Subgroup.normalizer (A : Set G))) (_ : y ∈ onA A T) => y • W)
        ⟨t, hT ht⟩ ht) (Subgroup.smul_mem_pointwise_smul w _ W hw)
    exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩

theorem conjClosure_map_le {T : Subgroup G} (hT : T ≤ Subgroup.normalizer (A : Set G))
    (W : Subgroup ↥A) : conjClosure (W.map A.subtype) T ≤ A := by
  rw [← map_biSup_smul hT]
  exact Subgroup.map_subtype_le _

theorem tilde_sup_modFix [IsMulCommutative ↥A] (J : Subgroup ↥A) :
    tilde (onA A X) ⊤ (J ⊔ modFix (onA A X) ⊤) = tilde (onA A X) ⊤ J := by
  rw [tilde, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rfl

theorem isIrrPlusIn_map_of_mem_irrPlusOn [IsMulCommutative ↥A] {T : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (A : Set G)) (hT : T ≤ Subgroup.normalizer (A : Set G))
    {I : Subgroup ↥A} (hI : I ∈ IrrPlusOn (onA A X) ⊤ (onA A T)) :
    IsIrrPlusIn X A T (I.map A.subtype) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (isIrrPlusBase_map_iff hX I).2 hI.1
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro J hCJ hJle hXJ hiso
  set C : Subgroup G := A ⊓ Subgroup.centralizer (X : Set G) with hCdef
  have hC : (modFix (onA A X) ⊤).map A.subtype = C := by
    rw [map_modFix hX, map_subtype_top]
  have hCA : C ≤ A := inf_le_left
  set W := ⨆ y ∈ onA A T, y • I with hWdef
  have hW : W.map A.subtype = conjClosure (I.map A.subtype) T := map_biSup_smul hT I
  have hJA : J ≤ A := hJle.trans (sup_le (conjClosure_map_le hT I) hCA)
  set J' := J.subgroupOf A with hJ'def
  have hJ' : J'.map A.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJA
  set K := I ⊔ modFix (onA A X) ⊤ with hKdef
  have hK : K.map A.subtype = I.map A.subtype ⊔ C := by
    rw [hKdef, Subgroup.map_sup, hC]
  have hKinv : IsModInv (onA A X) K := XMod.IsInv.sup hI.1.2.1 (XMod.isInv_fixed ⊤)
  have hJinv : IsModInv (onA A X) J' := isModInv_subgroupOf hX hJA hXJ
  have hJC : J ⊓ Subgroup.centralizer (X : Set G) = C :=
    le_antisymm (inf_le_inf_right _ hJA) (le_inf hCJ inf_le_right)
  have hKC : K.map A.subtype ⊓ Subgroup.centralizer (X : Set G) = C := by
    rw [hK]
    exact le_antisymm (inf_le_inf_right _ (sup_le (Subgroup.map_subtype_le I) hCA))
      (le_inf le_sup_right inf_le_right)
  have hiso' : IsXSectionIso₂ X (J'.map A.subtype)
      (J'.map A.subtype ⊓ Subgroup.centralizer (X : Set G))
      (K.map A.subtype) (K.map A.subtype ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hJ', hJC, hKC, hK]
    exact hiso
  have hti := iso_tilde_of_isXSectionIso₂ hX hJinv hKinv hiso'
  rw [hKdef, tilde_sup_modFix] at hti
  have hirrI := (isIrr_tilde hI.1).1
  have hirrJ : XMod.IsIrr ↥(onA A X) (tilde (onA A X) ⊤ J') :=
    XMod.isIrr_of_iso (isInv_tilde hJinv) hirrI hti
  have hJW : J' ≤ W ⊔ modFix (onA A X) ⊤ := by
    rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_sup, hW, hC, hJ']
    exact hJle
  have hJW' : tilde (onA A X) ⊤ J' ≤ tilde (onA A X) ⊤ W := by
    rw [← tilde_sup_modFix W]
    exact tilde_mono hJW
  have hle := hI.2.2.2 _ hJW' hirrJ hti
  have hJI : J' ≤ I ⊔ modFix (onA A X) ⊤ := by
    rw [← comap_tilde]
    exact Subgroup.map_le_iff_le_comap.1 hle
  rw [← hJ', ← hK]
  exact Subgroup.map_mono hJI

end CFSG.Quasithin.H13
