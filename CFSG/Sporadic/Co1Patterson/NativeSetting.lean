module

public import CFSG.Sporadic.Co1Patterson.NativeQ
public import CFSG.Sporadic.Co1Patterson.SettingCard
public import CFSG.Sporadic.Co1Patterson.SettingType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier
open CFSG.Blueprint (NativeSporadic.Co1)

@[expose] noncomputable def aNC : NativeSporadic.Co1 :=
  co1MatEquiv.symm ⟨aG, iotaA_mem_GA⟩

@[expose] noncomputable def nativeEmb :
    NativeSporadic.Co1 →* GL24 where
  toFun x := ((co1MatEquiv x : GA) : GL24)
  map_one' := by
    rw [map_one co1MatEquiv]
    rfl
  map_mul' x y := by
    rw [map_mul co1MatEquiv x y]
    rfl

@[expose] noncomputable def twoAQNC :
    Subgroup NativeSporadic.Co1 :=
  twoAQ.comap nativeEmb

theorem nativeEmb_apply (x : NativeSporadic.Co1) :
    nativeEmb x = ((co1MatEquiv x : GA) : GL24) := rfl

theorem nativeEmb_injective : Function.Injective nativeEmb := fun _ _ h =>
  co1MatEquiv.injective (Subtype.ext h)

theorem nativeEmb_mem (x : NativeSporadic.Co1) : nativeEmb x ∈ GA := (co1MatEquiv x).2

theorem co1MatEquiv_aNC : co1MatEquiv aNC = ⟨aG, iotaA_mem_GA⟩ := by
  unfold aNC
  exact MulEquiv.apply_symm_apply _ _

theorem nativeEmb_aNC : nativeEmb aNC = aG := by
  rw [nativeEmb_apply, co1MatEquiv_aNC]

theorem exists_nativeEmb_eq {g : GL24} (hg : g ∈ GA) : ∃ x, nativeEmb x = g :=
  ⟨co1MatEquiv.symm ⟨g, hg⟩, by rw [nativeEmb_apply, MulEquiv.apply_symm_apply]⟩

theorem mem_twoAQNC_iff {x : NativeSporadic.Co1} : x ∈ twoAQNC ↔ nativeEmb x ∈ twoAQ :=
  Iff.rfl

theorem orderOf_aNC :
    orderOf aNC = 2 := by
  rw [← orderOf_co1MatEquiv, co1MatEquiv_aNC, Subgroup.orderOf_mk, orderOf_aG]

theorem mem_centralizer_aNC_iff {x : NativeSporadic.Co1} :
    x ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ↔
      nativeEmb x ∈ centralizer ({aG} : Set GL24) := by
  rw [@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC x,
    @mem_centralizer_singleton_iff GL24 inferInstance aG (nativeEmb x), ← nativeEmb_aNC,
    ← map_mul, ← map_mul]
  exact nativeEmb_injective.eq_iff.symm

@[expose] noncomputable def centEmb : centralizer ({aNC} : Set NativeSporadic.Co1) →* GL24 :=
  nativeEmb.comp (centralizer ({aNC} : Set NativeSporadic.Co1)).subtype

theorem centEmb_apply (c : centralizer ({aNC} : Set NativeSporadic.Co1)) :
    centEmb c = nativeEmb (c : NativeSporadic.Co1) := rfl

theorem centEmb_injective : Function.Injective centEmb :=
  nativeEmb_injective.comp Subtype.val_injective

theorem centEmb_mem (c : centralizer ({aNC} : Set NativeSporadic.Co1)) :
    centEmb c ∈ GA ⊓ centralizer {aG} :=
  mem_inf.2 ⟨nativeEmb_mem _, mem_centralizer_aNC_iff.1 c.2⟩

theorem exists_centEmb_eq {g : GL24} (hg : g ∈ GA ⊓ centralizer {aG}) :
    ∃ c, centEmb c = g := by
  obtain ⟨hgA, hgC⟩ := mem_inf.1 hg
  obtain ⟨x, rfl⟩ := exists_nativeEmb_eq hgA
  exact ⟨⟨x, mem_centralizer_aNC_iff.2 hgC⟩, rfl⟩

@[expose] noncomputable def twoAQC : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  twoAQ.comap centEmb

theorem map_twoAQC :
    twoAQC.map centEmb = twoAQ := by
  rw [twoAQC, Subgroup.map_comap_eq]
  refine inf_eq_right.2 fun g hg => ?_
  obtain ⟨c, hc⟩ := exists_centEmb_eq (twoAQ_le hg)
  exact ⟨c, hc⟩

@[expose] noncomputable def twoAQCEquiv :
    twoAQC ≃* twoAQ :=
  (twoAQC.equivMapOfInjective centEmb centEmb_injective).trans
    (MulEquiv.subgroupCongr map_twoAQC)

theorem card_twoAQC :
    Nat.card twoAQC = 2 ^ 9 := by
  rw [Nat.card_congr twoAQCEquiv.toEquiv, card_twoAQ]
  norm_num

theorem twoAQC_normal :
    twoAQC.Normal := by
  refine ⟨fun q hq c => ?_⟩
  change centEmb (c * q * c⁻¹) ∈ twoAQ
  rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  exact twoAQ_normal _ (centEmb_mem c) _ hq

theorem twoAQC_centralizer_le :
    centralizer (twoAQC : Set (centralizer ({aNC} : Set NativeSporadic.Co1))) ≤ twoAQC := by
  intro c hc
  change centEmb c ∈ twoAQ
  refine twoA_selfCentralizing _ (centEmb_mem c) fun q hq => ?_
  obtain ⟨q', hq'⟩ := exists_centEmb_eq (twoAQ_le hq)
  have hq'Q : q' ∈ twoAQC := by
    change centEmb q' ∈ twoAQ
    rw [hq']
    exact hq
  have h := congrArg centEmb (mem_centralizer_iff.1 hc q' hq'Q)
  rw [MonoidHom.map_mul, MonoidHom.map_mul, hq'] at h
  exact h.symm

theorem card_centralizer_aNC :
    Nat.card (centralizer ({aNC} : Set NativeSporadic.Co1)) = 89181388800 := by
  rw [card_centralizer_co1, co1MatEquiv_aNC, card_centralizer_GA]
  exact card_cent_aG

theorem twoAQC_extraspecial : IsExtraspecialPGroup 2 twoAQC := by
  have h := (Bridge.timmesfeldIsExtraspecial_iff (twoAQ : Subgroup GL24)).1 twoAQ_extraspecial
  exact @CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv 2 twoAQ twoAQC inferInstance
    inferInstance twoAQCEquiv.symm h

@[expose] noncomputable def nativeSetting : Setting NativeSporadic.Co1 :=
  settingOfCard aNC orderOf_aNC twoAQC twoAQC_normal twoAQC_extraspecial twoAQC_centralizer_le
    card_twoAQC card_centralizer_aNC

theorem nativeSetting_Q : nativeSetting.Q = twoAQC := rfl

theorem width_nativeSetting : nativeSetting.width = 4 :=
  nativeSetting.width_eq (card_twoAQC.trans (by norm_num))

theorem card_Mbar_nativeSetting : Nat.card nativeSetting.Mbar = 174182400 :=
  Setting.card_Mbar_of_card nativeSetting card_centralizer_aNC card_twoAQC

theorem fStar_centralizer :
    (timmesfeldFStar (centralizer ({aNC} : Set NativeSporadic.Co1))).map
      (centralizer ({aNC} : Set NativeSporadic.Co1)).subtype = twoAQNC := by
  have h : twoAQC = timmesfeldFStar (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
    Bridge.Q_eq_timmesfeldFStar nativeSetting
  rw [← h]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hx
    exact ⟨⟨x, mem_centralizer_aNC_iff.2 (mem_inf.1 (twoAQ_le hx)).2⟩, hx, rfl⟩

theorem pattersonCo1Hyp_native : PattersonCo1Hyp NativeSporadic.Co1 aNC where
  simple := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  noncomm := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_twoAQ_mul_ne
    obtain ⟨a, rfl⟩ := exists_nativeEmb_eq (mem_inf.1 (twoAQ_le hx)).1
    obtain ⟨b, rfl⟩ := exists_nativeEmb_eq (mem_inf.1 (twoAQ_le hy)).1
    refine ⟨a, b, fun h => hxy ?_⟩
    rw [← map_mul, ← map_mul, h]
  orderOf_eq := orderOf_aNC
  extraspecial := Bridge.timmesfeldIsExtraspecial_fstar nativeSetting
  card := (Bridge.card_fstar nativeSetting).trans (by rw [width_nativeSetting])
  quotient := by
    obtain ⟨e⟩ := Setting.nonempty_Mbar_equiv_omegaPlus nativeSetting width_nativeSetting
      card_Mbar_nativeSetting
    exact Bridge.quotientIso_congr_right (Bridge.quotientIso_Mbar nativeSetting) e

theorem setting_native_QG : (setting pattersonCo1Hyp_native).QG = twoAQNC :=
  fStar_centralizer

@[expose] noncomputable def nativeTypeSystem :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀
      (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  Setting.typeSystem nativeSetting width_nativeSetting
    (map_Mbar_eq_omega_of_card nativeSetting width_nativeSetting card_Mbar_nativeSetting)
    (isPlusType_of_card nativeSetting width_nativeSetting card_Mbar_nativeSetting)

end CFSG.Sporadic.Co1Patterson
