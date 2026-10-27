module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveCent
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section ImgK

variable (M V : Subgroup G) (g : G) [((KOf M V g).subgroupOf (LOf V g)).Normal]

theorem mem_imgK_iff {A : Subgroup G} {x : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)} :
    x ∈ imgK M V g A ↔ ∃ y : ↥(LOf V g), (y : G) ∈ A ∧
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y = x := by
  unfold imgK
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩, fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩⟩

theorem mem_sup_K_of_mk_mem_imgK {A : Subgroup G} {y : ↥(LOf V g)}
    (hy : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y ∈ imgK M V g A) :
    (y : G) ∈ A ⊔ KOf M V g := by
  obtain ⟨y', hy'A, hy'⟩ := (mem_imgK_iff M V g).1 hy
  have h1 : y'⁻¹ * y ∈ (KOf M V g).subgroupOf (LOf V g) := QuotientGroup.eq.1 hy'
  have h2 : ((y'⁻¹ * y : ↥(LOf V g)) : G) ∈ KOf M V g := Subgroup.mem_subgroupOf.1 h1
  have h3 : (y : G) = (y' : G) * ((y'⁻¹ * y : ↥(LOf V g)) : G) := by simp
  rw [h3]
  exact Subgroup.mul_mem_sup hy'A h2

theorem mk_mem_imgK_iff_of_K_le {A : Subgroup G} (hKA : KOf M V g ≤ A) (y : ↥(LOf V g)) :
    QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y ∈ imgK M V g A ↔ (y : G) ∈ A := by
  constructor
  · intro h
    have h1 := mem_sup_K_of_mk_mem_imgK M V g h
    rwa [sup_eq_left.2 hKA] at h1
  · intro h
    exact (mem_imgK_iff M V g).2 ⟨y, h, rfl⟩

theorem imgK_mono {A A' : Subgroup G} (h : A ≤ A') : imgK M V g A ≤ imgK M V g A' :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem card_imgK_eq_relIndex {A : Subgroup G} (hA : A ≤ LOf V g) :
    Nat.card (imgK M V g A) = (KOf M V g).relIndex A := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ ((KOf M V g).subgroupOf L)) :=
    QuotientGroup.mk' ((KOf M V g).subgroupOf L)
  let f : ↥A →* (↥L ⧸ ((KOf M V g).subgroupOf L)) := π.comp (Subgroup.inclusion hA)
  have hrange : f.range = (A.subgroupOf L).map π := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
    congr 1
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.inclusion_range hA
  have hker : f.ker = (KOf M V g).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' ((KOf M V g).subgroupOf L) (Subgroup.inclusion hA a) = 1 ↔
      (a : G) ∈ KOf M V g
    rw [mk_eq_one_iff_mem_K M V g (Subgroup.inclusion hA a), Subgroup.coe_inclusion]
  change Nat.card ((A.subgroupOf L).map π) = (KOf M V g).relIndex A
  calc Nat.card ((A.subgroupOf L).map π) = Nat.card f.range := by rw [hrange]
    _ = (f.ker).index := (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
    _ = ((KOf M V g).subgroupOf A).index := by rw [hker]
    _ = (KOf M V g).relIndex A := rfl

end ImgK

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G} [((KOf M V g).subgroupOf (LOf V g)).Normal]

theorem card_imgK_V (h : Hyp612Sym n M V g) :
    Nat.card (imgK M V g V) = (conjSubgroup M g).relIndex V := by
  rw [card_imgK_eq_relIndex M V g (le_sup_left : V ≤ LOf V g),
    ← Subgroup.inf_relIndex_right (KOf M V g) V, inf_comm, h.V_inf_KOf, UOf,
    Subgroup.inf_relIndex_left]

theorem card_imgK_conjV (h : Hyp612Sym n M V g) :
    Nat.card (imgK M V g (conjSubgroup V g)) = Nat.card (imgK M V g V) := by
  rw [card_imgK_eq_relIndex M V g (le_sup_right : conjSubgroup V g ≤ LOf V g),
    card_imgK_eq_relIndex M V g (le_sup_left : V ≤ LOf V g)]
  have h1 := Subgroup.relIndex_mul_card (KOf M V g) V
  have h2 := Subgroup.relIndex_mul_card (KOf M V g) (conjSubgroup V g)
  rw [inf_comm, h.V_inf_KOf] at h1
  rw [inf_comm, h.conjV_inf_KOf] at h2
  have hU : 0 < Nat.card (UOf M V g) := Nat.card_pos
  rw [E3.card_conjSubgroup V g, ← h.card_UOf_eq_card_BOf] at h2
  exact Nat.eq_of_mul_eq_mul_right hU (h2.trans h1.symm)

theorem imgK_V_ne_bot (h : Hyp612Sym n M V g) : imgK M V g V ≠ ⊥ := by
  intro hbot
  have hbot' : (V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) = ⊥ := hbot
  have hle : V.subgroupOf (LOf V g) ≤ (KOf M V g).subgroupOf (LOf V g) := by
    have h1 : V.subgroupOf (LOf V g) ≤
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))).ker :=
      (Subgroup.map_eq_bot_iff (V.subgroupOf (LOf V g))).1 hbot'
    rwa [QuotientGroup.ker_mk'] at h1
  have hVK : V ≤ KOf M V g := by
    intro v hv
    exact hle (show (⟨v, (le_sup_left : V ≤ LOf V g) hv⟩ : ↥(LOf V g)) ∈
      V.subgroupOf (LOf V g) from hv)
  have hVeq : V = UOf M V g := by
    rw [← h.V_inf_KOf]
    exact le_antisymm (le_inf le_rfl hVK) inf_le_left
  exact h.not_V_le_conjM (by rw [hVeq]; exact inf_le_right)

theorem imgK_CKOf_le_center (h : Hyp612Sym n M V g) :
    imgK M V g (CKOf M V g) ≤
      Subgroup.center (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_imgK_iff M V g).1 hx
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hk : ⁅(y : G), (l : G)⁆ ∈ KOf M V g := h.commutator_CKOf_LOf_mem_KOf hy l.2
  have hc : ⁅y, l⁆ ∈ (KOf M V g).subgroupOf (LOf V g) := by
    rw [Subgroup.mem_subgroupOf]
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hk
  exact ((QuotientGroup.commute_mk_iff (N := (KOf M V g).subgroupOf (LOf V g))).2 hc).eq.symm

theorem imgK_V_inf_imgK_CKOf (h : Hyp612Sym n M V g) :
    imgK M V g V ⊓ imgK M V g (CKOf M V g) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxD⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hyV, rfl⟩ := (mem_imgK_iff M V g).1 hxV
  have hyD : (y : G) ∈ CKOf M V g :=
    (mk_mem_imgK_iff_of_K_le M V g h.KOf_le_CKOf y).1 hxD
  have hyU : (y : G) ∈ UOf M V g := by
    rw [← h.V_inf_CKOf]
    exact Subgroup.mem_inf.2 ⟨hyV, hyD⟩
  have hyK : (y : G) ∈ KOf M V g := (le_sup_left : UOf M V g ≤ KOf M V g) hyU
  rw [Subgroup.mem_bot]
  exact (mk_eq_one_iff_mem_K M V g y).2 hyK

theorem imgK_conjV_inf_imgK_CKOf (h : Hyp612Sym n M V g) :
    imgK M V g (conjSubgroup V g) ⊓ imgK M V g (CKOf M V g) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxD⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hyV, rfl⟩ := (mem_imgK_iff M V g).1 hxV
  have hyD : (y : G) ∈ CKOf M V g :=
    (mk_mem_imgK_iff_of_K_le M V g h.KOf_le_CKOf y).1 hxD
  have hyB : (y : G) ∈ BOf M V g := by
    rw [← h.conjV_inf_CKOf]
    exact Subgroup.mem_inf.2 ⟨hyV, hyD⟩
  have hyK : (y : G) ∈ KOf M V g := (le_sup_right : BOf M V g ≤ KOf M V g) hyB
  rw [Subgroup.mem_bot]
  exact (mk_eq_one_iff_mem_K M V g y).2 hyK

theorem imgK_conjV_le_imgK_EOf (h : Hyp612Sym n M V g) :
    imgK M V g (conjSubgroup V g) ≤ imgK M V g (EOf M V g) :=
  imgK_mono M V g h.conjV_le_EOf

theorem commutator_mem_imgK_CKOf (h : Hyp612Sym n M V g)
    {e e' : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)}
    (he : e ∈ imgK M V g (EOf M V g)) (he' : e' ∈ imgK M V g (EOf M V g)) :
    ⁅e, e'⁆ ∈ imgK M V g (CKOf M V g) := by
  obtain ⟨y, hy, rfl⟩ := (mem_imgK_iff M V g).1 he
  obtain ⟨y', hy', rfl⟩ := (mem_imgK_iff M V g).1 he'
  rw [← map_commutatorElement]
  refine (mem_imgK_iff M V g).2 ⟨⁅y, y'⁆, ?_, rfl⟩
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using
    h.commutator_mem_CKOf_of_mem_EOf hy hy'

theorem mem_imgK_CKOf_of_comm (h : Hyp612Sym n M V g)
    {e : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)} (he : e ∈ imgK M V g (EOf M V g))
    (hc : ∀ t ∈ imgK M V g V, e * t = t * e) : e ∈ imgK M V g (CKOf M V g) := by
  obtain ⟨y, hy, rfl⟩ := (mem_imgK_iff M V g).1 he
  obtain ⟨v, hv, hvU⟩ : ∃ v ∈ V, v ∉ UOf M V g := by
    by_contra hcon
    apply h.not_V_le_conjM
    intro v hv
    by_contra hvM
    exact hcon ⟨v, hv, fun hU => hvM hU.2⟩
  have hvL : v ∈ LOf V g := (le_sup_left : V ≤ LOf V g) hv
  have hπv : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨v, hvL⟩ ∈ imgK M V g V :=
    (mem_imgK_iff M V g).2 ⟨⟨v, hvL⟩, hv, rfl⟩
  have hcomm := hc _ hπv
  have hcm : Commute ((y : ↥(LOf V g)) : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))
      ((⟨v, hvL⟩ : ↥(LOf V g)) : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := hcomm
  have hc2 := (QuotientGroup.commute_mk_iff (N := (KOf M V g).subgroupOf (LOf V g))).1 hcm
  have hK : ⁅(y : G), v⁆ ∈ KOf M V g := by
    have h3 := Subgroup.mem_subgroupOf.1 hc2
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h3
  have hyD : (y : G) ∈ CKOf M V g :=
    h.mem_CKOf_of_mem_EOf_of_commutator_mem_KOf hy hv hvU hK
  exact (mem_imgK_iff M V g).2 ⟨y, hyD, rfl⟩

end Hyp612Sym

theorem Hyp612.four_le_card_imgK {n : ℕ} {M V : Subgroup G} {g : G}
    [((KOf M V g).subgroupOf (LOf V g)).Normal] (h : Hyp612 n M V g) :
    4 ≤ Nat.card (imgK M V g V) := by
  rw [h.card_imgK_V]
  have h2 := h.two_le_mQuot_UOf
  unfold E3.mQuot at h2
  have h3 : (UOf M V g).relIndex V = (conjSubgroup M g).relIndex V := by
    rw [UOf, Subgroup.inf_relIndex_left]
  rw [h3] at h2
  haveI : (conjSubgroup M g).IsFiniteRelIndex V :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have hne : (conjSubgroup M g).relIndex V ≠ 0 := Subgroup.relIndex_ne_zero
  have h4 : 2 ^ 2 ∣ (conjSubgroup M g).relIndex V :=
    (padicValNat_dvd_iff_le_of_ne_one (by norm_num) hne).2 h2
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (by simpa using h4)

end CFSG.LocalAnalysis.WeakClosure81
