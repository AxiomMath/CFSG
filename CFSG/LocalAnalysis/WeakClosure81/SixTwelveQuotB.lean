module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveQuotA
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveKeyB
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_K_of_mk_mem_normalizer_imgK (M V : Subgroup G) (g : G)
    [((KOf M V g).subgroupOf (LOf V g)).Normal] {A : Subgroup G} (hA : A ≤ LOf V g)
    {b : ↥(LOf V g)}
    (hb : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) b ∈
      Subgroup.normalizer (imgK M V g A : Set (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))))
    {w : G} (hw : w ∈ A) : (b : G) * w * (b : G)⁻¹ ∈ A ⊔ KOf M V g := by
  let π := QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))
  have hwA : π ⟨w, hA hw⟩ ∈ imgK M V g A :=
    (mem_imgK_iff M V g).2 ⟨⟨w, hA hw⟩, hw, rfl⟩
  have hb' : π b * π ⟨w, hA hw⟩ * (π b)⁻¹ ∈ imgK M V g A :=
    (Subgroup.mem_normalizer_iff.1 hb (π ⟨w, hA hw⟩)).1 hwA
  have hbw : π (b * ⟨w, hA hw⟩ * b⁻¹) ∈ imgK M V g A := by
    simpa only [map_mul, map_inv] using hb'
  have hmem := mem_sup_K_of_mk_mem_imgK M V g hbw
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem

namespace Hyp612H3

variable {n : ℕ} {M V : Subgroup G} {g : G} [((KOf M V g).subgroupOf (LOf V g)).Normal]

theorem closed_imgK (h : Hyp612H3 n M V g) :
    ∀ x y : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g),
      ∀ a ∈ CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g V), a ≠ 1 →
      ∀ b ∈ CFSG.CGT.Timmesfeld75.conjSubgroup y (imgK M V g V), b ≠ 1 →
      ⁅a, b⁆ ∈ imgK M V g (CKOf M V g) →
      CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g V) =
        CFSG.CGT.Timmesfeld75.conjSubgroup y (imgK M V g V) := by
  intro x y a ha ha1 b hb hb1 hab
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨u', rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [imgK_conj M V g u V] at ha ⊢
  rw [imgK_conj M V g u' V] at hb ⊢
  obtain ⟨a₀, ha₀, ha₀K, rfl⟩ := exists_lift_of_mem_imgK M V g ha ha1
  obtain ⟨b₀, hb₀, hb₀K, rfl⟩ := exists_lift_of_mem_imgK M V g hb hb1
  have hcD : ⁅(a₀ : G), (b₀ : G)⁆ ∈ CKOf M V g := by
    have h1 : ((⁅a₀, b₀⁆ : ↥(LOf V g)) : G) ∈ CKOf M V g :=
      (mk_mem_imgK_iff_of_K_le M V g h.KOf_le_CKOf ⁅a₀, b₀⁆).1 (by
        rw [← map_commutatorElement] at hab
        exact hab)
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hEq : conjSubgroup V (u : G)⁻¹ = conjSubgroup V (u' : G)⁻¹ :=
    h.conjSubgroup_eq_of_commutator_mem (l := (u : G)⁻¹) (l' := (u' : G)⁻¹)
      ((LOf V g).inv_mem u.2) ((LOf V g).inv_mem u'.2) ha₀ ha₀K hb₀ hb₀K hcD
  rw [hEq]

theorem closed₁_imgK (h : Hyp612H3 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) :
    ∀ x y : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g),
      ∀ a ∈ CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g (conjSubgroup V g)), a ≠ 1 →
      ∀ b ∈ CFSG.CGT.Timmesfeld75.conjSubgroup y (imgK M V g (conjSubgroup V g)), b ≠ 1 →
      ⁅a, b⁆ ∈ imgK M V g (CKOf M V g) →
      CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g (conjSubgroup V g)) =
        CFSG.CGT.Timmesfeld75.conjSubgroup y (imgK M V g (conjSubgroup V g)) := by
  intro x y a ha ha1 b hb hb1 hab
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨u', rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [imgK_conj M V g u (conjSubgroup V g)] at ha ⊢
  rw [imgK_conj M V g u' (conjSubgroup V g)] at hb ⊢
  obtain ⟨a₀, ha₀, ha₀K, rfl⟩ := exists_lift_of_mem_imgK M V g ha ha1
  obtain ⟨b₀, hb₀, hb₀K, rfl⟩ := exists_lift_of_mem_imgK M V g hb hb1
  have hcD : ⁅(a₀ : G), (b₀ : G)⁆ ∈ CKOf M V g := by
    have h1 : ((⁅a₀, b₀⁆ : ↥(LOf V g)) : G) ∈ CKOf M V g :=
      (mk_mem_imgK_iff_of_K_le M V g h.KOf_le_CKOf ⁅a₀, b₀⁆).1 (by
        rw [← map_commutatorElement] at hab
        exact hab)
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hEq : conjSubgroup (conjSubgroup V g) (u : G)⁻¹ =
      conjSubgroup (conjSubgroup V g) (u' : G)⁻¹ :=
    h.conjSubgroup_conjV_eq_of_commutator_mem hd (l := (u : G)⁻¹) (l' := (u' : G)⁻¹)
      ((LOf V g).inv_mem u.2) ((LOf V g).inv_mem u'.2) ha₀ ha₀K hb₀ hb₀K hcD
  rw [hEq]

theorem inf_normalizer_imgK (h : Hyp612H3 n M V g) :
    ∀ s ∈ imgK M V g (conjSubgroup V g),
      s ∈ Subgroup.normalizer (imgK M V g V : Set (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))) →
      s = 1 := by
  intro s hs hsN
  by_contra hs1
  obtain ⟨b, hb, hbK, rfl⟩ := exists_lift_of_mem_imgK M V g hs hs1
  have hbV : ∀ v ∈ V, (b : G) * v * (b : G)⁻¹ ∈ V ⊔ KOf M V g := fun v hv =>
    mem_sup_K_of_mk_mem_normalizer_imgK M V g (le_sup_left : V ≤ LOf V g) hsN hv
  exact h.false_of_mem_normalizer_sup hb hbK hbV

theorem le_imgK_EOf (h : Hyp612H3 n M V g) :
    ∀ s ∈ imgK M V g (conjSubgroup V g), s ≠ 1 →
      ∀ x : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g),
      s ∈ Subgroup.normalizer
          (CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g V) :
            Set (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))) →
      CFSG.CGT.Timmesfeld75.conjSubgroup x (imgK M V g V) ≤ imgK M V g (EOf M V g) := by
  intro s hs hs1 x hsN
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨b, hb, hbK, rfl⟩ := exists_lift_of_mem_imgK M V g hs hs1
  rw [imgK_conj M V g u V] at hsN ⊢
  have hl : (u : G)⁻¹ ∈ LOf V g := (LOf V g).inv_mem u.2
  have hVl : conjSubgroup V (u : G)⁻¹ ≤ LOf V g :=
    conjSubgroup_le_LOf_of_mem (le_sup_left : V ≤ LOf V g) hl
  have hbl : ∀ w ∈ conjSubgroup V (u : G)⁻¹,
      (b : G) * w * (b : G)⁻¹ ∈ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g := fun w hw =>
    mem_sup_K_of_mk_mem_normalizer_imgK M V g hVl hsN hw
  exact imgK_mono M V g (h.conjSubgroup_le_EOf_of_mem_normalizer_sup hb hbK hl hbl)

theorem abs612_of_four_le (h : Hyp612H3 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹)
    (h4 : 4 ≤ Nat.card (imgK M V g V)) :
    Abs612 (imgK M V g V) (imgK M V g (conjSubgroup V g)) (imgK M V g (CKOf M V g))
      (imgK M V g (EOf M V g)) :=
  ⟨imgK_isElemAbelian M V g h.elemAbelian, imgK_isElemAbelian M V g h.elemAbelian_conj,
    h.imgK_V_ne_bot, h4, h.card_imgK_conjV, imgK_sup M V g, h.imgK_CKOf_le_center,
    h.imgK_V_inf_imgK_CKOf, h.imgK_conjV_inf_imgK_CKOf, h.closed_imgK, h.closed₁_imgK hd,
    h.inf_normalizer_imgK, h.imgK_conjV_le_imgK_EOf, h.le_imgK_EOf,
    fun _ he _ he' => h.commutator_mem_imgK_CKOf he he',
    fun _ he hc => h.mem_imgK_CKOf_of_comm he hc⟩

end Hyp612H3

theorem Hyp612.abs612 {n : ℕ} {M V : Subgroup G} {g : G}
    [((KOf M V g).subgroupOf (LOf V g)).Normal] (h : Hyp612 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) :
    Abs612 (imgK M V g V) (imgK M V g (conjSubgroup V g)) (imgK M V g (CKOf M V g))
      (imgK M V g (EOf M V g)) :=
  h.toHyp612H3.abs612_of_four_le hd h.four_le_card_imgK

end CFSG.LocalAnalysis.WeakClosure81
