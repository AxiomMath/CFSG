module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7A7Free
public import CFSG.Quasithin.Background.Basic
import CFSG.Quasithin.Vol2.Ch10SecV1Q
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7A7Setup
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise commutatorElement

namespace Res162Seven

namespace Conf683

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
  {b : G} {Lb : Subgroup G}

theorem normalizer_sup_le₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤ Subgroup.normalizer (Y₁ : Set G) := by
  have hY : Y₁ ∈ scriptY0Star A (lB A) := h.maxCE.1.mem₁
  have hNX := normalizer_x_eq_of_main h.item153 h.claim153Normal hY
  have hS : S ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A)
        (Subgroup.normalizer (Y₁ : Set G))) : Set G)) (piOf 2) := by
    rw [hNX]
    exact h.maxCE.1.s₁
  have hle := (h.item153 Y₁ hY).2.1 S hS
  rw [hNX] at hle
  exact hle.2

theorem normalizer_sup_le₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤ Subgroup.normalizer (Y₂ : Set G) := by
  have hY : Y₂ ∈ scriptY0Star A (lB A) := h.maxCE.1.mem₂
  have hNX := normalizer_x_eq_of_main h.item153 h.claim153Normal hY
  have hS : S ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A)
        (Subgroup.normalizer (Y₂ : Set G))) : Set G)) (piOf 2) := by
    rw [hNX]
    exact h.maxCE.1.s₂
  have hle := (h.item153 Y₂ hY).2.1 S hS
  rw [hNX] at hle
  exact hle.2

theorem centralizer_Q_le (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    (Y₁ ⊔ S) ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) : Set G) ≤
      CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) :=
  CFSG.Quasithin.Vol2.Ch10.V1C.C27.sup_inf_centralizer_pCoreOf_le
    (K := Y₁) (R := S)
    (isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₁.prop)
    h.maxCE.1.s₁.prop.1.2
    (inf_centralizer_pCoreOf_le h.item153 h.maxCE.1.mem₁)

theorem centralizer_R_le (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    (Y₂ ⊔ S) ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) : Set G) ≤
      CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) :=
  CFSG.Quasithin.Vol2.Ch10.V1C.C27.sup_inf_centralizer_pCoreOf_le
    (K := Y₂) (R := S)
    (isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₂.prop)
    h.maxCE.1.s₂.prop.1.2
    (inf_centralizer_pCoreOf_le h.item153 h.maxCE.1.mem₂)

private theorem pCoreOf_ne_bot_of_a7 {Y : Subgroup G}
    (h153 : Item153Main A (lB A)) (hY : Y ∈ scriptY0Star A (lB A))
    (h7 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) :
    CFSG.Open.pCoreOf 2 Y ≠ ⊥ := by
  intro hbot
  have hYle_bot : Y ≤ (⊥ : Subgroup G) := by
    have h := inf_centralizer_pCoreOf_le h153 hY
    rw [hbot] at h
    have hYc : Y ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw1 : w = 1 := Subgroup.mem_bot.mp hw
      rw [hw1, mul_one, one_mul]
    exact (le_inf le_rfl hYc).trans h
  have hYbot : Y = ⊥ := le_bot_iff.mp hYle_bot
  haveI hnt : Nontrivial (alternatingGroup (Fin 7)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hnt' : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := h7.some.toEquiv.nontrivial
  haveI : Subsingleton ↥Y := by
    rw [hYbot]
    infer_instance
  obtain ⟨x, y, hxy⟩ := hnt'
  exact hxy (Subsingleton.elim x y)

theorem pCoreOf_ne_bot₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Open.pCoreOf 2 Y₂ ≠ ⊥ :=
  pCoreOf_ne_bot_of_a7 h.item153 h.maxCE.1.mem₂ h.a7₂

theorem omegaOneCenterOf_le_R (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Quasithin.omegaOneCenterOf S ≤ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := by
  have hle := CFSG.Quasithin.Vol2.Ch10.V1C.C27.omegaOneCenterOf_le
    (K := Y₂) (R := S) (Q := CFSG.Open.pCoreOf 2 (Y₂ ⊔ S))
    (R_le h) (centralizer_R_le h)
  exact hle.trans (CFSG.Quasithin.A4.omegaOneCenterOf_le _)

theorem omegaOneCenterOf_inf_centralizer_eq_bot (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Quasithin.omegaOneCenterOf S ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxR : x ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := omegaOneCenterOf_le_R h hxZ
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    centralizer_singleton_le_normalizer_zpowers b hxC
  have hbot : x ∈ (⊥ : Subgroup G) := by
    rw [← h.free]
    exact ⟨hxR, hxN⟩
  exact hbot

theorem four_le_card_omegaOneCenterOf (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    4 ≤ Nat.card (CFSG.Quasithin.omegaOneCenterOf S) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := CFSG.Quasithin.omegaOneCenterOf S with hZ
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₂.prop
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hle := pCoreOf_le₂ h
    rw [hbot] at hle
    exact pCoreOf_ne_bot₂ h (le_bot_iff.mp hle)
  have hZ2 : IsPGroup 2 Z := hS2.to_le (CFSG.Quasithin.A4.omegaOneCenterOf_le S)
  have hZne : Z ≠ ⊥ := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hSne
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp h.omega_b).1
  have hBnorm : Subgroup.zpowers b ≤
      Subgroup.normalizer (Z : Set G) :=
    (Subgroup.zpowers_le.mpr hbA).trans
      (h.maxCE.1.s₂.prop.1.1.1.2.2.trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf S))
  letI : MulAction ↥(Subgroup.zpowers b) ↥Z :=
    MulAction.compHom _ (Subgroup.inclusion hBnorm)
  have hsmul : ∀ (g : ↥(Subgroup.zpowers b)) (z : ↥Z),
      ((g • z : ↥Z) : G) = (g : G) * (z : G) * (g : G)⁻¹ := by
    intro g z
    rw [MulAction.compHom_smul_def]
    rfl
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers b) ↥Z = {1} := by
    ext z
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hz
      have hbz := hz ⟨b, Subgroup.mem_zpowers b⟩
      have hcoe : b * (z : G) * b⁻¹ = (z : G) := by
        rw [← hsmul ⟨b, Subgroup.mem_zpowers b⟩ z]
        exact congrArg (fun w : ↥Z => (w : G)) hbz
      have hcomm : (z : G) * b = b * (z : G) := by
        calc (z : G) * b = (b * (z : G) * b⁻¹) * b := by rw [hcoe]
          _ = b * (z : G) := by group
      have hzC : (z : G) ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hbot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← omegaOneCenterOf_inf_centralizer_eq_bot h]
        exact ⟨z.2, hzC⟩
      rw [Subgroup.mem_bot] at hbot
      exact Subtype.ext hbot
    · rintro rfl g
      exact Subtype.ext (by rw [hsmul]; simp)
  have hfix_card : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers b) ↥Z) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  have hB3 : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [(zpowers_mem_omegaA_iff.mp h.omega_b).2.1]; norm_num)
  have hmod : Nat.card ↥Z ≡ 1 [MOD 3] := by
    have h := hB3.card_modEq_card_fixedPoints (α := ↥Z)
    rwa [hfix_card] at h
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hZne (Subgroup.card_eq_one.mp hm)
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [pow_one] at hm
    rw [hm] at hmod
    norm_num [Nat.ModEq] at hmod
  have hmge : 2 ≤ m := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := pow_le_pow_right' (by norm_num) hmge
    _ = Nat.card Z := hm.symm
    _ = Nat.card (CFSG.Quasithin.omegaOneCenterOf S) := by rw [hZ]

end Conf683

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16
