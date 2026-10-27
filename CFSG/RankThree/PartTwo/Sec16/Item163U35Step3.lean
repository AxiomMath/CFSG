module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35CE
import CFSG.RankThree.PartTwo.Sec16.Item163U35Y
import CFSG.RankThree.PartTwo.Sec16.Item163U35Pt
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofU
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1421
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

private theorem exists_card_nine_not_le_centralizer {E U X : Subgroup G} (hE : Late.IsE27 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hX2 : IsPGroup 2 X) (hXU : ¬ X ≤ U) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = 9 ∧ ¬ X ⊓ Subgroup.centralizer (B : Set G) ≤ U := by
  by_contra hno
  have hno' : ∀ B : Subgroup G, B ≤ E → Nat.card B = 9 →
      X ⊓ Subgroup.centralizer (B : Set G) ≤ U := by
    intro B hBE hB
    by_contra hBU
    exact hno ⟨B, hBE, hB, hBU⟩
  have hcop : Nat.Coprime 3 (Nat.card X) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact hXU (Sec5.le_of_forall_inf_centralizer_sub_le (p := 3) (k := 2) Nat.prime_three
    hE.1 (by rw [hE.2]; norm_num) hEX hcop hno')

private theorem exists_inf_not_mem_zpowers {E B₁ B₂ : Subgroup G} {c : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hEcard : Nat.card E = 27)
    (hB₁E : B₁ ≤ E) (hB₂E : B₂ ≤ E) (hB₁card : Nat.card B₁ = 9)
    (hB₂card : Nat.card B₂ = 9) (hcB₁ : c ∉ B₁)
    (hc3 : Nat.card (Subgroup.zpowers c) = 3) :
    ∃ a ∈ B₁ ⊓ B₂, a ∉ Subgroup.zpowers c := by
  have hEab : IsMulCommutative E := hE.1
  have hB₁C : B₁ ≤ Subgroup.centralizer (B₂ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hcomm : (⟨b, hB₁E hb⟩ : ↥E) * ⟨b', hB₂E hb'⟩ =
        ⟨b', hB₂E hb'⟩ * ⟨b, hB₁E hb⟩ := hEab.is_comm.comm _ _
    exact (congrArg Subtype.val hcomm).symm
  have hprod := Sec6.card_sup_mul_card_inf (X := B₁) (N := B₂)
    (hB₁C.trans (Subgroup.centralizer_le_normalizer (B₂ : Set G)))
  have hsup_le : Nat.card (B₁ ⊔ B₂ : Subgroup G) ≤ 27 := by
    rw [← hEcard]
    exact Subgroup.card_le_of_le (sup_le hB₁E hB₂E)
  have hdvd : Nat.card (B₁ ⊓ B₂ : Subgroup G) ∣ 9 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : B₁ ⊓ B₂ ≤ B₁)
    rwa [hB₁card] at h
  have hdvd' : Nat.card (B₁ ⊓ B₂ : Subgroup G) ∣ 3 ^ 2 := by simpa using hdvd
  obtain ⟨k, -, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkcard
    rw [hkcard, mul_one, hB₁card, hB₂card] at hprod
    omega
  have h3le : 3 ≤ Nat.card (B₁ ⊓ B₂ : Subgroup G) := by
    rw [hkcard]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDne : B₁ ⊓ B₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3le
    omega
  obtain ⟨⟨a, haD⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have ha1' : a ≠ 1 := fun hh => ha1 (Subtype.ext hh)
  refine ⟨a, haD, ?_⟩
  intro haz
  apply hcB₁
  have hordc : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hc3
  have hadvd : orderOf a ∣ orderOf c := orderOf_dvd_of_mem_zpowers haz
  have hane : orderOf a ≠ 1 := fun hh => ha1' (orderOf_eq_one_iff.mp hh)
  have ha3 : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hordc ▸ hadvd) with h | h
    · exact absurd h hane
    · exact h
  have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, ha3]
  have heq : Subgroup.zpowers a = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) (by rw [hcarda, hc3])
  exact (Subgroup.zpowers_le.mpr haD.1) (heq ▸ Subgroup.mem_zpowers c)

private theorem card_lt_of_not_le_sup_le {U P T T' : Subgroup G} (hP : ¬ P ≤ U)
    (hsup : P ⊔ U ≤ T ⊓ T') : Nat.card U < Nat.card (T ⊓ T' : Subgroup G) := by
  have hlt : U < P ⊔ U := by
    refine lt_of_le_of_ne le_sup_right (fun heq => hP ?_)
    rw [heq]
    exact le_sup_left
  exact (Subgroup.card_lt_of_lt hlt).trans_le (Subgroup.card_le_of_le hsup)

namespace Conf684

private theorem delta_data_of_isZeta (h : Conf684 A c L Y) {T K U : Subgroup G}
    (hTK : IsZeta A L T K) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    {a : G} (haA : a ∈ A) :
    IsPGroup 2 (T ⊓ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) : Subgroup G) ∧
      A ≤ Subgroup.normalizer
        (T ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G) : Set G) ∧
      T ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G) ∈
        scriptQ A (lB A) ∧
      T ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G) ≤
        delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ⊓
          Subgroup.normalizer (U : Set G) := by
  set P : Subgroup G :=
    T ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G) with hP
  have hTQ : T ∈ scriptQ A (lB A) := hTK.2.2.prop.1.1
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hTK.2.2.prop
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTQ.1.2.2
  have hANN : A ≤ Subgroup.normalizer (Subgroup.normalizer (U : Set G) : Set G) :=
    hAU.trans Subgroup.le_normalizer
  have hACa : A ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      h.sec15R.toSec13Data.isElemAbelian.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hNQ : T ⊓ Subgroup.normalizer (U : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hTQ inf_le_left (Late.le_normalizer_inf hAT hANN)
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    Late.le_normalizer_inf (Late.le_normalizer_inf hAT hANN) (hACa.trans Subgroup.le_normalizer)
  have hPQ : P ∈ scriptQ A (lB A) := mem_scriptQ_of_le hNQ inf_le_left hAP
  have hP2 : IsPGroup 2 P :=
    hT2.to_le ((inf_le_left : P ≤ T ⊓ Subgroup.normalizer (U : Set G)).trans inf_le_left)
  have hPN : P ≤ Subgroup.normalizer (U : Set G) :=
    (inf_le_left : P ≤ T ⊓ Subgroup.normalizer (U : Set G)).trans inf_le_right
  exact ⟨hP2, hAP, hPQ, le_inf (le_delta hPQ inf_le_right) hPN⟩

private theorem exists_isZeta_sup_top (h : Conf684 A c L Y) {U S : Subgroup G}
    (hUQ : U ∈ scriptQ A (lB A)) (hSQ : S ∈ scriptQ A (lB A))
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hS2 : IsPGroup 2 S) (hU2 : IsPGroup 2 U) :
    ∃ T₃ K₃, T₃ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧ S ⊔ U ≤ T₃ ∧ IsZeta A L T₃ K₃ := by
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.sec15R.toSec13Data.mem_partTwoE
  have hSUpi : S ⊔ U ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    sup_mem_scriptQPi_of_item146 hE27 h.item146
      ⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩
      ⟨⟨hUQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two U).mpr hU2⟩ hSU
  obtain ⟨T₃, hT₃, hSUT₃⟩ := Proof1413.exists_scriptQPiStar_top hSUpi
  obtain ⟨K₃, hK₃⟩ := h.exists_isZeta hT₃
  exact ⟨T₃, K₃, hT₃, hSUT₃, hK₃⟩

theorem false_of_not_le_centralizer (h : Conf684 A c L Y) {K₁ K₂ T₁ T₂ : Subgroup G}
    (hmax : MaxCE684 A L K₁ K₂ T₁ T₂) {a : G} (haA : a ∈ A)
    (haz : a ∉ Subgroup.zpowers c)
    (h₁ : ¬ T₁ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) ≤ T₁ ⊓ T₂)
    (h₂ : ¬ T₂ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) ≤ T₁ ⊓ T₂) : False := by
  obtain ⟨hz₁, hz₂, -, -⟩ := hmax.1
  set U : Subgroup G := T₁ ⊓ T₂ with hU
  set N₁ : Subgroup G := T₁ ⊓ Subgroup.normalizer (U : Set G) with hN₁
  set N₂ : Subgroup G := T₂ ⊓ Subgroup.normalizer (U : Set G) with hN₂
  set P₁ : Subgroup G := N₁ ⊓ Subgroup.centralizer ({a} : Set G) with hP₁
  set P₂ : Subgroup G := N₂ ⊓ Subgroup.centralizer ({a} : Set G) with hP₂
  have hP₁le : ¬ P₁ ≤ U := h₁
  have hP₂le : ¬ P₂ ≤ U := h₂
  have hT₁Q : T₁ ∈ scriptQ A (lB A) := hz₁.2.2.prop.1.1
  have hT₂Q : T₂ ∈ scriptQ A (lB A) := hz₂.2.2.prop.1.1
  have hT₁2 : IsPGroup 2 T₁ := isPGroup_of_mem_scriptQPi Nat.prime_two hz₁.2.2.prop
  have hT₂2 : IsPGroup 2 T₂ := isPGroup_of_mem_scriptQPi Nat.prime_two hz₂.2.2.prop
  have hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G) := hT₁Q.1.2.2
  have hAT₂ : A ≤ Subgroup.normalizer (T₂ : Set G) := hT₂Q.1.2.2
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := Late.le_normalizer_inf hAT₁ hAT₂
  have hUQ : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hT₁Q inf_le_left hAU
  have hU2 : IsPGroup 2 U := hT₁2.to_le inf_le_left
  obtain ⟨hP₁2, hAP₁, -, hP₁Δ⟩ :=
    delta_data_of_isZeta h hz₁ hAU haA
  obtain ⟨hP₂2, hAP₂, -, hP₂Δ⟩ :=
    delta_data_of_isZeta h hz₂ hAU haA
  obtain ⟨S, hP₁S, hS2, hAS, hSΔU, x, hx, hP₂Sx⟩ :=
    exists_conj_sylow h haA haz hAU hP₁2 hP₂2 hAP₁ hAP₂ hP₁Δ hP₂Δ
  have hSQ : S ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le (delta_centralizer_mem_scriptQ h haA haz)
      (hSΔU.trans inf_le_left) hAS
  obtain ⟨T₃, K₃, -, hSUT₃, hK₃⟩ :=
    exists_isZeta_sup_top h hUQ hSQ (hSΔU.trans inf_le_right) hS2 hU2
  have hP₁U_le : P₁ ⊔ U ≤ T₁ ⊓ T₃ :=
    le_inf (sup_le (inf_le_left.trans inf_le_left) inf_le_left)
      (sup_le ((hP₁S.trans le_sup_left).trans hSUT₃) (le_sup_right.trans hSUT₃))
  have hcard₁ : Nat.card (T₁ ⊓ T₂ : Subgroup G) < Nat.card (T₁ ⊓ T₃ : Subgroup G) :=
    card_lt_of_not_le_sup_le hP₁le hP₁U_le
  obtain ⟨y₁, hy₁, hK₁⟩ := hmax.exists_conj_of_card_lt hz₁ hK₃ hcard₁
  have hK₃x : IsZeta A L (T₃.map (MulAut.conj x).toMonoidHom)
      (K₃.map (MulAut.conj x).toMonoidHom) :=
    map_conj_isZeta h (((pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G))).trans
      (Subgroup.centralizer_le_normalizer (A : Set G))) hx.1) hK₃
  have hUmap : U.map (MulAut.conj x).toMonoidHom = U :=
    Late.map_conj_eq_of_mem_normalizer hx.2
  have hU_le : U ≤ T₃.map (MulAut.conj x).toMonoidHom := by
    rw [← hUmap]
    exact Subgroup.map_mono (le_sup_right.trans hSUT₃)
  have hP₂U_le : P₂ ⊔ U ≤ T₂ ⊓ T₃.map (MulAut.conj x).toMonoidHom :=
    le_inf (sup_le (inf_le_left.trans inf_le_left) inf_le_right)
      (sup_le (hP₂Sx.trans (Subgroup.map_mono (le_sup_left.trans hSUT₃))) hU_le)
  have hcard₂ : Nat.card (T₁ ⊓ T₂ : Subgroup G) <
      Nat.card (T₂ ⊓ T₃.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
    card_lt_of_not_le_sup_le hP₂le hP₂U_le
  obtain ⟨y₂, hy₂, hK₂⟩ := hmax.exists_conj_of_card_lt hz₂ hK₃x hcard₂
  have hK₂' : K₂ = K₃.map (MulAut.conj (y₂ * x)).toMonoidHom := by
    rw [hK₂, Late.map_conj_map_conj]
  refine hmax.1.not_conj
    ⟨y₁ * x⁻¹ * y₂⁻¹, mul_mem (mul_mem hy₁ (inv_mem hx.1)) (inv_mem hy₂), ?_⟩
  rw [hK₁, hK₂', Late.map_conj_map_conj,
    show (y₁ * x⁻¹ * y₂⁻¹) * (y₂ * x) = y₁ by group]

theorem not_le_left_of_maxCE684 (h : Conf684 A c L Y) {K₁ K₂ T₁ T₂ : Subgroup G}
    (hmax : MaxCE684 A L K₁ K₂ T₁ T₂) (hne₁ : T₁ ⊓ T₂ ≠ T₁) (hne₂ : T₁ ⊓ T₂ ≠ T₂) :
    ¬ T₁ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ≤ T₁ ⊓ T₂ := by
  intro hle
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.sec15R.toSec13Data.mem_partTwoE
  obtain ⟨hz₁, hz₂, -, -⟩ := hmax.1
  set U : Subgroup G := T₁ ⊓ T₂ with hU
  set N₁ : Subgroup G := T₁ ⊓ Subgroup.normalizer (U : Set G) with hN₁
  set N₂ : Subgroup G := T₂ ⊓ Subgroup.normalizer (U : Set G) with hN₂
  have hle' : N₁ ⊓ Subgroup.centralizer ({c} : Set G) ≤ U := hle
  have hT₁Q : T₁ ∈ scriptQ A (lB A) := hz₁.2.2.prop.1.1
  have hT₂Q : T₂ ∈ scriptQ A (lB A) := hz₂.2.2.prop.1.1
  have hT₁2 : IsPGroup 2 T₁ := isPGroup_of_mem_scriptQPi Nat.prime_two hz₁.2.2.prop
  have hT₂2 : IsPGroup 2 T₂ := isPGroup_of_mem_scriptQPi Nat.prime_two hz₂.2.2.prop
  have hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G) := hT₁Q.1.2.2
  have hAT₂ : A ≤ Subgroup.normalizer (T₂ : Set G) := hT₂Q.1.2.2
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := Late.le_normalizer_inf hAT₁ hAT₂
  have hANN : A ≤ Subgroup.normalizer (Subgroup.normalizer (U : Set G) : Set G) :=
    hAU.trans Subgroup.le_normalizer
  have hAN₁ : A ≤ Subgroup.normalizer (N₁ : Set G) := Late.le_normalizer_inf hAT₁ hANN
  have hAN₂ : A ≤ Subgroup.normalizer (N₂ : Set G) := Late.le_normalizer_inf hAT₂ hANN
  have hN₁2 : IsPGroup 2 N₁ := hT₁2.to_le inf_le_left
  have hN₂2 : IsPGroup 2 N₂ := hT₂2.to_le inf_le_left
  have hlt₁ : Nat.card U < Nat.card N₁ :=
    (Proof162.card_lt_and_mem_of_lt (S := T₁) (U := U) hz₁.2.2.prop hAU inf_le_left hne₁).1
  have hlt₂ : Nat.card U < Nat.card N₂ :=
    (Proof162.card_lt_and_mem_of_lt (S := T₂) (U := U) hz₂.2.2.prop hAU inf_le_right hne₂).1
  have hN₁U : ¬ N₁ ≤ U := fun hle => absurd (Subgroup.card_le_of_le hle) (Nat.not_le.mpr hlt₁)
  have hN₂U : ¬ N₂ ≤ U := fun hle => absurd (Subgroup.card_le_of_le hle) (Nat.not_le.mpr hlt₂)
  obtain ⟨B₁, hB₁E, hB₁card, hB₁ne⟩ :=
    exists_card_nine_not_le_centralizer hE27 hAN₁ hN₁2 hN₁U
  obtain ⟨B₂, hB₂E, hB₂card, hB₂ne⟩ :=
    exists_card_nine_not_le_centralizer hE27 hAN₂ hN₂2 hN₂U
  have hcB₁ : c ∉ B₁ := by
    intro hc
    exact hB₁ne ((inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc))).trans hle')
  obtain ⟨a, haD, haz⟩ := exists_inf_not_mem_zpowers hE27.1 hE27.2 hB₁E hB₂E hB₁card
    hB₂card hcB₁ h.sec15R.toSec13Data.card_zpowers
  refine false_of_not_le_centralizer h hmax (hB₁E haD.1) haz ?_ ?_
  · intro hcon
    exact hB₁ne ((inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD.1))).trans hcon)
  · intro hcon
    exact hB₂ne ((inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD.2))).trans hcon)

theorem not_le_right_of_maxCE684 (h : Conf684 A c L Y) {K₁ K₂ T₁ T₂ : Subgroup G}
    (hmax : MaxCE684 A L K₁ K₂ T₁ T₂) (hne₁ : T₁ ⊓ T₂ ≠ T₁) (hne₂ : T₁ ⊓ T₂ ≠ T₂) :
    ¬ T₂ ⊓ Subgroup.normalizer ((T₁ ⊓ T₂ : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ≤ T₁ ⊓ T₂ := by
  intro hle
  have hne₂' : T₂ ⊓ T₁ ≠ T₂ := by rwa [inf_comm T₂ T₁]
  have hne₁' : T₂ ⊓ T₁ ≠ T₁ := by rwa [inf_comm T₂ T₁]
  refine not_le_left_of_maxCE684 h hmax.symm hne₂' hne₁' ?_
  simpa only [inf_comm T₁ T₂] using hle

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
