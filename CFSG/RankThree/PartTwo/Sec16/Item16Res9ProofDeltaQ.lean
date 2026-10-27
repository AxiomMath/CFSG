module

public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofVB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res9DeltaQ

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_cover {P Y L : Subgroup G} (hP2 : IsPGroup 2 P) (hPY : P ≤ Y)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hLY : L ≤ Y)
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y) : P ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  set M := P ⊔ O with hM
  have hMY : M ≤ Y := sup_le hPY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hM2 : IsPGroup 2 M := IsPGroup.to_sup_of_normal_right' hP2 hO2 (hPY.trans hYO)
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := Sec14.le_normalizer_sup hLP (hLY.trans hYO)
  have hOM : O ≤ Subgroup.normalizer (M : Set G) := le_sup_right.trans Subgroup.le_normalizer
  have hYM : Y ≤ Subgroup.normalizer (M : Set G) :=
    hcov.le.trans (sup_le (inf_le_right.trans hLM) hOM)
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hMY hYM hM2)

theorem le_sup_pCoreOf_of_card {L Y : Subgroup G} (hLY : L ≤ Y)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥)
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Nat.card L) :
    Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hLO : L ⊓ O = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hLY.trans hYO))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right)
  set φ : ↥L →* ↥Y ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hLY) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : Subgroup.inclusion hLY l ∈ N := (QuotientGroup.eq_one_iff _).mp hl
    have h2 : (l : G) ∈ L ⊓ O :=
      ⟨l.2, ⟨Subgroup.inclusion hLY l, by exact h1, rfl⟩⟩
    rw [hLO] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hrange : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hcard
  intro y hy
  obtain ⟨l, hl⟩ : QuotientGroup.mk' N ⟨y, hy⟩ ∈ φ.range := hrange ▸ Subgroup.mem_top _
  have h3 : (Subgroup.inclusion hLY l)⁻¹ * ⟨y, hy⟩ ∈ N := QuotientGroup.eq.mp hl
  have h4 : (l : G)⁻¹ * y ∈ O :=
    ⟨(Subgroup.inclusion hLY l)⁻¹ * ⟨y, hy⟩, by exact h3, rfl⟩
  have hy' : y = (l : G) * ((l : G)⁻¹ * y) := by group
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right h4)

theorem le_pCoreOf_of_alternating {P Y L : Subgroup G} (hP2 : IsPGroup 2 P) (hPY : P ≤ Y)
    (hLY : L ≤ Y) (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hO : CFSG.Open.pCoreOf 2 L = ⊥)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    (χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    P ≤ CFSG.Open.pCoreOf 2 Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set π : ↥Y →* Equiv.Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp (QuotientGroup.mk' N)) with hπ
  have hπA : ∀ y, π y ∈ alternatingGroup (Fin 10) := fun y => (φ (QuotientGroup.mk' N y)).2
  have hπ1 : ∀ y : ↥Y, π y = 1 → (y : G) ∈ O := by
    intro y h
    rw [← Step163Alt.mem_pCore_two_iff]
    have h' : φ (QuotientGroup.mk' N y) = 1 := Subtype.val_injective h
    exact (QuotientGroup.eq_one_iff y).mp ((map_eq_one_iff φ φ.injective).mp h')
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  set M := P ⊔ O with hM
  have hM2 : IsPGroup 2 M := IsPGroup.to_sup_of_normal_right' hP2 hO2 (hPY.trans hYO)
  have hLM : L ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer
        (Sec14.le_normalizer_sup hLP (hLY.trans hYO))) (hM2.to_le inf_le_right)
  set fL : ↥L →* Equiv.Perm (Fin 10) := π.comp (Subgroup.inclusion hLY) with hfL
  set fP : ↥P →* Equiv.Perm (Fin 10) := π.comp (Subgroup.inclusion hPY) with hfP
  have hfLinj : Function.Injective fL := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : ((Subgroup.inclusion hLY l : ↥Y) : G) ∈ O := hπ1 _ hl
    have h2 : (l : G) ∈ L ⊓ M := ⟨l.2, Subgroup.mem_sup_right h1⟩
    rw [hLM] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  set K := fL.range with hK
  set V := fP.range with hV
  have hVA : V ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨p, rfl⟩
    exact hπA _
  have hKA : K ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨l, rfl⟩
    exact hπA _
  have hV2 : IsPGroup 2 V := hP2.of_surjective fP.rangeRestrict fP.rangeRestrict_surjective
  have hKV : K ≤ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 10))) := by
    rintro _ ⟨l, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨p, rfl⟩ := hx
    have hlp : (l : G) * p * (l : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hLP l.2) p).mp p.2
    refine ⟨⟨_, hlp⟩, ?_⟩
    change π (Subgroup.inclusion hPY ⟨_, hlp⟩) = π (Subgroup.inclusion hLY l) *
      π (Subgroup.inclusion hPY p) * (π (Subgroup.inclusion hLY l))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hVK : V ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨p, rfl⟩, ⟨l, hl⟩⟩
    have h1 : π ((Subgroup.inclusion hLY l)⁻¹ * Subgroup.inclusion hPY p) = 1 := by
      rw [map_mul, map_inv]
      change (fL l)⁻¹ * fP p = 1
      rw [hl, inv_mul_cancel]
    have h2 := hπ1 _ h1
    have h3 : (l : G) ∈ L ⊓ M := by
      refine ⟨l.2, ?_⟩
      have e : (l : G) = (p : G) *
          ((((Subgroup.inclusion hLY l)⁻¹ * Subgroup.inclusion hPY p : ↥Y)) : G)⁻¹ := by
        simp
      rw [e]
      exact M.mul_mem (Subgroup.mem_sup_left p.2) (M.inv_mem (Subgroup.mem_sup_right h2))
    rw [hLM] at h3
    have hl1 : l = 1 := Subtype.ext (Subgroup.mem_bot.mp h3)
    rw [Subgroup.mem_bot, ← hl, hl1, map_one]
  have h2520 : 2520 ∣ Nat.card K := by
    rw [hK, ← Nat.card_congr (MonoidHom.ofInjective hfLinj).toEquiv]
    have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
    rwa [Nat.card_congr χ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h1
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ψ : ↥L →* alternatingGroup (Fin 7) := χ.toMonoidHom.comp (QuotientGroup.mk' θ) with hψ
  have hψsurj : Function.Surjective ψ := χ.surjective.comp (QuotientGroup.mk'_surjective θ)
  obtain ⟨l₅, hl₅⟩ := hψsurj ⟨Res9A10.cFive, Res9A10.cFive_mem⟩
  obtain ⟨e, m, hm5, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos l₅).ne' 5
    (by norm_num)
  set y₀ := l₅ ^ m with hy₀
  have hy₀5 : y₀ ^ (5 ^ e) = 1 := by
    rw [hy₀, ← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have hψy₀ : ψ y₀ ≠ 1 := by
    rw [hy₀, map_pow, hl₅]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [Subgroup.orderOf_mk, Res9A10.orderOf_cFive] at h1
    exact hm5 h1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy5 : IsPGroup 5 (Subgroup.zpowers (fL y₀)) := by
    have h1 : fL y₀ ^ (5 ^ e) = 1 := by rw [← map_pow, hy₀5, map_one]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
      (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hVbot : V = ⊥ := by
    refine Res9A10.eq_bot_of_normalized hVA hKA hV2 hKV hVK h2520 (y := fL y₀) ⟨y₀, rfl⟩ hy5 ?_
    intro N' hNK hKN hyN
    set N'' := N'.comap fL with hN''
    have hN''n : N''.Normal := ⟨fun n hn l => by
      change fL (l * n * l⁻¹) ∈ N'
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hKN ⟨l, rfl⟩) (fL n)).mp hn⟩
    have hmap : N''.map ψ = ⊤ := by
      have hn := hN''n.map ψ hψsurj
      rcases hsimple.eq_bot_or_eq_top_of_normal (H := N''.map ψ) with h | h
      · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_map_of_mem ψ hyN)) hψy₀
      · exact h
    obtain ⟨n, hnN, hn⟩ : (⟨Res9A10.cSeven, Res9A10.cSeven_mem⟩ : alternatingGroup (Fin 7)) ∈
        N''.map ψ := hmap ▸ Subgroup.mem_top _
    have hon : 7 ∣ orderOf n := by
      have h1 := orderOf_map_dvd ψ n
      rwa [hn, Subgroup.orderOf_mk, Res9A10.orderOf_cSeven] at h1
    refine ⟨fL (n ^ (orderOf n / 7)), N''.pow_mem hnN _, ?_⟩
    rw [orderOf_injective fL hfLinj, orderOf_pow_orderOf_div (orderOf_pos n).ne' hon]
  intro p hp
  have h1 : fP ⟨p, hp⟩ ∈ V := ⟨⟨p, hp⟩, rfl⟩
  rw [hVbot, Subgroup.mem_bot] at h1
  exact hπ1 _ h1

theorem le_of_mem_of_fpf {P Y : Subgroup G} {c : G} (hP2 : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hc3 : IsPGroup 3 (Subgroup.zpowers c))
    (hfpf : P ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) (hcY : c ∈ Y) : P ≤ Y := by
  have hcP' : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hcP
  have hP3 : ¬ 3 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers c) P hc3 hP3 hcP'
  have hbot' : P ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hfpf]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  rw [hbot', sup_bot_eq] at hfac
  rw [hfac, Subgroup.commutator_le]
  intro p hp x hx
  have hxY : x ∈ Y := (Subgroup.zpowers_le.mpr hcY) hx
  rw [commutatorElement_def]
  exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPY hp) x).mp hxY) (Y.inv_mem hxY)

end Res9DeltaQ

open Res9DeltaQ

theorem Res9DeltaQ.mem_scriptQ_of_alternating_ten (h142 : Concl142R) (h1514 : Item1514R)
    (hMeets : Step163Meets) (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hL : ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) {R : Subgroup G}
    (hgood : GoodR163 A L R) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hfpf : CFSG.Open.pCoreOf 2 (R ⊔ L) ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 (R ⊔ L) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := hR.toSec13Data
  have hLY : L ≤ Y := hL Y hY
  have hFE : partTwoF G = partTwoE G :=
    (hR.toTheoremFourHyp.partTwoF_eq_partTwoE hR.partTwoS_eq).1
  have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
      E ≤ B → B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
  have hcY : c ∈ Y := Step163Alt.le_of_alternating_ten hmax hD.isElemAbelian hY.prop.1.1.2
    hY.prop.2.2 φ hD.mem_A
  have hQ0 : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    ProofVB167.pCoreOf_mem_scriptQ_of_cover hR.toSec14Std (h1444 G A c L hR.toSec14Std)
      (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std) (h142 G A c L hR) hY.prop.1
      (Or.inr hcY)
  set P := CFSG.Open.pCoreOf 2 (R ⊔ L) with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (R ⊔ L)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hgood.1.1.1.1.2.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    (Sec14.le_normalizer_sup hAR hAL).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (R ⊔ L))
  have hLP : L ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (R ⊔ L))
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ L)).trans
      (sup_le hRY (hLY.trans Subgroup.le_normalizer))
  have hPleY : P ≤ Y :=
    Res9DeltaQ.le_of_mem_of_fpf hP2 hPY (hAP hD.mem_A)
      (IsPGroup.of_card (n := 1) (by rw [hD.card_zpowers, pow_one])) hfpf hcY
  have hPO : P ≤ CFSG.Open.pCoreOf 2 Y := by
    rcases h1514 G A c L hR Y hY (hMeets G A c L hR Y hY hLY) with
      ⟨hcov, -⟩ | ⟨⟨h7⟩, -⟩ | ⟨-, -, -, -, hno, -⟩
    · exact Res9DeltaQ.le_pCoreOf_of_cover hP2 hPleY hLP hLY hcov
    · exact Res9DeltaQ.le_pCoreOf_of_alternating hP2 hPleY hLY hLP hO φ h7
    · exact absurd hLY (hno Y hY)
  exact mem_scriptQ_of_le hQ0 hPO hAP

end CFSG.RankThree.PartTwo.Sec16
