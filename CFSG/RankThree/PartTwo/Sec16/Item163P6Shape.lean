module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item16Res10ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y S : Subgroup G}

namespace Conf685

theorem inf_pCoreOf_eq_bot (h : Conf685 A c L Y S) {Y₀ : Subgroup G}
    (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) : L ⊓ CFSG.Open.pCoreOf 2 Y₀ = ⊥ := by
  have hLY : L ≤ Y₀ := h.le_y Y₀ hY₀
  have h2 : IsPGroup 2 ↥(L ⊓ CFSG.Open.pCoreOf 2 Y₀) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀).to_le inf_le_right
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀))
      ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hle : L ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm h2
  rw [h.pCoreOf_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem shape (h : Conf685 A c L Y S) {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) :
    Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∨
      (Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) ∧ A ≤ Y₀ ∧
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) := by
  have hLY : L ≤ Y₀ := h.le_y Y₀ hY₀
  rcases h.item1514 Y₀ hY₀ (h.meets G A c L h.sec15R Y₀ hY₀ hLY) with
    ⟨hcov, -, -, -, -⟩ | ⟨hA7, -, -, hYQ⟩ | ⟨-, -, -, -, hno, -⟩
  · left
    rw [inf_eq_right.mpr hLY] at hcov
    exact hcov
  · rcases hYQ with ⟨⟨φY⟩⟩ | ⟨⟨φY⟩⟩
    · left
      have hcardY : Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = 2520 := by
        rw [Nat.card_congr φY.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      have hcardL : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
        obtain ⟨φL⟩ := hA7
        rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      have hle := CFSG.RankThree.PartTwo.Sec16.Res10A7.le_sup_pCoreOf_of_card_le hLY
        (by rw [hcardY, hcardL])
      exact le_antisymm hle (sup_le hLY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀))
    · right
      refine ⟨⟨φY⟩, ?_, hA7⟩
      exact CFSG.RankThree.PartTwo.Sec16.Step163Alt.le_of_alternating_ten
        (CFSG.RankThree.PartTwo.Sec16.Res162.partTwoE_maximal h.sec15R)
        h.sec15R.toSec13Data.isElemAbelian hY₀.prop.1.1.2 hY₀.prop.2.2 φY
  · exact absurd hLY (hno Y₀ hY₀)

theorem cover (h : Conf685 A c L Y S) {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) :
    Y₀ = (Y₀ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ ∨ c ∈ Y₀ := by
  rcases shape h hY₀ with hcov | ⟨-, hAY₀, -⟩
  · left
    calc Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := hcov
      _ = (Y₀ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
        rw [inf_eq_right.mpr (h.le_y Y₀ hY₀)]
  · exact Or.inr (hAY₀ h.sec15R.toSec13Data.mem_A)

theorem theta_eq_bot
    (h : Conf685 A c L Y S) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have hL4 : L ∈ scriptY4 A (lB A) :=
    mem_scriptY4_of_le h.sec15R h.concl142 h.item1514 h.meets h.l4a7 h.mem_y
      (h.le_y Y h.mem_y)
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hL4.2.2.2
  have htypes := (h.sec15R.chosen136.2 c h.sec15R.zpowers_mem_omegaA L h.sec15R.mem_lA).1
  have hS : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.M22) := by
    rcases htypes with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)
  have hθeq := Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult hq hS
  rw [hθeq, ← CFSG.openPCoreOf_subgroupOf 2 L, h.pCoreOf_eq_bot]
  exact Subgroup.bot_subgroupOf (G := G) (H := L)

theorem isType163P6
    (h : Conf685 A c L Y S) : KFacts.IsType163P6 ↥L := by
  have hθ := theta_eq_bot h
  have hmeets := h.meets G A c L h.sec15R Y h.mem_y (h.le_y Y h.mem_y)
  let eθ : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
  have htypes := (h.sec15R.chosen136.2 c h.sec15R.zpowers_mem_omegaA L h.sec15R.mem_lA).1
  rcases htypes with hJ | hL3 | hA7 | hM22 | hM12
  · exact Or.inr (Or.inr (Or.inl ⟨eθ.symm.trans hJ.some⟩))
  · obtain ⟨p, e, hpf, he, hiso⟩ := hL3
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_isL3TwoPow ⟨e, he, hiso⟩
    have hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
      rcases h.item1514 Y h.mem_y hmeets with
        ⟨-, -, -, hprod, -⟩ | ⟨⟨φ7⟩, -, -, -⟩ | ⟨-, -, -, -, hno, -⟩
      · exact hprod
      · exfalso
        have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
          rw [Nat.card_congr φ7.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
        exact not_isoLThreePi_of_card_eq_2520 hcard p e hiso
      · exact absurd (h.le_y Y h.mem_y) (hno Y h.mem_y)
    refine Or.inr (Or.inr (Or.inr ⟨p, e, hpf, hp2, he, ?_, ?_⟩))
    · rcases hiso with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
      · exact Or.inl ⟨h3, ⟨eθ.symm.trans φ⟩⟩
      · exact Or.inr ⟨h3, ⟨eθ.symm.trans φ⟩⟩
    · exact Sec15.not_modNine_of_inner h.sec15R h.item138 KFacts.kSL3PiOrder3TypeC he hiso hprod
  · exact Or.inl ⟨eθ.symm.trans hA7.some⟩
  · exact Or.inr (Or.inl ⟨eθ.symm.trans hM22.some⟩)
  · exfalso
    rcases h.item1514 Y h.mem_y hmeets with
      ⟨-, -, -, -, hempty⟩ | ⟨⟨φ7⟩, -, -, -⟩ | ⟨-, -, -, -, hno, -⟩
    · exact hempty.false hM12.some
    · have hcard := Nat.card_congr (hM12.some.symm.trans φ7).toEquiv
      rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1,
        KFacts.KS14.card_nativeM12] at hcard
      norm_num at hcard
    · exact absurd (h.le_y Y h.mem_y) (hno Y h.mem_y)

theorem facts_inf
    (h : Conf685 A c L Y S) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hD := h.sec15R.toSec13Data
  have htypes := (h.sec15R.chosen136.2 c h.sec15R.zpowers_mem_omegaA L h.sec15R.mem_lA).1
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    Sec15.center_eq_bot_of_types hD.mem_thetaComponentsAt htypes
  have hmeets := h.meets G A c L h.sec15R Y h.mem_y (h.le_y Y h.mem_y)
  rcases h.item1514 Y h.mem_y hmeets with
    ⟨-, -, -, hprod, -⟩ | ⟨⟨φ7⟩, -, -, -⟩ | ⟨-, -, -, -, hno, -⟩
  · have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD hZ
    have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
      Sec13.card_inf_eq_nine hD (Sec13.isPerfect_lBar hD) hprod.some
    have hsup := Sec13.sup_zpowers_eq_of_card hD.card_eq inf_le_left h9 hD.mem_A
      (fun hc => hcL hc.2)
    rw [sup_comm] at hsup
    exact ⟨hcL, h9, hsup.symm⟩
  · have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rintro ⟨p, e, hpf, he, hiso⟩
      have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
        rw [Nat.card_congr φ7.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      exact not_isoLThreePi_of_card_eq_2520 hcard p e hiso
    exact Sec14.point_facts_of_inner h.item131 Sec13.sporadicModels131 hD hZ hnL3
  · exact absurd (h.le_y Y h.mem_y) (hno Y h.mem_y)

theorem isElemAbelian_inf (h : Conf685 A c L Y S) :
    CFSG.Open.IsElemAbelian 3 ((A ⊓ L).subgroupOf L) :=
  CFSG.Open.IsElemAbelian.subgroupOf
    (CFSG.Open.IsElemAbelian.mono h.sec15R.toSec13Data.isElemAbelian inf_le_left) L

theorem card_inf_subgroupOf
    (h : Conf685 A c L Y S) :
    Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  exact (facts_inf h).2.1

theorem isMaxInvTwo
    (h : Conf685 A c L Y S) :
    KFacts.IsMaxInvTwo ((A ⊓ L).subgroupOf L) ((S ⊓ L).subgroupOf L) := by
  have hD := h.sec15R.toSec13Data
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (mem_scriptQ_iff.mp h.mem_s.prop.1.1).2.1
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_s.prop.2
  have hD2 : IsPGroup 2 ((S ⊓ L).subgroupOf L) :=
    (hS2.to_le inf_le_left).comap_subtype (K := L)
  have hED : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((S ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have heA : (e : G) ∈ A := (Subgroup.mem_subgroupOf.mp he).1
    have hxSL : (x : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hx
    have hconjS : (e : G) * (x : G) * (e : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hAS heA) (x : G)).mp hxSL.1
    exact Subgroup.mem_subgroupOf.mpr ⟨hconjS,
      L.mul_mem (L.mul_mem e.2 x.2) (L.inv_mem e.2)⟩
  refine ⟨⟨hD2, hED⟩, ?_⟩
  intro T hT hDT
  set T₀ : Subgroup G := T.map L.subtype with hT₀
  have hT₀L : T₀ ≤ L := Subgroup.map_subtype_le _
  have hT₀2 : IsPGroup 2 T₀ := hT.1.map L.subtype
  have h3T₀ : ¬ 3 ∣ Nat.card T₀ := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT.1
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hALT₀ : A ⊓ L ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have he : (⟨a, ha.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr ha
    have hmem : (⟨a, ha.2⟩ : ↥L) * y * (⟨a, ha.2⟩ : ↥L)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hT.2 he) y).mp hy
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G) := by
    rw [(facts_inf h).2.2]
    refine sup_le ?_ hALT₀
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hT₀L hx))
  have hT₀inv : T₀ ∈ invariantPiSubgroups
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) :=
    ⟨hT₀L.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three T₀).mpr h3T₀, hAT₀⟩
  have hT₀Q : T₀ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_concl142 h.concl142 h.sec15R.zpowers_mem_omegaA hT₀inv
  have hT₀QPi : T₀ ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨hT₀Q, hT₀L⟩, (isPiSubgroup_piOf_iff Nat.prime_two T₀).mpr hT₀2⟩
  have hle : S ⊓ L ≤ T₀ := by
    have h := Subgroup.map_mono (f := L.subtype) hDT
    rwa [Subgroup.subgroupOf_map_subtype (S ⊓ L) L, inf_eq_left.mpr inf_le_right] at h
  have hT₀eq : T₀ = S ⊓ L := le_antisymm (h.mem_d.2 hT₀QPi hle) hle
  intro x hx
  have hxT₀ : (x : G) ∈ T₀ := ⟨x, hx, rfl⟩
  rw [hT₀eq] at hxT₀
  exact Subgroup.mem_subgroupOf.mpr ⟨hxT₀.1, x.2⟩

theorem xA_le_normalizer
    (h : Conf685 A c L Y S) (hN : KFacts.KS163P6Norm) :
    xA A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  intro x hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    xA_le_normalizer_of_mem_lA h.sec15R h.sec15R.zpowers_mem_omegaA h.sec15R.mem_lA hx
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := Sec14.pPrimeCoreOf_le 3 _ hx
  have hx3 : Nat.Coprime 3 (orderOf x) :=
    (Sec14.coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ hx)
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩ with hσ
  have hσfix : ∀ e ∈ (A ⊓ L).subgroupOf L, σ e = e := by
    intro e he
    have heA : (e : G) ∈ A := (Subgroup.mem_subgroupOf.mp he).1
    have hcomm : (e : G) * x = x * (e : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (e : G) heA
    apply Subtype.ext
    show x * (e : G) * x⁻¹ = (e : G)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hσdvd : orderOf σ ∣ orderOf x := by
    have h := orderOf_map_dvd L.normalizerMonoidHom ⟨x, hxL⟩
    rwa [← hσ, Subgroup.orderOf_mk] at h
  have hcopσ : Nat.Coprime (orderOf σ) 3 := (hx3.coprime_dvd_right hσdvd).symm
  have hmap := hN ↥L (isType163P6 h) ((A ⊓ L).subgroupOf L) (isElemAbelian_inf h)
    (card_inf_subgroupOf h) ((S ⊓ L).subgroupOf L) (isMaxInvTwo h) σ hσfix hcopσ
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hy' : (⟨y, hy.2⟩ : ↥L) ∈ (S ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
  have hσy : σ ⟨y, hy.2⟩ ∈ (S ⊓ L).subgroupOf L := by
    have := Subgroup.mem_map_of_mem σ.toMonoidHom hy'
    rwa [hmap] at this
  have hσyG : ((σ ⟨y, hy.2⟩ : ↥L) : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hσy
  show x * y * x⁻¹ ∈ S ⊓ L
  convert hσyG using 2
  show ((σ ⟨y, hy.2⟩ : ↥L) : G) = x * y * x⁻¹
  rfl

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6
