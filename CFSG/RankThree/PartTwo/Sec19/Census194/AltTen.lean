module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.AGLEmbedding

theorem exp_le_seven_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 1814400) : k ≤ 7 := by
  by_contra hk
  have h8 : 2 ^ 8 ∣ 1814400 := (pow_dvd_pow 2 (by omega)).trans h
  exact absurd h8 (by decide)

theorem two_pow_mul_lieExp_dvd {t : StatedLieTag} {n f : ℕ} (hn : lieMin t ≤ n)
    (h : lieOrd t n (2 ^ f) = 1814400) : 2 ^ (f * lieExp t n) ∣ 1814400 := by
  rw [pow_mul, ← h]
  exact pow_lieExp_dvd hn _

theorem le_seven_of_mul_le {f e : ℕ} (hf : 1 ≤ f) (h : f * e ≤ 7) : e ≤ 7 := by
  nlinarith

theorem le_four_of_tri_le {n : ℕ} (h : (n - 1) * n / 2 ≤ 7) : n ≤ 4 := by
  by_contra hc
  have h1 : 4 * 5 ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 20 / 2 ≤ (n - 1) * n / 2 := Nat.div_le_div_right h1
  norm_num at h2
  linarith

theorem ordA_ne_alt10 {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (h : f * ((n - 1) * n / 2) ≤ 7) : CFSG.Open.ordA (n - 1) (2 ^ f) ≠ 1814400 := by
  have hn4 : n ≤ 4 := le_four_of_tri_le (le_seven_of_mul_le hf h)
  interval_cases n <;> norm_num at h <;> have hf7 : f ≤ 7 := by omega
  all_goals interval_cases f <;> first | omega | decide +kernel

theorem ordTwistedA_ne_alt10 {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (h : f * ((n - 1) * n / 2) ≤ 7) : CFSG.Open.ordTwistedA (n - 1) (2 ^ f) ≠ 1814400 := by
  have hn4 : n ≤ 4 := le_four_of_tri_le (le_seven_of_mul_le hf h)
  interval_cases n <;> norm_num at h <;> have hf7 : f ≤ 7 := by omega
  all_goals interval_cases f <;> first | omega | decide +kernel

theorem ordBC_ne_alt10 {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (h : f * (n * n) ≤ 7) :
    CFSG.Open.ordBC n (2 ^ f) ≠ 1814400 := by
  have hsq : n * n ≤ 7 := le_seven_of_mul_le hf h
  have hn2 : n ≤ 2 := by
    by_contra hc
    have h3 : 3 * 3 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    linarith
  obtain rfl : n = 2 := by omega
  norm_num at h
  have hf1 : f ≤ 1 := by omega
  obtain rfl : f = 1 := by omega
  decide +kernel

theorem orthogonal_false {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (h : f * (n * (n - 1)) ≤ 7) :
    False := by
  have h1 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have h2 := le_seven_of_mul_le hf h
  linarith

theorem alt10_false_PSL {G : Type} [Group G] {n p f : ℕ} (hp : p = 2)
    (hm : StatedClassicalModel G .PSL n p f) (hG : Nat.card G = 1814400) : False := by
  subst hp
  have hord : lieOrd .PSL n (2 ^ f) = 1814400 := (card_eq_lieOrd_of_classical hm).symm.trans hG
  have hadm : StatedLieAdmissible .PSL n 2 f := hm.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have h7 : f * ((n - 1) * n / 2) ≤ 7 :=
    exp_le_seven_of_two_pow_dvd (two_pow_mul_lieExp_dvd (t := .PSL) hn hord)
  exact ordA_ne_alt10 hn hf h7 hord

theorem alt10_false_PSU {G : Type} [Group G] {n p f : ℕ} (hp : p = 2)
    (hm : StatedClassicalModel G .PSU n p f) (hG : Nat.card G = 1814400) : False := by
  subst hp
  have hord : lieOrd .PSU n (2 ^ f) = 1814400 := (card_eq_lieOrd_of_classical hm).symm.trans hG
  have hadm : StatedLieAdmissible .PSU n 2 f := hm.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have h7 : f * ((n - 1) * n / 2) ≤ 7 :=
    exp_le_seven_of_two_pow_dvd (two_pow_mul_lieExp_dvd (t := .PSU) hn hord)
  exact ordTwistedA_ne_alt10 hn hf h7 hord

theorem alt10_false_PSp {G : Type} [Group G] {n p f : ℕ} (hp : p = 2)
    (hm : StatedClassicalModel G .PSp n p f) (hG : Nat.card G = 1814400) : False := by
  subst hp
  have hord : lieOrd .PSp n (2 ^ f) = 1814400 := (card_eq_lieOrd_of_classical hm).symm.trans hG
  have hadm : StatedLieAdmissible .PSp n 2 f := hm.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have h7 : f * (n * n) ≤ 7 :=
    exp_le_seven_of_two_pow_dvd (two_pow_mul_lieExp_dvd (t := .PSp) hn hord)
  exact ordBC_ne_alt10 hn hf h7 hord

theorem alt10_false_POmegaPlus {G : Type} [Group G] {n p f : ℕ} (hp : p = 2)
    (hm : StatedClassicalModel G .POmegaPlus n p f) (hG : Nat.card G = 1814400) : False := by
  subst hp
  have hord : lieOrd .POmegaPlus n (2 ^ f) = 1814400 :=
    (card_eq_lieOrd_of_classical hm).symm.trans hG
  have hadm : StatedLieAdmissible .POmegaPlus n 2 f := hm.1
  have hn : 4 ≤ n := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have h7 : f * (n * (n - 1)) ≤ 7 :=
    exp_le_seven_of_two_pow_dvd (two_pow_mul_lieExp_dvd (t := .POmegaPlus) hn hord)
  exact orthogonal_false hn hf h7

theorem alt10_false_POmegaMinus {G : Type} [Group G] {n p f : ℕ} (hp : p = 2)
    (hm : StatedClassicalModel G .POmegaMinus n p f) (hG : Nat.card G = 1814400) : False := by
  subst hp
  have hord : lieOrd .POmegaMinus n (2 ^ f) = 1814400 :=
    (card_eq_lieOrd_of_classical hm).symm.trans hG
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f := hm.1
  have hn : 4 ≤ n := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have h7 : f * (n * (n - 1)) ≤ 7 :=
    exp_le_seven_of_two_pow_dvd (two_pow_mul_lieExp_dvd (t := .POmegaMinus) hn hord)
  exact orthogonal_false hn hf h7

theorem alt10_false_of_classical_index
    (hG2 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group ≠ 1814400)
    (idx : TauCeti.LieTypeIndex) (hv : idx.Valid) {Y : Type} [Group Y]
    (hd : IsClassicalOrG2Index idx) (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨idx, hv⟩).Group)
    (hG : Nat.card Y = 1814400) : False := by
  cases idx
  case A r q =>
    have hp : q.p = 2 := hd
    exact alt10_false_PSL hp (CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e) hG
  case twistedA r q =>
    have hp : q.p = 2 := hd
    exact alt10_false_PSU hp (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hG
  case B r q =>
    have hp : q.p = 2 := hd
    have hr2 : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · obtain rfl : r = 2 := by omega
      exact alt10_false_PSp hp (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hG
    · exact alt10_false_PSp hp
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp h3 e) hG
  case D r q =>
    have hp : q.p = 2 := hd
    exact alt10_false_POmegaPlus hp
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e) hG
  case twistedD r q =>
    have hp : q.p = 2 := hd
    exact alt10_false_POmegaMinus hp
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e) hG
  case G2 q =>
    have hp : q.p = 2 := hd
    exact hG2 q hv hp ((Nat.card_congr e.toEquiv).symm.trans hG)
  all_goals exact (show False from hd).elim

theorem alt_card_ne_alt10 {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 1814400 := by
  rcases hn with rfl | rfl | rfl <;>
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] <;> decide

theorem alt10_false_A17 {Y : Type} [Group Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) (hG : Nat.card Y = 1814400) : False := by
  have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  have hord : lieOrd .PSL (1 + 1) (q.p ^ q.exponent) = 1814400 :=
    (card_eq_lieOrd_of_classical hm).symm.trans hG
  rw [← TauCeti.PrimePower.card_def, hq] at hord
  have key : CFSG.Open.ordA 1 7 ≠ 1814400 := by decide +kernel
  exact key hord

theorem alt10_false_U23 {Y : Type} [Group Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) (hG : Nat.card Y = 1814400) :
    False := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hord : lieOrd .PSU (2 + 1) (q.p ^ q.exponent) = 1814400 :=
    (card_eq_lieOrd_of_classical hm).symm.trans hG
  rw [← TauCeti.PrimePower.card_def, hq] at hord
  have key : CFSG.Open.ordTwistedA 2 3 ≠ 1814400 := by decide +kernel
  exact key hord

theorem not_isClassicalTwoOrG2_alt_ten_of_G2_order
    (hG2 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group ≠ 1814400) :
    ¬ IsClassicalTwoOrG2 (alternatingGroup (Fin 10)) := by
  have hY : Nat.card (alternatingGroup (Fin 10)) = 1814400 :=
    CFSG.RankThree.PartTwo.Sec15.card_alternatingGroup_ten
  rintro (⟨⟨idx, hv⟩, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩)
  · exact alt10_false_of_classical_index hG2 idx hv hd e hY
  · exact alt_card_ne_alt10 hn ((Nat.card_congr e.toEquiv).symm.trans hY)
  · dsimp only at hd
    rcases hd with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact alt10_false_A17 q hv hq e hY
    · exact alt10_false_U23 q hv hq e hY

theorem four_le_of_two_pow {e : ℕ} (h : 3 ≤ 2 ^ e) : 4 ≤ 2 ^ e := by
  rcases Nat.lt_or_ge e 2 with he | he
  · interval_cases e <;> norm_num at h
  · calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem ordG2_ne_alt10 {x : ℕ} (hx : 4 ≤ x) : ordG2 x ≠ 1814400 := by
  have h6 : 4 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have h2 : 4 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  have hbig : 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1) ≤ x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h6 (Nat.sub_le_sub_right h6 1))
      (Nat.sub_le_sub_right h2 1)
  show x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) ≠ 1814400
  intro heq
  have hle := hbig.trans_eq heq
  norm_num at hle

theorem not_isClassicalTwoOrG2_alt_ten_of_G2_formula
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = ordG2 q.card) :
    ¬ IsClassicalTwoOrG2 (alternatingGroup (Fin 10)) := by
  refine not_isClassicalTwoOrG2_alt_ten_of_G2_order (fun q hv hp => ?_)
  rw [hord q hv hp]
  have h3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
  have h4 : 4 ≤ q.card := by
    rw [hq]
    exact four_le_of_two_pow (by rw [← hq]; exact h3)
  exact ordG2_ne_alt10 h4

theorem not_isClassicalTwoOrG2_alt_ten :
    ¬ IsClassicalTwoOrG2 (alternatingGroup (Fin 10)) :=
  not_isClassicalTwoOrG2_alt_ten_of_G2_formula fun q hv _ =>
    CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv

end CFSG.RankThree.PartTwo.Sec19.Census194
