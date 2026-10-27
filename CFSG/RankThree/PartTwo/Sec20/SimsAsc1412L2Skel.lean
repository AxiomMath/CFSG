module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

@[expose] def NoSmallEight1412 (X : Type) [Group X] (L : Subgroup X) (t : X) : Prop :=
  ∀ I : Subgroup X, I.Normal → Sec3.IsElemTwo I → (∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) →
    8 < (centralizer ({t} : Set X)).relIndex I

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

@[expose] noncomputable def pTwo (T P : Subgroup X) : Subgroup X :=
  sSup {A | A ∈ Sec3.famG T 2 ∧ A ≤ P}

omit [Finite X] in
theorem pTwo_le (T P : Subgroup X) : pTwo T P ≤ P := sSup_le fun _ h => h.2

omit [Finite X] in
theorem pTwo_le_jG (T P : Subgroup X) : pTwo T P ≤ Sec3.jG T 2 :=
  sSup_le fun _ h => Sec3.le_jG h.1

omit [Finite X] in
theorem le_pTwo {T P A : Subgroup X} (h : A ∈ Sec3.famG T 2) (hP : A ≤ P) : A ≤ pTwo T P :=
  le_sSup ⟨h, hP⟩

omit [Finite X] in
theorem conj_mem_pTwo {T P : Subgroup X} (hPT : P ≤ T) {g : X}
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {x : X} (hx : x ∈ pTwo T P) : g * x * g⁻¹ ∈ pTwo T P := by
  have hle : (pTwo T P).map (MulAut.conj g).toMonoidHom ≤ pTwo T P := by
    rw [pTwo, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    refine iSup₂_le fun A hA => le_sSup ⟨Sec3.map_conj_mem_famG hA.1 g
      (fun a ha => hPT (hgP a (hA.2 ha))), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hgP a (hA.2 ha)
  exact hle ⟨x, hx, rfl⟩

theorem relIndex_centralizer_omegaG_le_of_famG {Q : Subgroup X} (hQS : Q ≤ S) {i : ℕ}
    {B : Subgroup X} (hB : B ∈ Sec3.famG S i) {t : X} (htB : t ∈ B) :
    (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q) ≤ 2 ^ i * Q.relIndex B := by
  have hQV : Q ≤ centralizer ((Sec3.omegaG Q : Subgroup X) : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have h1 := Sec3.relIndex_centralizer_le_of_famG ((Sec3.omegaG_le Q).trans hQS)
    (Sec3.isElemTwo_omegaG Q) hB
  have h2 : (centralizer ((Sec3.omegaG Q : Subgroup X) : Set X)).relIndex B ≤ Q.relIndex B :=
    Subgroup.relIndex_le_of_le_left hQV (Sec3.relIndex_ne_zero_of_finite _ _)
  have h3 : (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q) ≤
      (centralizer (B : Set X)).relIndex (Sec3.omegaG Q) :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htB))
      (Sec3.relIndex_ne_zero_of_finite _ _)
  calc (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q)
      ≤ (centralizer (B : Set X)).relIndex (Sec3.omegaG Q) := h3
    _ ≤ 2 ^ i * (centralizer ((Sec3.omegaG Q : Subgroup X) : Set X)).relIndex B := h1
    _ ≤ 2 ^ i * Q.relIndex B := Nat.mul_le_mul_left _ h2

theorem relIndex_le_two_or_eq_four {Q B : Subgroup X} (hB : IsPGroup 2 B)
    (h4 : Q.relIndex B ≤ 4) : Q.relIndex B ≤ 2 ∨ Q.relIndex B = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hB
  have hdvd : Q.relIndex B ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card Q B
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hj] at h4 ⊢
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j <;> simp

theorem inf_mem_famG_two {Q A : Subgroup X} (hA : A ∈ Sec3.famG S 0) (h4 : Q.relIndex A = 4) :
    A ⊓ Q ∈ Sec3.famG S 2 := by
  refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
    fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := Q) (K := A)
  rw [h4, hA.2.2, inf_comm] at h
  have hr : 2 ≤ CFSG.pRank 2 S := by
    by_contra hr
    push Not at hr
    have hle : 2 ^ (CFSG.pRank 2 S - 0) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < Nat.card ↥(A ⊓ Q) := Nat.card_pos
    omega
  have h' : 2 ^ (CFSG.pRank 2 S - 0) = 4 * 2 ^ (CFSG.pRank 2 S - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h'] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem normal_omegaG_jG_one_of_relIndex_le_two (hS2 : IsPGroup 2 S)
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) (hQS : CFSG.pCore 2 X ≤ S)
    (hL : L.Normal) (hSL : S ⊔ L = ⊤) (hNS : NoSmall1411 X L S) {A : Subgroup X}
    (hA : A ∈ Sec3.famG S 0) (hAidx : (CFSG.pCore 2 X).relIndex A ≤ 2)
    (hAQ : ¬ A ≤ CFSG.pCore 2 X) : (Sec3.omegaG (Sec3.jG S 1)).Normal := by
  set Q := CFSG.pCore 2 X
  have hQ2 : IsPGroup 2 Q := hS2.to_le hQS
  by_contra hEnn
  have hr : 2 ≤ CFSG.pRank 2 S := by
    by_contra h
    push Not at h
    apply hEnn
    rw [Sec3.omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨t, htA, htQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have h2 : Q.relIndex A = 2 := by
    have h1 : Q.relIndex A ≠ 1 := fun h => hAQ (Subgroup.relIndex_eq_one.mp h)
    have h0 := Sec3.relIndex_ne_zero_of_finite Q A
    omega
  have hAQ' : A ⊓ Q ∈ Sec3.famG S 1 := inf_mem_famG_one (by omega) hA h2
  have hO2 : ∀ K : Subgroup X, K ≤ ⊤ → (∀ h ∈ (⊤ : Subgroup X), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ Q := fun K _ hK hK2 =>
    le_sSup ⟨⟨fun k hk g => hK g trivial k hk⟩, hK2⟩
  have hQn : ∀ h ∈ (⊤ : Subgroup X), ∀ p ∈ Q, h * p * h⁻¹ ∈ Q := fun h _ p hp =>
    CFSG.pCore_normal.conj_mem p hp h
  have hXnc := Sec3.not_centralizes_omegaG_pOne (X := L) le_rfl hQS hQ2 hQ2 hCQ hQn hO2 le_top
    (fun t ht e he => Sec3.conj_mem_omegaG_jG ht he) hr hAQ' inf_le_right
    (fun N hNS' hNL => normal_of_normalized_by_sup_eq_top hL hSL hNS' hNL) hEnn
  push Not at hXnc
  have hWn : (Sec3.omegaG (Sec3.pOne S Q)).Normal :=
    ⟨fun w hw g => Sec3.conj_mem_omegaG_pOne hQS
      (fun p hp => CFSG.pCore_normal.conj_mem p hp g)
      (fun p hp => by
        have := CFSG.pCore_normal.conj_mem p hp g⁻¹
        rwa [inv_inv] at this) hw⟩
  have h4 := hNS _ hWn (Sec3.isElemTwo_omegaG _) hXnc t (hA.1 htA) htQ (hA.2.1.2 t htA)
  have h5 := Sec3.relIndex_centralizer_le_two hQS hA hAQ' htA
  omega

theorem omegaG_pTwo_normal (hQS : CFSG.pCore 2 X ≤ S) :
    (Sec3.omegaG (pTwo S (CFSG.pCore 2 X))).Normal :=
  ⟨fun w hw g => Sec3.conj_mem_omegaG
    (fun x hx => conj_mem_pTwo hQS (fun p hp => CFSG.pCore_normal.conj_mem p hp g) hx)
    (fun x hx => by
      have := conj_mem_pTwo hQS (g := g⁻¹) (fun p hp => CFSG.pCore_normal.conj_mem p hp g⁻¹) hx
      rwa [inv_inv] at this) hw⟩

theorem relIndex_centralizer_omegaG_pTwo_le_four {Q A : Subgroup X} (hQS : Q ≤ S)
    (hA : A ∈ Sec3.famG S 0) (hAQ : A ⊓ Q ∈ Sec3.famG S 2) {t : X} (htA : t ∈ A) :
    (centralizer ({t} : Set X)).relIndex (Sec3.omegaG (pTwo S Q)) ≤ 4 := by
  set W := Sec3.omegaG (pTwo S Q) with hWdef
  have hAPle : A ⊓ Q ≤ pTwo S Q := le_pTwo hAQ inf_le_right
  have hcomm : ∀ a ∈ A ⊓ Q, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (hw.2.1 a (hAPle ha)).symm
  have hD := Sec3.card_sup_mul_card_inf_of_commute hcomm
  have hDel : Sec3.IsElemTwo ((A ⊓ Q) ⊔ W) :=
    Sec3.isElemTwo_sup hAQ.2.1 (Sec3.isElemTwo_omegaG _) hcomm
  have hDT : (A ⊓ Q) ⊔ W ≤ S :=
    sup_le (inf_le_left.trans hA.1) ((Sec3.omegaG_le _).trans ((pTwo_le S Q).trans hQS))
  have hle := Sec3.card_le_two_pow_pRank hDT hDel
  rw [hAQ.2.2] at hD
  have h2 : 2 ^ CFSG.pRank 2 S ≤ 4 * 2 ^ (CFSG.pRank 2 S - 2) := by
    rcases Nat.lt_or_ge (CFSG.pRank 2 S) 2 with h | h
    · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, mul_one]
      calc 2 ^ CFSG.pRank 2 S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h.le
        _ = 4 := by norm_num
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : Nat.card W ≤ 4 * Nat.card ↥((A ⊓ Q) ⊓ W) := by
    have hpos : 0 < 2 ^ (CFSG.pRank 2 S - 2) := by positivity
    have : 2 ^ (CFSG.pRank 2 S - 2) * Nat.card W ≤
        2 ^ (CFSG.pRank 2 S - 2) * (4 * Nat.card ↥((A ⊓ Q) ⊓ W)) := by
      rw [← hD]
      calc Nat.card ↥((A ⊓ Q) ⊔ W) * Nat.card ↥((A ⊓ Q) ⊓ W)
          ≤ 4 * 2 ^ (CFSG.pRank 2 S - 2) * Nat.card ↥((A ⊓ Q) ⊓ W) :=
            Nat.mul_le_mul_right _ (hle.trans h2)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  have hrel : (A ⊓ Q).relIndex W ≤ 4 := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ Q) (K := W)
    have hpos : 0 < Nat.card ↥((A ⊓ Q) ⊓ W) := Nat.card_pos
    have : (A ⊓ Q).relIndex W * Nat.card ↥((A ⊓ Q) ⊓ W) ≤ 4 * Nat.card ↥((A ⊓ Q) ⊓ W) := by
      rw [inf_comm (A ⊓ Q) W] at hW
      rw [h]
      calc Nat.card W ≤ 4 * Nat.card ↥(W ⊓ (A ⊓ Q)) := hW
        _ = 4 * Nat.card ↥((A ⊓ Q) ⊓ W) := by rw [inf_comm]
    exact Nat.le_of_mul_le_mul_right this hpos
  have hcent : A ⊓ Q ≤ centralizer ({t} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA.2.1.1 a ha.1 t htA
  exact (Subgroup.relIndex_le_of_le_left hcent (Sec3.relIndex_ne_zero_of_finite _ _)).trans hrel

theorem mem_omegaG_pTwo {Q A₂ : Subgroup X} (hr : 3 ≤ CFSG.pRank 2 S)
    (hA₂ : A₂ ∈ Sec3.famG S 2) (hA₂Q : A₂ ≤ Q) (hQS : Q ≤ S) {e : X}
    (he : e ∈ Sec3.omegaG (Sec3.jG S 2)) (heQ : e ∈ Q) : e ∈ Sec3.omegaG (pTwo S Q) := by
  obtain ⟨heJ, hec, he2⟩ := he
  refine ⟨?_, fun x hx => hec x (pTwo_le_jG S Q hx), he2⟩
  by_cases heA : e ∈ A₂
  · exact le_pTwo hA₂ hA₂Q heA
  obtain ⟨hA₂S, hA₂2, hA₂card⟩ := hA₂
  have hpow : 2 ^ (CFSG.pRank 2 S - 3) ∣ Nat.card A₂ := by
    rw [hA₂card]
    exact Nat.pow_dvd_pow 2 (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hpow
  set K := K'.map A₂.subtype with hKdef
  have hKA : K ≤ A₂ := Subgroup.map_subtype_le K'
  have hKcard : Nat.card K = 2 ^ (CFSG.pRank 2 S - 3) := by
    rw [hKdef, Subgroup.card_map_of_injective A₂.subtype_injective, hK']
  have he1 : e ≠ 1 := fun h => heA (h ▸ A₂.one_mem)
  have hzp : Nat.card (Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact he2) he1
  have hcomm : ∀ k ∈ K, ∀ l ∈ Subgroup.zpowers e, k * l = l * k := by
    intro k hk l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact ((Commute.zpow_left (hec k (Sec3.le_jG ⟨hA₂S, hA₂2, hA₂card⟩ (hKA hk))) n).symm).eq
  have hinf : K ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxe⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [Subgroup.mem_bot]
    have he2' : e ^ 2 = 1 := by rw [pow_two]; exact he2
    have hmod : e ^ n = e ^ (n % (2 : ℕ)) := zpow_eq_zpow_emod' n he2'
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · exfalso
      apply heA
      have : e ^ n = e := by
        rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rw [← this]
      exact hKA hxK
  have hDcard : Nat.card ↥(K ⊔ Subgroup.zpowers e) = 2 ^ (CFSG.pRank 2 S - 2) := by
    have h := Sec3.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hKcard, hzp] at h
    rw [h, ← pow_succ]
    congr 1
    omega
  have hD : K ⊔ Subgroup.zpowers e ∈ Sec3.famG S 2 := by
    refine ⟨sup_le (hKA.trans hA₂S) ((Subgroup.zpowers_le).mpr (hQS heQ)), ?_, hDcard⟩
    refine Sec3.isElemTwo_sup ⟨fun a ha b hb => hA₂2.1 a (hKA ha) b (hKA hb),
      fun a ha => hA₂2.2 a (hKA ha)⟩ ⟨fun a ha b hb => ?_, fun a ha => ?_⟩ hcomm
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_add, ← two_mul, zpow_mul, show e ^ (2 : ℤ) = 1 by
        rw [zpow_two]; exact he2, one_zpow]
  have hDQ : K ⊔ Subgroup.zpowers e ≤ Q :=
    sup_le (hKA.trans hA₂Q) ((Subgroup.zpowers_le).mpr heQ)
  exact le_pTwo hD hDQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))

theorem normal_omegaG_jG_two_of_centralizes (hS2 : IsPGroup 2 S)
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) (hQS : CFSG.pCore 2 X ≤ S)
    (hL : L.Normal) (hSL : S ⊔ L = ⊤) {A₂ : Subgroup X} (hA₂ : A₂ ∈ Sec3.famG S 2)
    (hA₂Q : A₂ ≤ CFSG.pCore 2 X)
    (hLD : ∀ l ∈ L, ∀ d ∈ Sec3.omegaG (pTwo S (CFSG.pCore 2 X)), l * d * l⁻¹ = d) :
    (Sec3.omegaG (Sec3.jG S 2)).Normal := by
  set Q := CFSG.pCore 2 X with hQdef
  have hQ2 : IsPGroup 2 Q := hS2.to_le hQS
  by_cases hr : CFSG.pRank 2 S ≤ 2
  ·
    have hJ : Sec3.jG S 2 = ⊥ := by
      rw [eq_bot_iff, Sec3.jG]
      refine sSup_le fun A hA => ?_
      have hA1 : Nat.card A = 1 := by
        rw [hA.2.2, Nat.sub_eq_zero_of_le hr, pow_zero]
      rw [Subgroup.card_eq_one] at hA1
      rw [hA1]
    have hE : Sec3.omegaG (Sec3.jG S 2) = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      have := Sec3.omegaG_le _ he
      rwa [hJ] at this
    rw [hE]
    exact Subgroup.normal_bot
  push Not at hr
  set D := Sec3.omegaG (pTwo S Q) with hDdef
  have hDQ : D ≤ Q := (Sec3.omegaG_le _).trans (pTwo_le S Q)
  have hDJ : D ≤ Sec3.jG S 2 := (Sec3.omegaG_le _).trans (pTwo_le_jG S Q)
  have hDn : D.Normal := omegaG_pTwo_normal hQS
  have hO2 : ∀ K : Subgroup X, K ≤ ⊤ → (∀ h ∈ (⊤ : Subgroup X), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ Q := fun K _ hK hK2 =>
    le_sSup ⟨⟨fun k hk g => hK g trivial k hk⟩, hK2⟩
  have hEQ : Sec3.omegaG (Sec3.jG S 2) ≤ Q := by
    intro e he
    refine Sec3.mem_of_stabilizes (H := ⊤) (W := D) hQ2 hDQ le_rfl hCQ hQ2
      (fun h _ p hp => CFSG.pCore_normal.conj_mem p hp h) (fun h _ w hw => hDn.conj_mem w hw h)
      hO2 (Subgroup.mem_top e) (fun w hw => ?_) (fun p hp => ?_)
    · rw [he.2.1 w (hDJ hw), mul_inv_cancel_right]
    · have hcE : e * p * e⁻¹ * p⁻¹ ∈ Sec3.omegaG (Sec3.jG S 2) := by
        have h1 : p * e⁻¹ * p⁻¹ ∈ Sec3.omegaG (Sec3.jG S 2) :=
          Sec3.conj_mem_omegaG_jG (hQS hp) ((Sec3.omegaG (Sec3.jG S 2)).inv_mem he)
        have : e * p * e⁻¹ * p⁻¹ = e * (p * e⁻¹ * p⁻¹) := by group
        rw [this]
        exact (Sec3.omegaG (Sec3.jG S 2)).mul_mem he h1
      have hcQ : e * p * e⁻¹ * p⁻¹ ∈ Q :=
        Q.mul_mem (CFSG.pCore_normal.conj_mem p hp e) (Q.inv_mem hp)
      exact mem_omegaG_pTwo hr hA₂ hA₂Q hQS hcE hcQ
  refine normal_of_normalized_by_sup_eq_top hL hSL
    (fun s hs n hn => Sec3.conj_mem_omegaG_jG hs hn) (fun l hl n hn => ?_)
  rw [hLD l hl n (mem_omegaG_pTwo hr hA₂ hA₂Q hQS hn (hEQ hn))]
  exact hn

theorem two_fourChar_normal_of_relIndex_le_four
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (hS2 : IsPGroup 2 S) (hQS : CFSG.pCore 2 X ≤ S) (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 4)
    (hfour : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A = 4 →
      ∃ t ∈ A, t ∉ CFSG.pCore 2 X ∧ NoSmallEight1412 X L t)
    (hNS : NoSmall1411 X L S) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ (Sec18.fourChar S i₁).Normal ∧ (Sec18.fourChar S i₂).Normal := by
  set Q := CFSG.pCore 2 X with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal
  have hp2 : ∀ B : Subgroup X, B ≤ S → IsPGroup 2 B := fun B hB => hS2.to_le hB
  have hV : ∀ (i : ℕ) (B : Subgroup X), i ≤ 1 → B ∈ Sec3.famG S i → ¬ B ≤ Q →
      ∀ l ∈ L, ∀ v ∈ Sec3.omegaG Q, l * v * l⁻¹ = v := by
    intro i B hi hB hBQ
    by_contra hnc
    push Not at hnc
    have hVn := Sec3.omegaG_normal hQn
    have h2i : 2 ^ i ≤ 2 := (Nat.pow_le_pow_right (by norm_num) hi).trans (by norm_num)
    rcases relIndex_le_two_or_eq_four (hp2 B hB.1) (hidx B hB.1 hB.2.1) with h2 | h4
    · obtain ⟨t, htB, htQ⟩ := SetLike.not_le_iff_exists.mp hBQ
      have h5 := hNS _ hVn (Sec3.isElemTwo_omegaG _) hnc t (hB.1 htB) htQ (hB.2.1.2 t htB)
      have h6 := relIndex_centralizer_omegaG_le_of_famG hQS hB htB
      have h7 : 2 ^ i * Q.relIndex B ≤ 2 * 2 := Nat.mul_le_mul h2i h2
      omega
    · obtain ⟨t, htB, -, h8⟩ := hfour B hB.1 hB.2.1 h4
      have h5 := h8 _ hVn (Sec3.isElemTwo_omegaG _) hnc
      have h6 := relIndex_centralizer_omegaG_le_of_famG hQS hB htB
      rw [h4] at h6
      have h7 : 2 ^ i * 4 ≤ 2 * 4 := Nat.mul_le_mul_right 4 h2i
      omega
  by_cases hP : (∀ B ∈ Sec3.famG S 0, B ≤ Q) ∧ ∀ B ∈ Sec3.famG S 1, B ≤ Q
  · obtain ⟨hP0, hP1⟩ := hP
    refine ⟨1, 2, by decide, ?_, ?_⟩
    · rw [Sec18.Item181ThreeProof.fourChar_one]
      exact jG_normal_of_forall_le hQn hQS hP0
    · rw [Sec18.Item181ThreeProof.fourChar_two]
      exact Sec3.omegaG_normal (jG_normal_of_forall_le hQn hQS hP1)
  · have hex : ∃ i, i ≤ 1 ∧ ∃ B ∈ Sec3.famG S i, ¬ B ≤ Q := by
      by_contra hno
      push Not at hno
      exact hP ⟨hno 0 (by norm_num), hno 1 le_rfl⟩
    obtain ⟨i, hi, B, hB, hBQ⟩ := hex
    have hS1 : (Sec3.omegaG S).Normal :=
      normal_omegaG_of_centralizes_omegaG_pCore hCQ hQS hL hSL (hV i B hi hB hBQ)
    by_cases hP0 : ∀ B ∈ Sec3.famG S 0, B ≤ Q
    · refine ⟨0, 1, by decide, ?_, ?_⟩
      · rw [Sec18.Item181ThreeProof.fourChar_zero]
        exact hS1
      · rw [Sec18.Item181ThreeProof.fourChar_one]
        exact jG_normal_of_forall_le hQn hQS hP0
    · push Not at hP0
      obtain ⟨A, hA, hAQ⟩ := hP0
      rcases relIndex_le_two_or_eq_four (hp2 A hA.1) (hidx A hA.1 hA.2.1) with h2 | h4
      · refine ⟨0, 2, by decide, ?_, ?_⟩
        · rw [Sec18.Item181ThreeProof.fourChar_zero]
          exact hS1
        · rw [Sec18.Item181ThreeProof.fourChar_two]
          exact normal_omegaG_jG_one_of_relIndex_le_two hS2 hCQ hQS hL hSL hNS hA h2 hAQ
      · refine ⟨0, 3, by decide, ?_, ?_⟩
        · rw [Sec18.Item181ThreeProof.fourChar_zero]
          exact hS1
        · rw [Sec18.Item181ThreeProof.fourChar_three]
          have hA₂ : A ⊓ Q ∈ Sec3.famG S 2 := inf_mem_famG_two hA h4
          refine normal_omegaG_jG_two_of_centralizes hS2 hCQ hQS hL hSL hA₂ inf_le_right ?_
          by_contra hnc
          push Not at hnc
          obtain ⟨t, htA, htQ⟩ := SetLike.not_le_iff_exists.mp hAQ
          have h5 := hNS _ (omegaG_pTwo_normal hQS) (Sec3.isElemTwo_omegaG _) hnc t (hA.1 htA)
            htQ (hA.2.1.2 t htA)
          have h6 := relIndex_centralizer_omegaG_pTwo_le_four (Q := CFSG.pCore 2 X) hQS hA hA₂
            htA
          omega

end CFSG.RankThree.PartTwo.Sec20
