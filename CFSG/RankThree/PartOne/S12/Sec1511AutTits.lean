module

public import CFSG.RankThree.PartOne.S12.Sec1511AutCore
public import CFSG.RankThree.PartOne.K159.AutTits
public import CFSG.RankThree.PartOne.KE.TitsPlaneLocalCores
public import Certificates.Certificate14978
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne.K159
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits

namespace Sec1511

section Generic

variable {G : Type*} [Group G]

theorem conj_eq_of_comm {x y u : G} (h : (x⁻¹ * y) * u * (x⁻¹ * y)⁻¹ = u) :
    y * u * y⁻¹ = x * u * x⁻¹ := by
  have : y * u * y⁻¹ = x * ((x⁻¹ * y) * u * (x⁻¹ * y)⁻¹) * x⁻¹ := by group
  rw [this, h]

theorem bigAutWit_of_family [Finite G] {p : ℕ} (hp : p.Prime) (K : Subgroup G) {a b : G} (haK : a ∈ K)
    (hbK : b ∈ K) (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < p → j < p → i' < p → j' < p →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    {m : ℕ} (x : ℕ → G) (d : ℕ → ℕ × ℕ × ℕ × ℕ) (hxK : ∀ n < m, x n ∈ K)
    (hlt : ∀ n < m, (d n).1 < p ∧ (d n).2.1 < p ∧ (d n).2.2.1 < p ∧ (d n).2.2.2 < p)
    (hxa : ∀ n < m, x n * a * (x n)⁻¹ = a ^ (d n).1 * b ^ (d n).2.1)
    (hxb : ∀ n < m, x n * b * (x n)⁻¹ = a ^ (d n).2.2.1 * b ^ (d n).2.2.2)
    (hd : ∀ n < m, ∀ n' < m, d n = d n' → n = n') :
    BigAutWit p (p ^ 2) m ↥K := by
  classical
  have hp0 : 0 < p := hp.pos
  set U : Subgroup G := pairSub p hp0 a b ha hb hab with hU
  have hUK : U ≤ K := by
    rintro _ ⟨i, j, rfl⟩
    exact mul_mem (pow_mem haK i) (pow_mem hbK j)
  have haU : a ∈ U := ⟨1, 0, by simp⟩
  have hbU : b ∈ U := ⟨0, 1, by simp⟩
  have hdat : ∀ n < m, ∀ n' < m, x n * a * (x n)⁻¹ = x n' * a * (x n')⁻¹ →
      x n * b * (x n)⁻¹ = x n' * b * (x n')⁻¹ → n = n' := by
    intro n hn n' hn' h1 h2
    apply hd n hn n' hn'
    obtain ⟨h3, h4, h5, h6⟩ := hlt n hn
    obtain ⟨h3', h4', h5', h6'⟩ := hlt n' hn'
    rw [hxa n hn, hxa n' hn'] at h1
    rw [hxb n hn, hxb n' hn'] at h2
    obtain ⟨e1, e2⟩ := hinj _ _ _ _ h3 h4 h3' h4' h1
    obtain ⟨e3, e4⟩ := hinj _ _ _ _ h5 h6 h5' h6' h2
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
  let xK : ℕ → ↥K := fun n => if h : n < m then ⟨x n, hxK n h⟩ else 1
  have hxK_eq : ∀ n < m, ((xK n : ↥K) : G) = x n := by
    intro n hn
    simp [xK, hn]
  refine ⟨U.subgroupOf K, (Finset.range m).image xK, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩ hu'
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_subgroupOf.1 hu'
    apply Subtype.ext
    have hc : Commute (a ^ i) (b ^ j) := Commute.pow_pow hab i j
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i p, mul_comm j p, pow_mul, pow_mul, ha, hb]
    simp
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
    apply le_antisymm
    · have hsurj : Function.Surjective
          (fun y : Fin p × Fin p => (⟨a ^ (y.1 : ℕ) * b ^ (y.2 : ℕ), y.1, y.2, rfl⟩ : U)) := by
        rintro ⟨_, i, j, rfl⟩
        refine ⟨(⟨i % p, Nat.mod_lt _ hp0⟩, ⟨j % p, Nat.mod_lt _ hp0⟩), ?_⟩
        apply Subtype.ext
        show a ^ (i % p) * b ^ (j % p) = a ^ i * b ^ j
        rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
      have := Nat.card_le_card_of_surjective _ hsurj
      simpa [Nat.card_eq_fintype_card, sq] using this
    · have hinj' : Function.Injective
          (fun y : Fin p × Fin p => (⟨a ^ (y.1 : ℕ) * b ^ (y.2 : ℕ), y.1, y.2, rfl⟩ : U)) := by
        rintro ⟨i, j⟩ ⟨i', j'⟩ h
        have h' := congrArg Subtype.val h
        obtain ⟨e1, e2⟩ := hinj i j i' j' i.2 j.2 i'.2 j'.2 h'
        simp [Fin.ext e1, Fin.ext e2]
      have := Nat.card_le_card_of_injective _ hinj'
      simpa [Nat.card_eq_fintype_card, sq] using this
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro n hn n' hn' h
    have hn1 : n < m := Finset.mem_range.1 hn
    have hn1' : n' < m := Finset.mem_range.1 hn'
    have h1 : x n = x n' := by
      rw [← hxK_eq n hn1, ← hxK_eq n' hn1']
      exact congrArg Subtype.val h
    exact hdat n hn1 n' hn1' (by rw [h1]) (by rw [h1])
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hy
    have hn1 : n < m := Finset.mem_range.1 hn
    rintro ⟨u, hu⟩ hu'
    refine Subgroup.mem_subgroupOf.2 ?_
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_subgroupOf.1 hu'
    have hga' : x n * a * (x n)⁻¹ ∈ U := by
      rw [hxa n hn1]
      exact ⟨_, _, rfl⟩
    have hgb' : x n * b * (x n)⁻¹ ∈ U := by
      rw [hxb n hn1]
      exact ⟨_, _, rfl⟩
    have : x n * (a ^ i * b ^ j) * (x n)⁻¹ = (x n * a * (x n)⁻¹) ^ i * (x n * b * (x n)⁻¹) ^ j := by
      rw [conj_pow, conj_pow]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxK_eq n hn1]
    rw [this]
    exact mul_mem (pow_mem hga' i) (pow_mem hgb' j)
  · intro y hy z hz hyz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨n', hn', rfl⟩ := Finset.mem_image.1 hz
    have hn1 : n < m := Finset.mem_range.1 hn
    have hn1' : n' < m := Finset.mem_range.1 hn'
    have hne : n ≠ n' := fun h => hyz (by rw [h])
    by_contra hcon
    push Not at hcon
    have hxa' := hcon ⟨a, haK⟩ (Subgroup.mem_subgroupOf.2 haU)
    have hxb' := hcon ⟨b, hbK⟩ (Subgroup.mem_subgroupOf.2 hbU)
    have e1 : ((xK n)⁻¹ * xK n' : ↥K) * ⟨a, haK⟩ * ((xK n)⁻¹ * xK n')⁻¹ = ⟨a, haK⟩ := hxa'
    have e2 : ((xK n)⁻¹ * xK n' : ↥K) * ⟨b, hbK⟩ * ((xK n)⁻¹ * xK n')⁻¹ = ⟨b, hbK⟩ := hxb'
    have f1 := congrArg Subtype.val e1
    have f2 := congrArg Subtype.val e2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxK_eq n hn1, hxK_eq n' hn1'] at f1 f2
    exact hne (hdat n hn1 n' hn1' (conj_eq_of_comm f1).symm (conj_eq_of_comm f2).symm)

end Generic

section Tits

theorem bigAutWit_titsD :
    BigAutWit 5 25 48 ↥titsD := by
  obtain ⟨hlA, hlB, -, hA5, hB5, hAB, hdist, -, -, -⟩ := Certificates.certificate14973
  obtain ⟨hlen, hnodup, hall⟩ := Certificates.certificate14978
  have rA := rep_wordArr_titsT hlA
  have rB := rep_wordArr_titsT hlB
  set a := wordIn 13 titsT titsAWord with ha_def
  set b := wordIn 13 titsT titsBWord with hb_def
  have hpa : ∀ k, Rep 1755 (powArr titsAArr k) (a ^ k) := rep_powArr rA
  have hpb : ∀ k, Rep 1755 (powArr titsBArr k) (b ^ k) := rep_powArr rB
  have ha5 : a ^ 5 = 1 := eq_of_eqA (hpa 5) rep_idA hA5
  have hb5 : b ^ 5 = 1 := eq_of_eqA (hpb 5) rep_idA hB5
  have hab : a * b = b * a := eq_of_eqA (rep_compA rA rB) (rep_compA rB rA) hAB
  have hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have h1 := allLt_spec (allLt_spec (allLt_spec (allLt_spec hdist hi) hj) hi') hj'
    have heq : eqA 1755 (pairArr i j) (pairArr i' j') = true :=
      (eqA_iff (rep_compA (hpa i) (hpb j)) (rep_compA (hpa i') (hpb j'))).2 h
    simp only [heq, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1
  have hfam : ∀ n < 48, (titsBigDat n).1 < 5 ∧ (titsBigDat n).2.1 < 5 ∧ (titsBigDat n).2.2.1 < 5 ∧
      (titsBigDat n).2.2.2 < 5 ∧
      wordIn 13 titsT (titsBigWord n) * a * (wordIn 13 titsT (titsBigWord n))⁻¹ =
        a ^ (titsBigDat n).1 * b ^ (titsBigDat n).2.1 ∧
      wordIn 13 titsT (titsBigWord n) * b * (wordIn 13 titsT (titsBigWord n))⁻¹ =
        a ^ (titsBigDat n).2.2.1 * b ^ (titsBigDat n).2.2.2 := by
    intro n hn
    have h := allLt_spec hall hn
    simp only [titsBigOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hl, h1⟩, h2⟩, h3⟩, h4⟩, hea⟩, heb⟩ := h
    have rx : Rep 1755 (titsBigArr n) (wordIn 13 titsT (titsBigWord n)) := rep_wordArr_titsT hl
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩
    · exact mul_inv_eq_iff_eq_mul.2
        (eq_of_eqA (rep_compA rx rA) (rep_compA (rep_compA (hpa _) (hpb _)) rx) hea)
    · exact mul_inv_eq_iff_eq_mul.2
        (eq_of_eqA (rep_compA rx rB) (rep_compA (rep_compA (hpa _) (hpb _)) rx) heb)
  have hdd : ∀ n < 48, ∀ n' < 48, titsBigDat n = titsBigDat n' → n = n' := by
    intro n hn n' hn' h
    have hn1 : n < titsBigData.length := by omega
    have hn1' : n' < titsBigData.length := by omega
    simp only [titsBigDat, List.getD_eq_getElem _ _ hn1, List.getD_eq_getElem _ _ hn1'] at h
    exact (hnodup.getElem_inj_iff).1 h
  have := bigAutWit_of_family Nat.prime_five titsD (wordIn_titsT_mem_titsD titsAWord)
    (wordIn_titsT_mem_titsD titsBWord) ha5 hb5 hab hinj (m := 48)
    (fun n => wordIn 13 titsT (titsBigWord n)) titsBigDat (fun n _ => wordIn_titsT_mem_titsD _)
    (fun n hn => ⟨(hfam n hn).1, (hfam n hn).2.1, (hfam n hn).2.2.1, (hfam n hn).2.2.2.1⟩)
    (fun n hn => (hfam n hn).2.2.2.2.1) (fun n hn => (hfam n hn).2.2.2.2.2) hdd
  simpa using this

theorem tits_row
    {H : Type} [Group H] [Finite H] {S : Subgroup H} [S.Normal]
    (hiso : Census3.IsoLie ↥S .tits) (hC : Subgroup.centralizer (S : Set H) = ⊥)
    {P : Subgroup H} (hP : IsSylowOf 5 P ⊤) :
    Nat.card (omegaOne 5 P) = 25 ∧
      ∃ F : Finset H, F.card = 48 ∧
        (∀ x ∈ F, x ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H)) ∧
        ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
          x⁻¹ * y ∉ Subgroup.centralizer ((omegaOne 5 P : Subgroup H) : Set H) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨e⟩ := titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hiso)
  have hPS : P ≤ S := by
    intro x hx
    obtain ⟨k, hk⟩ := hP.2.1 ⟨x, hx⟩
    have hx' : x ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine KE.titsActor_mem_of_pow_eq_one S e hC (p := 5 ^ k) ?_ hx'
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow hd)
    omega
  have hPcard : Nat.card P ≤ 25 := by
    obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
    have h1 : Nat.card P ∣ Nat.card S := Subgroup.card_dvd_of_le hPS
    have h2 : Nat.card S = 17971200 := by
      rw [Nat.card_congr e.toEquiv, card_titsD]
    rw [ha, h2] at h1
    have ha2 : a ≤ 2 := by
      by_contra hcon
      have h125 : 5 ^ 3 ∣ 5 ^ a := pow_dvd_pow 5 (by omega)
      have := h125.trans h1
      norm_num at this
    rw [ha]
    calc 5 ^ a ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
      _ = 25 := by norm_num
  have hΩle : Nat.card (omegaOne 5 P) ≤ 25 := by
    refine le_trans ?_ hPcard
    exact Subgroup.card_le_of_le ((Subgroup.closure_le _).2 fun x hx => hx.1)
  exact (BigAutWit.of_mulEquiv e.symm bigAutWit_titsD).row hp hP hΩle

end Tits

end Sec1511

end CFSG.RankThree.PartOne
