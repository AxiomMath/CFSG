module

public import CFSG.Quasithin.H13.QTESylowHeRuStmt
public import CFSG.Quasithin.H13.QTESylowJ2
public import CFSG.Quasithin.H13.LocDblOddHe
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.H13.LocDblRuCheck

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.Blueprint
open scoped Pointwise

theorem overgroups_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {k : ℕ}
    {L : List ℕ}
    (h : ∃ R : Subgroup Y, Nat.card R = 2 ^ k ∧ ¬ 2 ∣ R.index ∧
      ∀ W : Subgroup Y, R ≤ W → W ≠ ⊤ → ∃ v ∈ L, Nat.card W ∣ v) :
    ∃ R : Subgroup X, Nat.card R = 2 ^ k ∧ ¬ 2 ∣ R.index ∧
      ∀ W : Subgroup X, R ≤ W → W ≠ ⊤ → ∃ v ∈ L, Nat.card W ∣ v := by
  obtain ⟨R, hR, hodd, hW⟩ := h
  refine ⟨R.comap φ.toMonoidHom, ?_, ?_, fun W hW0 hWtop => ?_⟩
  · rw [← hR]
    exact Nat.card_congr (φ.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  · rw [Subgroup.index_comap_of_surjective (H := R) φ.surjective]
    exact hodd
  · have hle : R ≤ W.map φ.toMonoidHom := by
      intro y hy
      refine ⟨φ.symm y, hW0 ?_, φ.apply_symm_apply y⟩
      show φ (φ.symm y) ∈ R
      rw [φ.apply_symm_apply]
      exact hy
    have hne : W.map φ.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hWtop
      rw [eq_top_iff]
      intro x _
      have hx : φ x ∈ W.map φ.toMonoidHom := htop ▸ Subgroup.mem_top (φ x)
      obtain ⟨w, hw, hwx⟩ := hx
      rw [← φ.injective hwx]
      exact hw
    obtain ⟨v, hv, hdvd⟩ := hW _ hle hne
    exact ⟨v, hv, by rwa [Subgroup.card_map_of_injective φ.injective] at hdvd⟩

theorem noncyclic_product_ne_of_overgroups {X : Type*} [Group X] [Finite X] {k : ℕ}
    {L : List ℕ}
    (h : ∃ R : Subgroup X, Nat.card R = 2 ^ k ∧ ¬ 2 ∣ R.index ∧
      ∀ W : Subgroup X, R ≤ W → W ≠ ⊤ → ∃ v ∈ L, Nat.card W ∣ v)
    (h3 : 3 ∣ Nat.card X) (hL : ∀ v ∈ L, ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ 2 ^ k * p ^ 2 ∣ v)
    (S : Sylow 2 X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (P : Subgroup X) (hP : IsPGroup p P)
    (hnc : ¬ IsCyclic P) : (P : Set X) * (S : Set X) ≠ (S : Set X) * (P : Set X) := by
  classical
  intro hPS
  obtain ⟨R, hR, hRodd, hW⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hQR : ((IsPGroup.of_card hR).toSylow hRodd : Subgroup X) = R := IsPGroup.toSylow_coe _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S ((IsPGroup.of_card hR).toSylow hRodd)
  set P' := P.map (MulAut.conj g).toMonoidHom with hP'
  have hP'card : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hSQ : (S : Subgroup X).map (MulAut.conj g).toMonoidHom = R := by
    rw [← hQR, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'R : (P' : Set X) * (R : Set X) = (R : Set X) * (P' : Set X) := by
    have hPS' : (P : Set X) * ((S : Subgroup X) : Set X) =
        ((S : Subgroup X) : Set X) * (P : Set X) := hPS
    rw [← hSQ, hP', Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hPS', Set.image_mul]
  set M := CFSG.Quasithin.H13.NQBlock.mulCommSubgroup P' R hP'R with hMdef
  have hPM : P' ≤ M := fun x hx => ⟨x, hx, 1, R.one_mem, mul_one x⟩
  have hRM : R ≤ M := fun x hx => ⟨1, P'.one_mem, x, hx, one_mul x⟩
  have hidx : (R.subgroupOf M).index ∣ Nat.card P' :=
    index_dvd_card_of_le_mul hPM hRM fun m hm => by
      obtain ⟨a, ha, r, hr, rfl⟩ := hm
      exact ⟨a, ha, r, hr, rfl⟩
  have hMcard : Nat.card M = 2 ^ k * (R.subgroupOf M).index := by
    have h1 := Subgroup.card_mul_index (R.subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hR] at h1
    exact h1.symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 0 ∨ n = 1 := by omega
    rcases hn1 with rfl | rfl
    · rw [pow_zero] at hn
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hn).1
      exact hnc isCyclic_of_subsingleton
    · rw [pow_one] at hn
      exact hnc (isCyclic_of_prime_card hn)
  have hM3 : ¬ 3 ∣ Nat.card M := by
    rw [hMcard]
    intro h3M
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3M with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
    · rw [hP'card, hn] at hidx
      have h3p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h.trans hidx)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
      omega
  have hMtop : M ≠ ⊤ := by
    intro hM
    apply hM3
    rw [hM, Subgroup.card_top]
    exact h3
  obtain ⟨v, hv, hdvd⟩ := hW M hRM hMtop
  have hPdvd : p ^ n ∣ Nat.card M := by
    rw [← hn, ← hP'card]
    exact Subgroup.card_dvd_of_le hPM
  have hRdvd : 2 ^ k ∣ Nat.card M := by
    rw [← hR]
    exact Subgroup.card_dvd_of_le hRM
  have hcop : Nat.Coprime (2 ^ k) (p ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have hboth : 2 ^ k * p ^ n ∣ Nat.card M := hcop.mul_dvd_of_dvd_of_dvd hRdvd hPdvd
  exact hL v hv p hp hp5
    ((Nat.mul_dvd_mul_left _ (pow_dvd_pow p hn2)).trans (hboth.trans hdvd))

theorem not_two_pow_mul_sq_dvd {k m q : ℕ} (B : ℕ) (hm : 0 < m) (hmB : m < (B + 1) ^ 2)
    (hB : ∀ r : ℕ, 5 ≤ r → r ≤ B → ¬ r ^ 2 ∣ m) (hq5 : 5 ≤ q) :
    ¬ 2 ^ k * q ^ 2 ∣ 2 ^ k * m := by
  intro h
  have hq2 : q ^ 2 ∣ m := (Nat.mul_dvd_mul_iff_left (by positivity)).1 h
  have hle : q ^ 2 ≤ m := Nat.le_of_dvd hm hq2
  have hqB : q ≤ B := by
    by_contra hlt
    have : (B + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  exact hB q hq5 hqB hq2

section He

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He CFSG.Quasithin.H13.LocDbl

theorem he_overgroups :
    ∃ R : Subgroup J, Nat.card R = 2 ^ 10 ∧ ¬ 2 ∣ R.index ∧
      ∀ Y : Subgroup J, R ≤ Y → Y ≠ ⊤ → ∃ v ∈ [138240, 138240, 21504], Nat.card Y ∣ v := by
  have hb : OddIndexBound ↥J [138240, 138240, 21504] := oddIndexBound_He_group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥J) 2 (n := 10)
    (by rw [card_J]; norm_num)
  have hidx : K.index = 3935925 := by
    have h := Subgroup.card_mul_index K
    rw [hK, card_J] at h
    omega
  refine ⟨K, hK, by rw [hidx]; norm_num, fun Y hKY hY => ?_⟩
  have hodd : ¬ 2 ∣ Y.index := fun h => by
    have h2 := h.trans (Subgroup.index_dvd_of_le hKY)
    rw [hidx] at h2
    norm_num at h2
  exact hb Y hodd hY

theorem he_orders_not_dvd : ∀ v ∈ [138240, 138240, 21504], ∀ q : ℕ, q.Prime → 5 ≤ q →
    ¬ 2 ^ 10 * q ^ 2 ∣ v := by
  intro v hv q _ hq5
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  have h135 : ¬ 2 ^ 10 * q ^ 2 ∣ 138240 := by
    rw [show (138240 : ℕ) = 2 ^ 10 * 135 by norm_num]
    exact not_two_pow_mul_sq_dvd 11 (by norm_num) (by norm_num)
      (fun r h1 h2 => by interval_cases r <;> norm_num) hq5
  rcases hv with rfl | rfl | rfl
  · exact h135
  · exact h135
  · rw [show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num]
    exact not_two_pow_mul_sq_dvd 4 (by norm_num) (by norm_num) (fun r h1 h2 => by omega) hq5

theorem he_noncyclic_prime_sylow_product
    {K : Type*} [Group K] [Finite K] (e : K ≃* NativeSporadic.He) (S : Sylow 2 K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (P : Subgroup K) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K) := by
  have φ : K ≃* J := e.trans heEquivJ
  have hcard : Nat.card K = 4030387200 := (Nat.card_congr φ.toEquiv).trans card_J
  exact noncyclic_product_ne_of_overgroups
    (@overgroups_of_mulEquiv K ↥J inferInstance inferInstance φ 10 _ he_overgroups)
    (by rw [hcard]; norm_num) he_orders_not_dvd S hp hp5 P hP hnc

end He

section Ru

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Quasithin.H13.LocDbl
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_overgroups :
    ∃ R : Subgroup (J ruData), Nat.card R = 2 ^ 14 ∧ ¬ 2 ∣ R.index ∧
      ∀ Y : Subgroup (J ruData), R ≤ Y → Y ≠ ⊤ → ∃ v ∈ [245760, 344064], Nat.card Y ∣ v :=
  ⟨RuCov.ruS, RuCert.ru_S_card, by rw [RuCert.ru_S_index]; decide, RuCert.ru_over_dvd⟩

theorem ru_orders_not_dvd : ∀ v ∈ [245760, 344064], ∀ q : ℕ, q.Prime → 5 ≤ q →
    ¬ 2 ^ 14 * q ^ 2 ∣ v := by
  intro v hv q _ hq5
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl
  · rw [show (245760 : ℕ) = 2 ^ 14 * 15 by norm_num]
    exact not_two_pow_mul_sq_dvd 3 (by norm_num) (by norm_num) (fun r h1 h2 => by omega) hq5
  · rw [show (344064 : ℕ) = 2 ^ 14 * 21 by norm_num]
    exact not_two_pow_mul_sq_dvd 4 (by norm_num) (by norm_num) (fun r h1 h2 => by omega) hq5

theorem ru_noncyclic_prime_sylow_product
    {K : Type*} [Group K] [Finite K] (e : K ≃* NativeSporadic.Ru) (S : Sylow 2 K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (P : Subgroup K) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ψ : NativeSporadic.Ru ≃* J ruData := seedEquiv hF.toBaseFacts
  have φ : K ≃* J ruData := e.trans ψ
  have hcard : Nat.card K = 145926144000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
  exact noncyclic_product_ne_of_overgroups
    (@overgroups_of_mulEquiv K ↥(J ruData) inferInstance inferInstance φ 14 _ ru_overgroups)
    (by rw [hcard]; norm_num) ru_orders_not_dvd S hp hp5 P hP hnc

end Ru

theorem he_ru_noncyclic_prime_sylow_product :
    StmtHeRuNoncyclicPrimeSylowProduct := by
  intro K _ _ hK S p hp hp5 P hP hnc
  rcases hK with h | h
  · obtain ⟨e⟩ := h
    exact he_noncyclic_prime_sylow_product e S hp hp5 P hP hnc
  · obtain ⟨e⟩ := h
    exact ru_noncyclic_prime_sylow_product e S hp hp5 P hP hnc

end CFSG.Quasithin.H13.QTESylow
