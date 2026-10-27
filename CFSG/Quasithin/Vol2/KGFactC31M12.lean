module

public import CFSG.Quasithin.Vol2.KGFactC31Act
public import Certificates.Certificate7198
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu
  CFSG.Quasithin.KGC31.Native

theorem prime_dvd_m12 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 95040) : p = 5 ∨ p = 11 := by
  have h' : p ∣ 2 ^ 6 * 3 ^ 3 * 5 * 11 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)

theorem noOddAct_m12 :
    NoOddAct ↥NativeSporadic.M12 := by
  obtain ⟨h5, h11, hc5, hc11⟩ := Certificates.certificate7198
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hcard : Nat.card NativeSporadic.M12 = 95040 := m12_card
  have hgens : ∀ l, M12.gensG l ∈ NativeSporadic.M12 := fun l => by
    unfold M12.gensG
    split_ifs
    · exact m12a.2
    · exact m12b.2
  have hrep : ∀ l, Rep 12 (M12.gensT l) (M12.gensG l) := fun l => by
    unfold M12.gensT M12.gensG
    split_ifs
    · exact rep_toTable hn _
    · exact rep_toTable hn _
  have hinvs : ∀ t : NativeSporadic.M12, orderOf t = 2 →
      ∃ T ∈ orderTables m12Certificate 2, Rep 12 T (t : Equiv.Perm (Fin 12)) := fun t ht =>
    exists_orderTables hn _ hQ (by rw [m12Certificate_originalSubgroup]; exact t.2)
      (by rw [Subgroup.orderOf_coe]; exact ht)
  have key : ∀ (q : ℕ) [Fact q.Prime] (w : List ℤ), ordTest 12 q (wordT 12 M12.gensT w) = true →
      ¬ q ∣ 95040 / q →
      actCheck 12 q (orderTables m12Certificate 2) (powTabs 12 (wordT 12 M12.gensT w) q) = true →
      ∀ y : NativeSporadic.M12, (∃ k : ℕ, y ^ q ^ k = 1) → ∀ W : Subgroup NativeSporadic.M12,
        IsElemAbelian 2 W → y ∈ Subgroup.normalizer (W : Set NativeSporadic.M12) →
        ∀ t ∈ W, y * t * y⁻¹ = t := by
    intro q _ w hq hqi hc y hy W hW hyW t ht
    set x : NativeSporadic.M12 := ⟨wordG M12.gensG w, wordG_mem_of _ hgens w⟩
    have hx : Rep 12 (wordT 12 M12.gensT w) (x : Equiv.Perm (Fin 12)) :=
      Rep.wordT hn w fun l _ => hrep l
    have hox : orderOf x = q := by
      rw [← Subgroup.orderOf_coe]
      exact (ordTest_iff perm_faithful hx (Fact.out : q.Prime).pos).1 hq
    have hcardx : Nat.card (Subgroup.zpowers x) = q := by rw [Nat.card_zpowers, hox]
    have hP : IsPGroup q (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one])
    have hPi : ¬ q ∣ (Subgroup.zpowers x).index := by
      have h := (Subgroup.zpowers x).card_mul_index
      rw [hcardx, hcard] at h
      rw [← h, Nat.mul_div_cancel_left _ (Fact.out : q.Prime).pos] at hqi
      exact hqi
    refine forall_act_of_sylow hn hP hPi (fun z hz => ?_) hinvs hc hy hW hyW ht
    have := exists_powTabs hn hx hz
    rwa [hox] at this
  intro p hp hp5 y hy W hW hyW t ht
  by_cases hpd : p ∣ 95040
  · rcases prime_dvd_m12 hp hp5 hpd with rfl | rfl
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact key 5 M12.w5 h5 (by norm_num) hc5 y hy W hW hyW t ht
    · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      exact key 11 M12.w11 h11 (by norm_num) hc11 y hy W hW hyW t ht
  · rw [eq_one_of_pow_of_not_dvd hp (by rwa [hcard]) hy]
    group

theorem inspC31SporadicAt_m12 :
    CFSG.Quasithin.InspC31SporadicAt .M12 :=
  inspC31SporadicAt_of_noOddAct noOddAct_m12

end CFSG.Quasithin.KGC31

end
