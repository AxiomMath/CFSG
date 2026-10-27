module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.Quasithin.A312J2

theorem isSolvable_of_card_pq {G : Type} [Group G] [Finite G] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  let _ : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem isSolvable_of_card_dvd_sixty {G : Type} [Group G] [Finite G] (hdvd : Nat.card G ∣ 60)
    (hlt : Nat.card G < 60) : Group.IsSolvable G := by
  have hmem : Nat.card G ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h2 : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
  rw [h2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 0) (b := 0)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 1) (b := 0)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 0) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 0)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_five (by norm_num) (a := 0) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 1) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_five (by norm_num) (a := 1) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_three Nat.prime_five (by norm_num) (a := 1) (b := 1)
      (by rw [h]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_five (by norm_num) (a := 2) (b := 1)
      (by rw [h]; norm_num)
  · have : IsZGroup G := IsZGroup.of_squarefree (by rw [h]; decide +kernel)
    infer_instance
  · omega

theorem isSimpleGroup_of_perfect_card_sixty {G : Type} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) (hG : Nat.card G = 60) : IsSimpleGroup G := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hG]; norm_num)
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbot, htop⟩ := hcon
  have hNpos : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hq1 : 1 < Nat.card (G ⧸ N) := by
    have h0 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have h1 : Nat.card (G ⧸ N) ≠ 1 := fun h => htop (Subgroup.index_eq_one.mp h)
    omega
  have hdvd : Nat.card (G ⧸ N) ∣ 60 := ⟨Nat.card N, by rw [← hG]; exact hprod⟩
  have hlt : Nat.card (G ⧸ N) < 60 := by
    rw [hG] at hprod
    nlinarith
  have hsolv := isSolvable_of_card_dvd_sixty hdvd hlt
  have : Nontrivial (G ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp hq1
  have : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem nonempty_mulEquiv_alt5_of_perfect {G : Type} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) (hG : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have := isSimpleGroup_of_perfect_card_sixty hperf hG
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hG

end CFSG.Quasithin.A312J2
