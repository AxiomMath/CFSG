module

public import CFSG.Quasithin.H13.LocDblCriterion
public import CFSG.LocalAnalysis.ComponentInitial.J4CommutingFactors

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem sq_primes_ncard_eq {n : ℕ} (hn : n ≠ 0) :
    {r : ℕ | r.Prime ∧ r ^ 2 ∣ n}.ncard = (n.primeFactors.filter (fun r => r ^ 2 ∣ n)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext r
  simp only [Finset.coe_filter, Nat.mem_primeFactors]
  exact ⟨fun ⟨hr, h⟩ => ⟨⟨hr, (dvd_pow_self r two_ne_zero).trans h, hn⟩, h⟩,
    fun ⟨⟨hr, _, _⟩, h⟩ => ⟨hr, h⟩⟩

variable {A : Type*} [Group A] [Finite A]

theorem sq_card_radQuot_dvd {Y U V : Subgroup A} (hU : U ∈ cComp Y) (hV : V ∈ cComp Y)
    (hUV : U ≠ V) (e : ↥U ≃* ↥V) :
    Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) ^ 2 ∣ Nat.card A := by
  have hdvd := card_dvd_of_mem_cComp hU hV hUV (le_top : U ⊔ V ≤ ⊤)
  rw [← card_radQuot_congr e, Subgroup.card_top] at hdvd
  exact (pow_two (Nat.card (↥U ⧸ CFSG.solvableRadical ↥U)) ▸
    mul_dvd_mul_right (card_radQuot_dvd U) _).trans hdvd

theorem noIsoDouble_of_sq_primes (h : {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card A}.ncard ≤ 2)
    (Y : Subgroup A) : NoIsoDouble Y := by
  intro U hU V hV ⟨e⟩
  by_contra hUV
  have hsq := sq_card_radQuot_dvd hU hV hUV e
  have h3 := three_le_card_primeFactors_radQuot hU
  have hsub : ((Nat.card (↥U ⧸ CFSG.solvableRadical ↥U)).primeFactors : Set ℕ) ⊆
      {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card A} := by
    intro r hr
    rw [Finset.mem_coe, Nat.mem_primeFactors] at hr
    exact ⟨hr.1, (pow_dvd_pow_of_dvd hr.2.1 2).trans hsq⟩
  have := Set.ncard_le_ncard hsub (finite_sq_primes Nat.card_pos.ne')
  rw [Set.ncard_coe_finset] at this
  omega

theorem sylowNoDouble_of_sq_primes (h : {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card A}.ncard ≤ 2) :
    SylowNoDouble A := fun _ _ Y _ _ => noIsoDouble_of_sq_primes h Y

theorem sylowNoDouble_of_card {n : ℕ} (hA : Nat.card A = n)
    (h : (n.primeFactors.filter (fun r => r ^ 2 ∣ n)).card ≤ 2) : SylowNoDouble A := by
  refine sylowNoDouble_of_sq_primes ?_
  rw [hA, sq_primes_ncard_eq (hA ▸ Nat.card_pos.ne')]
  exact h

theorem noIsoDouble_of_card_dvd_J4 (h : Nat.card A ∣ 86775571046077562880) (Y : Subgroup A) :
    NoIsoDouble Y := by
  intro U hU V hV ⟨e⟩
  by_contra hUV
  have hsq := (sq_card_radQuot_dvd hU hV hUV e).trans h
  have hm := CFSG.LocalAnalysis.ComponentInitial.dvd_33792_of_sq_dvd hsq
  obtain ⟨hsimple, hnonab⟩ := radQuot_simple hU
  exact CFSG.LocalAnalysis.ComponentInitial.no_nonabelian_simple_order_dividing_33792 hsimple
    hnonab hm

end CFSG.Quasithin.H13.LocDbl
