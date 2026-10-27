module

public import CFSG.Permutation.FiveTransitive.Degree36LargeSylowCentralizer
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree36LargeSylowNormalizer

open MulAction Subgroup FixedNormalizerAction

private theorem normalizer_factorial_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (S : Sylow p P) :
    (36 % p).factorial ∣ Nat.card (Subgroup.normalizer (S : Set P)) := by
  obtain ⟨hf,hi⟩ := Degree36LargeSylowEntrance.fixed_and_image P hcard h5 hnotAlt hp S
  have hF : Nat.card (Fixed (X := X) (S : Subgroup P)) = 36 % p := by
    rw [fixed_eq]; exact hf
  let rho := toPermHom (Normalizer (S : Subgroup P)) (Fixed (X := X) (S : Subgroup P))
  have hd := Subgroup.card_range_dvd rho
  change Nat.card (Image (X := X) (S : Subgroup P)) ∣ _ at hd
  rw [hi,Subgroup.card_top,Nat.card_perm,hF] at hd
  exact hd

private theorem three_dvd_centralizer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 11 P) : 3 ∣ Nat.card (Subgroup.centralizer (S : Set P)) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hS := Degree36LargeSylowEntrance.sylow_card P hcard h5 hnotAlt (Or.inr rfl) S
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨hf,hi⟩ := Degree36LargeSylowEntrance.fixed_and_image P hcard h5 hnotAlt (Or.inr rfl) S
  have hF : Nat.card (Fixed (X := X) (S : Subgroup P)) = 3 := by
    rw [fixed_eq]; exact hf
  exact TwoPrimeCycleCentralizer.three_dvd_centralizer_card (S : Subgroup P) 3 (Or.inl rfl) hF
    (toPermHom (Normalizer (S : Subgroup P)) (Fixed (X := X) (S : Subgroup P)))
    (MonoidHom.range_eq_top.mp hi)

private theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) :
    ∃ c r k : ℕ, c ∣ (36 / p).factorial ∧ r ∣ p - 1 ∧ 0 < c ∧ 0 < r ∧
      k % p = 1 ∧ c * r * k * p = Nat.card P ∧ 2 ∣ c * r ∧ (p = 11 → 3 ∣ c) := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  let S : Sylow p P := Sylow.nonempty.some
  have hS := Degree36LargeSylowEntrance.sylow_card P hcard h5 hnotAlt hp S
  have hC := Degree36LargeSylowCentralizer.centralizer_card_dvd P hcard h5 hnotAlt hp S
  obtain ⟨hc,hr,hcp,hrp,hmod,hprod⟩ :=
    Degree31FiveFixerNormalizer.normalizer_constraints P (36 / p).factorial S hS hC
  let C : Subgroup P := Subgroup.centralizer (S : Set P)
  let N : Subgroup P := Subgroup.normalizer (S : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change c * r * N.index * p = Nat.card P at hprod
  have hNcard : Nat.card N = c * r * p := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite)
    calc
      N.index * Nat.card N = Nat.card P := N.index_mul_card
      _ = N.index * (c * r * p) := by rw [← hprod]; ring
  have heven : 2 ∣ c * r := by
    have hd := normalizer_factorial_dvd P hcard h5 hnotAlt hp S
    have he : 2 ∣ Nat.card N := (show 2 ∣ (36 % p).factorial by
      rcases hp with rfl | rfl <;> norm_num).trans hd
    rw [hNcard] at he
    rcases Nat.prime_two.dvd_mul.mp he with he | he
    · exact he
    · rcases hp with rfl | rfl <;> norm_num at he
  refine ⟨c,r,N.index,hc,hr,hcp,hrp,hmod,hprod,heven,?_⟩
  intro hp11
  subst p
  have hthree := three_dvd_centralizer P hcard h5 hnotAlt S
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  let _ : IsMulCommutative S := IsCyclic.isMulCommutative
  have hSle : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨b,hb⟩ : S) (⟨a,ha⟩ : S))
  have hSC : Nat.card ((S : Subgroup P).subgroupOf C) = 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv]
    exact hS
  have hcCard : c * 11 = Nat.card C := by
    have h := ((S : Subgroup P).subgroupOf C).index_mul_card
    rw [hSC] at h
    exact h
  change 3 ∣ Nat.card C at hthree
  rw [← hcCard] at hthree
  rcases Nat.prime_three.dvd_mul.mp hthree with h | h
  · exact h
  · norm_num at h

theorem combined_constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) :
    ∃ d k : ℕ, d ∣ (36 / p).factorial * (p - 1) ∧ 2 ∣ d ∧ k % p = 1 ∧
      d * k * p = Nat.card P ∧ (p = 11 → 3 ∣ d) := by
  obtain ⟨c,r,k,hc,hr,_,_,hk,hprod,he,hthree⟩ := constraints P hcard h5 hnotAlt hp
  exact ⟨c*r,k,Nat.mul_dvd_mul hc hr,he,hk,hprod,fun h => (hthree h).trans (dvd_mul_right c r)⟩

end FiveTransitive.Degree36LargeSylowNormalizer

end CFSG
