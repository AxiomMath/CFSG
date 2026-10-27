module

public import CFSG.Permutation.FiveTransitive.Degree48LargeSylowCentralizer
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage

public section

namespace CFSG

namespace FiveTransitive.Degree48LargeSylowNormalizer

open MulAction Subgroup FixedNormalizerAction

theorem constraints_for_sylow
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 47 ∨ p = 23 ∨ p = 11)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) :
    ∃ d k : ℕ, d ∣ (48 / p).factorial * (p - 1) ∧ (48 % p).factorial ∣ d ∧
      k % p = 1 ∧ d * k * p = Nat.card P ∧
      k = (Subgroup.normalizer (S : Set P)).index ∧
      Nat.card (Subgroup.normalizer (S : Set P)) = d * p := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> norm_num
  let _ : Fact p.Prime := ⟨hprime⟩
  have hS := Degree48LargeSylowData.sylow_card P hcard h5 hp hfree S
  have hC := Degree48LargeSylowCentralizer.centralizer_card_dvd P hcard h5 hnotAlt hp hfree S
  obtain ⟨hc,hr,_,_,hk,hprod⟩ := Degree31FiveFixerNormalizer.normalizer_constraints
    P (48 / p).factorial S hS hC
  let C := Subgroup.centralizer (S : Set P)
  let N := Subgroup.normalizer (S : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change c * r * N.index * p = Nat.card P at hprod
  have hNcard : Nat.card N = c * r * p := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite)
    calc
      N.index * Nat.card N = Nat.card P := N.index_mul_card
      _ = N.index * (c * r * p) := by rw [← hprod]; ring
  refine ⟨c*r,N.index,Nat.mul_dvd_mul hc hr,?_,hk,hprod,rfl,hNcard⟩
  have hf := Degree48LargeSylowData.sylow_fixed_card P hcard h5 hp hfree S
  have hi := AmbientSylowSmallFixedImage.sylow_fixed_image p (48 % p) hprime
    (by rcases hp with rfl | rfl | rfl <;> norm_num) P (by omega) h5 S hf
  have hF : Nat.card (Fixed (X := X) (S : Subgroup P)) = 48 % p := by
    rw [fixed_eq]; exact hf
  let rho := toPermHom (Normalizer (S : Subgroup P)) (Fixed (X := X) (S : Subgroup P))
  have hd := Subgroup.card_range_dvd rho
  change Nat.card (Image (X := X) (S : Subgroup P)) ∣ _ at hd
  rw [hi,Subgroup.card_top,Nat.card_perm,hF] at hd
  change (48 % p).factorial ∣ Nat.card N at hd
  rw [hNcard] at hd
  have hcop : Nat.Coprime (48 % p).factorial p := by
    rcases hp with rfl | rfl | rfl <;> norm_num
  exact hcop.dvd_of_dvd_mul_right hd

theorem constraints_of_prime_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 47 ∨ p = 23 ∨ p = 11)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s)) :
    ∃ d k : ℕ, d ∣ (48 / p).factorial * (p - 1) ∧ (48 % p).factorial ∣ d ∧
      k % p = 1 ∧ d * k * p = Nat.card P := by
  let S : Sylow p P := Sylow.nonempty.some
  obtain ⟨d,k,hd,hf,hk,he,_,_⟩ := constraints_for_sylow P hcard h5 hnotAlt hp hfree S
  exact ⟨d,k,hd,hf,hk,he⟩

end FiveTransitive.Degree48LargeSylowNormalizer

end CFSG
