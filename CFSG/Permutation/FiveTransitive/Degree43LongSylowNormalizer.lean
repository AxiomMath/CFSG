module

public import CFSG.Permutation.FiveTransitive.Degree43LongSylowData
public import CFSG.Permutation.FiveTransitive.Degree43LongSylowCentralizer
public import CFSG.Permutation.FiveTransitive.Degree43LargePrimeFree
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage

public section

namespace CFSG

namespace FiveTransitive.Degree43LongSylowNormalizer
open MulAction Subgroup FixedNormalizerAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 41 ∨ p = 43) :
    ∃ d k : ℕ, d ∣ p - 1 ∧ (p = 41 → 2 ∣ d) ∧ k % p = 1 ∧ d * k * p = Nat.card P := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fact (Nat.Prime p) := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  let S : Sylow p P := Sylow.nonempty.some
  have hS := Degree43LongSylowData.sylow_card P hcard h5 hp (fun s hs =>
    Degree43LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p
      (by rcases hp with rfl | rfl <;> norm_num) (by rcases hp with rfl | rfl <;> omega)) S
  have hC := Degree43LongSylowCentralizer.centralizer_card_dvd P hcard h5 hnotAlt hp S hS
  obtain ⟨hc,hr,_,_,hk,hprod⟩ := Degree31FiveFixerNormalizer.normalizer_constraints
    P 1 S hS (by simpa using hC)
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
  refine ⟨c*r,N.index,?_,?_,hk,hprod⟩
  · simpa using Nat.mul_dvd_mul hc hr
  · intro hp41
    subst p
    have hf := Degree43LongSylowCentralizer.fortyone_fixed_card P hcard S hS
    have hi := AmbientSylowSmallFixedImage.sylow_fixed_image 41 2 (by norm_num)
      (by omega) P (by omega) h5 S hf
    have hF : Nat.card (Fixed (X := X) (S : Subgroup P)) = 2 := by rw [fixed_eq]; exact hf
    let rho := toPermHom (Normalizer (S : Subgroup P)) (Fixed (X := X) (S : Subgroup P))
    have hd := Subgroup.card_range_dvd rho
    change Nat.card (Image (X := X) (S : Subgroup P)) ∣ _ at hd
    rw [hi,Subgroup.card_top,Nat.card_perm,hF] at hd
    change 2 ∣ Nat.card N at hd
    rw [hNcard] at hd
    exact (show Nat.Coprime 2 41 by norm_num).dvd_of_dvd_mul_right hd

end FiveTransitive.Degree43LongSylowNormalizer

end CFSG
