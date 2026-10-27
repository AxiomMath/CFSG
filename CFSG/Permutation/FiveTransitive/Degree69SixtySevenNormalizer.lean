module

public import CFSG.Permutation.FiveTransitive.Degree69SixtySevenData
public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeFree
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage

public section

namespace CFSG

namespace FiveTransitive.Degree69SixtySevenNormalizer
open MulAction Subgroup FixedNormalizerAction

private theorem two_dvd_normalizer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 67 P) : 2 ∣ Nat.card (Subgroup.normalizer (S : Set P)) := by
  classical
  let _ : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  have hfree := fun s hs => Degree69LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 67
    (by norm_num) (by omega)
  have hS := Degree69SixtySevenData.sylow_card P hcard h5 hfree S
  have hne : (S : Subgroup P) ≠ ⊥ := by
    intro he
    have hh : Nat.card (S : Subgroup P) = 1 := Subgroup.card_eq_one.mpr he
    rw [hS] at hh
    omega
  have hf := Degree69SixtySevenData.fixed_card P hcard hfree (S : Subgroup P) S.isPGroup' hne
  have hi := AmbientSylowSmallFixedImage.sylow_fixed_image 67 2 (by norm_num) (by omega)
    P (by omega) h5 S hf
  have hF : Nat.card (Fixed (X := X) (S : Subgroup P)) = 2 := by rw [fixed_eq]; exact hf
  let rho := toPermHom (Normalizer (S : Subgroup P)) (Fixed (X := X) (S : Subgroup P))
  have hd := Subgroup.card_range_dvd rho
  change Nat.card (Image (X := X) (S : Subgroup P)) ∣ _ at hd
  rw [hi,Subgroup.card_top,Nat.card_perm,hF] at hd
  norm_num only [Nat.factorial] at hd
  exact hd

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 66 ∧ 2 ∣ d ∧ k % 67 = 1 ∧ d * k * 67 = Nat.card P := by
  classical
  let S : Sylow 67 P := Sylow.nonempty.some
  have hS := Degree69SixtySevenData.sylow_card P hcard h5 (fun s hs =>
    Degree69LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 67
      (by norm_num) (by omega)) S
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  obtain ⟨hd,_,hk,he⟩ := Degree19.long_prime_normalizer_constraints X P hexp hnotAlt
    (p := 67) (f := 2) (by norm_num) (by omega) (by omega) (by simpa using hcard) S hS
  let C := Subgroup.centralizer (S : Set P)
  let N := Subgroup.normalizer (S : Set P)
  let d := C.relIndex N
  have hNcard : Nat.card N = d * 67 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite)
    calc
      N.index * Nat.card N = Nat.card P := N.index_mul_card
      _ = N.index * (d * 67) := by rw [← he]; ring
  have htwo := two_dvd_normalizer P hcard h5 hnotAlt S
  change 2 ∣ Nat.card N at htwo
  rw [hNcard] at htwo
  have htwoD : 2 ∣ d := (Nat.prime_two.dvd_mul.mp htwo).resolve_right (by norm_num)
  exact ⟨d,N.index,hd,htwoD,hk,he⟩

end FiveTransitive.Degree69SixtySevenNormalizer

end CFSG
