module

public import CFSG.Permutation.FiveTransitive.Degree67SixtySevenData
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree67SixtySevenNormalizer

open MulAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 66 ∧ k % 67 = 1 ∧ d * k * 67 = Nat.card P := by
  classical
  let S : Sylow 67 P := Sylow.nonempty.some
  have hS := Degree67SixtySevenData.sylow_card P hcard h5 (fun s hs =>
    Degree67LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 67
      (by norm_num) (by omega)) S
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  obtain ⟨hd,_,hk,he⟩ := Degree19.long_prime_normalizer_constraints X P hexp hnotAlt
    (p := 67) (f := 0) (by norm_num) (by omega) (by omega) (by simpa using hcard) S hS
  exact ⟨_,_,hd,hk,he⟩

end FiveTransitive.Degree67SixtySevenNormalizer

end CFSG
