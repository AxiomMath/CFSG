module

public import CFSG.Permutation.FiveTransitive.Degree80SeventyNineData
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers

public section

namespace CFSG

namespace FiveTransitive.Degree80SeventyNineNormalizer
open MulAction Subgroup

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 78 ∧ k % 79 = 1 ∧ d * k * 79 = Nat.card P := by
  classical
  let S : Sylow 79 P := Sylow.nonempty.some
  have hS := Degree80SeventyNineData.sylow_card P hcard h5 hnotAlt S
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  obtain ⟨hd,_,hk,he⟩ := Degree19.long_prime_normalizer_constraints X P hexp hnotAlt
    (p := 79) (f := 1) (by norm_num) (by omega) (by omega) (by simpa using hcard) S hS
  exact ⟨_,_,hd,hk,he⟩

end FiveTransitive.Degree80SeventyNineNormalizer

end CFSG
