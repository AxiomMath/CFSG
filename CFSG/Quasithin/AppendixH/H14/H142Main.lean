module

public import CFSG.Quasithin.AppendixH.H14.H142Std
public import CFSG.Quasithin.AppendixH.H14.H142QF4

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Open
  CFSG.GH74.KGroups
open scoped Pointwise

theorem h142_part2 {a : Fin 24} {O : Finset (Fin 24)}
    {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)} (hS : IsSextet S) (hB : B ∈ S)
    (haB : a ∈ B) (haO : a ∈ O) (hOu : ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ O = B₁ ∪ B₂) :
    ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
      ConjIsoModel (MY (M23g a) (S.erase B)) (KY (M23g a) (S.erase B))
        (Multiplicative (Fin 2 → K)) (gammaLset 2 K) := by
  obtain ⟨c, hc, hca, hcQ, _⟩ := exists_std_data hS hB haB haO hOu
  refine ⟨GF4, inferInstance, card_gf4, ?_⟩
  apply conjIsoModel_of_map_conj c
  rw [(conj_stdQ hc hca hcQ).1, (conj_stdQ hc hca hcQ).2]
  exact stdMQ_conjIsoModel

theorem h142_part3 {a : Fin 24} {O : Finset (Fin 24)}
    {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)} (hS : IsSextet S) (hB : B ∈ S)
    (haB : a ∈ B) (haO : a ∈ O) (hOu : ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ O = B₁ ∪ B₂) :
    ((∃ π : ↥(MY (M23g a) (O.erase a)) →* ↥(alternatingGroup (Fin 7)),
        Function.Surjective π ∧
          π.ker = (KY (M23g a) (O.erase a)).subgroupOf (MY (M23g a) (O.erase a))) ∧
      Nat.card ↥(KY (M23g a) (O.erase a)) = 16 ∧
      ∀ W : Subgroup S24, W ≤ KY (M23g a) (O.erase a) → W ≠ ⊥ →
        (∀ g ∈ MY (M23g a) (O.erase a), W.map (MulAut.conj g).toMonoidHom = W) →
          W = KY (M23g a) (O.erase a)) := by
  obtain ⟨c, hc, hca, _, hcH⟩ := exists_std_data hS hB haB haO hOu
  have hMQ : (MY (M23g a) (O.erase a)).map (MulAut.conj c).toMonoidHom = stdMH :=
    (conj_stdH hc hca hcH).1
  have hKH : (KY (M23g a) (O.erase a)).map (MulAut.conj c).toMonoidHom = stdEH :=
    (conj_stdH hc hca hcH).2
  have keyQ : ∀ X Y : Subgroup S24, X = stdMH → Y = stdEH →
      ∃ π : ↥X →* ↥(alternatingGroup (Fin 7)),
        Function.Surjective π ∧ π.ker = Y.subgroupOf X := by
    rintro X Y rfl rfl
    exact exists_surj_alt7
  have keyI : ∀ X Y : Subgroup S24, X = stdMH → Y = stdEH →
      ∀ W : Subgroup S24, W ≤ Y → W ≠ ⊥ →
        (∀ g ∈ X, W.map (MulAut.conj g).toMonoidHom = W) → W = Y := by
    rintro X Y rfl rfl
    exact stdEH_irreducible
  refine ⟨?_, ?_, ?_⟩
  · exact exists_surj_ker_of_map_conj c (keyQ _ _ hMQ hKH)
  · rw [← card_map_conj c (KY (M23g a) (O.erase a)), hKH, card_stdEH]
  · exact irreducible_of_map_conj c (keyI _ _ hMQ hKH)

end CFSG.Quasithin.AppendixH.H14
