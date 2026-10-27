module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

private lemma s16c167_eq_three_of_three_dvd_of_dvd_six {n : ℕ} (h3 : 3 ∣ n) (h6 : n ∣ 6)
    (hodd : Odd n) : n = 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  rw [Nat.odd_iff] at hodd
  interval_cases n <;> omega

theorem s16c167_card_relPPrimeCore_of_isSym_three {A : Type} [Group A] [Finite A]
    {K L X : Subgroup A} (h : IsInternalDirect K L X) (hK : IsSym ↥K 3)
    (hle : relPPrimeCore 2 X ≤ K) : Nat.card ↥(relPPrimeCore 2 X) = 3 := by
  obtain ⟨hc, _hdisj, rfl⟩ := h
  obtain ⟨e⟩ := hK
  let M : Subgroup ↥K := (alternatingGroup (Fin 3)).map e.symm.toMonoidHom
  let A₃ : Subgroup A := M.map K.subtype
  have hA₃K : A₃ ≤ K := Subgroup.map_subtype_le M
  have hK6 : Nat.card ↥K = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hA₃card : Nat.card A₃ = 3 := by
    have h1 : Nat.card A₃ = Nat.card M := Subgroup.card_subtype K M
    have h2 : Nat.card M = Nat.card (alternatingGroup (Fin 3)) :=
      Subgroup.card_map_of_injective e.symm.injective
    rw [h1, h2, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hMn : M.Normal :=
    Subgroup.Normal.map alternatingGroup.normal e.symm.toMonoidHom e.symm.surjective
  have hA₃sub : A₃.subgroupOf K = M :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective M
  have hKn : K ≤ Subgroup.normalizer (A₃ : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA₃K).1 (by rw [hA₃sub]; exact hMn)
  have hLc : L ≤ Subgroup.centralizer (A₃ : Set A) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc (hA₃K ha))) l hl).symm
  have hLn : L ≤ Subgroup.normalizer (A₃ : Set A) :=
    hLc.trans (Subgroup.centralizer_le_normalizer (A₃ : Set A))
  have hsupn : K ⊔ L ≤ Subgroup.normalizer (A₃ : Set A) := sup_le hKn hLn
  have hnormal : (A₃.subgroupOf (K ⊔ L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hA₃K.trans le_sup_left)).2 hsupn
  have hA₃le : A₃ ≤ relPPrimeCore 2 (K ⊔ L) := by
    refine le_sSup ⟨hA₃K.trans le_sup_left, hnormal, ?_⟩
    rw [hA₃card]
    decide
  have h3dvd : 3 ∣ Nat.card ↥(relPPrimeCore 2 (K ⊔ L)) := by
    rw [← hA₃card]
    exact Subgroup.card_dvd_of_le hA₃le
  have hdvd6 : Nat.card ↥(relPPrimeCore 2 (K ⊔ L)) ∣ 6 := by
    rw [← hK6]
    exact Subgroup.card_dvd_of_le hle
  have hodd : Odd (Nat.card ↥(relPPrimeCore 2 (K ⊔ L))) :=
    Nat.coprime_two_left.1 (coprime_card_relPPrimeCore Nat.prime_two (K ⊔ L))
  exact s16c167_eq_three_of_three_dvd_of_dvd_six h3dvd hdvd6 hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
