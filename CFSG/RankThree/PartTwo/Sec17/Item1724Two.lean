module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1724Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      Q ⊓ Subgroup.normalizer (Y₀ : Set G) = ⊥

variable {G : Type} [Group G] [Finite G]

theorem isConjIn_of_not_three_dvd {A : Subgroup G} (hA : IsE27 A) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card (oPrimeResidualOf p (delta A (lB A) Y)))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf p))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf p)) :
    IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) S T := by
  have : Fact p.Prime := ⟨hp⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  set D := delta A (lB A) Y with hD
  set R := oPrimeResidualOf p D with hR
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := le_normalizer_oPrimeResidualOf hAD
  have hRinv : R ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr h3, hAR⟩
  set E := delta A (lB A) R with hE
  have hEQ : E ∈ scriptQ A (lB A) := delta_mem_scriptQ hA h146 hRinv
  have hER : E ≤ R := delta_le R
  have hRY : R ≤ Y := (oPrimeResidualOf_le_self p D).trans (delta_le Y)
  have hE3 : ¬ 3 ∣ Nat.card E := fun h => h3 (h.trans (Subgroup.card_dvd_of_le hER))
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hsyl : ∀ S ∈ scriptQPiStar A (lB A) Y (piOf p), CFSG.Open.fusionIsSylowIn p S E ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hSp : IsPGroup p S := isPGroup_of_mem_scriptQPi hp hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
    have hSD : S ≤ D := le_delta hSQ hS.prop.1.2
    have hSR : S ≤ R := by
      rw [hR, oPrimeResidualOf_eq_closure]
      intro x hx
      obtain ⟨k, hk⟩ := hSp ⟨x, hx⟩
      exact Subgroup.subset_closure ⟨hSD hx, k, by simpa using congrArg Subtype.val hk⟩
    have hSE : S ≤ E := le_delta hSQ hSR
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three hp hA3 hE3 hAE hSE hSp hAS
    have hS'mem : S' ∈ scriptQPi A (lB A) Y (piOf p) :=
      ⟨⟨mem_scriptQ_of_le hEQ hS'.1 hAS', hS'.1.trans (hER.trans hRY)⟩,
        (isPiSubgroup_piOf_iff hp S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'mem hSS'
    exact ⟨this ▸ hS', hAS⟩
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three hp
    hA3 hE3 hAE hSs hTs hAS hAT
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hCEA : E ⊓ Subgroup.centralizer (A : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hEQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hAE (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCEA hx, hER.trans hRY (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

end CFSG.RankThree.PartTwo.Sec17
