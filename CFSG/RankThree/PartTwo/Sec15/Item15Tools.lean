module

public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem map_conj_mem_scriptQPi (hnat : IsNaturalFamily A LB) {H : Subgroup G} {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwH : w ∈ Subgroup.normalizer (H : Set G))
    {Q : Subgroup G} {π : Set Nat.Primes} (hQ : Q ∈ scriptQPi A LB H π) :
    Q.map (MulAut.conj w).toMonoidHom ∈ scriptQPi A LB H π := by
  have h := map_conj_mem_scriptQPi_top hnat hwA (Q := Q) (π := π) ⟨⟨hQ.1.1, le_top⟩, hQ.2⟩
  refine ⟨⟨h.1.1, ?_⟩, h.2⟩
  rw [← Late.map_conj_eq_of_mem_normalizer hwH]
  exact Subgroup.map_mono hQ.1.2

theorem inf_mem_scriptQPiStar_of_transOn (hnat : IsNaturalFamily A LB) {H : Subgroup G}
    (hWH : Subgroup.normalizer (A : Set G) ≤ H)
    (htr : TransOn A LB (Subgroup.normalizer (A : Set G)) ⊤)
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2)) :
    S ⊓ H ∈ scriptQPiStar A LB H (piOf 2) := by
  have hAH : A ≤ H := Subgroup.le_normalizer.trans hWH
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A LB H (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨T, -, hT⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A LB H (piOf 2))) hbot
  obtain ⟨T', hTT', hT'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A LB ⊤ (piOf 2))) (a := T) ⟨⟨hT.prop.1.1, le_top⟩, hT.prop.2⟩
  obtain ⟨w, hw, hwT'⟩ := htr S hS T' hT'
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
  have hwH : w ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer (hWH hwA)
  have hw'A : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem hwA
  have hw'H : w⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem hwH
  have hSH : S ⊓ H ∈ scriptQPi A LB H (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hS.prop.1.1 inf_le_left
        (le_normalizer_inf hS.prop.1.1.1.2.2 (hAH.trans Subgroup.le_normalizer)), inf_le_right⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
        ((isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop).to_le inf_le_left)⟩
  have hconj : (S ⊓ H).map (MulAut.conj w).toMonoidHom = T' ⊓ H := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, ← hwT',
      Late.map_conj_eq_of_mem_normalizer hwH]
  have hTle : T ≤ (S ⊓ H).map (MulAut.conj w).toMonoidHom := by
    rw [hconj]
    exact le_inf hTT' hT.prop.1.2
  have hTeq : T = (S ⊓ H).map (MulAut.conj w).toMonoidHom :=
    hT.eq_of_le (map_conj_mem_scriptQPi hnat hwA hwH hSH) hTle
  have hSHT : S ⊓ H = T.map (MulAut.conj w⁻¹).toMonoidHom := by
    rw [hTeq, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  rw [hSHT]
  exact maximal_map_conj (W := Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (H : Set G))
    (fun Q hQ v hv => map_conj_mem_scriptQPi hnat (Subgroup.mem_inf.mp hv).1
      (Subgroup.mem_inf.mp hv).2 hQ) hT (Subgroup.mem_inf.mpr ⟨hw'A, hw'H⟩)

end CFSG.RankThree.PartTwo.Sec15
