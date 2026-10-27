module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3AutLineStabilizer
public import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFixVec
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.UnitaryFlag

theorem subgroup_map_mulAut_eq_of_map_mulEquiv {Y S : Type} [Group Y] [Group S] (f : Y ≃* S)
    {L' : Subgroup S} {β : MulAut Y}
    (h : L'.map (f.symm.trans (β.trans f)).toMonoidHom = L') :
    (L'.map f.symm.toMonoidHom).map β.toMonoidHom = L'.map f.symm.toMonoidHom := by
  let β' : MulAut S := f.symm.trans (β.trans f)
  have hLf : (L'.map f.symm.toMonoidHom).map f.toMonoidHom = L' := by
    rw [Subgroup.map_map]
    simp
  have h1 : ((L'.map f.symm.toMonoidHom).map β.toMonoidHom).map f.toMonoidHom = L' := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rw [show (f.toMonoidHom.comp β.toMonoidHom).comp f.symm.toMonoidHom = β'.toMonoidHom
      from rfl]
    exact h
  exact Subgroup.map_injective f.injective (by rw [h1, hLf])

theorem exists_isL2_le_of_isU3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU3 Y n)
    (hn : 2 ≤ n) (heven : Even n) {T : Subgroup Y} (hTc : IsMulCommutative T)
    (hT : Nat.card T = 2 ^ n - 1) :
    ∃ L : Subgroup Y, IsL2 L n ∧ T ≤ L ∧
      ∀ β : MulAut Y, (∀ a ∈ T, β a = a) → L.map β.toMonoidHom = L := by
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have hmod : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
    have hnot : ¬ 3 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
      norm_num
    exact Nat.prime_three.coprime_iff_not_dvd.2 hnot
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K := unitaryFieldDataOfCard hK
  have hbot : unitaryScalars h 3 = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, card_unitaryScalars h (by norm_num : 1 ≤ 3), hgcd]
  have hinj : Function.Injective (unitaryProj h 3) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj]
    exact hbot
  let e : Y ≃* StatedSU 3 (2 ^ n) K :=
    e0.trans ((unitaryPSUEquivStated hK).symm.trans
      (MulEquiv.ofBijective (unitaryProj h 3) ⟨hinj, unitaryProj_surjective h 3⟩).symm)
  have hq : 2 < 2 ^ n := by
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num at h2
    omega
  let T' : Subgroup (StatedSU 3 (2 ^ n) K) := T.map e.toMonoidHom
  have hTc' : IsMulCommutative T' := by
    let : IsMulCommutative T := hTc
    exact Subgroup.map_isMulCommutative T e.toMonoidHom
  have hT' : Nat.card T' = 2 ^ n - 1 := by
    rw [Subgroup.card_map_of_injective e.injective, hT]
  obtain ⟨v, hvne, hvfix, hvspan, L', hL', hL'2⟩ :=
    exists_fixVec_isL2_of_torus hK hn hTc' hT'
  let L : Subgroup Y := L'.map e.symm.toMonoidHom
  have hLf : L.map e.toMonoidHom = L' := by
    rw [Subgroup.map_map]
    simp
  have hL2 : IsL2 L n :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((MulEquiv.subgroupMap e L).trans (MulEquiv.subgroupCongr hLf)).symm hL'2
  refine ⟨L, hL2, ?_, ?_⟩
  · intro a ha
    have hfa : e a ∈ T' := Subgroup.mem_map_of_mem e.toMonoidHom ha
    have hfa' : e a ∈ L' := (hL' (e a)).2 (hvfix (e a) hfa)
    have hmem : e.symm (e a) ∈ L := Subgroup.mem_map_of_mem e.symm.toMonoidHom hfa'
    rwa [e.symm_apply_apply] at hmem
  · intro β hβ
    let β' : MulAut (StatedSU 3 (2 ^ n) K) := e.symm.trans (β.trans e)
    have hβ' : ∀ b ∈ T', β' b = b := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
      change e (β (e.symm (e a))) = e a
      rw [show e.symm (e a) = a from e.symm_apply_apply a, hβ a ha]
    exact subgroup_map_mulAut_eq_of_map_mulEquiv e
      (map_stabilizer_eq_of_forall_mem_eq hK hq hvne hvfix hvspan hL' β' hβ')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
