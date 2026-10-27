module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Blk
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourConj
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofImg
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_z3_commute_of_pow_three {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hL : Nat.card ↥L = 3) {q : MulAut W} (hqA : q ∈ A) (hq3 : q ^ 3 = 1) :
    L.map (MulAut.conj q).toMonoidHom = L ∧ (∀ l ∈ L, q * l = l * q) ∧
      ∀ l ∈ L₂, q * l = l * q := by
  classical
  have hcard :
      Set.ncard {X : Subgroup (MulAut W) |
          ∃ φ ∈ A, X = L.map (MulAut.conj φ).toMonoidHom} ≤ 2 := by
    have hsub :
        {X : Subgroup (MulAut W) |
            ∃ φ ∈ A, X = L.map (MulAut.conj φ).toMonoidHom} ⊆
          ({L, L₂} : Set (Subgroup (MulAut W))) := by
      intro X hX
      obtain ⟨φ, hφA, rfl⟩ := hX
      rcases hB.perm φ hφA with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h.1)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h.1))
    calc Set.ncard _ ≤ Set.ncard ({L, L₂} : Set (Subgroup (MulAut W))) :=
          Set.ncard_le_ncard hsub (Set.Finite.insert L (Set.finite_singleton L₂))
      _ ≤ 2 := le_of_eq (Set.ncard_pair (Ne.symm hB.ne))
  have hqN : q ∈ normalizer (L : Set (MulAut W)) :=
    s15GapFour_mem_normalizer_of_odd A L hcard hqA (by norm_num : Odd 3) hq3
  have hqL : L.map (MulAut.conj q).toMonoidHom = L := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hqN
  have hcommL : ∀ l ∈ L, q * l = l * q := by
    intro l hl
    have hqnorm : ∀ z ∈ L, q * z * q⁻¹ ∈ L := by
      intro z hz
      have h := Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom hz
      rw [hqL] at h
      simpa [MulAut.conj_apply] using h
    exact CFSG.RankThree.PartTwo.Sec14.Res8ON.commute_of_card_eq_three hL hqnorm hq3 hl
  have hqL₂ : L₂.map (MulAut.conj q).toMonoidHom = L₂ := by
    rcases hB.perm q hqA with h | h
    · exact h.2
    · exact absurd (h.1.symm.trans hqL) hB.ne
  have hcardL₂ : Nat.card ↥L₂ = 3 := hB.card_eq.trans hL
  have hcommL₂ : ∀ l ∈ L₂, q * l = l * q := by
    intro l hl
    have hqnorm : ∀ z ∈ L₂, q * z * q⁻¹ ∈ L₂ := by
      intro z hz
      have h := Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom hz
      rw [hqL₂] at h
      simpa [MulAut.conj_apply] using h
    exact CFSG.RankThree.PartTwo.Sec14.Res8ON.commute_of_card_eq_three hcardL₂ hqnorm hq3 hl
  exact ⟨hqL, hcommL, hcommL₂⟩

theorem s16h_z3_exists_elem_nine {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hLA : L ≤ A) (hL : Nat.card ↥L = 3) {y : MulAut W} (hyA : y ∈ A)
    (hyU₂ : y ∈ centSub (commSub (⊤ : Subgroup W) L₂)) (hyL : ∀ l ∈ L, y * l = l * y)
    (hy3 : y ^ 3 = 1) (hyL' : y ∉ L) :
    ∃ P : Subgroup (MulAut W), P ≤ A ⊓ centSub (commSub (⊤ : Subgroup W) L) ∧
      IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup (MulAut W) := L ⊔ Subgroup.zpowers y
  have hy_ne_one : y ≠ 1 := by
    intro hy1
    exact hyL' (by rw [hy1]; exact L.one_mem)
  have hzy_card : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy_ne_one
  have hL_comm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have ha3 : a ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := L) (x := ⟨a, ha⟩)
      rw [hL] at h
      exact congrArg (fun z : L => (z : MulAut W)) h
    exact CFSG.RankThree.PartTwo.Sec14.Res8ON.commute_of_card_eq_three hL
      (fun z hz => L.mul_mem (L.mul_mem ha hz) (L.inv_mem ha)) ha3 hb
  have hLel : IsElemAbelian 3 L := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hL_comm a a.2 b b.2)⟩⟩, ?_⟩
    intro x hx
    have h := pow_card_eq_one' (G := L) (x := ⟨x, hx⟩)
    rw [hL] at h
    exact congrArg (fun z : L => (z : MulAut W)) h
  have hLy : IsElemAbelian 3 (Subgroup.zpowers y) := isElemAbelian_zpowers hy3
  have hcomm : ∀ a ∈ L, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (Commute.symm (show Commute y a from hyL a ha)) k).eq
  have hEabel : IsElemAbelian 3 E := IsElemAbelian.sup_of_commute hLel hLy hcomm
  have h_inf : L ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(L ⊓ Subgroup.zpowers y) ∣ 3 := by
      rw [← hzy_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (H := L ⊓ Subgroup.zpowers y) h1
    · exfalso
      have heq : L ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hle : Subgroup.zpowers y ≤ L := by rw [← heq]; exact inf_le_left
      exact hyL' (hle (Subgroup.mem_zpowers y))
  have hEcard : Nat.card E = 9 := by
    have h1 : Nat.card ↥(L ⊔ Subgroup.zpowers y) *
          Nat.card ↥(L ⊓ Subgroup.zpowers y) = Nat.card L * Nat.card (Subgroup.zpowers y) :=
      CFSG.LocalAnalysis.ComponentInitial.card_sup_mul_card_inf_of_commute hcomm
    rw [h_inf, hL, hzy_card] at h1
    simpa using h1
  have hEA : E ≤ A := sup_le hLA (Subgroup.zpowers_le.mpr hyA)
  have hEcent : E ≤ centSub (commSub (⊤ : Subgroup W) L₂) :=
    sup_le hB.cent₁ (Subgroup.zpowers_le.mpr hyU₂)
  let P : Subgroup (MulAut W) := E.map (MulAut.conj x⁻¹).toMonoidHom
  have hPA : P ≤ A := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hp
    exact A.mul_mem (A.mul_mem (A.inv_mem hB.mem) (hEA he)) hB.mem
  have hPcent : P ≤ centSub (commSub (⊤ : Subgroup W) L) := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hp
    rw [mem_centSub]
    intro u hu
    have hxu : x u ∈ commSub (⊤ : Subgroup W) L₂ := (hB.swap u).mp hu
    have hefix : e (x u) = x u := (mem_centSub.mp (hEcent he)) (x u) hxu
    simp [MulAut.conj_apply, MulAut.mul_apply, hefix, MulAut.inv_apply_self]
  have hPabel : IsElemAbelian 3 P := hEabel.map (MulAut.conj x⁻¹).toMonoidHom
  have hPcard : Nat.card P = 9 := by
    have h := Subgroup.card_map_of_injective (K := E)
      (f := (MulAut.conj x⁻¹).toMonoidHom) (MulAut.conj x⁻¹).injective
    rw [hEcard] at h
    exact h
  exact ⟨P, le_inf hPA hPcent, hPabel, le_of_eq hPcard.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
