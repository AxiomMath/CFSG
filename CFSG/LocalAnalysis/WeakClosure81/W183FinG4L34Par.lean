module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Map
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem isSylowIn_T0 :
    IsSylowIn 2 T0 S := by
  have hrel : T0.relIndex S = 315 := by
    have h := Subgroup.relIndex_mul_card T0 S
    rw [inf_eq_left.mpr T0_le_S, card_T0, card_S] at h
    omega
  refine ⟨T0_le_S, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 6) ?_
    rw [card_T0]
    norm_num
  · rw [hrel]
    norm_num

theorem le_P1_or_le_P2_of_borel_le
    {X : Subgroup (Equiv.Perm (Fin 42))} (hXS : X ≤ S) (hB : B0 ≤ X) (hne : X ≠ S) :
    X ≤ P1 ∨ X ≤ P2 := by
  have key : ∀ g ∈ X, g ∈ P1 ∨ g ∈ P2 := by
    intro g hg
    obtain ⟨k, hk, hb⟩ := exists_rep (hXS hg)
    have hyX : wordPerm (wReps.getD k []) ∈ X := by
      have := X.mul_mem hg (X.inv_mem (hB hb))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    have hg' : g = wordPerm (wReps.getD k []) * ((wordPerm (wReps.getD k []))⁻¹ * g) := by
      group
    rcases rep_cases hk with h | h | h
    · left
      rw [hg']
      exact P1.mul_mem h (B0_le_P1_P2.1 hb)
    · right
      rw [hg']
      exact P2.mul_mem h (B0_le_P1_P2.2 hb)
    · exfalso
      apply hne
      refine le_antisymm hXS ?_
      rw [← h, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases List.mem_append.1 hw with hw | hw
      · exact hB (Subgroup.subset_closure ⟨w, hw, rfl⟩)
      · rw [List.mem_singleton.1 hw]
        exact hyX
  have hsub : (X : Set (Equiv.Perm (Fin 42))) ⊆ (P1 : Set _) ∪ P2 := fun g hg => key g hg
  rcases SubgroupClass.subset_union.1 hsub with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem exists_conj_of_isMaxParabolicMod
    {P : Subgroup (Equiv.Perm (Fin 42))}
    (hP : IsMaxParabolicMod ⊥ S P) :
    ∃ k ∈ S, P = conjSubgroup P1 k ∨ P = conjSubgroup P2 k := by
  have hPmod : IsMaxParabolicMod ⊥ S P := hP
  obtain ⟨_, hPLt, _, S₁, _, hS₁S, hpow, hidx, hnorm⟩ := hPmod
  have hS₁pg : IsPGroup 2 S₁ := by
    intro s
    obtain ⟨n, hn⟩ := hpow s s.2
    exact ⟨n, Subtype.ext (by simpa using Subgroup.mem_bot.mp hn)⟩
  have hS₁syl : IsSylowIn 2 S₁ S := ⟨hS₁S, hS₁pg, hidx⟩
  obtain ⟨k, hkS, hk⟩ := exists_conj_isSylowIn isSylowIn_T0 hS₁syl
  have hkSinv : k⁻¹ ∈ S := S.inv_mem hkS
  let X : Subgroup (Equiv.Perm (Fin 42)) := conjSubgroup P k
  have hS₁eq : S₁ = conjSubgroup T0 k⁻¹ := by
    rw [hk, conjSubgroup, inv_inv]
  have hXmod : IsMaxParabolicMod ⊥ S X := by
    have hconj := isMaxParabolicMod_conj (L := S) (P := P) (τ := k⁻¹)
      (Subgroup.le_normalizer hkSinv) hP
    simpa [X, inv_inv] using hconj
  have hXmax : ∀ Y : Subgroup (Equiv.Perm (Fin 42)), X < Y → Y ≤ S → Y = S :=
    hXmod.2.2.1
  have hPX : conjSubgroup X k⁻¹ = P := by
    simp only [X]
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hXS : X ≤ S := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact S.mul_mem (S.mul_mem hkSinv (hPLt.le hp)) hkS
  have hB0conj_le_norm : conjSubgroup B0 k⁻¹ ≤
      Subgroup.normalizer (S₁ : Set (Equiv.Perm (Fin 42))) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro y
    have hbT0 : b ∈ Subgroup.normalizer (T0 : Set (Equiv.Perm (Fin 42))) :=
      B0_le_normalizer hb
    have h1 : y ∈ S₁ ↔ k⁻¹ * y * k ∈ T0 := by
      rw [hS₁eq, mem_conjSubgroup_iff, inv_inv]
    have h2 : (k * b * k⁻¹) * y * (k * b * k⁻¹)⁻¹ ∈ S₁ ↔
        b * (k⁻¹ * y * k) * b⁻¹ ∈ T0 := by
      rw [hS₁eq, mem_conjSubgroup_iff, inv_inv]
      rw [show k⁻¹ * ((k * b * k⁻¹) * y * (k * b * k⁻¹)⁻¹) * k =
          b * (k⁻¹ * y * k) * b⁻¹ by group]
    rw [h1, h2]
    exact Subgroup.mem_normalizer_iff.mp hbT0 (k⁻¹ * y * k)
  have hB0conj_le_S : conjSubgroup B0 k⁻¹ ≤ S := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulAut.conj_apply, inv_inv]
    exact S.mul_mem (S.mul_mem hkS (B0_le_S hb)) (S.inv_mem hkS)
  have hB0conjP : conjSubgroup B0 k⁻¹ ≤ P :=
    (le_inf hB0conj_le_S hB0conj_le_norm).trans hnorm
  have hB0X : B0 ≤ X := by
    intro b hb
    have hmemB0 : k * b * k⁻¹ ∈ conjSubgroup B0 k⁻¹ := by
      refine Subgroup.mem_map.mpr ⟨b, hb, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h : k * b * k⁻¹ ∈ P := hB0conjP hmemB0
    exact (mem_conjSubgroup_iff (A := P) (g := k) (x := b)).mpr h
  have hneX : X ≠ S := by
    intro hXS_eq
    have h1 : conjSubgroup S k⁻¹ = S :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hkSinv)
    have hPS : P = S := by rw [← hPX, hXS_eq, h1]
    exact hPLt.ne hPS
  have hP1S : P1 ≤ S := closure_wordSet_le wP₁
  have hP2S : P2 ≤ S := closure_wordSet_le wP₂
  have hne_card : (960 : ℕ) ≠ 20160 := by norm_num
  rcases le_P1_or_le_P2_of_borel_le hXS hB0X hneX with hX1 | hX2
  · have hXeqP1 : X = P1 := by
      by_contra hne
      have hlt : X < P1 := lt_of_le_of_ne hX1 hne
      exact hne_card (by rw [← card_P1, hXmax P1 hlt hP1S, card_S])
    exact ⟨k⁻¹, hkSinv, Or.inl (by rw [← hPX, hXeqP1])⟩
  · have hXeqP2 : X = P2 := by
      by_contra hne
      have hlt : X < P2 := lt_of_le_of_ne hX2 hne
      exact hne_card (by rw [← card_P2, hXmax P2 hlt hP2S, card_S])
    exact ⟨k⁻¹, hkSinv, Or.inr (by rw [← hPX, hXeqP2])⟩

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
