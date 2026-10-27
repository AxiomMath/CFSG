module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private lemma s16c13bcA_three_const {α : Type*} [Fintype α] [DecidableEq α] (f : α → ZMod 2)
    (h : 4 < Fintype.card α) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 2)
    (by simp [ZMod.card]; omega)
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact ⟨a, b, c, hab, hac, hbc, ha.trans hb.symm, ha.trans hc.symm⟩

theorem s16c13bcA_pairFixed_altPerm {N : ℕ} (hN : 8 ≤ N) :
    s16c13bcA_PairFixed (alternatingGroup (Fin N)) (Fin N → ZMod 2) := by
  intro f
  obtain ⟨a, b, c, hab, hac, hbc, hfab, hfac⟩ :=
    s16c13bcA_three_const f (by rw [Fintype.card_fin]; omega)
  set T1 : Finset (Fin N) := {a, b, c} with hT1
  have hT1c : T1.card = 3 := by simp [hT1, hab, hac, hbc]
  have hT1mem : ∀ x, x ∈ T1 ↔ x = a ∨ x = b ∨ x = c := by intro x; rw [hT1]; simp
  have hcard : Fintype.card {x : Fin N // x ∉ T1} = N - 3 := by
    rw [Fintype.card_subtype_compl (fun x : Fin N => x ∈ T1), Fintype.card_fin,
      Fintype.card_coe, hT1c]
  obtain ⟨d, e, g, hde, hdg, heg, hfde, hfdg⟩ :=
    s16c13bcA_three_const (fun x : {x : Fin N // x ∉ T1} => f x.1)
      (by rw [hcard]; omega)
  have hde' : d.1 ≠ e.1 := fun h => hde (Subtype.ext h)
  have hdg' : d.1 ≠ g.1 := fun h => hdg (Subtype.ext h)
  have heg' : e.1 ≠ g.1 := fun h => heg (Subtype.ext h)
  have hdT1 : d.1 ∉ T1 := d.2
  have heT1 : e.1 ∉ T1 := e.2
  have hgT1 : g.1 ∉ T1 := g.2
  set T2 : Finset (Fin N) := {d.1, e.1, g.1} with hT2
  have hT2mem : ∀ x, x ∈ T2 ↔ x = d.1 ∨ x = e.1 ∨ x = g.1 := by intro x; rw [hT2]; simp
  set σ₁ : Equiv.Perm (Fin N) := Equiv.swap a b * Equiv.swap a c with hσ₁
  set σ₂ : Equiv.Perm (Fin N) := Equiv.swap d.1 e.1 * Equiv.swap d.1 g.1 with hσ₂
  have h3₁ : σ₁.IsThreeCycle := by
    rw [hσ₁]; exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have h3₂ : σ₂.IsThreeCycle := by
    rw [hσ₂]; exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hde' hdg' heg'
  have hout1 : ∀ x, x ∉ T1 → σ₁ x = x := by
    intro x hx
    have hxa : x ≠ a := fun h => hx (by rw [hT1]; simp [h])
    have hxb : x ≠ b := fun h => hx (by rw [hT1]; simp [h])
    have hxc : x ≠ c := fun h => hx (by rw [hT1]; simp [h])
    simp [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxc,
      Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hout2 : ∀ x, x ∉ T2 → σ₂ x = x := by
    intro x hx
    have hxd : x ≠ d.1 := fun h => hx (by rw [hT2]; simp [h])
    have hxe : x ≠ e.1 := fun h => hx (by rw [hT2]; simp [h])
    have hxg : x ≠ g.1 := fun h => hx (by rw [hT2]; simp [h])
    simp [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxd hxg,
      Equiv.swap_apply_of_ne_of_ne hxd hxe]
  have hdisj : Equiv.Perm.Disjoint σ₁ σ₂ := by
    intro x
    by_cases hx : x ∈ T1
    · right
      apply hout2
      intro hx2
      rcases (hT2mem x).mp hx2 with h | h | h
      · exact hdT1 (h ▸ hx)
      · exact heT1 (h ▸ hx)
      · exact hgT1 (h ▸ hx)
    · left
      exact hout1 x hx
  let g₁ : alternatingGroup (Fin N) := ⟨σ₁, h3₁.mem_alternatingGroup⟩
  let g₂ : alternatingGroup (Fin N) := ⟨σ₂, h3₂.mem_alternatingGroup⟩
  have hf1 : ∀ x, x ∈ T1 → f x = f a := by
    intro x hx
    rcases (hT1mem x).mp hx with rfl | rfl | rfl
    · rfl
    · exact hfab.symm
    · exact hfac.symm
  have hf2 : ∀ x, x ∈ T2 → f x = f d.1 := by
    intro x hx
    rcases (hT2mem x).mp hx with rfl | rfl | rfl
    · rfl
    · exact hfde.symm
    · exact hfdg.symm
  have hfixd : σ₁ d.1 = d.1 := hout1 d.1 hdT1
  have hσ₂d : σ₂ d.1 = g.1 := by
    rw [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hdg'.symm heg'.symm
  have hnot : g₂ ∉ Subgroup.zpowers g₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : σ₂ = σ₁ ^ k := by
      have hcoe := congrArg (fun x : alternatingGroup (Fin N) => (x : Equiv.Perm (Fin N))) hk
      simpa [Subgroup.coe_zpow] using hcoe.symm
    have hd2 : σ₂ d.1 = d.1 := by
      rw [hk']
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfixd k
    rw [hσ₂d] at hd2
    exact hdg' hd2.symm
  refine ⟨g₁, g₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.orderOf_mk σ₁ h3₁.mem_alternatingGroup).trans h3₁.orderOf
  · exact (Subgroup.orderOf_mk σ₂ h3₂.mem_alternatingGroup).trans h3₂.orderOf
  · apply Subtype.ext
    show σ₁ * σ₂ = σ₂ * σ₁
    exact hdisj.commute
  · exact hnot
  · funext i
    change f ((σ₁⁻¹) i) = f i
    by_cases hi : i ∈ T1
    · have hin : σ₁⁻¹ i ∈ T1 := by
        by_contra h
        have h1 := hout1 _ h
        have h2 : σ₁ (σ₁⁻¹ i) = i := by simp
        rw [h2] at h1
        exact h (h1 ▸ hi)
      rw [hf1 _ hin, hf1 _ hi]
    · have hii : σ₁⁻¹ i = i := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (hout1 i hi).symm
      rw [hii]
  · funext i
    change f ((σ₂⁻¹) i) = f i
    by_cases hi : i ∈ T2
    · have hin : σ₂⁻¹ i ∈ T2 := by
        by_contra h
        have h1 := hout2 _ h
        have h2 : σ₂ (σ₂⁻¹ i) = i := by simp
        rw [h2] at h1
        exact h (h1 ▸ hi)
      rw [hf2 _ hin, hf2 _ hi]
    · have hii : σ₂⁻¹ i = i := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (hout2 i hi).symm
      rw [hii]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
