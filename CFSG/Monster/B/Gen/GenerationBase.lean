
module

public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.Data

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot

@[expose] noncomputable def psiImage (G : Subgroup Cbar) :
    Submodule (ZMod 2) (Wv (phi0 (coordOf rStar))) where
  carrier := {w | ∃ e : Ebar, (e : Cbar) ∈ G ∧ Multiplicative.toAdd (psiBar e) = w}
  add_mem' := by
    rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
    exact ⟨e₁ * e₂, G.mul_mem h₁ h₂, by rw [map_mul, toAdd_mul]⟩
  zero_mem' := ⟨1, G.one_mem, by rw [map_one, toAdd_one]⟩
  smul_mem' := by
    rintro c _ ⟨e, he, rfl⟩
    rcases (show c = 0 ∨ c = 1 by fin_cases c; exacts [Or.inl rfl, Or.inr rfl]) with rfl | rfl
    · exact ⟨1, G.one_mem, by rw [map_one, toAdd_one, zero_smul]⟩
    · exact ⟨e, he, by rw [one_smul]⟩

theorem mem_psiImage {G : Subgroup Cbar} {w : Wv (phi0 (coordOf rStar))} :
    w ∈ psiImage G ↔ ∃ e : Ebar, (e : Cbar) ∈ G ∧ Multiplicative.toAdd (psiBar e) = w :=
  Iff.rfl

section Generation

variable (G : Subgroup Cbar)
  (hsurj : ∀ k : Kstab (phi0 (coordOf rStar)), ∃ g : Jbar, (g : Cbar) ∈ G ∧ jbarToKv g = k)

include hsurj in
theorem psiImage_invariant (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar)))
    (hw : w ∈ psiImage G) : wAct _ k w ∈ psiImage G := by
  obtain ⟨g, hgG, rfl⟩ := hsurj k
  obtain ⟨e, heG, rfl⟩ := hw
  refine ⟨⟨(g : Cbar)⁻¹ * e * g, conj_mem_Ebar g.2 e.2⟩,
    G.mul_mem (G.mul_mem (G.inv_mem hgG) heG) hgG, ?_⟩
  have h := psiBar_conj g.2 e.2
  rw [h, toAdd_ofAdd]

theorem eq_top_of_cover {E : Type*} [Group E] (G' : Subgroup E) (x : E)
    (hxc : ∀ e, e * x = x * e) (hrep : ∀ e, ∃ e' ∈ G', e = e' ∨ e = e' * x)
    (hcomm : ∀ a ∈ G', ∀ b ∈ G', (b * a)⁻¹ * (a * b) = 1 ∨ (b * a)⁻¹ * (a * b) = x)
    (hnonab : ∃ a b : E, a * b ≠ b * a) : G' = ⊤ := by
  have hxG : x ∈ G' := by
    by_contra hxG
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hc : ∀ a' ∈ G', ∀ b' ∈ G', a' * b' = b' * a' := by
      intro a' ha' b' hb'
      rcases hcomm a' ha' b' hb' with h | h
      · rw [← mul_inv_cancel_left (b' * a') (a' * b'), h, mul_one]
      · exfalso
        apply hxG
        rw [← h]
        exact G'.mul_mem (G'.inv_mem (G'.mul_mem hb' ha')) (G'.mul_mem ha' hb')
    obtain ⟨a', ha', ha⟩ := hrep a
    obtain ⟨b', hb', hb⟩ := hrep b
    have hab' := hc a' ha' b' hb'
    have hxa := hxc a'
    have hxb := hxc b'
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · exact hab'
    · calc a' * (b' * x) = (a' * b') * x := (mul_assoc _ _ _).symm
        _ = (b' * a') * x := by rw [hab']
        _ = b' * (a' * x) := mul_assoc _ _ _
        _ = b' * (x * a') := by rw [hxa]
        _ = (b' * x) * a' := (mul_assoc _ _ _).symm
    · calc (a' * x) * b' = a' * (x * b') := mul_assoc _ _ _
        _ = a' * (b' * x) := by rw [hxb]
        _ = (a' * b') * x := (mul_assoc _ _ _).symm
        _ = (b' * a') * x := by rw [hab']
        _ = b' * (a' * x) := mul_assoc _ _ _
    · calc (a' * x) * (b' * x) = a' * ((x * b') * x) := by simp only [mul_assoc]
        _ = a' * ((b' * x) * x) := by rw [hxb]
        _ = (a' * b') * (x * x) := by simp only [mul_assoc]
        _ = (b' * a') * (x * x) := by rw [hab']
        _ = b' * ((a' * x) * x) := by simp only [mul_assoc]
        _ = b' * ((x * a') * x) := by rw [hxa]
        _ = (b' * x) * (a' * x) := by simp only [mul_assoc]
  rw [eq_top_iff]
  intro e _
  obtain ⟨e', he', h⟩ := hrep e
  rcases h with h | h
  · rw [h]
    exact he'
  · rw [h]
    exact G'.mul_mem he' hxG

end Generation

theorem Ebar_nonabelian : ∃ a b : Ebar, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Ebar = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [Subgroup.mem_center_iff]
    intro b
    exact h b a
  have h2 : Nat.card (Subgroup.center Ebar) = 2 ^ 23 := by
    rw [hc, Subgroup.card_top]
    exact Ebar_extraspecial.2
  rw [center_Ebar, Nat.card_zpowers, orderOf_xbarE] at h2
  norm_num at h2

theorem xbarE_comm (e : Ebar) : e * ⟨xbar, xbar_mem_Ebar⟩ = ⟨xbar, xbar_mem_Ebar⟩ * e := by
  have hx : (⟨xbar, xbar_mem_Ebar⟩ : Ebar) ∈ Subgroup.center Ebar := by
    rw [center_Ebar]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_center_iff.1 hx e

theorem alphaWord_mem_closure (w : List ℤ) :
    Co2.alphaWord w ∈ Subgroup.closure (Set.range Co2.alpha) := by
  have hN : ∀ j, Co2.alphaN j ∈ Subgroup.closure (Set.range Co2.alpha) := by
    intro j
    unfold Co2.alphaN
    split_ifs with h
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · exact Subgroup.one_mem _
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    rw [Co2.alphaWord]
    refine Subgroup.mul_mem _ ?_ ih
    split_ifs
    · exact hN _
    · exact Subgroup.inv_mem _ (hN _)

theorem closure_insert_taubar_Jbar : Subgroup.closure (insert taubar (Jbar : Set Cbar)) = ⊤ := by
  set H := Subgroup.closure (insert taubar (Jbar : Set Cbar)) with hH
  have hle : Cgen ≤ (H.comap kappa).map Cgen.subtype := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro f hf
    rcases hf with rfl | hf
    · exact ⟨tauC, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
    · refine ⟨⟨f, Jstar_le_Cgen hf⟩, Subgroup.subset_closure (Set.mem_insert_of_mem _ ?_), rfl⟩
      exact ⟨⟨f, Jstar_le_Cgen hf⟩, hf, rfl⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨g, rfl⟩ := kappa_surjective y
  obtain ⟨g', hg', hgg'⟩ := hle g.2
  have h : g' = g := Subtype.ext hgg'
  rw [← h]
  exact hg'

theorem closure_insert_taubar_eq_top {G : Subgroup Cbar} (hG : Jbar ≤ G) :
    Subgroup.closure (insert taubar (G : Set Cbar)) = ⊤ := by
  rw [eq_top_iff, ← closure_insert_taubar_Jbar]
  exact Subgroup.closure_mono (Set.insert_subset_insert hG)

end CFSG.Monster.B
