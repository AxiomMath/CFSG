module

public import CFSG.LocalAnalysis.StandardType.GGP3LineGlue
public import CFSG.LocalAnalysis.StandardType.GGP3WitnessE
public import CFSG.LocalAnalysis.StandardType.GGP3WitnessD
public import CFSG.LocalAnalysis.StandardType.GGForkExtDatum
public import CFSG.LocalAnalysis.StandardType.GGForkRestTrichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggInvTest3_of_indefCellZero {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b c : Λ} (hF : GGForkMatrix C b c) (h : GGIndefCellZero C b) (h5 : 5 ≤ Fintype.card Λ) :
    GGInvTest3 (ggAttachCartan C c) := by
  unfold GGIndefCellZero at h
  rcases h with ⟨n, hn, e, hC, hb⟩ | ⟨e, hC, _⟩ | ⟨e, hC, _⟩ | ⟨e, hC, _⟩ |
    ⟨e, hC, _⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hc : c = e ⟨m + 2, by omega⟩ := by
      rcases ggLeafPos_D m (hF.leafPos e hC) with ⟨hi, _⟩ | ⟨_, hk⟩
      · exfalso
        rcases hb with hb | hb
        · have hv : (e.symm b).val = m + 3 := by
            rw [hb, Equiv.symm_apply_apply]
            dsimp only
            omega
          omega
        · have hv : (e.symm b).val = m + 4 := by
            rw [hb, Equiv.symm_apply_apply]
            dsimp only
            omega
          omega
      · have hk' : e.symm c = (⟨m + 2, by omega⟩ : Fin (m + 5)) := Fin.ext hk
        rw [← hk', e.apply_symm_apply]
    exact ggInvTest3_D_cell (by omega) e hC (by simpa using hc)
  · rcases ggLeafPos_E6 (hF.leafPos e hC) with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
    · exact ggInvTest3_E6_cell e hC (Or.inl (by rw [← hk, e.apply_symm_apply]))
    · exact ggInvTest3_E6_cell e hC (Or.inr (Or.inl (by rw [← hk, e.apply_symm_apply])))
    · exact ggInvTest3_E6_cell e hC (Or.inr (Or.inr (by rw [← hk, e.apply_symm_apply])))
  · rcases ggLeafPos_E7 (hF.leafPos e hC) with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
    · exact ggInvTest3_E7_cell e hC (Or.inl (by rw [← hk, e.apply_symm_apply]))
    · exact ggInvTest3_E7_cell e hC (Or.inr (Or.inl (by rw [← hk, e.apply_symm_apply])))
    · exact ggInvTest3_E7_cell e hC (Or.inr (Or.inr (by rw [← hk, e.apply_symm_apply])))
  · rcases ggLeafPos_E8 (hF.leafPos e hC) with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
    · exact ggInvTest3_E8_cell e hC (Or.inl (by rw [← hk, e.apply_symm_apply]))
    · exact ggInvTest3_E8_cell e hC (Or.inr (Or.inl (by rw [← hk, e.apply_symm_apply])))
    · exact ggInvTest3_E8_cell e hC (Or.inr (Or.inr (by rw [← hk, e.apply_symm_apply])))
  · exfalso
    have hcard : Fintype.card Λ = 4 := by
      rw [← Fintype.card_congr e]
      simp
    omega

theorem ggInvTest3_of_indefCellOne {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (h : GGIndefCellOne C b) : GGInvTest3 (ggAttachCartan C b) := by
  unfold GGIndefCellOne at h
  rcases h with ⟨n, hn, e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩
  · exact ggInvTest3_D_cell_one hn e hC hb
  · exact ggInvTest3_E7_cell_one e hC hb
  · exact ggInvTest3_E8_cell_one e hC hb

theorem ggFork_false_of_indefCell_three (ha₀ : GGLNoncyclicInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNT : GGNoTransvection p Bs)
    {K : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} {b c : Λ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hAK : ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}))
    (h5 : 5 ≤ Fintype.card Λ)
    (hcell : (αa (h b) = 0 ∧ GGIndefCellZero C b) ∨ (αa (h b) = 1 ∧ GGIndefCellOne C b)) :
    False := by
  have hu : αa (h b) = 0 ∨ αa (h b) = 1 := by
    rcases hcell with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact Or.inl h0
    · exact Or.inr h1
  have hp2 : p ≠ 2 := by omega
  have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := by
    intro i
    have h1 : φ i ∈ ggAutomizer L Bs := by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact mem_ggAutomizer_iff.mp (ggAutomizer_mono Bs (le_top : L ≤ ⊤) h1)
  have hφa : φa ∈ ggInduced ⊤ Bs := by
    have h1 : φa ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Or.inr rfl)
    exact mem_ggAutomizer_iff.mp (ggAutomizer_mono Bs (le_top : K ≤ ⊤) h1)
  obtain ⟨X, φ', h', α', hD, hX0, hX1, hsame, _⟩ :=
    ggForkExtDatum hp2 hNT ι hF hφ hφa hlin hlina hind hu
  have hAL' : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)) := by
    have hφeq : (fun i : Λ => φ' (some i)) = φ := funext fun i => (hsame i).1
    rw [hAL, hφeq]
  rcases hu with hu0 | hu1
  · have hcell0 : GGIndefCellZero C b := by
      rcases hcell with ⟨_, hz⟩ | ⟨h1, _⟩
      · exact hz
      · exact absurd (hu0.symm.trans h1) zero_ne_one
    have hT : GGInvTest3 X := by
      rw [hX0 hu0]
      exact ggInvTest3_of_indefCellZero hF.toMatrix hcell0 h5
    have hC' : GGIntCartan M fun i j => X (some i) (some j) := by
      rw [hX0 hu0]
      simpa only [ggAttachCartan_some_some] using hC
    exact ggFork_false_of_invTest_three ha₀ hp3 hcfg hD hM hC' hAL' hT
  · have hcell1 : GGIndefCellOne C b := by
      rcases hcell with ⟨h0, _⟩ | ⟨_, hz⟩
      · exact absurd (hu1.symm.trans h0) one_ne_zero
      · exact hz
    have hT : GGInvTest3 X := by
      rw [hX1 hu1]
      exact ggInvTest3_of_indefCellOne hcell1
    have hC' : GGIntCartan M fun i j => X (some i) (some j) := by
      rw [hX1 hu1]
      simpa only [ggAttachCartan_some_some] using hC
    exact ggFork_false_of_invTest_three ha₀ hp3 hcfg hD hM hC' hAL' hT

end CFSG.StandardType
