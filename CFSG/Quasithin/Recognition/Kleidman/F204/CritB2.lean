module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Main
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPUd

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem zData_omega (F : Frame L1 L2 S D X) : ZData L1 L2 S (quasithinOmegaOneCenter S) where
  le_S := omegaOneCenter_le_self S
  central := fun z hz s hs => by
    have hle : quasithinOmegaOneCenter S ≤ S ⊓ Subgroup.centralizer (S : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hx => hx.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hz).2 s hs).symm
  sq := fun z hz => by
    have := (isElemAbelian_omegaOneCenter' S).2 z hz
    rwa [pow_two] at this
  norm := fun b hb z hz => by
    have hbS : b ∈ Subgroup.normalizer (S : Set G) := F.B_le_normalizer_S hb
    have e : conjSub b (quasithinOmegaOneCenter S) = quasithinOmegaOneCenter S := by
      rw [conjSub_omegaOneCenter, F7.conjSub_eq_of_mem_normalizer hbS]
    have : b * z * b⁻¹ ∈ conjSub b (quasithinOmegaOneCenter S) := by
      rw [mem_conjSub]; simpa [mul_assoc] using hz
    rwa [e] at this

theorem Zv_γ₀_eq (F : Frame L1 L2 S D X) :
    Zv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) =
      Frame.Z1 L1 L2 S (quasithinOmegaOneCenter S) := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have hT : IsSylowTwoOf S (stab (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))) := by
    rw [stab_γ₀ h₁]; exact F.sylow_P1
  rw [Zv_eq_conjClosure hT, stab_γ₀ h₁]

theorem Zv_γ₁_eq (F : Frame L1 L2 S D X) :
    Zv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) =
      Frame.Z2 L1 L2 S (quasithinOmegaOneCenter S) := by
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hT : IsSylowTwoOf S (stab (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))) := by
    rw [stab_γ₁ h₂]; exact F.sylow_P2
  rw [Zv_eq_conjClosure hT, stab_γ₁ h₂]

theorem Zv_le_Qv_of_mem_nbrs (F : Frame L1 L2 S D X) {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : μ ∈ nbrs δ) : Zv δ ≤ Qv μ := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj δ μ from hμ)
  · rw [← hg0, ← hg1, Zv_smul, Qv_smul, Zv_γ₀_eq F, hQ1]
    exact conjSub_mono _ (F.Z1_le_Q2 (zData_omega F))
  · rw [← hg0, ← hg1, Zv_smul, Qv_smul, Zv_γ₁_eq F, hQ0]
    exact conjSub_mono _ (Z2_le_Q1 F (zData_omega F))

theorem two_le_bAt (F : Frame L1 L2 S D X) (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) : 2 ≤ bAt δ := by
  have hA := Amal.of_frame F
  have h1 := hA.bAt_pos δ
  by_contra h
  have hb : bAt δ = 1 := by omega
  obtain ⟨μ, hd, hn⟩ := hA.bAt_spec δ
  rw [hb] at hd
  exact hn (Zv_le_Qv_of_mem_nbrs F (show μ ∈ nbrs δ from dist_eq_one_iff_adj.mp hd))

theorem two_le_bMin (F : Frame L1 L2 S D X) : 2 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S) := by
  obtain ⟨δ, hδ⟩ := (Amal.of_frame F).exists_bAt_eq_bMin
  rw [← hδ]; exact two_le_bAt F δ

end CFSG.Quasithin.Kleidman.F204
