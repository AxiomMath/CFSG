module

public import CFSG.Quasithin.MS93.S4AVtx
import CFSG.Quasithin.MS93.S33Trans

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem stab_eq_ltil_sup_qv_gen {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) : stab _ δ = Ltil h.le L δ ⊔ Qv _ ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _) (adj_baseA_baseB _)
    hδ hδρ
  rw [PU.stab_smul, Ltil, puTrans_smul h.le (S4A.L_normal h), PU.qv_smul, ← Subgroup.map_sup,
    puAmalgam.stab_baseA, puTrans_baseA h.le (S4A.L_normal h), puAmalgam.qv_baseB,
    ← S33.imM_sup h.le h.L_le h.le, ← h.eq_sup]

theorem le_qv_of_commutator_le_gen {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {R : Subgroup (puAmalgam h.le).Universal}
    (hR : R ≤ Qv _ ρ) (hRL : ⁅R, Ltil h.le L δ⁆ ≤ Qv _ δ) : R ≤ Qv _ δ := by
  have hQδρ : Qv (puAmalgam h.le) δ ≤ Qv _ ρ := qv_le_qv _ h.hyp20 hδ hδρ
  have hρs : Qv (puAmalgam h.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hδρ.symm
  have hQn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Qv _ δ : Set _) :=
    stab_le_normalizer_qv _ δ
  set W := conjCl (Qv (puAmalgam h.le) ρ) R ⊔ Qv _ δ with hW
  have hCl : conjCl (Qv (puAmalgam h.le) ρ) R ≤ Qv _ ρ := conjCl_le_of_le hR
  have hTW : Qv (puAmalgam h.le) ρ ≤ Subgroup.normalizer (W : Set _) :=
    (le_inf (le_normalizer_conjCl _ _) (hρs.trans hQn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hLW : Ltil h.le L δ ≤ Subgroup.normalizer (W : Set _) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of ?_ ?_ (le_sup_left.trans Subgroup.le_normalizer)
      (le_sup_right.trans Subgroup.le_normalizer)
    · exact (commutator_conjCl_le (hρs.trans hQn)
        (hρs.trans (stab_le_normalizer_ltil h δ)) ((hR.trans hρs).trans hQn) hRL).trans
          le_sup_right
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h δ).trans hQn)).trans le_sup_right
  have hsW : stab _ δ ≤ Subgroup.normalizer (W : Set _) := by
    rw [stab_eq_ltil_sup_qv_gen h hδ hδρ]
    exact sup_le hLW hTW
  exact (le_conjCl _ _).trans (le_sup_left.trans
    (le_qv_of_normalizer _ h.hyp20 hδ hδρ (sup_le hCl hQδρ) hsW))

theorem ltil_le_of_normal_gen {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {C K : Subgroup (puAmalgam h.le).Universal}
    (hCs : C ≤ stab _ δ) (hCn : stab _ δ ≤ Subgroup.normalizer (C : Set _)) (hKC : K ≤ C)
    (hKρ : K ≤ Qv _ ρ) (hKQ : ¬ K ≤ Qv _ δ) : Ltil h.le L δ ≤ C := by
  have hLs := ltil_le_stab h δ
  have hLn := stab_le_normalizer_ltil h δ
  set C' := C ⊓ Ltil h.le L δ with hC'
  have hC'n : Ltil h.le L δ ≤ Subgroup.normalizer (C' : Set _) :=
    (le_inf (hLs.trans hCn) Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  rcases commutator_ltil_le_or h hδ (K := C') inf_le_right hC'n with hO | hle
  · exfalso
    apply hKQ
    have hCL : ⁅C, Ltil h.le L δ⁆ ≤ C' := le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hCn))
      (by rw [Subgroup.commutator_comm]
          exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hCs.trans hLn))
    have hQn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Qv _ δ : Set _) :=
      stab_le_normalizer_qv _ δ
    have h2 : ⁅⁅C, Ltil h.le L δ⁆, Ltil h.le L δ⁆ ≤ Qv _ δ :=
      ((Subgroup.commutator_mono hCL le_rfl).trans hO).trans (pCoreLtil_le_qv h hδ)
    have h3 : ⁅C, Ltil h.le L δ⁆ ≤ Qv _ δ := by
      have h4 := three_subgroups_le (N := Qv (puAmalgam h.le) δ) (H₁ := Ltil h.le L δ)
        (H₂ := Ltil h.le L δ) (H₃ := C) (hLs.trans hQn) (hLs.trans hQn) (hCs.trans hQn)
        (by rw [Subgroup.commutator_comm (Ltil h.le L δ) C]; exact h2) h2
      rw [ltil_perfect h hδ, Subgroup.commutator_comm] at h4
      exact h4
    exact le_qv_of_commutator_le_gen h hδ hδρ hKρ
      ((Subgroup.commutator_mono hKC le_rfl).trans h3)
  · exact hle.trans inf_le_left

theorem commutator_ltil_le_of_commutator_le_gen {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {A B K : Subgroup (puAmalgam h.le).Universal}
    (hA : stab _ δ ≤ Subgroup.normalizer (A : Set _))
    (hB : stab _ δ ≤ Subgroup.normalizer (B : Set _)) (hAK : ⁅A, K⁆ ≤ B)
    (hKρ : K ≤ Qv _ ρ) (hKQ : ¬ K ≤ Qv _ δ) : ⁅A, Ltil h.le L δ⁆ ≤ B := by
  have hKs : K ≤ stab (puAmalgam h.le) δ := hKρ.trans (qv_le_stab_of_adj _ hδρ.symm)
  let C : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {g | g ∈ stab (puAmalgam h.le) δ ∧ ∀ a ∈ A, ⁅a, g⁆ ∈ B}
      mul_mem' := by
        rintro g k ⟨hg, hgA⟩ ⟨hk, hkA⟩
        refine ⟨Subgroup.mul_mem _ hg hk, fun a ha => ?_⟩
        have e : ⁅a, g * k⁆ = ⁅a, g⁆ * (g * ⁅a, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem (hgA a ha) ((Subgroup.mem_normalizer_iff.mp (hB hg) _).mp (hkA a ha))
      one_mem' := ⟨Subgroup.one_mem _, fun a _ => by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro g ⟨hg, hgA⟩
        refine ⟨Subgroup.inv_mem _ hg, fun a ha => ?_⟩
        have e : ⁅a, g⁻¹⁆ = g⁻¹ * (⁅a, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hB (Subgroup.inv_mem _ hg)) _).mp
          (B.inv_mem (hgA a ha)) }
  have hCs : C ≤ stab (puAmalgam h.le) δ := fun g hg => hg.1
  have hCn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (C : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ y ∈ stab (puAmalgam h.le) δ, ∀ g ∈ C, y * g * y⁻¹ ∈ C := by
      rintro y hy g ⟨hg, hgA⟩
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hg) (Subgroup.inv_mem _ hy),
        fun a ha => ?_⟩
      have ha' : y⁻¹ * a * y⁻¹⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hA (Subgroup.inv_mem _ hy)) a).mp ha
      have e : ⁅a, y * g * y⁻¹⁆ = y * ⁅y⁻¹ * a * y⁻¹⁻¹, g⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hB hy) _).mp (hgA _ ha')
    constructor
    · exact key x hx g
    · intro hg
      have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hg
      simpa [mul_assoc] using this
  have hKC : K ≤ C := fun k hk =>
    ⟨hKs hk, fun a ha => hAK (Subgroup.commutator_mem_commutator ha hk)⟩
  have hLC := ltil_le_of_normal_gen h hδ hδρ hCs hCn hKC hKρ hKQ
  rw [Subgroup.commutator_le]
  intro a ha l hl
  exact (hLC hl).2 a ha

end CFSG.Quasithin.MS93.S34F
