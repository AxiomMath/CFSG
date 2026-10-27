module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentGrp
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotNormal

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem permHom_apply_eq_self_of_mem_dentQ {S0 : Finset (Fin 8)} {x : S.H}
    (hx : (x : X) ∈ S.dentQ S0) {i : Fin 8} (hi : i ∉ S0) : S.permHom x i = i := by
  apply S.permHom_apply_eq_self_of_mulVec_single x
  have hv : VanishesOn S0 (Pi.single i 1) := by
    intro j hj
    exact Pi.single_eq_of_ne (i := i) (i' := j) (fun hji => hi (hji ▸ hj)) 1
  exact (S.mem_dentQ_iff).1 hx _ hv

theorem exists_mem_dentQ_permHom_eq {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0)
    {σ : Equiv.Perm (Fin 8)} (hσ : ∀ i, i ∉ S0 → σ i = i) :
    ∃ x : S.H, (x : X) ∈ S.dentQ S0 ∧ S.permHom x = σ := by
  have hσ0 : σ 0 = 0 := hσ 0 h0
  obtain ⟨y, hyperm, hyρ⟩ := S.exists_permHom_eq hσ0
  refine ⟨y, ?_, hyperm⟩
  rw [S.mem_dentQ_iff]
  intro v hv
  rw [hyρ, spMat_mulVec]
  funext i
  simp only [one_mul]
  by_cases hi : i ∈ S0
  · have hsymm : σ.symm i ∈ S0 := by
      by_contra hc
      have hfix := hσ (σ.symm i) hc
      rw [Equiv.apply_symm_apply] at hfix
      exact hc (hfix ▸ hi)
    rw [hv (σ.symm i) hsymm, hv i hi]
  · have hs : σ.symm i = i := by rw [Equiv.symm_apply_eq, hσ i hi]
    rw [hs]

theorem exists_mem_dentF2_eq_sgn_pair {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0)
    {i j : Fin 8} (hi : i ∈ S0) (hj : j ∈ S0) (hij : i ≠ j) :
    ∃ f ∈ S.dentF2 S0, S.ρ f = sgn {i, j} := by
  have h0' : (0 : Fin 8) ∉ ({i, j} : Finset (Fin 8)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h0 (h ▸ hi), fun h => h0 (h ▸ hj)⟩
  have hcard : ({i, j} : Finset (Fin 8)).card = 2 := Finset.card_pair hij
  have heven : Even ({i, j} : Finset (Fin 8)).card := by
    rw [hcard]; exact even_two
  have hmem : sgn ({i, j} : Finset (Fin 8)) ∈ F1set := ⟨{i, j}, h0', heven, rfl⟩
  obtain ⟨f, hfF1, hfρ⟩ := S.exists_mem_F1_of_mem_F1set hmem
  refine ⟨f, ?_, hfρ⟩
  change f ∈ S.F1 ⊓ S.dentQ S0
  refine ⟨hfF1, ?_⟩
  show f ∈ S.dentQ S0
  rw [S.mem_dentQ_iff]
  intro v hv
  rw [hfρ, q2nN7_sgn_mulVec]
  funext l
  by_cases hl : l ∈ ({i, j} : Finset (Fin 8))
  · have hlS0 : l ∈ S0 := by
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h]; exact hi
      · rw [Finset.mem_singleton.mp h]; exact hj
    rw [if_pos hl, hv l hlS0]
    exact neg_zero
  · rw [if_neg hl]

theorem mem_F1_of_comm_dentF2 {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0) (hc : S0.card = 6)
    {x : X} (hx : x ∈ S.H) (hcomm : ∀ f ∈ S.dentF2 S0, x * f = f * x) : x ∈ S.F1 := by
  let y : S.H := ⟨x, hx⟩
  have hfix : ∀ i ∈ S0, S.permHom y i = i :=
    perm_apply_eq_self_of_preserves_pairs (σ := S.permHom y) (T := S0)
      (by rw [hc]; norm_num)
      (fun i hi j hj hij l => by
        obtain ⟨f, hf, hfρ⟩ := S.exists_mem_dentF2_eq_sgn_pair h0 hi hj hij
        have hcommρ : S.ρ y * sgn {i, j} = sgn {i, j} * S.ρ y := by
          have h := congrArg S.ρ (hcomm f hf)
          rw [map_mul, map_mul, hfρ] at h
          simpa only using h
        have hmem := S.permHom_mem_iff_of_comm_sgn y hcommρ l
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem)
  have hperm : S.permHom y = 1 := by
    apply perm_fin_eight_eq_one_of_fixes_card_seven (σ := S.permHom y) (T := insert 0 S0)
    · rw [Finset.card_insert_of_notMem h0, hc]
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hiS0
      · exact S.permHom_zero y
      · exact hfix i hiS0
  have hyx : (y : X) = x := rfl
  rw [← hyx]
  exact (S.permHom_eq_one_iff_mem_F1 y).1 hperm

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
