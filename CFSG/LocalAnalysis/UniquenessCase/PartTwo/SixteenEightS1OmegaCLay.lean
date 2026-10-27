module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveEquiv
public import CFSG.Quasithin.Background.C124YLA6Grp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16e_omc_equiv_alt_five_of_isOmegaPlus {X : Type} [Group X] (h : IsOmegaPlus X 4 2) :
    Nonempty (X ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  obtain ⟨K, _, _, _, hcard, ⟨e⟩⟩ := s16c13bcA_omegaPlus_equiv h
  obtain ⟨eA⟩ := CFSG.Quasithin.C124.YL.A6.sl2_equiv_alt_five (F := K) hcard
  exact ⟨e.trans (MulEquiv.prodCongr eA eA)⟩

theorem s16e_omc_le_layer_of_equiv_prod {H : Type} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] {S : Type} [Group S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (e : ↥N ≃* S × S) : N ≤ CFSG.layer H := by
  let p2 : (Fin 2 → S) ≃* S × S :=
    { piFinTwoEquiv (fun _ : Fin 2 => S) with map_mul' := fun _ _ => rfl }
  have hN : CFSG.layer ↥N = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Fin 2) (S := fun _ => S)
      (fun _ => hnab) (e.trans p2.symm)
  have h2 := CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.map_layer_le_layer_of_normal (W := N)
  rw [hN, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

private theorem s16e_omc_alt_five_nonabelian :
    ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  by_contra h
  have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := fun a b =>
    by_contra fun hne => h ⟨a, b, hne⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  have hc : x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcomm g x
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  exact hx hc

theorem s16e_omc_le_layer_of_equiv_alt_five {H : Type} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] (e : ↥N ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    N ≤ CFSG.layer H := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  exact s16e_omc_le_layer_of_equiv_prod s16e_omc_alt_five_nonabelian e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
