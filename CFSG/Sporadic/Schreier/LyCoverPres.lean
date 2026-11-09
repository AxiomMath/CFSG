module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm
public import CFSG.Sporadic.Schreier.LyChain11
import CFSG.HardMathSupport.RichardWeiss.Proving.CarmichaelLift

public section

namespace CFSG.Sporadic.LySchreier

open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.RichardWeiss.Proving

theorem exists_quotient_equiv_of_carmichael {C : Type*} [Group C] (c : Fin 2 → C)
    (hc : Subgroup.closure (Set.range c) = ⊤) (N : Subgroup C) [N.Normal]
    (p : Fin 2 → alternatingGroup (Fin 11)) (t : Fin 9 → FreeGroup (Fin 2))
    (u : Fin 2 → FreeGroup (Fin 9))
    (h3 : ∀ i, (FreeGroup.lift c (t i) : C ⧸ N) ^ 3 = 1)
    (h2 : ∀ i j, i ≠ j →
      ((FreeGroup.lift c (t i) : C ⧸ N) * (FreeGroup.lift c (t j) : C ⧸ N)) ^ 2 = 1)
    (hu : ∀ k, FreeGroup.lift altThreeCycle (u k) = p k)
    (huc : ∀ k, FreeGroup.lift (fun i => (FreeGroup.lift c (t i) : C ⧸ N)) (u k) = (c k : C ⧸ N))
    (hc0 : c 0 ∉ N) :
    ∃ e : C ⧸ N ≃* alternatingGroup (Fin 11), ∀ k, e (c k : C ⧸ N) = p k := by
  obtain ⟨φ, hφ⟩ := exists_hom_altThreeCycle_eq 9 _ h3 h2
  have hφp : ∀ k, φ (p k) = (c k : C ⧸ N) := by
    intro k
    rw [← hu k, ← MonoidHom.comp_apply]
    have : φ.comp (FreeGroup.lift altThreeCycle) =
        FreeGroup.lift fun i => (FreeGroup.lift c (t i) : C ⧸ N) :=
      FreeGroup.ext_hom _ _ fun i => by simp [hφ]
    rw [this, huc k]
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hgen : Subgroup.closure (Set.range fun k => (c k : C ⧸ N)) = ⊤ := by
      have := MonoidHom.map_closure (QuotientGroup.mk' N) (Set.range c)
      rw [hc, ← Set.range_comp, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N)] at this
      exact this.symm
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨p k, hφp k⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 11)) := alternatingGroup.isSimpleGroup (by simp)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have : p 0 ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφp 0, QuotientGroup.eq_one_iff] at this
      exact hc0 this
  refine ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun k => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact (hφp k).symm

theorem evalWord_carWords : ∀ i : Fin 9, evalWord pPerm (carWords i) = altThreeCyclePerm i := by
  decide +kernel

theorem prod_carGenWords : ∀ k : Fin 2, ((carGenWords k).map altThreeCyclePerm).prod = pGen k := by
  decide +kernel

theorem carWords_idx : ∀ i : Fin 9, ∀ l ∈ carWords i, letterIdx l < 12 := by
  decide +kernel

@[expose] def carT (i : Fin 9) : FreeGroup (Fin 2) := evalWord strongF (carWords i)

@[expose] def carU (k : Fin 2) : FreeGroup (Fin 9) := ((carGenWords k).map FreeGroup.of).prod

theorem lift_carT (i : Fin 9) : FreeGroup.lift pGen (carT i) = altThreeCyclePerm i := by
  rw [carT, map_evalWord, ← evalWord_carWords i]
  exact evalWord_congr fun l hl => lift_strongF (carWords_idx i l hl)

theorem lift_carU {Q : Type*} [Group Q] (f : Fin 9 → Q) (k : Fin 2) :
    FreeGroup.lift f (carU k) = ((carGenWords k).map f).prod := by
  simp [carU, map_list_prod, List.map_map, Function.comp_def]

theorem coe_lift_carU (k : Fin 2) :
    ((FreeGroup.lift altThreeCycle (carU k) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) =
      pGen k := by
  rw [lift_carU, ← Subgroup.coe_subtype, map_list_prod, List.map_map, ← prod_carGenWords k]
  rfl

end CFSG.Sporadic.LySchreier
