module

public import CFSG.LocalAnalysis.SteinbergCCHSChecks
public import CFSG.Sporadic.HS
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.HigmanSimsCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.TwoGen
open CFSG.Sporadic.Th
open CFSG.Sporadic.HS.Native (hsData)

theorem lift_lift_mk {m k : ℕ} {G : Type*} [Group G] (f : Fin m → G)
    (hs : List (List (Fin m × Bool))) (r : List (Fin k × Bool)) :
    FreeGroup.lift (fun i : Fin k => FreeGroup.lift f (FreeGroup.mk (hs.getD i [])))
      (FreeGroup.mk r) = FreeGroup.lift f (FreeGroup.mk (substWord hs r)) := by
  induction r with
  | nil => simp [substWord]
  | cons l r ih =>
    obtain ⟨i, s⟩ := l
    rw [show FreeGroup.mk ((i, s) :: r) = FreeGroup.mk [(i, s)] * FreeGroup.mk r from
      by rw [FreeGroup.mul_mk]; rfl, map_mul, ih]
    simp only [substWord, List.flatMap_cons]
    rw [← FreeGroup.mul_mk, map_mul]
    congr 1
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← FreeGroup.inv_mk, map_inv, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl,
        map_inv, FreeGroup.lift_apply_of]
    · simp only [↓reduceIte]
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]

theorem baseFacts : BaseFacts hsData := CFSG.Sporadic.HS.hsFacts.toBaseFacts

noncomputable def genAB : Fin 2 → J hsData := fun i => img2 (a hsData) (b hsData) i.val

noncomputable def genXYT : Fin 3 → J hsData :=
  fun i => FreeGroup.lift genAB (FreeGroup.mk (genWords.getD i []))

theorem lift_genXYT (r : List (Fin 3 × Bool)) :
    FreeGroup.lift genXYT (FreeGroup.mk r) = FreeGroup.lift genAB (FreeGroup.mk (substAB r)) :=
  lift_lift_mk genAB genWords r

theorem hsWords_eval
    : ∀ w ∈ hsWords, FreeGroup.lift genAB (FreeGroup.mk w) = 1 := by
  have := faithful baseFacts
  have hA := rep_a baseFacts
  have hB := rep_b baseFacts
  have h := wordProd_eq_one_of_relCheck (n_lt_two_pow CFSG.Sporadic.HS.hsFacts) hA
    (Rep.inv_of_invOK hA baseFacts.invA) hB (Rep.inv_of_invOK hB baseFacts.invB) hs_check
  intro w hw
  show FreeGroup.lift (fun i : Fin 2 => img2 (a hsData) (b hsData) i.val) (FreeGroup.mk w) = 1
  rw [lift_mk_eq_wordProd]
  exact h _ (List.mem_map_of_mem hw)

theorem rels_eval
    : ∀ r ∈ rels, FreeGroup.lift genXYT (FreeGroup.mk r) = 1 := by
  intro r hr
  rw [lift_genXYT]
  exact hsWords_eval _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr)))

theorem pairs_eval (i : Fin 3) :
    FreeGroup.lift genXYT (FreeGroup.mk (commWords (pairs i))) = genXYT i := by
  have h := hsWords_eval (substAB (commWords (pairs i) ++ [(i, false)]))
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem (List.mem_finRange i))))
  rw [← lift_genXYT, ← FreeGroup.mul_mk, map_mul,
    show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
    FreeGroup.lift_apply_of, mul_inv_eq_one] at h
  exact h

theorem abWords_eval :
    FreeGroup.lift genXYT (FreeGroup.mk (abWords.getD 0 [])) = a hsData ∧
      FreeGroup.lift genXYT (FreeGroup.mk (abWords.getD 1 [])) = b hsData := by
  have key : ∀ j : Fin 2, substAB (abWords.getD j []) ++ [(j, false)] ∈ hsWords →
      FreeGroup.lift genXYT (FreeGroup.mk (abWords.getD j [])) = genAB j := by
    intro j hj
    have h := hsWords_eval _ hj
    rw [← FreeGroup.mul_mk, map_mul, show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl,
      map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] at h
    rw [lift_genXYT]
    exact h
  refine ⟨key 0 (List.mem_append_right _ (by simp)), key 1 (List.mem_append_right _ (by simp))⟩

theorem closure_genXYT
    : Subgroup.closure (Set.range genXYT) = ⊤ := by
  rw [eq_top_iff, ← closure_ab hsData, Subgroup.closure_le, ← FreeGroup.range_lift_eq_closure]
  rintro _ (rfl | rfl)
  · exact ⟨_, abWords_eval.1⟩
  · exact ⟨_, abWords_eval.2⟩

theorem card_presented_le
    : Finite (PG 3 rels) ∧ Nat.card (PG 3 rels) ≤ 44352000 :=
  presented_bound

noncomputable def hsEquivJ : CFSG.Blueprint.NativeSporadic.HS ≃* J hsData := seedEquiv baseFacts

theorem card_J : Nat.card (J hsData) = 44352000 := by
  rw [← Nat.card_congr hsEquivJ.toEquiv, CFSG.Sporadic.HS.card_HS]

theorem isPresentation_J
    : IsPresentation genXYT (wordSet rels) := by
  have := card_presented_le.1
  refine IsPresentation.of_card_le ?_ closure_genXYT ?_
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact rels_eval v hv
  · rw [card_J]
    exact card_presented_le.2

noncomputable def genHS : Fin 3 → CFSG.Blueprint.NativeSporadic.HS :=
  fun i => hsEquivJ.symm (genXYT i)

theorem lift_genHS (w : FreeGroup (Fin 3)) :
    FreeGroup.lift genHS w = hsEquivJ.symm (FreeGroup.lift genXYT w) := by
  rw [show genHS = fun j => hsEquivJ.symm (genXYT j) from rfl, lift_mulEquiv]

theorem isPresentation_HS : IsPresentation genHS (wordSet rels) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := isPresentation_J.lift_surjective (hsEquivJ h)
    exact ⟨w, by rw [lift_genHS, hw, MulEquiv.symm_apply_apply]⟩
  · ext w
    rw [MonoidHom.mem_ker, lift_genHS, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
      isPresentation_J.ker_lift]

theorem pairs_eval_HS (i : Fin 3) :
    FreeGroup.lift genHS (FreeGroup.mk (commWords (pairs i))) = genHS i := by
  rw [lift_genHS, pairs_eval]
  rfl

end CFSG.LocalAnalysis.HigmanSimsCover
