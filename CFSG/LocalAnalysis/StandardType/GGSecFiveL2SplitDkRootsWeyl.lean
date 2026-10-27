module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic
public import CFSG.LieType.RootSystem.Positivity
public import CFSG.Timmesfeld.ARS.CaseOAWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem weylAction_simpleD {k : ℕ} (i : Fin k) :
    weylAction (isFiniteType_cartanD k) ((coxeterMatrix (isFiniteType_cartanD k)).simple i) =
      reflection (cartanD k) i := by
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
    weylAction_simple (isFiniteType_cartanD k) i

private theorem weylAction_simpleD_single {k : ℕ} (i : Fin k) :
    weylAction (isFiniteType_cartanD k) ((coxeterMatrix (isFiniteType_cartanD k)).simple i)
      (Pi.single i 1) = -Pi.single i 1 := by
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
    weylAction_simple_single (isFiniteType_cartanD k) i

theorem ggDDot_toStdD_weylAction {k : ℕ} (hk : 2 ≤ k) (w : ggWeylD k) (u v : Fin k → ℤ) :
    ggDDot (toStdD k (weylAction (isFiniteType_cartanD k) w u))
        (toStdD k (weylAction (isFiniteType_cartanD k) w v)) =
      ggDDot (toStdD k u) (toStdD k v) := by
  obtain ⟨π, s, hs, -, h⟩ :=
    CFSG.Timmesfeld.ARS.CaseOA.exists_signedPerm_toStdD_weylAction hk w
  rw [h, h, ggDDot, ggDDot, ← Equiv.sum_comp π fun c => toStdD k u c * toStdD k v c]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases hs c with h1 | h1 <;> simp only [h1] <;> ring

private theorem coroot_cartanD_eq_ggDDot {k : ℕ} (hk : 2 ≤ k) (i : Fin k) (u : Fin k → ℤ) :
    coroot (cartanD k) i u = ggDDot (toStdD k u) (toStdD k (Pi.single i 1)) := by
  rw [ggDDot_eq_dotProduct]
  by_cases h : i.val + 1 < k
  · rw [coroot_cartanD_of_lt k h, toStdD_single_of_lt k h, dotProduct_sub, dotProduct_single,
      dotProduct_single, mul_one, mul_one]
  · have e : (⟨i.val - 1, by omega⟩ : Fin k) = ⟨k - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [coroot_cartanD_of_not_lt k h, toStdD_single_of_not_lt k h hk, dotProduct_add,
      dotProduct_single, dotProduct_single, mul_one, mul_one, e]

theorem GGDReflRoot.action {k : ℕ} (hk : 2 ≤ k) {t : ggWeylD k} {γ : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (v : Fin k → ℤ) :
    toStdD k (weylAction (isFiniteType_cartanD k) t v) = ggDReflect γ (toStdD k v) := by
  obtain ⟨w, i, rfl, rfl⟩ := h
  rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simpleD, reflection_apply_coroot,
    map_sub, map_zsmul, weylAction_apply_inv_apply, toStdD_sub, toStdD_smul,
    coroot_cartanD_eq_ggDDot hk, ← ggDDot_toStdD_weylAction hk w, weylAction_apply_inv_apply,
    ggDReflect]

theorem GGDReflRoot.unique {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k} {γ γ' : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t' γ') (hγ : γ' = γ ∨ γ' = -γ) : t = t' := by
  apply weylAction_injective (isFiniteType_cartanD k)
  refine LinearMap.ext fun v => toStdD_injective k ?_
  rw [h.action hk, h'.action hk]
  rcases hγ with rfl | rfl
  · rfl
  · rw [ggDReflect_neg]

theorem GGDReflRoot.neg {k : ℕ} {t : ggWeylD k} {γ : Fin k → ℤ} (h : GGDReflRoot k t γ) :
    GGDReflRoot k t (-γ) := by
  obtain ⟨w, i, rfl, rfl⟩ := h
  refine ⟨w * (coxeterMatrix (isFiniteType_cartanD k)).simple i, i, by group, ?_⟩
  rw [weylAction_mul_apply, weylAction_simpleD_single, map_neg, toStdD_neg]

theorem GGDReflRoot.conj {k : ℕ} {t : ggWeylD k} {γ : Fin k → ℤ} (h : GGDReflRoot k t γ)
    {g : ggWeylD k} {f : (Fin k → ℤ) → Fin k → ℤ}
    (hg : ∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g v) = f (toStdD k v)) :
    GGDReflRoot k (g * t * g⁻¹) (f γ) := by
  obtain ⟨w, i, rfl, rfl⟩ := h
  exact ⟨g * w, i, by group, by rw [weylAction_mul_apply, hg]⟩

theorem ggDReflRoot_simple (k : ℕ) (i : Fin k) :
    GGDReflRoot k ((coxeterMatrix (isFiniteType_cartanD k)).simple i)
      (toStdD k (Pi.single i 1)) :=
  ⟨1, i, by group, by rw [map_one, Module.End.one_apply]⟩

theorem GGDReflRoot.mem {k : ℕ} (hk : k ≠ 1) {t : ggWeylD k} {γ : Fin k → ℤ}
    (h : GGDReflRoot k t γ) : γ ∈ ggDRootSet k := by
  obtain ⟨w, i, -, rfl⟩ := h
  have hmem : weylAction (isFiniteType_cartanD k) w (Pi.single i 1) ∈
      roots (isFiniteType_cartanD k) ∅ := Or.inl ⟨w, i, rfl⟩
  rw [rootsD_eq k hk] at hmem
  obtain ⟨a, b, s, s', hab, hs, hs', he⟩ := hmem
  exact ⟨a, b, s, s', hab, hs, hs', he⟩

theorem exists_ggDReflRoot {k : ℕ} {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k) :
    ∃ t, GGDReflRoot k t γ := by
  obtain ⟨a, b, s, s', hab, hs, hs', rfl⟩ := hγ
  obtain ⟨v, hv, hve⟩ := exists_mem_rootsD_toStdD_eq k hab hs hs'
  rcases hv with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · exact ⟨_, w, i, rfl, hve⟩
  · exact absurd hi (Set.notMem_empty i)

theorem ggD_exists_perm {k : ℕ} (hk : 2 ≤ k) (π : Equiv.Perm (Fin k)) :
    ∃ g : ggWeylD k, ∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g v) =
      toStdD k v ∘ π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, fun v => by rw [map_one, Module.End.one_apply]; rfl⟩
  | swap_mul f x y hxy ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨t, ht⟩ :=
      exists_ggDReflRoot (k := k) ⟨x, y, 1, -1, hxy, Or.inl rfl, Or.inr rfl, rfl⟩
    refine ⟨g * t, fun v => ?_⟩
    rw [weylAction_mul_apply, hg, ht.action hk, ggDReflect_swap hxy, Equiv.Perm.coe_mul]
    rfl

theorem ggD_exists_negPair {k : ℕ} (hk : 2 ≤ k) {x y : Fin k} (hxy : x ≠ y) :
    ∃ g : ggWeylD k, ∀ v, toStdD k (weylAction (isFiniteType_cartanD k) g v) =
      fun c => if c = x ∨ c = y then -toStdD k v c else toStdD k v c := by
  obtain ⟨t, ht⟩ :=
    exists_ggDReflRoot (k := k) ⟨x, y, 1, -1, hxy, Or.inl rfl, Or.inr rfl, rfl⟩
  obtain ⟨t', ht'⟩ :=
    exists_ggDReflRoot (k := k) ⟨x, y, 1, 1, hxy, Or.inl rfl, Or.inl rfl, rfl⟩
  refine ⟨t * t', fun v => ?_⟩
  rw [weylAction_mul_apply, ht.action hk, ht'.action hk, ggDReflect_swap hxy]
  funext c
  rw [Function.comp_apply, ggDReflect_apply, ggDDot_comm, ggDDot_single_add_single]
  by_cases hcx : c = x
  · rw [hcx, Equiv.swap_apply_left, ggDPair_apply_right hxy, if_pos (Or.inl rfl)]
    ring
  by_cases hcy : c = y
  · rw [hcy, Equiv.swap_apply_right, ggDPair_apply_left hxy, if_pos (Or.inr rfl)]
    ring
  rw [Equiv.swap_apply_of_ne_of_ne hcx hcy, ggDPair_apply_of_ne hcx hcy,
    if_neg (not_or.2 ⟨hcx, hcy⟩)]
  ring

end CFSG.StandardType

end
