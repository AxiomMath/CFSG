module

public import CFSG.LocalAnalysis.StandardType.GGQ2A4Checks
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType

open Module

structure GGQ2A4Conf (V : Type) [AddCommGroup V] [Module (ZMod 3) V] where
  c : Fin 4 → V
  α : Fin 4 → Dual (ZMod 3) V
  x : V
  pairing : ∀ i j, α i (c j) = ggA4C i j
  root_x : ∀ i, α i x = 0
  ind : LinearIndependent (ZMod 3) c
  x_notMem : x ∉ Submodule.span (ZMod 3) (Set.range c)

namespace GGQ2A4Conf

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (K : GGQ2A4Conf V)

@[expose] def H : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) (Set.range K.c)

@[expose] def Full : Prop :=
  Submodule.span (ZMod 3) (Set.range K.c) ⊔ Submodule.span (ZMod 3) {K.x} = ⊤

@[expose] noncomputable def κ : (Fin 4 → ZMod 3) →ₗ[ZMod 3] V :=
  Fintype.linearCombination (ZMod 3) K.c

theorem κ_apply (n : Fin 4 → ZMod 3) : K.κ n = ∑ j, n j • K.c j := by
  rw [κ, Fintype.linearCombination_apply]

theorem κ_single (j : Fin 4) : K.κ (Pi.single j 1) = K.c j := by
  simp [κ]

theorem κ_injective : Function.Injective K.κ := by
  intro n m h
  have hli := Fintype.linearIndependent_iff.mp K.ind
  have h0 : n - m = 0 := by
    funext i
    have hz : K.κ (n - m) = 0 := by simp [map_sub, h]
    rw [κ_apply] at hz
    simpa using hli (n - m) hz i
  exact sub_eq_zero.mp h0

theorem mem_H_iff {v : V} : v ∈ K.H ↔ ∃ n, K.κ n = v := by
  constructor
  · intro hv
    change v ∈ Submodule.span (ZMod 3) (Set.range K.c) at hv
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3) (v := K.c)).mp hv
    exact ⟨n, by rw [κ_apply, hn]⟩
  · rintro ⟨n, rfl⟩
    change (∑ j, n j • K.c j) ∈ Submodule.span (ZMod 3) (Set.range K.c)
    exact Submodule.sum_mem (p := Submodule.span (ZMod 3) (Set.range K.c))
      fun i _ => Submodule.smul_mem (Submodule.span (ZMod 3) (Set.range K.c)) (n i)
        (Submodule.subset_span ⟨i, rfl⟩)

theorem κ_mem_H (n : Fin 4 → ZMod 3) : K.κ n ∈ K.H := by
  exact (mem_H_iff (K := K) (v := K.κ n)).mpr ⟨n, rfl⟩

theorem finite (hF : K.Full) : Module.Finite (ZMod 3) V := by
  have hF' : Submodule.span (ZMod 3) (Set.range K.c) ⊔ Submodule.span (ZMod 3) {K.x} = ⊤ := hF
  rw [Module.finite_def]
  rw [show (⊤ : Submodule (ZMod 3) V) =
      Submodule.span (ZMod 3) (Set.range K.c) ⊔ Submodule.span (ZMod 3) {K.x}
    from hF'.symm]
  exact Submodule.FG.sup (Submodule.fg_span (Set.finite_range K.c))
    (Submodule.fg_span (Set.finite_singleton K.x))

theorem decomp (hF : K.Full) (v : V) :
    ∃ (l : ZMod 3) (n : Fin 4 → ZMod 3), v = l • K.x + K.κ n := by
  have hF' : Submodule.span (ZMod 3) (Set.range K.c) ⊔ Submodule.span (ZMod 3) {K.x} = ⊤ := hF
  have hv : v ∈ K.H ⊔ Submodule.span (ZMod 3) {K.x} := by
    change v ∈ Submodule.span (ZMod 3) (Set.range K.c) ⊔
      Submodule.span (ZMod 3) {K.x}
    rw [hF']
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  obtain ⟨n, hn⟩ := (mem_H_iff (K := K) (v := a)).mp ha
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hb
  exact ⟨l, n, by rw [← hab, ← hn, ← hl, add_comm]⟩

theorem α_κ (i : Fin 4) (n : Fin 4 → ZMod 3) : K.α i (K.κ n) = ggA4B (Pi.single i 1) n := by
  rw [κ_apply, map_sum]
  simp only [map_smul, K.pairing, smul_eq_mul, ggA4B_single]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem coroot_two (i : Fin 4) : K.α i (K.c i) = 2 := by
  rw [K.pairing]
  fin_cases i <;> decide

theorem decomp_ker (v : V) : ∃ n : Fin 4 → ZMod 3, ∀ k, K.α k (v - K.κ n) = 0 := by
  let f : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3) := fun n k => ggA4B (Pi.single k 1) n
  have hinj : Function.Injective f := by
    intro n m hnm
    have h0 : n - m = 0 := by
      refine ggA4_nondeg (n - m) fun i => ?_
      rw [← K.α_κ, map_sub, map_sub, K.α_κ, K.α_κ]
      exact sub_eq_zero.mpr (congrFun hnm i)
    exact sub_eq_zero.mp h0
  obtain ⟨n, hn⟩ := Finite.injective_iff_surjective.mp hinj (fun k => K.α k v)
  refine ⟨n, fun k => ?_⟩
  rw [map_sub, K.α_κ]
  exact sub_eq_zero.mpr (congrFun hn k).symm

theorem refl_κ {m : Fin 4 → ZMod 3} {φ : Dual (ZMod 3) V} {ε : ZMod 3} (hφ : φ (K.κ m) = 2)
    (hφH : ∀ n, φ (K.κ n) = ε * ggA4B m n) (n : Fin 4 → ZMod 3) :
    Module.reflection hφ (K.κ n) = K.κ (ggA4RAct ε m n) := by
  rw [Module.reflection_apply, hφH n, ggA4RAct, map_sub, map_smul]

@[expose] noncomputable def s (i : Fin 4) : V ≃ₗ[ZMod 3] V :=
  Module.reflection (K.coroot_two i)

theorem s_apply (i : Fin 4) (v : V) : K.s i v = v - K.α i v • K.c i := by
  change Module.reflection (K.coroot_two i) v = v - K.α i v • K.c i
  rw [Module.reflection_apply]

theorem s_κ (i : Fin 4) (n : Fin 4 → ZMod 3) :
    K.s i (K.κ n) = K.κ (ggA4RAct 1 (Pi.single i 1) n) := by
  rw [s_apply, α_κ, ggA4RAct, map_sub, map_smul, κ_single, one_mul]

theorem s_x (i : Fin 4) : K.s i K.x = K.x := by
  rw [s_apply, K.root_x i, zero_smul, sub_zero]

theorem s_isRefl (i : Fin 4) : IsReflLin (p := 3) (K.s i) := by
  exact ⟨K.c i, K.α i, K.coroot_two i, rfl⟩

theorem word_κ (w : List (Fin 4)) (n : Fin 4 → ZMod 3) :
    (w.map K.s).prod (K.κ n) = K.κ (ggA4WordAct w n) := by
  induction w with
  | nil => simp [ggA4WordAct]
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, s_κ]
      rfl

theorem word_ker (w : List (Fin 4)) {v : V} (hv : ∀ k, K.α k v = 0) : (w.map K.s).prod v = v := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, s_apply, hv i, zero_smul,
        sub_zero]

@[expose] noncomputable def rootFun (γ : Fin 10) : Dual (ZMod 3) V :=
  ∑ k, ggA4Root γ k • K.α k

@[expose] noncomputable def rootVec (γ : Fin 10) : V :=
  K.κ (ggA4Root γ)

private theorem ggA4B_sum_single (u n : Fin 4 → ZMod 3) :
    ggA4B u n = ∑ k, u k * ggA4B (Pi.single k 1) n := by
  change (∑ i, ∑ j, u i * ggA4C i j * n j) =
    ∑ k, u k * ggA4B (Pi.single k 1) n
  simp only [ggA4B_single, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rootFun_κ (γ : Fin 10) (n : Fin 4 → ZMod 3) :
    K.rootFun γ (K.κ n) = ggA4B (ggA4Root γ) n := by
  rw [rootFun]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, K.α_κ]
  rw [ggA4B_sum_single]

theorem rootFun_x (γ : Fin 10) : K.rootFun γ K.x = 0 := by
  rw [rootFun]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, K.root_x, smul_zero,
    Finset.sum_const_zero]

theorem rootFun_ker (γ : Fin 10) {v : V} (hv : ∀ k, K.α k v = 0) : K.rootFun γ v = 0 := by
  rw [rootFun]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_zero, Finset.sum_const_zero]

theorem rootFun_rootVec (γ : Fin 10) : K.rootFun γ (K.rootVec γ) = 2 := by
  rw [rootVec, rootFun_κ]
  exact ggA4_root_norm γ

@[expose] noncomputable def rootRefl (γ : Fin 10) : V ≃ₗ[ZMod 3] V :=
  Module.reflection (K.rootFun_rootVec γ)

theorem rootRefl_eq_word (γ : Fin 10) : K.rootRefl γ = ((ggA4RootWord γ).map K.s).prod := by
  ext v
  obtain ⟨n, hn⟩ := K.decomp_ker v
  have hH : K.rootRefl γ (K.κ n) = ((ggA4RootWord γ).map K.s).prod (K.κ n) :=
    calc K.rootRefl γ (K.κ n)
        = Module.reflection (K.rootFun_rootVec γ) (K.κ n) := rfl
      _ = K.κ (ggA4RAct 1 (ggA4Root γ) n) :=
        K.refl_κ (m := ggA4Root γ) (φ := K.rootFun γ) (ε := 1)
          (K.rootFun_rootVec γ) (fun m => by rw [rootFun_κ, one_mul]) n
      _ = K.κ (ggA4WordAct (ggA4RootWord γ) n) := by rw [ggA4_rootWord]
      _ = ((ggA4RootWord γ).map K.s).prod (K.κ n) :=
        (word_κ K (ggA4RootWord γ) n).symm
  have hk : K.rootRefl γ (v - K.κ n) = ((ggA4RootWord γ).map K.s).prod (v - K.κ n) := by
    rw [word_ker K _ hn, rootRefl, Module.reflection_apply, K.rootFun_ker γ hn, zero_smul,
      sub_zero]
  calc K.rootRefl γ v = K.rootRefl γ (K.κ n + (v - K.κ n)) := by congr 1; abel
    _ = ((ggA4RootWord γ).map K.s).prod (K.κ n + (v - K.κ n)) := by
      rw [map_add, map_add, hH, hk]
    _ = ((ggA4RootWord γ).map K.s).prod v := by congr 1; abel

theorem rootRefl_mem {G : Subgroup (V ≃ₗ[ZMod 3] V)} (hs : ∀ i, K.s i ∈ G) (γ : Fin 10) :
    K.rootRefl γ ∈ G := by
  rw [rootRefl_eq_word]
  exact Subgroup.list_prod_mem G fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hs i

theorem rootRefl_x (γ : Fin 10) : K.rootRefl γ K.x = K.x := by
  rw [rootRefl, Module.reflection_apply, K.rootFun_x γ, zero_smul, sub_zero]

theorem rootRefl_isRefl (γ : Fin 10) : IsReflLin (p := 3) (K.rootRefl γ) := by
  exact ⟨K.rootVec γ, K.rootFun γ, K.rootFun_rootVec γ, rfl⟩

theorem rootVec_simple (i : Fin 4) : K.rootVec (Fin.castLE (by decide) i) = K.c i := by
  rw [rootVec, ggA4_root_simple, κ_single]

theorem rootFun_simple (i : Fin 4) : K.rootFun (Fin.castLE (by decide) i) = K.α i := by
  rw [rootFun, ggA4_root_simple]
  simp [Pi.single_apply, ite_smul]

theorem hfix (hF : K.Full) : ∀ z, (∀ i, K.α i z = 0) → z ∈ Submodule.span (ZMod 3) {K.x} := by
  intro z hz
  obtain ⟨l, n, rfl⟩ := K.decomp hF z
  have hn : n = 0 := by
    refine ggA4_nondeg n fun i => ?_
    have h := hz i
    rw [map_add, map_smul, K.root_x i, smul_zero, zero_add, K.α_κ] at h
    exact h
  rw [hn, map_zero, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self K.x)

theorem hconn : ∀ i j : Fin 4,
    Relation.ReflTransGen (fun a b => K.α a (K.c b) ≠ 0 ∧ K.α b (K.c a) ≠ 0) i j := by
  let r : Fin 4 → Fin 4 → Prop :=
    fun a b => K.α a (K.c b) ≠ 0 ∧ K.α b (K.c a) ≠ 0
  have hstep : ∀ i : Fin 3, r (Fin.castSucc i) i.succ := by
    intro i
    refine ⟨?_, ?_⟩ <;> rw [K.pairing] <;> fin_cases i <;> decide
  have hsymm : Symmetric r := fun a b h => ⟨h.2, h.1⟩
  have hR : Symmetric (Relation.ReflTransGen r) := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.head (hsymm hbc)
  have h0 : ∀ i : Fin 4, Relation.ReflTransGen r i 0 := by
    intro i
    fin_cases i
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (hsymm (hstep 0))
    · exact (Relation.ReflTransGen.single (hsymm (hstep 1))).trans
        (Relation.ReflTransGen.single (hsymm (hstep 0)))
    · exact ((Relation.ReflTransGen.single (hsymm (hstep 2))).trans
        (Relation.ReflTransGen.single (hsymm (hstep 1)))).trans
        (Relation.ReflTransGen.single (hsymm (hstep 0)))
  intro i j
  exact (h0 i).trans (hR (h0 j))

theorem finrank_H : Module.finrank (ZMod 3) K.H = 4 := by
  rw [H, finrank_span_eq_card K.ind, Fintype.card_fin]

private theorem hhyp_aux [hV : Module.Finite (ZMod 3) V] (hF : K.Full) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range K.c)) + 1 =
      Module.finrank (ZMod 3) V := by
  have hF' : Submodule.span (ZMod 3) (Set.range K.c) ⊔ Submodule.span (ZMod 3) {K.x} = ⊤ := hF
  have hx0 : K.x ≠ 0 := by
    intro h
    apply K.x_notMem
    rw [h]
    exact Submodule.zero_mem _
  have hdisj : Submodule.span (ZMod 3) (Set.range K.c) ⊓
      Submodule.span (ZMod 3) {K.x} = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvH, hvs⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvs
    by_cases ha : a = 0
    · rw [ha, zero_smul]
    · exfalso
      have hxH : K.x ∈ Submodule.span (ZMod 3) (Set.range K.c) := by
        have hx : K.x = a⁻¹ • (a • K.x) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [hx]
        exact Submodule.smul_mem _ _ hvH
      exact K.x_notMem hxH
  have h1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {K.x}) = 1 := by
    rw [finrank_span_singleton hx0]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod 3) (Set.range K.c)) (Submodule.span (ZMod 3) {K.x})
  rw [hF', finrank_top, hdisj, finrank_bot, h1, add_zero] at hsup
  omega

theorem hhyp (hF : K.Full) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range K.c)) + 1 =
      Module.finrank (ZMod 3) V := by
  have hfin : Module.Finite (ZMod 3) V := K.finite hF
  exact hhyp_aux K (hV := hfin) hF

end GGQ2A4Conf

end CFSG.StandardType

end
