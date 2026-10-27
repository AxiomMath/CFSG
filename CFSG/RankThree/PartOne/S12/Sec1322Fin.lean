module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.Sec1322Fin

open Equiv

set_option maxRecDepth 100000

abbrev Gp : Type := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)

@[expose] def z0 : Gp := (Multiplicative.ofAdd 1, 1)

@[expose] def nfix (σ : Equiv.Perm (Fin 4)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

@[expose] def isT (x : Gp) : Prop := x.1 = 1 ∧ x.2 * x.2 = 1 ∧ nfix x.2 = 2

@[expose] def isT' (x : Gp) : Prop := x.1 = Multiplicative.ofAdd 1 ∧ x.2 * x.2 = 1 ∧ nfix x.2 = 2

@[expose] def isV (x : Gp) : Prop := x.1 = 1 ∧ x.2 * x.2 = 1 ∧ nfix x.2 = 0

@[expose] def isV' (x : Gp) : Prop := x.1 = Multiplicative.ofAdd 1 ∧ x.2 * x.2 = 1 ∧ nfix x.2 = 0

instance : DecidablePred isT := fun x => by unfold isT; infer_instance
instance : DecidablePred isT' := fun x => by unfold isT'; infer_instance
instance : DecidablePred isV := fun x => by unfold isV; infer_instance
instance : DecidablePred isV' := fun x => by unfold isV'; infer_instance

theorem classes : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → (isT x ∨ isT' x ∨ isV x ∨ isV' x) := by
  decide

theorem trans_T : ∀ x y : Gp, isT x → isT y → ∃ g : Gp, g * x * g⁻¹ = y := by decide
theorem trans_T' : ∀ x y : Gp, isT' x → isT' y → ∃ g : Gp, g * x * g⁻¹ = y := by decide
theorem trans_V : ∀ x y : Gp, isV x → isV y → ∃ g : Gp, g * x * g⁻¹ = y := by decide
theorem trans_V' : ∀ x y : Gp, isV' x → isV' y → ∃ g : Gp, g * x * g⁻¹ = y := by decide

theorem z0_T : ∀ x : Gp, isT x → isT' (z0 * x) := by decide
theorem z0_V : ∀ x : Gp, isV x → isV' (z0 * x) := by decide

@[expose] def signMap : Gp →* ℤˣ :=
  (MonoidHom.mk' (fun a : Multiplicative (ZMod 2) => if a = 1 then (1 : ℤˣ) else -1)
      (by decide)).comp (MonoidHom.fst _ _) *
    (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ).comp (MonoidHom.snd _ _)

theorem signMap_T' : ∀ x : Gp, isT' x → signMap x = 1 := by
  intro x hx
  revert x
  decide

theorem signMap_V : ∀ x : Gp, isV x → signMap x = 1 := by decide

theorem signMap_z0 : signMap z0 ≠ 1 := by decide

@[expose] def kleinP (x : Gp) : Prop := x.2 * x.2 = 1 ∧ (nfix x.2 = 0 ∨ x.2 = 1)

instance : DecidablePred kleinP := fun x => by unfold kleinP; infer_instance

theorem kleinP_one : kleinP 1 := by decide
theorem kleinP_mul : ∀ a b : Gp, kleinP a → kleinP b → kleinP (a * b) := by decide
theorem kleinP_inv : ∀ a : Gp, kleinP a → kleinP a⁻¹ := by decide

@[expose] def klein : Subgroup Gp where
  carrier := {x | kleinP x}
  one_mem' := kleinP_one
  mul_mem' := fun {a b} ha hb => kleinP_mul a b ha hb
  inv_mem' := fun {a} ha => kleinP_inv a ha

theorem kleinP_V' : ∀ x : Gp, isV' x → kleinP x := by decide

theorem not_kleinP : ¬ kleinP ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) := by
  decide

theorem closure_eq_top_of_gens {H : Subgroup Gp}
    (h0 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ∈ H)
    (h1 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (1 : Fin 4) 2) ∈ H)
    (h2 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (2 : Fin 4) 3) ∈ H) (hz : z0 ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, σ⟩ -
  have hσ : ((1 : Multiplicative (ZMod 2)), σ) ∈ H := by
    have hσM : σ ∈ Submonoid.closure (Set.range fun i : Fin 3 ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have hle : Submonoid.closure (Set.range fun i : Fin 3 ↦ Equiv.swap i.castSucc i.succ) ≤
        H.toSubmonoid.comap (MonoidHom.inr (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 4))) := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    exact hle hσM
  have ha : (a, (1 : Equiv.Perm (Fin 4))) ∈ H := by
    have : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
    rcases this a with rfl | rfl
    · exact H.one_mem
    · exact hz
  have : (a, σ) = (a, (1 : Equiv.Perm (Fin 4))) * ((1 : Multiplicative (ZMod 2)), σ) := by simp
  rw [this]
  exact H.mul_mem ha hσ

theorem word_mem {H : Subgroup Gp} {g : Fin 3 → Gp} (hg : ∀ i, g i ∈ H) (l : List (Fin 3)) :
    (l.map g).prod ∈ H := by
  refine Subgroup.list_prod_mem H ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact hg i

@[expose] def gensOf (a : Multiplicative (ZMod 2)) : Fin 3 → Gp :=
  ![(Multiplicative.ofAdd 1, Equiv.swap 0 1 * Equiv.swap 2 3), (a, Equiv.swap 1 2),
    (a, Equiv.swap 0 1)]

theorem closure_gens_one : Subgroup.closure (Set.range (gensOf 1)) = ⊤ := by
  set H := Subgroup.closure (Set.range (gensOf 1)) with hH
  have hg : ∀ i, gensOf 1 i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have h0 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) =
        (([2] : List (Fin 3)).map (gensOf 1)).prod := by decide
    rw [e]
    exact word_mem hg _
  have h1 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (1 : Fin 4) 2) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (1 : Fin 4) 2) =
        (([1] : List (Fin 3)).map (gensOf 1)).prod := by decide
    rw [e]
    exact word_mem hg _
  have h2 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (2 : Fin 4) 3) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (2 : Fin 4) 3) =
        (([1, 0, 1, 2, 1, 0, 1] : List (Fin 3)).map (gensOf 1)).prod := by decide
    rw [e]
    exact word_mem hg _
  have hz : z0 ∈ H := by
    have e : z0 = (([0, 1, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)).map (gensOf 1)).prod := by decide
    rw [e]
    exact word_mem hg _
  exact closure_eq_top_of_gens h0 h1 h2 hz

theorem closure_gens_neg : Subgroup.closure (Set.range (gensOf (Multiplicative.ofAdd 1))) = ⊤ := by
  set H := Subgroup.closure (Set.range (gensOf (Multiplicative.ofAdd 1))) with hH
  have hg : ∀ i, gensOf (Multiplicative.ofAdd 1) i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have h0 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) =
        (([0, 1, 0, 1, 2, 1, 0, 1] : List (Fin 3)).map (gensOf (Multiplicative.ofAdd 1))).prod := by
      decide
    rw [e]
    exact word_mem hg _
  have h1 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (1 : Fin 4) 2) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (1 : Fin 4) 2) =
        (([0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)).map (gensOf (Multiplicative.ofAdd 1))).prod := by
      decide
    rw [e]
    exact word_mem hg _
  have h2 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (2 : Fin 4) 3) ∈ H := by
    have e : ((1 : Multiplicative (ZMod 2)), Equiv.swap (2 : Fin 4) 3) =
        (([0, 2] : List (Fin 3)).map (gensOf (Multiplicative.ofAdd 1))).prod := by decide
    rw [e]
    exact word_mem hg _
  have hz : z0 ∈ H := by
    have e : z0 = (([0, 1, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)).map
        (gensOf (Multiplicative.ofAdd 1))).prod := by decide
    rw [e]
    exact word_mem hg _
  exact closure_eq_top_of_gens h0 h1 h2 hz

theorem orderOf_eq_of_pow {x : Gp} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1)
    (h2 : ∀ m, m < n → 0 < m → x ^ m ≠ 1) : orderOf x = n :=
  (orderOf_eq_iff hn).2 ⟨h, h2⟩

theorem range_gensOf (a : Multiplicative (ZMod 2)) :
    Set.range (gensOf a) = {gensOf a 0, gensOf a 1, gensOf a 2} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem chain_props_one :
    gensOf 1 0 * gensOf 1 2 = gensOf 1 2 * gensOf 1 0 ∧
      orderOf (gensOf 1 0 * gensOf 1 1) = 4 ∧ orderOf (gensOf 1 1 * gensOf 1 2) = 3 := by
  refine ⟨by decide, orderOf_eq_of_pow (by norm_num) (by decide) (by decide),
    orderOf_eq_of_pow (by norm_num) (by decide) (by decide)⟩

theorem chain_props_neg :
    gensOf (Multiplicative.ofAdd 1) 0 * gensOf (Multiplicative.ofAdd 1) 2 =
        gensOf (Multiplicative.ofAdd 1) 2 * gensOf (Multiplicative.ofAdd 1) 0 ∧
      orderOf (gensOf (Multiplicative.ofAdd 1) 0 * gensOf (Multiplicative.ofAdd 1) 1) = 4 ∧
      orderOf (gensOf (Multiplicative.ofAdd 1) 1 * gensOf (Multiplicative.ofAdd 1) 2) = 3 := by
  refine ⟨by decide, orderOf_eq_of_pow (by norm_num) (by decide) (by decide),
    orderOf_eq_of_pow (by norm_num) (by decide) (by decide)⟩

theorem gens_one_mem : isV' (gensOf 1 0) ∧ isT (gensOf 1 1) ∧ isT (gensOf 1 2) := by decide

theorem gens_neg_mem :
    isV' (gensOf (Multiplicative.ofAdd 1) 0) ∧ isT' (gensOf (Multiplicative.ofAdd 1) 1) ∧
      isT' (gensOf (Multiplicative.ofAdd 1) 2) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pairs_one : ∀ s t : Gp, (isT s ∨ isV' s) → (isT t ∨ isV' t) → (s * t) ^ 4 = 1 →
    (s * t) ^ 2 ≠ 1 →
    ∃ x : Gp, (x * gensOf 1 0 * x⁻¹ = s ∧ x * gensOf 1 1 * x⁻¹ = t) ∨
      (x * gensOf 1 0 * x⁻¹ = t ∧ x * gensOf 1 1 * x⁻¹ = s) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pairs_neg : ∀ s t : Gp, (isT' s ∨ isV' s) → (isT' t ∨ isV' t) → (s * t) ^ 4 = 1 →
    (s * t) ^ 2 ≠ 1 →
    ∃ x : Gp, (x * gensOf (Multiplicative.ofAdd 1) 0 * x⁻¹ = s ∧
        x * gensOf (Multiplicative.ofAdd 1) 1 * x⁻¹ = t) ∨
      (x * gensOf (Multiplicative.ofAdd 1) 0 * x⁻¹ = t ∧
        x * gensOf (Multiplicative.ofAdd 1) 1 * x⁻¹ = s) := by decide

theorem chain_of_reflection_set {R D : Set Gp}
    (hRc : ∀ g x, x ∈ R → g * x * g⁻¹ ∈ R) (hDc : ∀ g x, x ∈ D → g * x * g⁻¹ ∈ D)
    (hDR : D ⊆ R) (hRi : ∀ x ∈ R, x * x = 1 ∧ x ≠ 1 ∧ x ≠ z0)
    (hdich : ∀ x : Gp, x * x = 1 → x ≠ 1 → x ≠ z0 → (x ∈ R ↔ z0 * x ∉ R))
    (hgen : Subgroup.closure D = ⊤) :
    D = R ∧ ((∀ x, x ∈ D ↔ isT x ∨ isV' x) ∨ (∀ x, x ∈ D ↔ isT' x ∨ isV' x)) ∧
      ∃ t₁ ∈ D, ∃ t₂ ∈ D, ∃ t₃ ∈ D, t₁ * t₃ = t₃ * t₁ ∧ orderOf (t₁ * t₂) = 4 ∧
      orderOf (t₂ * t₃) = 3 ∧ Subgroup.closure {t₁, t₂, t₃} = ⊤ ∧
      (∀ d ∈ D, (∃ x : Gp, x * t₁ * x⁻¹ = d) ∨ ∃ x : Gp, x * t₂ * x⁻¹ = d) ∧
      ∀ s ∈ D, ∀ t ∈ D, orderOf (s * t) = 4 →
        ∃ x : Gp, (x * t₁ * x⁻¹ = s ∧ x * t₂ * x⁻¹ = t) ∨
          (x * t₁ * x⁻¹ = t ∧ x * t₂ * x⁻¹ = s) := by
  classical
  have hcls : ∀ x ∈ R, isT x ∨ isT' x ∨ isV x ∨ isV' x := fun x hx =>
    classes x (hRi x hx).1 (hRi x hx).2.1 (hRi x hx).2.2
  have ht0 : isT ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) := by decide
  have hv0 : isV ((1 : Multiplicative (ZMod 2)),
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) := by decide
  have ht0i : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) *
        ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) = 1 ∧
      ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ≠ 1 ∧
      ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ≠ z0 := by decide
  have hv0i : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) *
        ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) = 1 ∧
      ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) ≠ 1 ∧
      ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) ≠ z0 := by
    decide
  set t0 : Gp := ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) with ht0def
  set v0 : Gp := ((1 : Multiplicative (ZMod 2)),
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) with hv0def
  have hT : ((∀ x, isT x → x ∈ R) ∧ (∀ x, isT' x → x ∉ R)) ∨
      ((∀ x, isT' x → x ∈ R) ∧ (∀ x, isT x → x ∉ R)) := by
    by_cases h0 : t0 ∈ R
    · left
      refine ⟨fun x hx => ?_, fun x hx hxR => ?_⟩
      · obtain ⟨g, hg⟩ := trans_T t0 x ht0 hx
        rw [← hg]
        exact hRc g t0 h0
      · have hnot : z0 * t0 ∉ R := (hdich t0 ht0i.1 ht0i.2.1 ht0i.2.2).1 h0
        obtain ⟨g, hg⟩ := trans_T' x (z0 * t0) hx (z0_T t0 ht0)
        apply hnot
        rw [← hg]
        exact hRc g x hxR
    · right
      have hin : z0 * t0 ∈ R := by
        by_contra hn
        exact h0 ((hdich t0 ht0i.1 ht0i.2.1 ht0i.2.2).2 hn)
      refine ⟨fun x hx => ?_, fun x hx hxR => ?_⟩
      · obtain ⟨g, hg⟩ := trans_T' (z0 * t0) x (z0_T t0 ht0) hx
        rw [← hg]
        exact hRc g _ hin
      · obtain ⟨g, hg⟩ := trans_T x t0 hx ht0
        apply h0
        rw [← hg]
        exact hRc g x hxR
  have hV : ((∀ x, isV x → x ∈ R) ∧ (∀ x, isV' x → x ∉ R)) ∨
      ((∀ x, isV' x → x ∈ R) ∧ (∀ x, isV x → x ∉ R)) := by
    by_cases h0 : v0 ∈ R
    · left
      refine ⟨fun x hx => ?_, fun x hx hxR => ?_⟩
      · obtain ⟨g, hg⟩ := trans_V v0 x hv0 hx
        rw [← hg]
        exact hRc g v0 h0
      · have hnot : z0 * v0 ∉ R := (hdich v0 hv0i.1 hv0i.2.1 hv0i.2.2).1 h0
        obtain ⟨g, hg⟩ := trans_V' x (z0 * v0) hx (z0_V v0 hv0)
        apply hnot
        rw [← hg]
        exact hRc g x hxR
    · right
      have hin : z0 * v0 ∈ R := by
        by_contra hn
        exact h0 ((hdich v0 hv0i.1 hv0i.2.1 hv0i.2.2).2 hn)
      refine ⟨fun x hx => ?_, fun x hx hxR => ?_⟩
      · obtain ⟨g, hg⟩ := trans_V' (z0 * v0) x (z0_V v0 hv0) hx
        rw [← hg]
        exact hRc g _ hin
      · obtain ⟨g, hg⟩ := trans_V x v0 hx hv0
        apply h0
        rw [← hg]
        exact hRc g x hxR
  have hz0 : z0 ∈ Subgroup.closure D := by rw [hgen]; trivial
  have h10 : ((1 : Multiplicative (ZMod 2)), Equiv.swap (0 : Fin 4) 1) ∈ Subgroup.closure D := by
    rw [hgen]; trivial
  have hfst : (∀ x ∈ D, x.1 = 1) → False := by
    intro h
    have hle : Subgroup.closure D ≤ (MonoidHom.fst (Multiplicative (ZMod 2))
        (Equiv.Perm (Fin 4))).ker := (Subgroup.closure_le _).2 fun x hx => h x hx
    have h1 := hle hz0
    rw [MonoidHom.mem_ker] at h1
    exact absurd (show z0.1 = 1 from h1) (by decide)
  have hsign : (∀ x ∈ D, signMap x = 1) → False := by
    intro h
    have hle : Subgroup.closure D ≤ signMap.ker := (Subgroup.closure_le _).2 fun x hx => h x hx
    exact signMap_z0 (hle hz0)
  have hkl : (∀ x ∈ D, kleinP x) → False := by
    intro h
    have hle : Subgroup.closure D ≤ klein := (Subgroup.closure_le _).2 fun x hx => h x hx
    exact not_kleinP (hle h10)
  have good : ∀ (C : Gp → Prop) (hC : ∀ x, C x → x ∈ R) (hCn : ∀ x, x ∈ R → C x ∨ isV' x)
      (htr : ∀ x y, C x → C y → ∃ g : Gp, g * x * g⁻¹ = y),
      (∀ x, C x → ¬ isV' x) → (∀ x, isV' x → x ∈ R) →
      ((∀ x ∈ D, ¬ C x) → False) → ((∀ x ∈ D, ¬ isV' x) → False) →
      D = R ∧ (∀ x, x ∈ D ↔ C x ∨ isV' x) := by
    intro C hC hCn htr hCV hV'R hDC hDV
    have hDC' : ∃ d ∈ D, C d := by
      by_contra hn
      push Not at hn
      exact hDC hn
    have hDV' : ∃ d ∈ D, isV' d := by
      by_contra hn
      push Not at hn
      exact hDV hn
    obtain ⟨d1, hd1, hCd1⟩ := hDC'
    obtain ⟨d2, hd2, hVd2⟩ := hDV'
    have hiff : ∀ x, x ∈ D ↔ C x ∨ isV' x := by
      intro x
      constructor
      · intro hx
        exact hCn x (hDR hx)
      · rintro (hx | hx)
        · obtain ⟨g, hg⟩ := htr d1 x hCd1 hx
          rw [← hg]
          exact hDc g d1 hd1
        · obtain ⟨g, hg⟩ := trans_V' d2 x hVd2 hx
          rw [← hg]
          exact hDc g d2 hd2
    refine ⟨Set.ext fun x => ⟨fun hx => hDR hx, fun hx => ?_⟩, hiff⟩
    exact (hiff x).2 (hCn x hx)
  rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩ <;> rcases hV with ⟨hV1, hV2⟩ | ⟨hV1, hV2⟩
  ·
    exfalso
    refine hfst fun x hx => ?_
    rcases hcls x (hDR hx) with h | h | h | h
    · exact h.1
    · exact absurd (hDR hx) (hT2 x h)
    · exact h.1
    · exact absurd (hDR hx) (hV2 x h)
  ·
    have hg := good isT (fun x hx => hT1 x hx)
      (fun x hx => by
        rcases hcls x hx with h | h | h | h
        · exact Or.inl h
        · exact absurd hx (hT2 x h)
        · exact absurd hx (hV2 x h)
        · exact Or.inr h)
      trans_T (fun x hx hv => by
        have h := hx.2.2.symm.trans hv.2.2
        omega)
      (fun x hx => hV1 x hx)
      (fun hn => hkl fun x hx => by
        rcases hcls x (hDR hx) with h | h | h | h
        · exact absurd h (hn x hx)
        · exact absurd (hDR hx) (hT2 x h)
        · exact absurd (hDR hx) (hV2 x h)
        · exact kleinP_V' x h)
      (fun hn => hfst fun x hx => by
        rcases hcls x (hDR hx) with h | h | h | h
        · exact h.1
        · exact absurd (hDR hx) (hT2 x h)
        · exact absurd (hDR hx) (hV2 x h)
        · exact absurd h (hn x hx))
    obtain ⟨hDR', hiff⟩ := hg
    have hmem : ∀ x, (x ∈ D) ↔ (isT x ∨ isV' x) := hiff
    refine ⟨hDR', Or.inl hmem, ?_⟩
    obtain ⟨hp1, hp2, hp3⟩ := chain_props_one
    obtain ⟨hm0, hm1, hm2⟩ := gens_one_mem
    refine ⟨gensOf 1 0, (hmem _).2 (Or.inr hm0), gensOf 1 1, (hmem _).2 (Or.inl hm1),
      gensOf 1 2, (hmem _).2 (Or.inl hm2), hp1, hp2, hp3, ?_, ?_, ?_⟩
    · rw [← range_gensOf]
      exact closure_gens_one
    · intro d hd
      rcases (hmem d).1 hd with h | h
      · right
        exact trans_T _ _ hm1 h
      · left
        exact trans_V' _ _ hm0 h
    · intro s hs t ht hord
      have hne : (s * t) ^ 2 ≠ 1 := by
        intro h2
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hord] at this
        omega
      have h4 : (s * t) ^ 4 = 1 := by
        have h5 := pow_orderOf_eq_one (s * t)
        rwa [hord] at h5
      exact pairs_one s t ((hmem s).1 hs) ((hmem t).1 ht) h4 hne
  ·
    exfalso
    refine hsign fun x hx => ?_
    rcases hcls x (hDR hx) with h | h | h | h
    · exact absurd (hDR hx) (hT2 x h)
    · exact signMap_T' x h
    · exact signMap_V x h
    · exact absurd (hDR hx) (hV2 x h)
  ·
    have hg := good isT' (fun x hx => hT1 x hx)
      (fun x hx => by
        rcases hcls x hx with h | h | h | h
        · exact absurd hx (hT2 x h)
        · exact Or.inl h
        · exact absurd hx (hV2 x h)
        · exact Or.inr h)
      trans_T' (fun x hx hv => by
        have h := hx.2.2.symm.trans hv.2.2
        omega)
      (fun x hx => hV1 x hx)
      (fun hn => hkl fun x hx => by
        rcases hcls x (hDR hx) with h | h | h | h
        · exact absurd (hDR hx) (hT2 x h)
        · exact absurd h (hn x hx)
        · exact absurd (hDR hx) (hV2 x h)
        · exact kleinP_V' x h)
      (fun hn => hsign fun x hx => by
        rcases hcls x (hDR hx) with h | h | h | h
        · exact absurd (hDR hx) (hT2 x h)
        · exact signMap_T' x h
        · exact absurd (hDR hx) (hV2 x h)
        · exact absurd h (hn x hx))
    obtain ⟨hDR', hiff⟩ := hg
    have hmem : ∀ x, (x ∈ D) ↔ (isT' x ∨ isV' x) := hiff
    refine ⟨hDR', Or.inr hmem, ?_⟩
    obtain ⟨hp1, hp2, hp3⟩ := chain_props_neg
    obtain ⟨hm0, hm1, hm2⟩ := gens_neg_mem
    refine ⟨gensOf (Multiplicative.ofAdd 1) 0, (hmem _).2 (Or.inr hm0),
      gensOf (Multiplicative.ofAdd 1) 1, (hmem _).2 (Or.inl hm1),
      gensOf (Multiplicative.ofAdd 1) 2, (hmem _).2 (Or.inl hm2), hp1, hp2, hp3, ?_, ?_, ?_⟩
    · rw [← range_gensOf]
      exact closure_gens_neg
    · intro d hd
      rcases (hmem d).1 hd with h | h
      · right
        exact trans_T' _ _ hm1 h
      · left
        exact trans_V' _ _ hm0 h
    · intro s hs t ht hord
      have hne : (s * t) ^ 2 ≠ 1 := by
        intro h2
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hord] at this
        omega
      have h4 : (s * t) ^ 4 = 1 := by
        have h5 := pow_orderOf_eq_one (s * t)
        rwa [hord] at h5
      exact pairs_neg s t ((hmem s).1 hs) ((hmem t).1 ht) h4 hne

end CFSG.RankThree.PartOne.Sec1322Fin
