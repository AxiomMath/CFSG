module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem list_prod_ofFn_mul {G : Type} [Group G] : ∀ {n : ℕ} (f g : Fin n → G),
    (∀ i j, Commute (g i) (f j)) →
      (List.ofFn fun i => f i * g i).prod = (List.ofFn f).prod * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, list_prod_ofFn_mul (fun i => f i.succ) (fun i => g i.succ)
        (fun i j => hc _ _)]
    have h : Commute (g 0) (List.ofFn fun i => f i.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        rw [List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact hc 0 j.succ
    calc f 0 * g 0 * ((List.ofFn fun i => f i.succ).prod * (List.ofFn fun i => g i.succ).prod)
        = f 0 * (g 0 * (List.ofFn fun i => f i.succ).prod) *
            (List.ofFn fun i => g i.succ).prod := by simp only [mul_assoc]
      _ = f 0 * ((List.ofFn fun i => f i.succ).prod * g 0) *
            (List.ofFn fun i => g i.succ).prod := by rw [h.eq]
      _ = f 0 * (List.ofFn fun i => f i.succ).prod *
            (g 0 * (List.ofFn fun i => g i.succ).prod) := by simp only [mul_assoc]

private theorem list_prod_ofFn_ite {G : Type} [Group G] : ∀ {n : ℕ} (i : Fin n) (x : G),
    (List.ofFn fun j => if j = i then x else 1).prod = x
  | n + 1, i, x => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero => simp [Fin.succ_ne_zero, List.ofFn_const]
    | succ i' =>
      rw [if_neg (Fin.succ_ne_zero i').symm, one_mul]
      simp only [Fin.succ_inj]
      exact list_prod_ofFn_ite i' x

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem b_mem_span (B : Basis3 G k) (i : Fin k) : B.b i ∈ B.span :=
  Subgroup.subset_closure (Set.mem_range_self i)

theorem vec_mem_span (B : Basis3 G k) (e : Coords k) : B.vec e ∈ B.span := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Subgroup.pow_mem _ (B.b_mem_span i) _

@[expose] def bS (B : Basis3 G k) (i : Fin k) : ↥B.span := ⟨B.b i, B.b_mem_span i⟩

theorem vec_add (B : Basis3 G k) (e e' : Coords k) : B.vec (e + e') = B.vec e * B.vec e' := by
  have hpow : ∀ i, B.b i ^ ((e + e') i).val = B.b i ^ (e i).val * B.b i ^ (e' i).val := by
    intro i
    rw [← pow_add, Pi.add_apply, ZMod.val_add]
    have h3 := pow_mod_orderOf (B.b i) ((e i).val + (e' i).val)
    rwa [B.ord i] at h3
  unfold vec
  simp only [hpow]
  exact list_prod_ofFn_mul _ _ fun i j => ((B.comm i j).pow_left _).pow_right _

theorem vec_zero (B : Basis3 G k) : B.vec 0 = 1 := by
  simp [vec, List.ofFn_const]

theorem vec_single (B : Basis3 G k) (i : Fin k) : B.vec (Pi.single i 1) = B.b i := by
  have h : (fun j => B.b j ^ ((Pi.single i 1 : Coords k) j).val) =
      fun j => if j = i then B.b i else 1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, if_pos rfl, ZMod.val_one, pow_one]
    · rw [Pi.single_eq_of_ne hj, if_neg hj, ZMod.val_zero, pow_zero]
  unfold vec
  rw [h]
  exact list_prod_ofFn_ite i (B.b i)

theorem exists_vec_eq (B : Basis3 G k) {y : G} (hy : y ∈ B.span) : ∃ e, B.vec e = y := by
  let S : Subgroup G :=
    { carrier := Set.range B.vec
      mul_mem' := by
        rintro _ _ ⟨e, rfl⟩ ⟨e', rfl⟩
        exact ⟨e + e', B.vec_add e e'⟩
      one_mem' := ⟨0, B.vec_zero⟩
      inv_mem' := by
        rintro _ ⟨e, rfl⟩
        exact ⟨-e, eq_inv_of_mul_eq_one_left (by rw [← B.vec_add, neg_add_cancel, B.vec_zero])⟩ }
  have hle : B.span ≤ S := (Subgroup.closure_le S).mpr (by
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, B.vec_single i⟩)
  exact hle hy

theorem mem_normalizer_of_acts [Finite G] (B : Basis3 G k) {g : G}
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (h : B.Acts g A) :
    g ∈ Subgroup.normalizer (B.span : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : B.span.map (↑(MulAut.conj g) : G →* G) ≤ B.span := by
    rw [span, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply]
    rw [h i]
    exact B.vec_mem_span _
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

noncomputable def coords (B : Basis3 G k) (y : ↥B.span) : Coords k :=
  Classical.choose (B.exists_vec_eq y.2)

theorem vec_coords (B : Basis3 G k) (y : ↥B.span) : B.vec (B.coords y) = y :=
  Classical.choose_spec (B.exists_vec_eq y.2)

@[expose] noncomputable def matOf (B : Basis3 G k) (φ : MulAut ↥B.span) :
    Matrix (Fin k) (Fin k) (ZMod 3) :=
  fun i j => B.coords (φ (B.bS j)) i

theorem matOf_apply (B : Basis3 G k) (φ : MulAut ↥B.span) (i j : Fin k) :
    B.matOf φ i j = B.coords (φ (B.bS j)) i :=
  rfl

theorem card_ggAutomizer_le [Finite G] (B : Basis3 G k) (H : Subgroup G) :
    Nat.card ↥(ggAutomizer H B.span) ≤ Nat.card ↥(B.realized H) := by
  have hmem : ∀ φ : ↥(ggAutomizer H B.span), B.matOf φ ∈ B.realized H := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgH, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    refine ⟨g, hgH, fun j => ?_⟩
    show g * B.b j * g⁻¹ = B.vec (B.coords (φ (B.bS j)))
    rw [B.vec_coords, hg]
    rfl
  let f : ↥(ggAutomizer H B.span) → ↥(B.realized H) := fun φ => ⟨B.matOf φ, hmem φ⟩
  have hf : Function.Injective f := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
    have hmat : B.matOf φ = B.matOf ψ := congrArg Subtype.val h
    apply Subtype.ext
    have hgen : ∀ j, φ (B.bS j) = ψ (B.bS j) := fun j => by
      apply Subtype.ext
      rw [← B.vec_coords (φ (B.bS j)), ← B.vec_coords (ψ (B.bS j))]
      congr 1
      funext i
      exact congrFun (congrFun hmat i) j
    have hcl : Subgroup.closure (Set.range B.bS) = ⊤ := by
      have hset : Set.range B.bS = ((↑) : ↥B.span → G) ⁻¹' Set.range B.b := by
        ext y
        constructor
        · rintro ⟨j, rfl⟩
          exact ⟨j, rfl⟩
        · rintro ⟨j, hj⟩
          exact ⟨j, Subtype.ext hj⟩
      rw [hset]
      exact Subgroup.closure_closure_coe_preimage
    refine MulEquiv.toMonoidHom_injective (MonoidHom.eq_of_eqOn_dense hcl ?_)
    rintro y ⟨j, rfl⟩
    exact hgen j
  have : Finite ↥(B.realized H) := Set.toFinite _ |>.to_subtype
  exact Nat.card_le_card_of_injective f hf

end Basis3

theorem card_spSet_le (k : ℕ) (p : Equiv.Perm (Fin k) → (Fin k → ZMod 3) → Prop) :
    Nat.card ↥(spSet p) ≤ 2 ^ k * k.factorial := by
  let T : Set (Fin k → ZMod 3) := {s | IsSign s}
  have hT : Nat.card ↥T ≤ 2 ^ k := by
    have hinj : Function.Injective
        (fun s : ↥T => fun i => decide ((s : Fin k → ZMod 3) i = 1)) := by
      rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
      apply Subtype.ext
      funext i
      have hi := congrFun h i
      revert hi
      show decide (s i = 1) = decide (s' i = 1) → s i = s' i
      rcases hs i with h1 | h1 <;> rcases hs' i with h2 | h2 <;> rw [h1, h2] <;> decide
    calc Nat.card ↥T ≤ Nat.card (Fin k → Bool) := Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ k := by simp
  let F : Equiv.Perm (Fin k) × ↥T → Matrix (Fin k) (Fin k) (ZMod 3) := fun q => spMat q.1 q.2
  have hsub : spSet p ⊆ Set.range F := by
    rintro _ ⟨σ, s, hs, -, rfl⟩
    exact ⟨(σ, ⟨s, hs⟩), rfl⟩
  calc Nat.card ↥(spSet p) ≤ Nat.card ↥(Set.range F) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (Equiv.Perm (Fin k) × ↥T) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization F) Set.rangeFactorization_surjective
    _ = k.factorial * Nat.card ↥T := by rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
    _ ≤ 2 ^ k * k.factorial := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hT

end CFSG.StandardType.FrameRoute.FS81

end
