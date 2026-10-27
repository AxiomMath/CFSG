module

public import Mathlib.RepresentationTheory.Maschke
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.GroupTheory.SteinbergCESmallBinaryOrbitCounts

public section

open Representation

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank SemidirectProduct
open scoped IsMulCommutative

section Atoms

variable {k : Type*} [Field k] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module k M]

@[expose] def fixedSub (σ : Representation k Γ M) (N : Subgroup Γ) [N.Normal] :
    Subrepresentation σ where
  toSubmodule :=
    { carrier := {v | ∀ n ∈ N, σ n v = v}
      add_mem' := fun {a b} ha hb n hn => by rw [map_add, ha n hn, hb n hn]
      zero_mem' := fun n _ => map_zero _
      smul_mem' := fun c v hv n hn => by rw [map_smul, hv n hn] }
  apply_mem_toSubmodule g v hv n hn := by
    have h1 : g⁻¹ * n * g ∈ N := by
      simpa using ‹N.Normal›.conj_mem n hn g⁻¹
    have h2 := hv (g⁻¹ * n * g) h1
    calc σ n (σ g v) = σ g (σ (g⁻¹ * n * g) v) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2; group
      _ = σ g v := by rw [h2]

theorem mem_fixedSub (σ : Representation k Γ M) (N : Subgroup Γ) [N.Normal] (v : M) :
    v ∈ fixedSub σ N ↔ ∀ n ∈ N, σ n v = v := Iff.rfl

instance isModularLattice_subrepresentation (σ : Representation k Γ M) :
    IsModularLattice (Subrepresentation σ) where
  sup_inf_le_assoc_of_le {x} y {z} hxz := by
    intro v hv
    have h1 : v ∈ (x.toSubmodule ⊔ y.toSubmodule) ⊓ z.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, ← Subrepresentation.toSubmodule_inf]
      exact hv
    have h2 : (x.toSubmodule ⊔ y.toSubmodule) ⊓ z.toSubmodule ≤
        x.toSubmodule ⊔ y.toSubmodule ⊓ z.toSubmodule :=
      sup_inf_le_assoc_of_le y.toSubmodule hxz
    have h3 := h2 h1
    rw [← Subrepresentation.toSubmodule_inf, ← Subrepresentation.toSubmodule_sup] at h3
    exact h3

variable [Finite Γ] [Finite M] [NeZero (Nat.card Γ : k)]

instance finite_subrepresentation (σ : Representation k Γ M) : Finite (Subrepresentation σ) :=
  Finite.of_injective (fun W : Subrepresentation σ => (W : Set M)) SetLike.coe_injective

theorem exists_atom_nontrivial_le (σ : Representation k Γ M) (N : Subgroup Γ) [N.Normal]
    (U : Subrepresentation σ) (h : ∃ n ∈ N, ∃ v ∈ U, σ n v ≠ v) :
    ∃ W : Subrepresentation σ, IsAtom W ∧ W ≤ U ∧ ∃ n ∈ N, ∃ w ∈ W, σ n w ≠ w := by
  obtain ⟨C, hC⟩ := ComplementedLattice.exists_isCompl (fixedSub σ N ⊓ U)
  have hU : U = (fixedSub σ N ⊓ U) ⊔ (U ⊓ C) := by
    have h1 : (fixedSub σ N ⊓ U) ⊔ C = ⊤ := hC.sup_eq_top
    have h2 : (fixedSub σ N ⊓ U ⊔ C) ⊓ U = fixedSub σ N ⊓ U ⊔ C ⊓ U :=
      sup_inf_assoc_of_le C inf_le_right
    rw [h1, top_inf_eq] at h2
    rw [inf_comm U C]
    exact h2
  have hne : U ⊓ C ≠ ⊥ := by
    intro h0
    rw [h0, sup_bot_eq] at hU
    obtain ⟨n, hn, v, hv, hnv⟩ := h
    apply hnv
    have : v ∈ fixedSub σ N ⊓ U := by rw [← hU]; exact hv
    exact this.1 n hn
  obtain ⟨W, hWatom, hWle⟩ := (eq_bot_or_exists_atom_le (U ⊓ C)).resolve_left hne
  refine ⟨W, hWatom, hWle.trans inf_le_left, ?_⟩
  by_contra hcon
  push Not at hcon
  have hW0 : W ≤ fixedSub σ N := fun w hw n hn => hcon n hn w hw
  have : W ≤ (fixedSub σ N ⊓ U) ⊓ C :=
    le_inf (le_inf hW0 (hWle.trans inf_le_left)) (hWle.trans inf_le_right)
  rw [hC.inf_eq_bot, le_bot_iff] at this
  exact hWatom.1 this

theorem exists_atom_nontrivial (σ : Representation k Γ M) (N : Subgroup Γ) [N.Normal]
    (h : ∃ n ∈ N, ∃ v, σ n v ≠ v) :
    ∃ W : Subrepresentation σ, IsAtom W ∧ ∃ n ∈ N, ∃ w ∈ W, σ n w ≠ w := by
  obtain ⟨n, hn, v, hv⟩ := h
  obtain ⟨W, hW, -, hW'⟩ := exists_atom_nontrivial_le σ N ⊤ ⟨n, hn, v, Submodule.mem_top, hv⟩
  exact ⟨W, hW, hW'⟩

end Atoms

section Irreducible

variable {k : Type*} [Field k] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module k M]

theorem isIrreducible_of_isAtom (σ : Representation k Γ M) {W : Subrepresentation σ}
    (hW : IsAtom W) : W.toRepresentation.IsIrreducible := by
  have hne : (⊥ : Subrepresentation W.toRepresentation) ≠ ⊤ := by
    intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show W.toSubmodule ≠ ⊥ from fun h' => hW.1 (Subrepresentation.ext h'))
    have h1 : (⟨w, hw⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation) :=
      Submodule.mem_top
    rw [← h] at h1
    have h2 : (⟨w, hw⟩ : W.toSubmodule) = 0 := (Submodule.mem_bot k).mp h1
    exact hw0 (congrArg Subtype.val h2)
  have : Nontrivial (Subrepresentation W.toRepresentation) := ⟨⟨⊥, ⊤, hne⟩⟩
  refine { eq_bot_or_eq_top := fun U => ?_ }
  let Ũ : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
      apply_mem_toSubmodule := fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨W.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  have hŨle : Ũ ≤ W := fun v hv => by
    obtain ⟨u, -, rfl⟩ := hv
    exact u.2
  rcases hW.le_iff.mp hŨle with h0 | h1
  · left
    refine Subrepresentation.ext ?_
    have : U.toSubmodule.map W.toSubmodule.subtype = ⊥ :=
      congrArg Subrepresentation.toSubmodule h0
    exact Submodule.map_injective_of_injective W.toSubmodule.injective_subtype
      (this.trans (Submodule.map_bot _).symm)
  · right
    refine Subrepresentation.ext ?_
    have : U.toSubmodule.map W.toSubmodule.subtype = W.toSubmodule :=
      congrArg Subrepresentation.toSubmodule h1
    refine Submodule.map_injective_of_injective W.toSubmodule.injective_subtype ?_
    change _ = Submodule.map W.toSubmodule.subtype (⊤ : Submodule k W.toSubmodule)
    rw [this, Submodule.map_top, Submodule.range_subtype]

end Irreducible


section Faithful

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem faithful_of_nontrivial
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (σ : Representation k (S ⋊[φ] A) M) (W : Subrepresentation σ)
    (hnt : ∃ s : S, ∃ w ∈ W, σ (inl s) w ≠ w) :
    ∀ s : S, (∀ w ∈ W, σ (inl s) w = w) → s = 1 := by
  have hone : ∀ (g : S ⋊[φ] A), g = 1 → ∀ w : M, σ g w = w := by
    rintro g rfl w
    rw [map_one]
    rfl
  let U : Subgroup S :=
    { carrier := {s | ∀ w ∈ W, σ (inl s) w = w}
      mul_mem' := fun {a b} ha hb w hw => by
        have h1 : (inl (a * b) : S ⋊[φ] A) = inl a * inl b := map_mul _ _ _
        rw [h1, map_mul, Module.End.mul_apply, hb w hw, ha w hw]
      one_mem' := fun w _ => hone _ (map_one _) w
      inv_mem' := fun {a} ha w hw => by
        have h := ha w hw
        have h1 : (inl a⁻¹ * inl a : S ⋊[φ] A) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        calc σ (inl a⁻¹) w = σ (inl a⁻¹) (σ (inl a) w) := by rw [h]
          _ = σ (inl a⁻¹ * inl a) w := by rw [map_mul, Module.End.mul_apply]
          _ = w := hone _ h1 w }
  have hU : ∀ a : A, ∀ x ∈ U, φ a x ∈ U := by
    intro a x hx w hw
    have h1 : (inl (φ a x) : S ⋊[φ] A) = inr a * inl x * (inr a)⁻¹ := by
      rw [inl_aut, map_inv]
    have hw' : σ (inr a)⁻¹ w ∈ W := W.apply_mem_toSubmodule (inr a)⁻¹ hw
    have h2 : (inr a * (inr a)⁻¹ : S ⋊[φ] A) = 1 := mul_inv_cancel _
    calc σ (inl (φ a x)) w = σ (inr a) (σ (inl x) (σ (inr a)⁻¹ w)) := by
          rw [h1, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = σ (inr a) (σ (inr a)⁻¹ w) := by rw [hx _ hw']
      _ = σ (inr a * (inr a)⁻¹) w := by rw [map_mul, Module.End.mul_apply]
      _ = w := hone _ h2 w
  rcases hirr U hU with h | h
  · intro s hs
    have : s ∈ U := hs
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨s, w, hw, hne⟩ := hnt
    have : s ∈ U := by rw [h]; exact Subgroup.mem_top s
    exact hne (this w hw)

end Faithful

section SB

variable {q : ℕ} [Fact q.Prime] {M : Type*} [AddCommGroup M] [Module (ZMod q) M]

theorem finrank_eigenspace_toRepresentation {Γ : Type*} [Group Γ] [Finite M]
    (σ : Representation (ZMod q) Γ M) (W : Subrepresentation σ) (g : Γ) :
    Module.finrank (ZMod q) ↥(Module.End.eigenspace (W.toRepresentation g) 1) =
      Module.finrank (ZMod q) ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ g) 1) := by
  have h : (Module.End.eigenspace (W.toRepresentation g) 1).map W.toSubmodule.subtype =
      W.toSubmodule ⊓ Module.End.eigenspace (σ g) 1 := by
    ext m
    simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, one_smul, Submodule.mem_inf,
      Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val hw⟩
    · rintro ⟨hm, hσ⟩
      exact ⟨⟨m, hm⟩, Subtype.ext hσ, rfl⟩
  rw [← h]
  exact (Submodule.finrank_map_subtype_eq W.toSubmodule _).symm

theorem eq_of_neg_one_pow_val_eq {K : Type*} [Field K] (hK : (2 : K) ≠ 0) {x y : ZMod 2}
    (h : (-1 : K) ^ ZMod.val x = (-1) ^ ZMod.val y) : x = y := by
  have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
  have h0 : ZMod.val (0 : ZMod 2) = 0 := rfl
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) x with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) y with rfl | rfl
  · rfl
  · exfalso
    apply hK
    rw [h1, h0] at h
    linear_combination h
  · exfalso
    apply hK
    rw [h1, h0] at h
    linear_combination -h
  · rfl

variable {S : Type*} [Group S] [Finite S] [IsElementaryAbelian 2 S] {A : Type*} [Group A]
  {φ : A →* MulAut S} [Finite M]

theorem sb_of_atom {p d : ℕ} (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) (hS : Nat.card S = 2 ^ d)
    (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq2 : (2 : ZMod q) ≠ 0) (σ : Representation (ZMod q) (S ⋊[φ] A) M)
    {W : Subrepresentation σ} (hW : IsAtom W)
    (hfaith : ∀ s : S, (∀ w ∈ W, σ (inl s) w = w) → s = 1) :
    ∃ e : ℕ, 1 ≤ e ∧ Module.finrank (ZMod q) W.toSubmodule = p * e ∧
      (p = 7 → ∀ s : S, s ≠ 1 → Module.finrank (ZMod q)
        ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 * e) ∧
      (p = 5 →
        Set.ncard {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 * e} = 10 ∧
        Set.ncard {s : S | s ≠ 1 ∧ Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = e} = 5 ∧
        ∀ s : S, s ≠ 1 → Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = 3 * e ∨
          Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) = e) ∧
      ((∀ s : S, s ≠ 1 → Module.finrank (ZMod q)
          ↥(W.toSubmodule ⊓ Module.End.eigenspace (σ (inl s)) 1) ≤ 4) → e = 1) ∧
      (e = 1 → ∃ (n : ℕ) (v : Fin n → M) (c : Fin n → S → ZMod q),
        (∀ i, v i ∈ W.toSubmodule) ∧ (∀ i, v i ≠ 0) ∧
        W.toSubmodule ≤ Submodule.span (ZMod q) (Set.range v) ∧
        (∀ i s, σ (inl s) (v i) = c i s • v i) ∧ (∀ i s, c i s = 1 ∨ c i s = -1) ∧
        (∀ i j, i ≠ j → ∃ s, c i s ≠ c j s)) := by
  let _ : CommGroup S := IsMulCommutative.instCommGroup
  let _ : Module (ZMod 2) (Additive S) := IsElementaryAbelian.isVectorSpace 2
  have hρ := isIrreducible_of_isAtom σ hW
  have hinj : Function.Injective (W.toRepresentation.comp (inl : S →* S ⋊[φ] A)) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    apply hfaith
    intro w hw
    have := congrArg (fun f => f ⟨w, hw⟩) hs
    exact congrArg Subtype.val this
  obtain ⟨-, -, e, he1, hwt, hdim, h7, h5, hle⟩ :=
    small_binary_prime_orbit_fixed_space_counts hpd hS hφ hirr hq2 W.toRepresentation hρ hinj
  simp only [finrank_eigenspace_toRepresentation] at h7 h5 hle
  refine ⟨e, he1, hdim, h7, h5, fun h => (hle h).1, fun he => ?_⟩
  subst he
  classical
  have : Fintype S := Fintype.ofFinite S
  have hfinD : Finite (Module.Dual (ZMod 2) (Additive S)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive S) => (f : Additive S → ZMod 2))
      DFunLike.coe_injective
  have : Fintype (Module.Dual (ZMod 2) (Additive S)) := Fintype.ofFinite _
  set ρS : Representation (ZMod q) S W.toSubmodule :=
    W.toRepresentation.comp (inl : S →* S ⋊[φ] A) with hρS
  have htop : ⨆ χ, signWeightSpace ρS χ = ⊤ := iSup_signWeightSpace_eq_top ρS hq2
  let ι := {χ : Module.Dual (ZMod 2) (Additive S) // signWeightSpace ρS χ ≠ ⊥}
  have hex : ∀ χ : ι, ∃ w : W.toSubmodule, w ∈ signWeightSpace ρS χ ∧ w ≠ 0 :=
    fun χ => Submodule.exists_mem_ne_zero_of_ne_bot χ.2
  choose w hwmem hw0 using hex
  have hline : ∀ χ : ι, signWeightSpace ρS χ ≤ Submodule.span (ZMod q) {w χ} := by
    intro χ x hx
    have h1 : Module.finrank (ZMod q) ↥(signWeightSpace ρS χ) = 1 := hwt χ χ.2
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨w χ, hwmem χ⟩ : ↥(signWeightSpace ρS χ))
      (fun h => hw0 χ (congrArg Subtype.val h))).mp h1 ⟨x, hx⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  have hspan : (⊤ : Submodule (ZMod q) W.toSubmodule) ≤ Submodule.span (ZMod q) (Set.range w) := by
    rw [← htop]
    refine iSup_le fun χ => ?_
    by_cases hχ : signWeightSpace ρS χ = ⊥
    · rw [hχ]; exact bot_le
    · exact (hline ⟨χ, hχ⟩).trans (Submodule.span_mono (by simp))
  let e₀ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => ((w (e₀.symm i) : W.toSubmodule) : M),
    fun i s => (-1 : ZMod q) ^ ZMod.val ((e₀.symm i).1 (Additive.ofMul s)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (w (e₀.symm i)).2
  · intro i h
    exact hw0 (e₀.symm i) (Subtype.ext h)
  · intro m hm
    have h1 : (⟨m, hm⟩ : W.toSubmodule) ∈ Submodule.span (ZMod q) (Set.range w) :=
      hspan Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := W.toSubmodule.subtype) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨χ, rfl⟩, rfl⟩
    exact ⟨e₀ χ, by simp⟩
  · intro i s
    have h := (mem_signWeightSpace ρS (e₀.symm i).1 (w (e₀.symm i))).mp (hwmem (e₀.symm i)) s
    have h' := congrArg (fun x : W.toSubmodule => (x : M)) h
    exact h'
  · intro i s
    exact neg_one_pow_eq_or (ZMod q) _
  · intro i j hij
    by_contra hcon
    push Not at hcon
    apply hij
    have hχ : (e₀.symm i).1 = (e₀.symm j).1 := by
      refine LinearMap.ext fun x => ?_
      obtain ⟨s, rfl⟩ : ∃ s : S, Additive.ofMul s = x := ⟨Additive.toMul x, rfl⟩
      have h := hcon s
      exact eq_of_neg_one_pow_val_eq hq2 h
    have : e₀.symm i = e₀.symm j := Subtype.ext hχ
    exact e₀.symm.injective this

end SB

end CFSG.RankThree.PartOne.Lifting36
