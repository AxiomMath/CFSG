module

public import CFSG.Sporadic.Th.Recog.A9Mod.Bits

public section

local instance (priority := high) CFSG.Sporadic.Th.Recog.A9Mod.instAddCommGroupZMod2NormalForm :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.Sporadic.Th.Recog.A9Mod

open Module

@[expose] def mulX (c : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := ![c 5, c 0, c 1, c 2 + c 5, c 3, c 4]

theorem mulX_generates : ∀ c : Fin 6 → ZMod 2, c ≠ 0 → ∃ a : Fin 6 → ZMod 2,
    ∑ k : Fin 6, a k • mulX^[k] c = Pi.single 0 1 := by
  decide +kernel

theorem mulX_iterate_six : ∀ a : Fin 6 → ZMod 2, mulX^[6] a = mulX^[3] a + a := by
  decide +kernel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def evalPoly (T : V →ₗ[ZMod 2] V) (u : V) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] V where
  toFun a := a 0 • u + a 1 • T u + a 2 • (T ^ 2) u + a 3 • (T ^ 3) u + a 4 • (T ^ 4) u +
    a 5 • (T ^ 5) u
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem evalPoly_apply (T : V →ₗ[ZMod 2] V) (u : V) (a : Fin 6 → ZMod 2) :
    evalPoly T u a = a 0 • u + a 1 • T u + a 2 • (T ^ 2) u + a 3 • (T ^ 3) u +
      a 4 • (T ^ 4) u + a 5 • (T ^ 5) u := rfl

theorem apply_pow_apply (T : V →ₗ[ZMod 2] V) (k : ℕ) (x : V) :
    T ((T ^ k) x) = (T ^ (k + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

theorem evalPoly_mulX (T : V →ₗ[ZMod 2] V) (u : V) (hu : (T ^ 6) u = (T ^ 3) u + u)
    (a : Fin 6 → ZMod 2) : evalPoly T u (mulX a) = T (evalPoly T u a) := by
  have e0 : mulX a 0 = a 5 := rfl
  have e1 : mulX a 1 = a 0 := rfl
  have e2 : mulX a 2 = a 1 := rfl
  have e3 : mulX a 3 = a 2 + a 5 := rfl
  have e4 : mulX a 4 = a 3 := rfl
  have e5 : mulX a 5 = a 4 := rfl
  have h2 : T (T u) = (T ^ 2) u := by rw [sq, Module.End.mul_apply]
  rw [evalPoly_apply, evalPoly_apply, e0, e1, e2, e3, e4, e5]
  simp only [map_add, map_smul]
  rw [h2, apply_pow_apply T 2, apply_pow_apply T 3, apply_pow_apply T 4, apply_pow_apply T 5, hu,
    add_smul, smul_add]
  abel

theorem evalPoly_iterate (T : V →ₗ[ZMod 2] V) (u : V) (hu : (T ^ 6) u = (T ^ 3) u + u) (k : ℕ)
    (c : Fin 6 → ZMod 2) : evalPoly T u (mulX^[k] c) = (T ^ k) (evalPoly T u c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', evalPoly_mulX T u hu, ih, apply_pow_apply]

theorem evalPoly_single (T : V →ₗ[ZMod 2] V) (u : V) : evalPoly T u (Pi.single 0 1) = u := by
  simp [evalPoly_apply, Pi.single_apply]

theorem mem_of_evalPoly (T : V →ₗ[ZMod 2] V) (u : V) (hu : (T ^ 6) u = (T ^ 3) u + u)
    (W : Submodule (ZMod 2) V) (hW : ∀ x ∈ W, T x ∈ W) {c : Fin 6 → ZMod 2} (hc : c ≠ 0)
    (hcW : evalPoly T u c ∈ W) : u ∈ W := by
  obtain ⟨a, ha⟩ := mulX_generates c hc
  rw [← evalPoly_single T u, ← ha, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul, evalPoly_iterate T u hu]
  exact W.smul_mem _ (Module.End.pow_apply_mem_of_forall_mem _ hW _ hcW)

theorem evalPoly_injective (T : V →ₗ[ZMod 2] V) (u : V) (hu : (T ^ 6) u = (T ^ 3) u + u)
    (hu0 : u ≠ 0) : Function.Injective (evalPoly T u) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  by_contra hc0
  refine hu0 ((Submodule.mem_bot (ZMod 2)).1 (mem_of_evalPoly T u hu ⊥ ?_ hc0 ?_))
  · intro x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
    exact Submodule.zero_mem _
  · rw [LinearMap.mem_ker] at hc
    rw [hc]
    exact Submodule.zero_mem _

theorem equivFun_toLin (b : Basis (Fin 8) (ZMod 2) V) (T : V →ₗ[ZMod 2] V) (N : Array ℕ)
    (hT : ∀ j, b.equivFun (T (b j)) = bv (N.getD j 0)) (x : V) :
    b.equivFun (T x) = toLin N (b.equivFun x) := by
  have : b.equivFun.toLinearMap ∘ₗ T = toLin N ∘ₗ b.equivFun.toLinearMap := b.ext fun j => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hT]
    rw [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single, toLin_single]
  exact LinearMap.congr_fun this x

theorem exists_nf (hV : Module.finrank (ZMod 2) V = 8) (T : V →ₗ[ZMod 2] V) (h9 : T ^ 9 = 1)
    (h3 : T ^ 3 ≠ 1) :
    ∃ e : V ≃ₗ[ZMod 2] V8, (∀ v, e (T v) = toLin N1 (e v)) ∨ (∀ v, e (T v) = toLin N2 (e v)) := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have hTT : ∀ (a b : ℕ) (x : V), (T ^ a) ((T ^ b) x) = (T ^ (a + b)) x := fun a b x => by
    rw [pow_add, Module.End.mul_apply]
  have h9x : ∀ x, (T ^ 9) x = x := fun x => by rw [h9, Module.End.one_apply]
  have h33 : ∀ x, (T ^ 3) ((T ^ 3) x) = (T ^ 6) x := fun x => hTT 3 3 x
  have h36 : ∀ x, (T ^ 3) ((T ^ 6) x) = x := fun x => (hTT 3 6 x).trans (h9x x)
  have h63 : ∀ x, (T ^ 6) ((T ^ 3) x) = x := fun x => (hTT 6 3 x).trans (h9x x)
  have h66 : ∀ x, (T ^ 6) ((T ^ 6) x) = (T ^ 3) x := fun x =>
    (hTT 6 6 x).trans ((hTT 3 9 x).symm.trans (by rw [h9x]))
  have hcomm : ∀ (a : ℕ) (x : V), (T ^ a) (T x) = T ((T ^ a) x) := fun a x => by
    have := hTT a 1 x
    rw [pow_one] at this
    rw [this, apply_pow_apply]
  have hTinj : ∀ x : V, T x = 0 → x = 0 := fun x hx => by
    have := hTT 8 1 x
    rw [pow_one, hx, map_zero] at this
    exact (this.trans (h9x x)).symm
  set KA : Submodule (ZMod 2) V := LinearMap.ker (T ^ 3 - 1) with hKA
  set KB : Submodule (ZMod 2) V := LinearMap.ker (T ^ 6 - T ^ 3 - 1) with hKB
  have mKA : ∀ x, x ∈ KA ↔ (T ^ 3) x = x := fun x => by
    rw [hKA, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have mKB : ∀ x, x ∈ KB ↔ (T ^ 6) x = (T ^ 3) x + x := fun x => by
    rw [hKB, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
      sub_sub, sub_eq_zero]
  have hKAinv : ∀ x ∈ KA, T x ∈ KA := fun x hx => by
    rw [mKA] at hx ⊢
    rw [hcomm, hx]
  have hKBinv : ∀ x ∈ KB, T x ∈ KB := fun x hx => by
    rw [mKB] at hx ⊢
    rw [hcomm, hcomm, hx, map_add]
  have hcompl : IsCompl KA KB := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxA hxB
      rw [mKA] at hxA
      rw [mKB, hxA] at hxB
      have h6 : (T ^ 6) x = x := by rw [← h33, hxA, hxA]
      rw [h6, ZModModule.add_self] at hxB
      exact hxB
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨(T ^ 6) x + (T ^ 3) x + x, ?_, (T ^ 6) x + (T ^ 3) x, ?_, ?_⟩
      · rw [mKA, map_add, map_add, h36, h33]
        abel
      · rw [mKB, map_add, map_add, h66, h63, h36, h33]
        calc (T ^ 3) x + x = (T ^ 3) x + x + ((T ^ 6) x + (T ^ 6) x) := by
              rw [ZModModule.add_self, add_zero]
          _ = x + (T ^ 6) x + ((T ^ 6) x + (T ^ 3) x) := by abel
      · calc (T ^ 6) x + (T ^ 3) x + x + ((T ^ 6) x + (T ^ 3) x)
            = ((T ^ 6) x + (T ^ 6) x) + ((T ^ 3) x + (T ^ 3) x) + x := by abel
          _ = x := by rw [ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]
  obtain ⟨v0, hv0⟩ : ∃ v0, (T ^ 3) v0 ≠ v0 := by
    by_contra h
    push Not at h
    exact h3 (LinearMap.ext fun x => by rw [h x, Module.End.one_apply])
  set v := (T ^ 3) v0 - v0 with hv
  have hvB : (T ^ 6) v = (T ^ 3) v + v := by
    rw [hv, map_sub, map_sub, h63, h33, ← neg_sub ((T ^ 6) v0) v0, ZModModule.neg_eq_self]
    abel
  have hv0' : v ≠ 0 := sub_ne_zero.2 hv0
  have hvKB : v ∈ KB := (mKB v).2 hvB
  set R := LinearMap.range (evalPoly T v) with hR
  have hRinv : ∀ x ∈ R, T x ∈ R := by
    rintro _ ⟨a, rfl⟩
    exact ⟨mulX a, evalPoly_mulX T v hvB a⟩
  have hRKB : R ≤ KB := by
    rintro _ ⟨a, rfl⟩
    rw [mKB, ← evalPoly_iterate T v hvB 6, ← evalPoly_iterate T v hvB 3, mulX_iterate_six,
      map_add]
  have hR6 : finrank (ZMod 2) R = 6 := by
    rw [hR, LinearMap.finrank_range_of_inj (evalPoly_injective T v hvB hv0')]
    simp
  have hKB6 : finrank (ZMod 2) KB = 6 := by
    have h1 := Submodule.finrank_mono hRKB
    rw [hR6] at h1
    by_contra hne6
    have hlt : R < KB := lt_of_le_of_ne hRKB fun h => hne6 (by rw [← h]; exact hR6)
    obtain ⟨w, hwKB, hwR⟩ := SetLike.exists_of_lt hlt
    have hw : (T ^ 6) w = (T ^ 3) w + w := (mKB w).1 hwKB
    have hw0 : w ≠ 0 := fun h => hwR (h ▸ R.zero_mem)
    have hR'6 : finrank (ZMod 2) (LinearMap.range (evalPoly T w)) = 6 := by
      rw [LinearMap.finrank_range_of_inj (evalPoly_injective T w hw hw0)]
      simp
    have hdisj : R ⊓ LinearMap.range (evalPoly T w) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxR, c, rfl⟩
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd (mem_of_evalPoly T w hw R hRinv hc hxR) hwR
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq R (LinearMap.range (evalPoly T w))
    rw [hdisj, finrank_bot, hR6, hR'6] at h2
    have h3 := Submodule.finrank_le (R ⊔ LinearMap.range (evalPoly T w))
    omega
  have hKA2 : finrank (ZMod 2) KA = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  let g : Fin 6 → V := ![v, T v, (T ^ 2) v, (T ^ 3) v, (T ^ 4) v, (T ^ 5) v]
  have hg : LinearIndependent (ZMod 2) g := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have : evalPoly T v a = 0 := by
      rw [← ha, Fin.sum_univ_six]
      rfl
    have h0 := evalPoly_injective T v hvB hv0' (this.trans (map_zero _).symm)
    exact fun i => congrFun h0 i
  have hgKB : Submodule.span (ZMod 2) (Set.range g) ≤ KB := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    fin_cases k
    · exact hvKB
    · exact hKBinv _ hvKB
    · exact Module.End.pow_apply_mem_of_forall_mem 2 hKBinv v hvKB
    · exact Module.End.pow_apply_mem_of_forall_mem 3 hKBinv v hvKB
    · exact Module.End.pow_apply_mem_of_forall_mem 4 hKBinv v hvKB
    · exact Module.End.pow_apply_mem_of_forall_mem 5 hKBinv v hvKB
  have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  obtain ⟨w1, w2, hw1, hw2, hli2, N, hN, hTw1, hTw2⟩ : ∃ w1 w2 : V, w1 ∈ KA ∧ w2 ∈ KA ∧
      LinearIndependent (ZMod 2) ![w1, w2] ∧ ∃ N : Array ℕ, (N = N1 ∨ N = N2) ∧
        (N = N1 → T w1 = w2 ∧ T w2 = w1 + w2) ∧ (N = N2 → T w1 = w1 ∧ T w2 = w2) := by
    by_cases hfix : ∀ x ∈ KA, T x = x
    · let bKA := Module.finBasisOfFinrankEq (ZMod 2) KA hKA2
      refine ⟨bKA 0, bKA 1, (bKA 0).2, (bKA 1).2, ?_, N2, Or.inr rfl, fun h => ?_,
        fun _ => ⟨hfix _ (bKA 0).2, hfix _ (bKA 1).2⟩⟩
      · have := bKA.linearIndependent.map' KA.subtype (Submodule.ker_subtype KA)
        convert this using 1
        funext i
        fin_cases i <;> rfl
      · exact absurd h (by decide)
    · push Not at hfix
      obtain ⟨u, huKA, hTu⟩ := hfix
      have hu3 : (T ^ 3) u = u := (mKA u).1 huKA
      have hw : T u - u ∈ KA := KA.sub_mem (hKAinv u huKA) huKA
      have hT2w : T (T (T u - u)) = (T u - u) + T (T u - u) := by
        have e1 : T (T u) = (T ^ 2) u := by rw [sq, Module.End.mul_apply]
        have e2 : T ((T ^ 2) u) = u := (apply_pow_apply T 2 u).trans hu3
        simp only [map_sub]
        rw [e1, e2, ← neg_sub ((T ^ 2) u) u, ZModModule.neg_eq_self]
        abel
      refine ⟨T u - u, T (T u - u), hw, hKAinv _ hw, ?_, N1, Or.inl rfl,
        fun _ => ⟨rfl, hT2w⟩, fun h => absurd h (by decide)⟩
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hw0 : T u - u ≠ 0 := sub_ne_zero.2 hTu
      rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst
        exact absurd (hTinj _ hst) hw0
      · rw [zero_smul, one_smul, add_zero] at hst
        exact absurd hst hw0
      · rw [one_smul, one_smul] at hst
        exfalso
        have hTw : T (T u - u) = T u - u := by
          rw [eq_neg_of_add_eq_zero_right hst, ZModModule.neg_eq_self]
        rw [hTw, hTw, ZModModule.add_self] at hT2w
        exact hw0 hT2w
  have hdisj : Disjoint (Submodule.span (ZMod 2) (Set.range g))
      (Submodule.span (ZMod 2) (Set.range ![w1, w2])) := by
    refine Disjoint.mono hgKB ?_ hcompl.disjoint.symm
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact hw1
    · exact hw2
  have hli : LinearIndependent (ZMod 2) (Sum.elim g ![w1, w2] ∘ finSumFinEquiv.symm) :=
    (hg.sum_type hli2 hdisj).comp _ finSumFinEquiv.symm.injective
  let f : Fin 8 → V := ![v, T v, (T ^ 2) v, (T ^ 3) v, (T ^ 4) v, (T ^ 5) v, w1, w2]
  have hf : f = Sum.elim g ![w1, w2] ∘ finSumFinEquiv.symm := by
    funext i
    fin_cases i <;> rfl
  have hlif : LinearIndependent (ZMod 2) f := by
    rw [hf]
    exact hli
  let b := basisOfLinearIndependentOfCardEqFinrank hlif (by simp [hV])
  have hb : ∀ i, b i = f i := fun i => by simp [b]
  have hbe : ∀ i, b.equivFun (f i) = Pi.single i 1 := fun i => by
    rw [← hb, Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single]
  have e1 : T (f 0) = f 1 := rfl
  have e2 : T (f 1) = f 2 := by
    show T (T v) = (T ^ 2) v
    rw [sq, Module.End.mul_apply]
  have e3 : T (f 2) = f 3 := apply_pow_apply T 2 v
  have e4 : T (f 3) = f 4 := apply_pow_apply T 3 v
  have e5 : T (f 4) = f 5 := apply_pow_apply T 4 v
  have e6 : T (f 5) = f 3 + f 0 := (apply_pow_apply T 5 v).trans hvB
  refine ⟨b.equivFun, ?_⟩
  rcases hN with rfl | rfl
  · left
    obtain ⟨hT1, hT2⟩ := hTw1 rfl
    have e7 : T (f 6) = f 7 := hT1
    have e8 : T (f 7) = f 6 + f 7 := hT2
    refine equivFun_toLin b T N1 fun j => ?_
    rw [hb]
    fin_cases j
    · exact (congrArg b.equivFun e1).trans ((hbe 1).trans (by decide +kernel))
    · exact (congrArg b.equivFun e2).trans ((hbe 2).trans (by decide +kernel))
    · exact (congrArg b.equivFun e3).trans ((hbe 3).trans (by decide +kernel))
    · exact (congrArg b.equivFun e4).trans ((hbe 4).trans (by decide +kernel))
    · exact (congrArg b.equivFun e5).trans ((hbe 5).trans (by decide +kernel))
    · exact (congrArg b.equivFun e6).trans (by rw [map_add, hbe, hbe]; decide +kernel)
    · exact (congrArg b.equivFun e7).trans ((hbe 7).trans (by decide +kernel))
    · exact (congrArg b.equivFun e8).trans (by rw [map_add, hbe, hbe]; decide +kernel)
  · right
    obtain ⟨hT1, hT2⟩ := hTw2 rfl
    have e7 : T (f 6) = f 6 := hT1
    have e8 : T (f 7) = f 7 := hT2
    refine equivFun_toLin b T N2 fun j => ?_
    rw [hb]
    fin_cases j
    · exact (congrArg b.equivFun e1).trans ((hbe 1).trans (by decide +kernel))
    · exact (congrArg b.equivFun e2).trans ((hbe 2).trans (by decide +kernel))
    · exact (congrArg b.equivFun e3).trans ((hbe 3).trans (by decide +kernel))
    · exact (congrArg b.equivFun e4).trans ((hbe 4).trans (by decide +kernel))
    · exact (congrArg b.equivFun e5).trans ((hbe 5).trans (by decide +kernel))
    · exact (congrArg b.equivFun e6).trans (by rw [map_add, hbe, hbe]; decide +kernel)
    · exact (congrArg b.equivFun e7).trans ((hbe 6).trans (by decide +kernel))
    · exact (congrArg b.equivFun e8).trans ((hbe 7).trans (by decide +kernel))

end CFSG.Sporadic.Th.Recog.A9Mod
