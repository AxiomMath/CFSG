module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private instance : AddCommGroup d6SumZero := Submodule.addCommGroup d6SumZero

private def ggQ2d6l_vec (a b : Fin 6) : Fin 6 → ZMod 3 :=
  Pi.single a 1 - Pi.single b 1

private lemma d6Vec_mem (a b : Fin 6) : ggQ2d6l_vec a b ∈ d6SumZero := by
  rw [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply]
  simp only [ggQ2d6l_vec, LinearMap.proj_apply, Pi.sub_apply, Pi.single_apply]
  have h : (∑ d : Fin 6, ((if d = a then (1 : ZMod 3) else 0) -
      (if d = b then (1 : ZMod 3) else 0)))
      = (∑ d : Fin 6, (if d = a then (1 : ZMod 3) else 0)) -
        (∑ d : Fin 6, (if d = b then (1 : ZMod 3) else 0)) :=
    Finset.sum_sub_distrib (s := Finset.univ) _ _
  rw [h]
  simp

private abbrev ggQ2d6l_pairIndep {M : Type} [AddCommGroup M] [Module (ZMod 3) M]
    (x y : M) : Prop := x ≠ 0 ∧ ∀ a : ZMod 3, a • x ≠ y

private abbrev ggQ2d6l_pairIndepFun (x y : Fin 6 → ZMod 3) : Prop :=
  x ≠ 0 ∧ ∀ a : ZMod 3, a • x ≠ y

private lemma pairIndep_comb {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {x y : V} (h : ggQ2d6l_pairIndep x y) {s t s' t' : ZMod 3}
    (heq : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' := by
  have hy0 : y ≠ 0 := by
    have h0 := h.2 0
    rw [zero_smul] at h0
    exact fun hy => h0 hy.symm
  have hax : (s - s') • x = (t' - t) • y := by
    have hsub : (s - s') • x - (t' - t) • y = 0 := by
      rw [sub_smul, sub_smul, sub_eq_zero]
      calc s • x - s' • x = (s • x + t • y) - (s' • x + t • y) := by abel
        _ = t' • y - t • y := by rw [heq]; abel
    exact sub_eq_zero.mp hsub
  by_cases ha : s - s' = 0
  · have hs : s = s' := sub_eq_zero.mp ha
    have hb : t' - t = 0 := by
      rw [ha, zero_smul] at hax
      rcases (smul_eq_zero.mp hax.symm) with h | h
      · exact h
      · exact absurd h hy0
    exact ⟨hs, (sub_eq_zero.mp hb).symm⟩
  · have hbne : t' - t ≠ 0 := by
      intro hb
      rw [hb, zero_smul] at hax
      exact ha ((smul_eq_zero.mp hax).resolve_right h.1)
    have hc : (s - s')⁻¹ * (t' - t) ≠ 0 :=
      mul_ne_zero (inv_ne_zero ha) hbne
    have hx : x = ((s - s')⁻¹ * (t' - t)) • y := by
      calc x = (s - s')⁻¹ • ((s - s') • x) := by rw [inv_smul_smul₀ ha]
        _ = (s - s')⁻¹ • ((t' - t) • y) := by rw [hax]
        _ = ((s - s')⁻¹ * (t' - t)) • y := by rw [mul_smul]
    have hy : y = ((s - s')⁻¹ * (t' - t))⁻¹ • x := by
      rw [hx, ← mul_smul, inv_mul_cancel₀ hc, one_smul]
    have := h.2 ((s - s')⁻¹ * (t' - t))⁻¹
    exact absurd hy.symm this

private abbrev IsTransp (σ : Equiv.Perm (Fin 6)) : Prop :=
  ∃ a b : Fin 6, a ≠ b ∧ σ = Equiv.swap a b

private abbrev D6Pair := {p : Fin 6 × Fin 6 // p.1 ≠ p.2}

private def d6PairVec (p : D6Pair) : Fin 6 → ZMod 3 := ggQ2d6l_vec p.1.1 p.1.2

private lemma d6PairVec_mem (p : D6Pair) : d6PairVec p ∈ d6SumZero :=
  d6Vec_mem p.1.1 p.1.2

private lemma d6_indep_witness_all :
    ∀ σ : Equiv.Perm (Fin 6), σ ≠ 1 → ¬ IsTransp σ →
      ∃ a : Fin 6, ∃ q : D6Pair, a ≠ σ a ∧
        ggQ2d6l_pairIndepFun (d6PermAct σ (ggQ2d6l_vec a (σ a)) - ggQ2d6l_vec a (σ a))
          (d6PermAct σ (d6PairVec q) - d6PairVec q) := by
  decide +kernel

private lemma d6_indep_witness (σ : Equiv.Perm (Fin 6)) (h1 : σ ≠ 1)
    (ht : ¬ IsTransp σ) :
    ∃ a : Fin 6, ∃ q : D6Pair, a ≠ σ a ∧
      ggQ2d6l_pairIndepFun (d6PermAct σ (ggQ2d6l_vec a (σ a)) - ggQ2d6l_vec a (σ a))
        (d6PermAct σ (d6PairVec q) - d6PairVec q) :=
  d6_indep_witness_all σ h1 ht

private lemma range_card_of_isRefl3 {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Finite V] (g : V ≃ₗ[ZMod 3] V) (h : IsRefl3 g) :
    Nat.card (LinearMap.range (g.toLinearMap - 1)) = 3 := by
  let f : V →ₗ[ZMod 3] V := g.toLinearMap - 1
  let e : {v : V // g v = v} ≃ LinearMap.ker f :=
    { toFun := fun v => ⟨v.1, by
        change (g.toLinearMap - 1) v.1 = 0
        rw [LinearMap.sub_apply]
        simp [v.2]⟩
      invFun := fun v => ⟨v.1, by
        have hv : (g.toLinearMap - 1) v.1 = 0 := v.2
        rw [LinearMap.sub_apply] at hv
        exact sub_eq_zero.1 hv⟩
      left_inv := fun v => by ext; rfl
      right_inv := fun v => by ext; rfl }
  have hcard : Nat.card V =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    have hV := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
    have hq : Nat.card (V ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
      Nat.card_congr (LinearMap.quotKerEquivRange f).toEquiv
    rw [hq] at hV
    exact hV
  change Nat.card (LinearMap.range f) = 3
  have hfix : Nat.card {v : V // g v = v} = Nat.card (LinearMap.ker f) :=
    Nat.card_congr e
  have hfixcard : Nat.card {v : V // g v = v} * 3 = Nat.card V := h.2
  rw [hfix] at hfixcard
  have hpos : 0 < Nat.card (LinearMap.ker f) := Nat.card_pos
  have hmul : Nat.card (LinearMap.ker f) * 3 =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    rw [hfixcard, hcard]
  exact Nat.mul_left_cancel hpos hmul.symm

theorem ggQ2d6l_refl_perm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (Dm : D6Mod V) (σ : Equiv.Perm (Fin 6)) (h : IsRefl3 (Dm.ρ σ)) : σ ∈ ggTransp 6 := by
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hfix : Nat.card {v : V // Dm.ρ σ v = v} = Nat.card V := by
      rw [h1, map_one]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => by simp))
    have hfixcard : Nat.card {v : V // Dm.ρ σ v = v} * 3 = Nat.card V := h.2
    rw [hfix] at hfixcard
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega
  by_contra hnotmem
  have hnot : ¬ IsTransp σ := by
    intro ht
    exact hnotmem (by simpa [IsTransp, ggTransp] using ht)
  obtain ⟨a, q, ha, hind⟩ := d6_indep_witness σ hσ1 hnot
  let u0 : d6SumZero := ⟨ggQ2d6l_vec a (σ a), d6Vec_mem a (σ a)⟩
  let v0 : d6SumZero := ⟨d6PairVec q, d6PairVec_mem q⟩
  let u1 : d6SumZero := ⟨d6PermAct σ (u0 : Fin 6 → ZMod 3), d6PermAct_mem σ u0.2⟩
  let v1 : d6SumZero := ⟨d6PermAct σ (v0 : Fin 6 → ZMod 3), d6PermAct_mem σ v0.2⟩
  let u : d6SumZero := u1 - u0
  let v : d6SumZero := v1 - v0
  let uA : Fin 6 → ZMod 3 := u
  let vA : Fin 6 → ZMod 3 := v
  have huval : (uA : Fin 6 → ZMod 3) =
      d6PermAct σ (ggQ2d6l_vec a (σ a)) - ggQ2d6l_vec a (σ a) := by
    funext i
    change (u1 : Fin 6 → ZMod 3) i - (u0 : Fin 6 → ZMod 3) i =
      (d6PermAct σ (ggQ2d6l_vec a (σ a))) i - (ggQ2d6l_vec a (σ a)) i
    rfl
  have hvval : (vA : Fin 6 → ZMod 3) =
      d6PermAct σ (d6PairVec q) - d6PairVec q := by
    funext i
    change (v1 : Fin 6 → ZMod 3) i - (v0 : Fin 6 → ZMod 3) i =
      (d6PermAct σ (d6PairVec q)) i - (d6PairVec q) i
    rfl
  have huv : ggQ2d6l_pairIndepFun uA vA := by
    rw [huval, hvval]
    exact hind
  let f : V →ₗ[ZMod 3] V := (Dm.ρ σ).toLinearMap - 1
  have hμu : Dm.μ u = Dm.ρ σ (Dm.μ u0) - Dm.μ u0 := by
    change Dm.μ (u1 - u0) = Dm.ρ σ (Dm.μ u0) - Dm.μ u0
    rw [map_sub, Dm.μ_comm σ u0]
  have hμv : Dm.μ v = Dm.ρ σ (Dm.μ v0) - Dm.μ v0 := by
    change Dm.μ (v1 - v0) = Dm.ρ σ (Dm.μ v0) - Dm.μ v0
    rw [map_sub, Dm.μ_comm σ v0]
  have hurange : Dm.μ u ∈ LinearMap.range f := by
    rw [LinearMap.mem_range]
    refine ⟨Dm.μ u0, ?_⟩
    change Dm.ρ σ (Dm.μ u0) - Dm.μ u0 = Dm.μ u
    exact hμu.symm
  have hvrange : Dm.μ v ∈ LinearMap.range f := by
    rw [LinearMap.mem_range]
    refine ⟨Dm.μ v0, ?_⟩
    change Dm.ρ σ (Dm.μ v0) - Dm.μ v0 = Dm.μ v
    exact hμv.symm
  have hμind : ggQ2d6l_pairIndep (M := V) (Dm.μ u) (Dm.μ v) := by
    refine ⟨?_, ?_⟩
    · intro h0
      have hu0 : u = 0 := Dm.μ_inj (by simpa using h0)
      apply huv.1
      simpa [uA] using congrArg Subtype.val hu0
    · intro c hc
      have hcu : c • u = v := Dm.μ_inj (by rw [map_smul]; exact hc)
      apply huv.2 c
      simpa [uA, vA, Submodule.coe_smul] using congrArg Subtype.val hcu
  let F : ZMod 3 × ZMod 3 → LinearMap.range f := fun p =>
    ⟨p.1 • Dm.μ u + p.2 • Dm.μ v, by
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ hurange) (Submodule.smul_mem _ _ hvrange)⟩
  have hF : Function.Injective F := by
    intro p r hpr
    have heq : p.1 • Dm.μ u + p.2 • Dm.μ v =
        r.1 • Dm.μ u + r.2 • Dm.μ v :=
      congrArg Subtype.val hpr
    have hpr' := pairIndep_comb hμind heq
    exact Prod.ext hpr'.1 hpr'.2
  have hle := Nat.card_le_card_of_injective F hF
  have hcard9 : Nat.card (ZMod 3 × ZMod 3) = 9 := by
    rw [Nat.card_prod, Nat.card_zmod]
  have hrange : Nat.card (LinearMap.range f) = 3 := by
    simpa [f] using range_card_of_isRefl3 (Dm.ρ σ) h
  rw [hcard9, hrange] at hle
  omega

end CFSG.StandardType

end
