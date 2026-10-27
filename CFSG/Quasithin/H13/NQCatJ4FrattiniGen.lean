module

public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped commutatorElement

@[expose] noncomputable def normalizerConj {G : Type*} [Group G] (P : Subgroup G) :
    normalizer (P : Set G) →* MulAut P :=
  (MulAut.congr (subgroupOfEquivOfLe (le_normalizer (H := P)))).toMonoidHom.comp
    (MulAut.conjNormal (H := P.subgroupOf (normalizer (P : Set G))))

theorem normalizerConj_apply {G : Type*} [Group G] (P : Subgroup G)
    (n : normalizer (P : Set G)) (x : P) :
    ((normalizerConj P n x : P) : G) = n * x * (n : G)⁻¹ := by
  simp [normalizerConj, MulAut.congr, MulAut.conjNormal_apply, subgroupOfEquivOfLe]

@[expose] noncomputable def normalizerFrattiniAction {G : Type*} [Group G] (P : Subgroup G) :
    normalizer (P : Set G) →* MulAut (P ⧸ frattini P) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P)).comp
    (normalizerConj P)

theorem normalizerFrattiniAction_mk {G : Type*} [Group G] (P : Subgroup G)
    (n : normalizer (P : Set G)) (x : P) :
    normalizerFrattiniAction P n (x : P ⧸ frattini P) =
      ((normalizerConj P n x : P) : P ⧸ frattini P) := by
  rw [normalizerFrattiniAction, MonoidHom.comp_apply]
  exact CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence_apply _ _ x

theorem eq_bot_of_isPerfect {G : Type*} [Group G] [Group.IsSolvable G] (K : Subgroup G)
    [Group.IsPerfect K] : K = ⊥ := by
  by_contra hK
  have : Nontrivial K := (nontrivial_iff_ne_bot K).2 hK
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem isSolvable_of_forall_isPerfect {G : Type*} [Group G] [Finite G]
    (h : ∀ K : Subgroup G, Group.IsPerfect K → K = ⊥) : Group.IsSolvable G := by
  by_contra hns
  have hstep : ∀ n, derivedSeries G (n + 1) < derivedSeries G n := by
    intro n
    refine lt_of_le_of_ne (derivedSeries_antitone G (Nat.le_succ n)) fun heq => hns ?_
    refine ⟨n, h _ ?_⟩
    rw [Subgroup.isPerfect_iff, ← derivedSeries_succ, heq]
  have hcard : ∀ n, Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    intro n
    induction n with
    | zero => rw [derivedSeries_zero, Subgroup.card_top, add_zero]
    | succ n ih =>
      have := Subgroup.card_lt_of_lt (hstep n)
      omega
  have h1 := hcard (Nat.card G + 1)
  have h2 := Nat.card_pos (α := ↥(derivedSeries G (Nat.card G + 1)))
  omega

theorem mulAut_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (α β : MulAut C) :
    α * β = β * α := by
  apply (IsCyclic.mulAutMulEquiv C).injective
  rw [map_mul, map_mul, mul_comm]

theorem isSolvable_of_stabilizes {E : Type*} [Group E] (hE : ∀ a b : E, a * b = b * a)
    (L : Subgroup E) [L.Normal] [IsCyclic L] [IsCyclic (E ⧸ L)] (Γ : Subgroup (MulAut E))
    (hΓ : ∀ γ ∈ Γ, L.map (MulEquiv.toMonoidHom (M := E) (N := E) γ) = L) :
    Group.IsSolvable Γ := by
  let res : Γ →* MulAut L :=
    { toFun := fun γ => (MulEquiv.subgroupMap (γ : MulAut E) L).trans
        (MulEquiv.subgroupCongr (hΓ γ γ.2))
      map_one' := MulEquiv.ext fun l => Subtype.ext rfl
      map_mul' := fun a b => MulEquiv.ext fun l => Subtype.ext rfl }
  have hres : ∀ (γ : Γ) (l : L), ((res γ l : L) : E) = (γ : MulAut E) l := fun _ _ => rfl
  let quo : Γ →* MulAut (E ⧸ L) :=
    { toFun := fun γ => QuotientGroup.congr L L (γ : MulAut E) (hΓ γ γ.2)
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H e => rfl
      map_mul' := fun a b => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H e => rfl }
  have hquo : ∀ (γ : Γ) (e : E), quo γ (e : E ⧸ L) = (((γ : MulAut E) e : E) : E ⧸ L) :=
    fun _ _ => rfl
  let K : Subgroup (MulAut E) :=
    { carrier := {σ | (∀ l ∈ L, σ l = l) ∧ ∀ e, e⁻¹ * σ e ∈ L}
      one_mem' := ⟨fun _ _ => rfl, fun e => by
        rw [MulAut.one_apply, inv_mul_cancel]
        exact one_mem _⟩
      mul_mem' := fun {σ τ} hσ hτ => ⟨fun l hl => by
          rw [MulAut.mul_apply, hτ.1 l hl, hσ.1 l hl], fun e => by
          rw [MulAut.mul_apply]
          have h1 := hτ.2 e
          have h2 : σ (τ e) = σ e * (e⁻¹ * τ e) := by
            rw [← hσ.1 _ h1, ← map_mul, mul_inv_cancel_left]
          rw [h2, ← mul_assoc]
          exact mul_mem (hσ.2 e) h1⟩
      inv_mem' := fun {σ} hσ => ⟨fun l hl => by
          have := hσ.1 l hl
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
          exact this.symm, fun e => by
          have hf : σ (σ⁻¹ e) = e := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
          have := inv_mem (hσ.2 (σ⁻¹ e))
          rw [hf, mul_inv_rev, inv_inv] at this
          exact this⟩ }
  have hK : ∀ σ ∈ K, ∀ τ ∈ K, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    refine MulEquiv.ext fun e => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have ha := hτ.2 e
    have hb := hσ.2 e
    have h1 : τ e = e * (e⁻¹ * τ e) := (mul_inv_cancel_left e (τ e)).symm
    have h2 : σ e = e * (e⁻¹ * σ e) := (mul_inv_cancel_left e (σ e)).symm
    calc σ (τ e) = σ (e * (e⁻¹ * τ e)) := by rw [← h1]
      _ = σ e * (e⁻¹ * τ e) := by rw [map_mul, hσ.1 _ ha]
      _ = e * (e⁻¹ * σ e) * (e⁻¹ * τ e) := by rw [← h2]
      _ = e * (e⁻¹ * τ e) * (e⁻¹ * σ e) := by
          rw [mul_assoc e, mul_assoc e, hE (e⁻¹ * σ e) (e⁻¹ * τ e)]
      _ = τ e * (e⁻¹ * σ e) := by rw [← h1]
      _ = τ (e * (e⁻¹ * σ e)) := by rw [map_mul, hτ.1 _ hb]
      _ = τ (σ e) := by rw [← h2]
  have hcomm : ∀ γ ∈ Γ, ∀ δ ∈ Γ, ⁅γ, δ⁆ ∈ K := by
    intro γ hγ δ hδ
    let γ' : Γ := ⟨γ, hγ⟩
    let δ' : Γ := ⟨δ, hδ⟩
    have hc : ((⁅γ', δ'⁆ : Γ) : MulAut E) = ⁅γ, δ⁆ := rfl
    have hr : res ⁅γ', δ'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mulAut_comm_of_isCyclic _ _
    have hq : quo ⁅γ', δ'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mulAut_comm_of_isCyclic _ _
    refine ⟨fun l hl => ?_, fun e => ?_⟩
    · have h1 := congrArg (fun α : MulAut L => ((α ⟨l, hl⟩ : L) : E)) hr
      simp only [hres, MulAut.one_apply] at h1
      rw [hc] at h1
      exact h1
    · have h1 := congrArg (fun α : MulAut (E ⧸ L) => α (e : E ⧸ L)) hq
      simp only [hquo, MulAut.one_apply] at h1
      rw [hc, QuotientGroup.eq] at h1
      have h2 := inv_mem h1
      rw [mul_inv_rev, inv_inv] at h2
      exact h2
  have hD1 : (derivedSeries Γ 1).map Γ.subtype ≤ K := by
    rw [derivedSeries_one, _root_.commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.commutator_le.2 hcomm
  have hD2 : (derivedSeries Γ 2).map Γ.subtype = ⊥ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, Subgroup.map_commutator]
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hK a (hD1 ha) b (hD1 hb))]
    exact one_mem _
  exact (Group.isSolvable_def _).2 ⟨2, (map_eq_bot_iff_of_injective _ Γ.subtype_injective).1 hD2⟩

end CFSG.Quasithin.H13.NQCat
