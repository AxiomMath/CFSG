module

public import CFSG.RankThree.PartOne.CTP.SeitzTransfer

public section

namespace CFSG.RankThree.PartOne.CTP

@[expose] def fixedSubgroup {K : Type*} [Group K] (α : MulAut K) : Subgroup K where
  carrier := {x | α x = x}
  one_mem' := map_one α
  mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) => by
    show α (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : α a = a) => by
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedSubgroup {K : Type*} [Group K] {α : MulAut K} {x : K} :
    x ∈ fixedSubgroup α ↔ α x = x := Iff.rfl

section Abstract

variable {K : Type*} [Group K]

theorem fixedSubgroup_subset_fixUnion {E : Subgroup (MulAut K)} {α : MulAut K} (hαE : α ∈ E)
    (hα1 : α ≠ 1) : (fixedSubgroup α : Set K) ⊆ fixUnion E := by
  intro x hx
  refine ⟨Subgroup.zpowers α, Subgroup.zpowers_le.2 hαE, ?_, ?_⟩
  · intro hbot
    exact hα1 (Subgroup.zpowers_eq_bot.1 hbot)
  · intro φ hφ
    have hmem : α ∈ MulAction.stabilizer (MulAut K) x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hx
    have := Subgroup.zpowers_le.2 hmem hφ
    rw [MulAction.mem_stabilizer_iff] at this
    exact this

theorem apply_eq_of_commute_conj (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {σ : MulAut K} {k : K} (h : σ * MulAut.conj k = MulAut.conj k * σ) : σ k = k := by
  have h1 : MulAut.conj (σ k) = MulAut.conj k := by
    ext y
    have := congrArg (fun φ : MulAut K => φ (σ.symm y)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at this ⊢
    simpa using this
  exact hinj h1

theorem closure_fixUnion_eq_top_of_pair (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {p : ℕ} (hp : p.Prime) (E : Subgroup (MulAut K)) {σ : MulAut K} (hσE : σ ∈ E)
    (hσinn : ∀ g : K, σ ≠ MulAut.conj g) {k : K} (hkE : MulAut.conj k ∈ E) (hk1 : k ≠ 1)
    (hkp : k ^ p = 1) (hcomm : σ * MulAut.conj k = MulAut.conj k * σ)
    (hcenter : p ∣ Nat.card (fixedSubgroup σ) → ∀ x ∈ fixedSubgroup σ,
      (∀ y ∈ fixedSubgroup σ, x * y = y * x) → x = 1)
    (hgen : fixedSubgroup σ ≠ fixedSubgroup (σ * MulAut.conj k) →
      Subgroup.closure ((fixedSubgroup σ : Set K) ∪ (fixedSubgroup (σ * MulAut.conj k) : Set K)) =
        ⊤ ∨ ¬ p ∣ Nat.card (fixedSubgroup σ)) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hστE : σ * MulAut.conj k ∈ E := E.mul_mem hσE hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hσk : σ k = k := apply_eq_of_commute_conj hinj hcomm
  have hkP : k ∈ fixedSubgroup σ := hσk
  have hpdvd : p ∣ Nat.card (fixedSubgroup σ) := by
    have hord : orderOf k = p := (orderOf_eq_prime hkp hk1 : orderOf k = p)
    have h1 : orderOf (⟨k, hkP⟩ : fixedSubgroup σ) ∣ Nat.card (fixedSubgroup σ) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hne : fixedSubgroup σ ≠ fixedSubgroup (σ * MulAut.conj k) := by
    intro heq
    apply hk1
    refine hcenter hpdvd k hkP fun y hy => ?_
    have hy' : y ∈ fixedSubgroup (σ * MulAut.conj k) := heq ▸ hy
    have h1 : σ y = y := hy
    have h2 : (σ * MulAut.conj k) y = y := hy'
    have h3 : σ (k * y * k⁻¹) = k * y * k⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσk, h1]
    have h4 : σ (k * y * k⁻¹) = y := by
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h2
    rw [h4] at h3
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [← h3]
  rcases hgen hne with hg | hsmall
  · rw [eq_top_iff, ← hg, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hσE hσ1 hx)
    · exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hστE hστ1 hx)
  · exact absurd hpdvd hsmall

end Abstract

section Data

@[expose] def IsOuterOfOrder {K : Type*} [Group K] (p : ℕ) (σ : MulAut K) : Prop :=
  orderOf σ = p ∧ ∀ g : K, σ ≠ MulAut.conj g

structure FieldAutData (K : Type) [Group K] (p : ℕ) : Prop where
  out_rank : ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∃ g : K, g ≠ 1 ∧ MulAut.conj g ∈ E
  center : ∀ σ : MulAut K, IsOuterOfOrder p σ → p ∣ Nat.card (fixedSubgroup σ) →
    ∀ x ∈ fixedSubgroup σ, (∀ y ∈ fixedSubgroup σ, x * y = y * x) → x = 1
  gen : ∀ σ τ : MulAut K, IsOuterOfOrder p σ → IsOuterOfOrder p τ →
    fixedSubgroup σ ≠ fixedSubgroup τ →
    Subgroup.closure ((fixedSubgroup σ : Set K) ∪ (fixedSubgroup τ : Set K)) = ⊤ ∨
      ¬ p ∣ Nat.card (fixedSubgroup σ)

variable {K : Type} [Group K]

theorem closure_fixUnion_eq_top_of_fieldAutData [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (hd : FieldAutData K p)
    (E : Subgroup (MulAut K)) [hE : CFSG.IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_simple hnab
  obtain ⟨k, hk1, hkE⟩ := hd.out_rank E hE hEc
  push Not at hout
  obtain ⟨σ, hσE, hσinn⟩ := hout
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hσp : σ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
  have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
  have hkp : k ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hkE
  have hcomm : σ * MulAut.conj k = MulAut.conj k * σ := hcommE σ hσE _ hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hστp : (σ * MulAut.conj k) ^ p = 1 := by
    rw [(show Commute σ (MulAut.conj k) from hcomm).mul_pow, hσp, ← map_pow, hkp, map_one, one_mul]
  have hστo : IsOuterOfOrder p (σ * MulAut.conj k) := by
    refine ⟨orderOf_eq_prime hστp hστ1, fun g h => hσinn (g * k⁻¹) ?_⟩
    rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  exact closure_fixUnion_eq_top_of_pair hinj hp E hσE hσinn hkE hk1 hkp hcomm
    (hd.center σ hσo) (hd.gen σ _ hσo hστo)

end Data


section Transport

variable {K P : Type} [Group K] [Group P]

theorem eq_conj_of_congr_eq_conj (e : K ≃* P) {σ : MulAut K} {g : P}
    (h : MulAut.congr e σ = MulAut.conj g) : σ = MulAut.conj (e.symm g) := by
  ext x
  have h1 : e (σ x) = g * e x * g⁻¹ := by
    have h2 := congrArg (fun φ : MulAut P => φ (e x)) h
    simpa [MulAut.conj_apply] using h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1]
  simp

theorem fixedSubgroup_congr (e : K ≃* P) (σ : MulAut K) :
    fixedSubgroup (MulAut.congr e σ) = (fixedSubgroup σ).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    have h1 : e (σ (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    change σ (e.symm y) = e.symm y
    apply e.injective
    rw [h1]
    simp
  · rintro ⟨x, hx, rfl⟩
    have h1 : σ x = x := hx
    change e (σ (e.symm (e x))) = e x
    simp [h1]

theorem FieldAutData.of_mulEquiv (e : K ≃* P) {p : ℕ} (hp : p.Prime) (h : FieldAutData P p) :
    FieldAutData K p := by
  have : Fact p.Prime := ⟨hp⟩
  have houter : ∀ σ : MulAut K, IsOuterOfOrder p σ → IsOuterOfOrder p (MulAut.congr e σ) :=
    fun σ hσ => ⟨(MulEquiv.orderOf_eq (MulAut.congr e) σ).trans hσ.1, fun g hg =>
      hσ.2 (e.symm g) (eq_conj_of_congr_eq_conj e hg)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro E hE hEc
    have hE' : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
      CFSG.IsElementaryAbelian.map _
    have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hEc]
    obtain ⟨g, hg1, hgE⟩ := h.out_rank _ hE' hc'
    obtain ⟨φ, hφE, hφ⟩ := hgE
    refine ⟨e.symm g, fun h1 => hg1 (by simpa using congrArg e h1), ?_⟩
    have := eq_conj_of_congr_eq_conj e (σ := φ) hφ
    rw [← this]
    exact hφE
  · intro σ hσ hdvd x hx hcomm
    have hfix := fixedSubgroup_congr e σ
    have hmem : e x ∈ fixedSubgroup (MulAut.congr e σ) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    have hdvd' : p ∣ Nat.card (fixedSubgroup (MulAut.congr e σ)) := by
      rwa [fixedSubgroup_congr, Subgroup.card_map_of_injective e.injective]
    have := h.center (MulAut.congr e σ) (houter σ hσ) hdvd' (e x) hmem (fun y hy => by
      rw [hfix] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      change e x * e y' = e y' * e x
      rw [← map_mul, ← map_mul]
      exact congrArg e (hcomm y' hy'))
    exact e.injective (this.trans (map_one e).symm)
  · intro σ τ hσ hτ hne
    have hne' : fixedSubgroup (MulAut.congr e σ) ≠ fixedSubgroup (MulAut.congr e τ) := by
      rw [fixedSubgroup_congr, fixedSubgroup_congr]
      exact fun heq => hne (Subgroup.map_injective e.injective heq)
    rcases h.gen _ _ (houter σ hσ) (houter τ hτ) hne' with hg | hsmall
    · left
      rw [fixedSubgroup_congr, fixedSubgroup_congr] at hg
      have hmap : (Subgroup.closure ((fixedSubgroup σ : Set K) ∪ fixedSubgroup τ)).map
          e.toMonoidHom = ⊤ := by
        rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map]
        exact hg
      calc Subgroup.closure ((fixedSubgroup σ : Set K) ∪ fixedSubgroup τ)
          = ((Subgroup.closure ((fixedSubgroup σ : Set K) ∪ fixedSubgroup τ)).map
              e.toMonoidHom).comap e.toMonoidHom :=
            (Subgroup.comap_map_eq_self_of_injective e.injective _).symm
        _ = ⊤ := by rw [hmap, Subgroup.comap_top]
    · right
      rwa [fixedSubgroup_congr, Subgroup.card_map_of_injective e.injective] at hsmall

end Transport

end CFSG.RankThree.PartOne.CTP
