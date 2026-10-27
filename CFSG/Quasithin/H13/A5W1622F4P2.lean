module

public import CFSG.Quasithin.H13.A5W1622F4P1

public section

namespace CFSG.Quasithin.H13.A5.F4P

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G] {F : Type} [Field F]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem natCard_addMonoidHom [Finite F] (h2 : (2 : F) = 0) :
    Nat.card ((Fin 3 → F) →+ ZMod 2) = Nat.card (Fin 3 → F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Fin 3 → F) :=
    AddCommGroup.zmodModule (n := 2) fun v => by
      funext j
      simp [h2]
  have : Module.Finite (ZMod 2) (Fin 3 → F) := Module.Finite.of_finite
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv]
  show Nat.card (Module.Dual (ZMod 2) (Fin 3 → F)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
    ← Module.natCard_eq_pow_finrank]

theorem natCard_eq {L V Z : Subgroup G} [Finite F] {α : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}
    {k : ℕ} (h : IsSumOfNaturalModulesVia L V Z α dual k) :
    Nat.card ↥V = Nat.card ↥Z * Nat.card F ^ (3 * k) := by
  obtain ⟨-, hZV, β, hβs, hβk, -⟩ := h
  have e1 := Subgroup.card_mul_index β.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hβs, Subgroup.card_top, hβk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at e1
  rw [← e1, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun, Nat.card_fin,
    Nat.card_fin, ← pow_mul]

theorem false_of_comm_mem [Finite G] {L Q V Z D : Subgroup G} [Finite F]
    {α : ↥L →* ↥(StatedSL 3 F)} (h2 : (2 : F) = 0) (hV : IsSumOfNaturalModulesVia L V Z α true 1)
    (hQ : IsSumOfNaturalModulesVia L Q D α false 2) (hVQ : V ≤ Q)
    (hZ : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hD : ∀ x ∈ Q, (∀ φ ∈ V, φ * x = x * φ) → x ∈ D) {c : G} (hc : c * c = 1)
    (hcQ : ∀ x ∈ Q, x * c = c * x)
    (h : ∀ φ ∈ V, ∀ x ∈ Q, φ * x * φ⁻¹ * x⁻¹ ∈ Subgroup.zpowers c) : False := by
  classical
  obtain ⟨κ, hκm, hκs, hκ0, -⟩ := exists_crd hV
  have hDQ : D ≤ Q := hQ.2.1
  have hzp : ∀ g ∈ Subgroup.zpowers c, g = 1 ∨ g = c := by
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
    rw [zpow_eq_zpow_emod m hc2]
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1
    · left
      rw [h0, zpow_zero]
    · right
      rw [h1, zpow_one]
  have hcen : ∀ g ∈ Subgroup.zpowers c, ∀ y ∈ Q, g * y = y * g := by
    intro g hg y hy
    rcases hzp g hg with rfl | rfl
    · simp
    · exact (hcQ y hy).symm
  have hK1 : ∀ φ ∈ V, ∀ φ' ∈ V, ∀ x ∈ Q, φ * φ' * x * (φ * φ')⁻¹ * x⁻¹ =
      (φ' * x * φ'⁻¹ * x⁻¹) * (φ * x * φ⁻¹ * x⁻¹) := by
    intro φ hφ φ' hφ' x hx
    have hk := hcen _ (h φ' hφ' x hx) φ (hVQ hφ)
    have e : φ * φ' * x * (φ * φ')⁻¹ * x⁻¹ =
        (φ * (φ' * x * φ'⁻¹ * x⁻¹)) * φ⁻¹ * (φ * x * φ⁻¹ * x⁻¹) := by group
    rw [e, ← hk, mul_inv_cancel_right]
  have hK2 : ∀ φ ∈ V, ∀ z ∈ Z, ∀ x ∈ Q, φ * z * x * (φ * z)⁻¹ * x⁻¹ = φ * x * φ⁻¹ * x⁻¹ := by
    intro φ _ z hz x hx
    have e : φ * z * x * (φ * z)⁻¹ * x⁻¹ = φ * (z * x) * z⁻¹ * φ⁻¹ * x⁻¹ := by group
    rw [e, hZ z hz x hx]
    group
  have hK3 : ∀ φ ∈ V, ∀ x ∈ Q, ∀ x' ∈ Q, φ * (x * x') * φ⁻¹ * (x * x')⁻¹ =
      (φ * x' * φ⁻¹ * x'⁻¹) * (φ * x * φ⁻¹ * x⁻¹) := by
    intro φ hφ x hx x' hx'
    have hk := hcen _ (h φ hφ x' hx') (φ * x * φ⁻¹)
      (Q.mul_mem (Q.mul_mem (hVQ hφ) hx) (Q.inv_mem (hVQ hφ)))
    have e : φ * (x * x') * φ⁻¹ * (x * x')⁻¹ =
        (φ * x * φ⁻¹) * (φ * x' * φ⁻¹ * x'⁻¹) * x⁻¹ := by group
    rw [e, ← hk]
    group
  let enc : G → ZMod 2 := fun g => if g = 1 then 0 else 1
  have henc : ∀ g ∈ Subgroup.zpowers c, ∀ g' ∈ Subgroup.zpowers c,
      enc (g * g') = enc g + enc g' := by
    intro g hg g' hg'
    rcases hzp g hg with h1 | h1 <;> rcases hzp g' hg' with h1' | h1' <;> rw [h1, h1']
    · simp [enc]
    · simp [enc]
    · simp [enc]
    · by_cases hc1 : c = 1
      · simp [enc, hc1]
      · simp only [enc, hc, hc1, ite_true, ite_false]
        decide
  have henc0 : ∀ g ∈ Subgroup.zpowers c, enc g = 0 → g = 1 := by
    intro g _ hg0
    by_contra hg1
    simp [enc, hg1] at hg0
  have henc_inj : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ Subgroup.zpowers c, enc a = enc b → a = b := by
    intro a ha b hb hab
    rcases hzp a ha with h1 | h1 <;> rcases hzp b hb with h1' | h1' <;> rw [h1, h1'] at hab ⊢
    · by_cases hc1 : c = 1
      · rw [hc1]
      · simp [enc, hc1] at hab
    · by_cases hc1 : c = 1
      · rw [hc1]
      · simp [enc, hc1] at hab
  have hκinv : ∀ w : ↥V, κ w⁻¹ = -κ w := fun w => by
    have h1 := hκm w⁻¹ w
    rw [inv_mul_cancel, (hκ0 1).mpr (by simp)] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  choose s hs using hκs
  have hsZ : ∀ t t', (((s t * s t')⁻¹ * s (t + t') : ↥V) : G) ∈ Z := fun t t' =>
    (hκ0 _).mp (by rw [hκm, hκinv, hκm, hs, hs, hs, neg_add_cancel])
  have hs0 : ((s 0 : ↥V) : G) ∈ Z := (hκ0 _).mp (hs 0)
  let ψ : ↥Q → ((Fin 3 → F) →+ ZMod 2) := fun x =>
    { toFun := fun t => enc ((s t : G) * x * (s t : G)⁻¹ * (x : G)⁻¹)
      map_zero' := by
        show enc _ = 0
        rw [hZ _ hs0 x x.2, mul_inv_cancel_right, mul_inv_cancel]
        simp [enc]
      map_add' := fun t t' => by
        show enc _ = enc _ + enc _
        have e : ((s (t + t') : ↥V) : G) =
            (s t : G) * s t' * ((s t * s t')⁻¹ * s (t + t') : ↥V) := by
          push_cast
          group
        rw [e, hK2 _ (V.mul_mem (s t).2 (s t').2) _ (hsZ t t') x x.2,
          hK1 _ (s t).2 _ (s t').2 x x.2, henc _ (h _ (s t').2 x x.2) _ (h _ (s t).2 x x.2),
          add_comm] }
  have hψ : ∀ (x : ↥Q) (t : Fin 3 → F),
      ψ x t = enc ((s t : G) * x * (s t : G)⁻¹ * (x : G)⁻¹) := fun _ _ => rfl
  have hcomm : ∀ x : ↥Q, (∀ t, ((s t : G) * x * (s t : G)⁻¹ * (x : G)⁻¹) = 1) →
      (x : G) ∈ D := by
    intro x hx
    refine hD x x.2 fun φ hφ => ?_
    have e : φ = (s (κ ⟨φ, hφ⟩) : G) * ((s (κ ⟨φ, hφ⟩))⁻¹ * ⟨φ, hφ⟩ : ↥V) := by
      push_cast
      group
    have hz : (((s (κ ⟨φ, hφ⟩))⁻¹ * ⟨φ, hφ⟩ : ↥V) : G) ∈ Z :=
      (hκ0 _).mp (by rw [hκm, hκinv, hs, neg_add_cancel])
    have h1 := hx (κ ⟨φ, hφ⟩)
    rw [← hK2 _ (s _).2 _ hz x x.2, ← e] at h1
    have h2 : φ * x * φ⁻¹ = x := by
      calc φ * x * φ⁻¹ = (φ * x * φ⁻¹ * (x : G)⁻¹) * x := by rw [inv_mul_cancel_right]
        _ = x := by rw [h1, one_mul]
    calc φ * x = φ * x * φ⁻¹ * φ := by rw [inv_mul_cancel_right]
      _ = x * φ := by rw [h2]
  have hinj : ∀ x y : ↥Q, ψ x = ψ y → x⁻¹ * y ∈ D.subgroupOf Q := by
    intro x y hxy
    rw [Subgroup.mem_subgroupOf]
    refine hcomm (x⁻¹ * y) fun t => ?_
    have h1 := congrArg (fun f => f t) hxy
    simp only [hψ] at h1
    have hab := henc_inj _ (h _ (s t).2 x x.2) _ (h _ (s t).2 y y.2) h1
    have hprod := hK3 _ (s t).2 _ (Q.inv_mem x.2) _ y.2
    have hinv := hK3 _ (s t).2 _ x.2 _ (Q.inv_mem x.2)
    rw [mul_inv_cancel, mul_one, mul_inv_cancel, mul_inv_cancel] at hinv
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hprod, ← hab, inv_inv]
    rw [inv_inv] at hinv
    rw [eq_comm] at hinv
    have hinv' := eq_inv_of_mul_eq_one_left hinv
    rw [hinv', mul_inv_cancel]
  have hfin : Finite ((Fin 3 → F) →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  have hgi : Function.Injective fun q : ↥Q ⧸ D.subgroupOf Q => ψ q.out := by
    intro q q' hqq
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact QuotientGroup.eq.mpr (hinj _ _ hqq)
  have h1 := Nat.card_le_card_of_injective _ hgi
  rw [natCard_addMonoidHom h2, Nat.card_fun, Nat.card_fin] at h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf Q)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv, natCard_eq hQ] at h3
  have hD0 : 0 < Nat.card ↥D := Nat.card_pos
  have hF : 2 ≤ Nat.card F := Finite.one_lt_card
  have h4 : Nat.card F ^ (3 * 2) ≤ Nat.card F ^ 3 := by
    have h5 : Nat.card ↥D * Nat.card F ^ (3 * 2) ≤ Nat.card ↥D * Nat.card F ^ 3 := by
      rw [h3, mul_comm (Nat.card ↥D)]
      exact Nat.mul_le_mul_right _ h1
    exact Nat.le_of_mul_le_mul_left h5 hD0
  have h6 : Nat.card F ^ 3 < Nat.card F ^ (3 * 2) :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end CFSG.Quasithin.H13.A5.F4P
