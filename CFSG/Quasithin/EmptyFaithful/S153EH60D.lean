module

public import CFSG.Quasithin.EmptyFaithful.S153EH60C
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153EH60

theorem exists_linModel_dual {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)} {L : Subgroup (MulAut V)} {I : Subgroup V}
    {π : ↥Γ →* ↥L} (hD : (FFModel.dualNat Γ).RealizesVia L I ⊥ π) :
    ∃ e : ↥I ≃* Multiplicative (Fin n → K), ∀ (γ : ↥Γ) (u : ↥I)
      (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ I),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = dualNatAct Γ γ (e u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hD
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  let e : ↥I ≃* Multiplicative (Fin n → K) :=
    (MulEquiv.ofBijective β ⟨hinj, hβs⟩).trans (B5.natQuotEquiv (Multiplicative (Fin n → K)))
  refine ⟨e, fun γ u hu => ?_⟩
  have h1 : β u = QuotientGroup.mk ⟨e u, trivial⟩ := by
    apply (B5.natQuotEquiv (Multiplicative (Fin n → K))).injective
    exact (rfl : B5.natQuotEquiv (Multiplicative (Fin n → K)) (β u) = e u)
  have h2 := hβe γ u ⟨e u, trivial⟩ hu trivial h1
  have h3 := congrArg (B5.natQuotEquiv (Multiplicative (Fin n → K))) h2
  exact h3

section Fixed

variable {V : Type*} [CommGroup V]

theorem mem_fixV_zpowers_iff (g : MulAut V) (v : V) :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_fixV_inf_eq {W : Subgroup V} {M : Type} [CommGroup M] (e : ↥W ≃* M) (g : MulAut V)
    (f : M → M) (hW : ∀ w ∈ W, g w ∈ W)
    (he : ∀ (u : ↥W) (hu : g (u : V) ∈ W), e ⟨g (u : V), hu⟩ = f (e u)) :
    Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ W) = Nat.card {m : M // f m = m} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e ⟨x.1, x.2.2⟩, ?_⟩
      invFun := fun m => ⟨((e.symm m.1 : ↥W) : V), ?_, (e.symm m.1).2⟩
      left_inv := fun x => ?_
      right_inv := fun m => ?_ }
  · have hx := (mem_fixV_zpowers_iff g x.1).mp x.2.1
    rw [← he ⟨x.1, x.2.2⟩ (hW _ x.2.2)]
    congr 1
    exact Subtype.ext hx
  · refine (mem_fixV_zpowers_iff g _).mpr ?_
    have h1 := he (e.symm m.1) (hW _ (e.symm m.1).2)
    rw [MulEquiv.apply_symm_apply, m.2] at h1
    have h2 := e.injective (h1.trans (MulEquiv.apply_symm_apply e m.1).symm)
    exact congrArg Subtype.val h2
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

end Fixed

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem card_fixV_zpowers_eq_four {K : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
    {π : L32 →* ↥K} (hπ : Function.Bijective π) (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
    (h₁ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π)
    (h₂ : (FFModel.dualNat (StatedSL 3 (ZMod 2))).RealizesVia K W₂ ⊥ π)
    {a : MulAut V} (ha : a ∈ K) (ha3 : orderOf a = 3) :
    Nat.card ↥(fixV (Subgroup.zpowers a)) = 4 := by
  obtain ⟨γ, hγ, hγ3⟩ := exists_preimage_order_three π hπ ha ha3
  have hπγ : ((π γ : ↥K) : MulAut V) = a := by rw [hγ]
  subst hπγ
  obtain ⟨e₁, he₁⟩ := B5.exists_linModel h₁
  obtain ⟨e₂, he₂⟩ := exists_linModel_dual h₂
  have hW₁ : ∀ w ∈ W₁, ((π γ : ↥K) : MulAut V) w ∈ W₁ := fun w hw => h₁.2.2.2.1 (π γ) w hw
  have hW₂ : ∀ w ∈ W₂, ((π γ : ↥K) : MulAut V) w ∈ W₂ := fun w hw => h₂.2.2.2.1 (π γ) w hw
  have c₁ : Nat.card ↥(fixV (Subgroup.zpowers ((π γ : ↥K) : MulAut V)) ⊓ W₁) = 2 := by
    rw [card_fixV_inf_eq e₁ ((π γ : ↥K) : MulAut V) (natAct (StatedSL 3 (ZMod 2)) γ) hW₁
      (fun u hu => he₁ γ u hu)]
    exact card_fix_nat hγ3
  have c₂ : Nat.card ↥(fixV (Subgroup.zpowers ((π γ : ↥K) : MulAut V)) ⊓ W₂) = 2 := by
    rw [card_fixV_inf_eq e₂ ((π γ : ↥K) : MulAut V) (dualNatAct (StatedSL 3 (ZMod 2)) γ) hW₂
      (fun u hu => he₂ γ u hu)]
    exact card_fix_dual hγ3
  set a : MulAut V := ((π γ : ↥K) : MulAut V) with hadef
  set F₁ := fixV (Subgroup.zpowers a) ⊓ W₁ with hF₁
  set F₂ := fixV (Subgroup.zpowers a) ⊓ W₂ with hF₂
  have hinf' : F₁ ⊓ F₂ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ W₁ ⊓ W₂ := ⟨hv.1.2, hv.2.2⟩
    rw [hinf] at this
    exact this
  have hsup' : F₁ ⊔ F₂ = fixV (Subgroup.zpowers a) := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro v hv
      have hv' : v ∈ W₁ ⊔ W₂ := by rw [hsup]; trivial
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hv'
      have hfix : a (w₁ * w₂) = w₁ * w₂ := (mem_fixV_zpowers_iff a _).mp hv
      rw [map_mul] at hfix
      have h3 : a w₁ * w₁⁻¹ = w₂ * (a w₂)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hfix, mul_comm]
      have h4 : a w₁ * w₁⁻¹ ∈ W₁ ⊓ W₂ :=
        ⟨W₁.mul_mem (hW₁ w₁ hw₁) (W₁.inv_mem hw₁), h3 ▸ W₂.mul_mem hw₂ (W₂.inv_mem (hW₂ w₂ hw₂))⟩
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h4
      have h5 : w₂ * (a w₂)⁻¹ = 1 := by rw [← h3, mul_inv_eq_one.mpr h4]
      have h6 : a w₂ = w₂ := (mul_inv_eq_one.mp h5).symm
      exact Subgroup.mul_mem_sup ⟨(mem_fixV_zpowers_iff a _).mpr h4, hw₁⟩
        ⟨(mem_fixV_zpowers_iff a _).mpr h6, hw₂⟩
  have hT : F₁ ≤ Subgroup.normalizer (F₂ : Set V) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [mul_comm x h, mul_assoc, mul_inv_cancel, mul_one]
  have hcard := S153E59.card_sup_mul_card_inf_of_normalizes hT
  rw [hsup', hinf', Subgroup.card_bot, mul_one, c₁, c₂] at hcard
  exact hcard

end Main

end S153EH60

end CFSG.Quasithin
