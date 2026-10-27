module

public import CFSG.Quasithin.Background.S1549DA6Fin
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.S1549D

open CFSG.Quasithin.S143 CFSG.Quasithin

private theorem zmod_two_add_self' (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

@[expose] def n6Rep (m : ↥(G6.coreMod 6)) : N6 :=
  ⟨Multiplicative.ofAdd (fun i => Multiplicative.toAdd (m : G6.PermMod 6) i +
      Multiplicative.toAdd (m : G6.PermMod 6) 5),
    mem_n6Sub_iff.2 ⟨by
      have hm : ∑ i, Multiplicative.toAdd (m : G6.PermMod 6) i = 0 := m.2
      rw [toAdd_ofAdd, Finset.sum_add_distrib, hm, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      have : (6 : ℕ) • Multiplicative.toAdd (m : G6.PermMod 6) 5 = 0 := by
        generalize Multiplicative.toAdd (m : G6.PermMod 6) 5 = x
        revert x
        decide
      rw [this, add_zero], by
      rw [toAdd_ofAdd]
      exact zmod_two_add_self' _⟩⟩

@[expose] def n6RepHom : ↥(G6.coreMod 6) →* N6 where
  toFun := n6Rep
  map_one' := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    simp [n6Rep]
  map_mul' a b := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    simp only [n6Rep, toAdd_ofAdd, Subgroup.coe_mul, toAdd_mul, Pi.add_apply]
    abel

theorem n6RepHom_surjective : Function.Surjective n6RepHom := by
  intro a
  have ha : ∑ i, Multiplicative.toAdd a.1 i = 0 := (mem_n6Sub_iff.1 a.2).1
  have ha5 : Multiplicative.toAdd a.1 5 = 0 := (mem_n6Sub_iff.1 a.2).2
  refine ⟨⟨a.1, ha⟩, ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd a.1 i + Multiplicative.toAdd a.1 5 = Multiplicative.toAdd a.1 i
  rw [ha5, add_zero]

theorem n6RepHom_ker : n6RepHom.ker =
    ((Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hc : ∀ i, Multiplicative.toAdd (m : G6.PermMod 6) i =
        Multiplicative.toAdd (m : G6.PermMod 6) 5 := by
      intro i
      have h1 := congrFun (congrArg (fun a : N6 => Multiplicative.toAdd a.1) h) i
      have h2 : Multiplicative.toAdd (m : G6.PermMod 6) i + Multiplicative.toAdd (m : G6.PermMod 6) 5
          = 0 := h1
      calc Multiplicative.toAdd (m : G6.PermMod 6) i
          = Multiplicative.toAdd (m : G6.PermMod 6) i +
            (Multiplicative.toAdd (m : G6.PermMod 6) 5 + Multiplicative.toAdd (m : G6.PermMod 6) 5) := by
            rw [zmod_two_add_self', add_zero]
        _ = (Multiplicative.toAdd (m : G6.PermMod 6) i + Multiplicative.toAdd (m : G6.PermMod 6) 5) +
            Multiplicative.toAdd (m : G6.PermMod 6) 5 := by rw [add_assoc]
        _ = Multiplicative.toAdd (m : G6.PermMod 6) 5 := by rw [h2, zero_add]
    refine ⟨?_, m.2⟩
    show (m : G6.PermMod 6) ∈ Subgroup.zpowers (G6.allOnes 6)
    rw [Subgroup.mem_zpowers_iff]
    have hc5 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc5 (Multiplicative.toAdd (m : G6.PermMod 6) 5) with h0 | h1
    · refine ⟨0, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      simp [hc i, h0]
    · refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      simp [hc i, h1, G6.allOnes]
  · rintro ⟨hz, -⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hzi : ∀ j, Multiplicative.toAdd (m : G6.PermMod 6) j = z • (1 : ZMod 2) := by
      intro j
      rw [← hz]
      simp [G6.allOnes, toAdd_zpow]
    show Multiplicative.toAdd (m : G6.PermMod 6) i + Multiplicative.toAdd (m : G6.PermMod 6) 5 = 0
    rw [hzi i, hzi 5, ← add_smul, zsmul_eq_mul, mul_one]
    have h2 : ((z + z : ℤ) : ZMod 2) = (z : ZMod 2) + (z : ZMod 2) := by push_cast; ring
    rw [h2]
    generalize (z : ZMod 2) = x
    exact zmod_two_add_self' x

@[expose] noncomputable def psiN6 : (FFModel.symDn 6).Mod ≃* N6 :=
  (QuotientGroup.quotientMulEquivOfEq n6RepHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective n6RepHom n6RepHom_surjective)

theorem psiN6_mk (m : ↥(G6.coreMod 6)) : psiN6 (QuotientGroup.mk m) = n6Rep m := rfl

theorem n6Rep_permAct (σ : Equiv.Perm (Fin 6)) (m : ↥(G6.coreMod 6)) :
    n6Rep ⟨G6.permAct 6 σ (m : G6.PermMod 6), G6.permAct_mem_coreMod σ m.2⟩ = n6Act σ (n6Rep m) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd (G6.permAct 6 σ (m : G6.PermMod 6)) i +
      Multiplicative.toAdd (G6.permAct 6 σ (m : G6.PermMod 6)) 5 =
    (Multiplicative.toAdd (m : G6.PermMod 6) (σ⁻¹ i) + Multiplicative.toAdd (m : G6.PermMod 6) 5) +
      (Multiplicative.toAdd (m : G6.PermMod 6) (σ⁻¹ 5) + Multiplicative.toAdd (m : G6.PermMod 6) 5)
  rw [G6.permAct_apply, G6.permAct_apply, add_add_add_comm, zmod_two_add_self', add_zero]

theorem exists_n6Equiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : Equiv.Perm (Fin 6) →* ↥H} (h : (FFModel.symDn 6).RealizesVia H ⊤ ⊥ π) :
    ∃ Θ : W ≃* N6, ∀ (σ : Equiv.Perm (Fin 6)) (w : W),
      Θ (((π σ : ↥H) : MulAut W) w) = n6Act σ (Θ w) := by
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv h
  refine ⟨e.trans psiN6, fun σ w => ?_⟩
  obtain ⟨m₀, hm⟩ := QuotientGroup.mk_surjective (e w)
  let m : ↥(G6.coreMod 6) := m₀
  have hact : G6.permAct 6 σ (m : G6.PermMod 6) ∈ G6.coreMod 6 := G6.permAct_mem_coreMod σ m.2
  have h1 : e (((π σ : ↥H) : MulAut W) w) =
      (QuotientGroup.mk ⟨G6.permAct 6 σ (m : G6.PermMod 6), hact⟩ : (FFModel.symDn 6).Mod) :=
    he σ w m₀ hact hm.symm
  show psiN6 (e (((π σ : ↥H) : MulAut W) w)) = n6Act σ (psiN6 (e w))
  rw [h1, ← hm]
  exact n6Rep_permAct σ m

theorem a6u0_ne_one : a6u0 ≠ 1 := by decide

theorem exists_normalized_dict {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {π : Equiv.Perm (Fin 6) →* ↥H}
    (h : (FFModel.symDn 6).RealizesVia H ⊤ ⊥ π) {ū : W} (hū : ū ≠ 1) :
    ∃ (π' : Equiv.Perm (Fin 6) →* ↥H) (Θ : W ≃* N6), Function.Bijective π' ∧ Θ ū = a6u0 ∧
      ∀ (σ : Equiv.Perm (Fin 6)) (w : W), Θ (((π' σ : ↥H) : MulAut W) w) = n6Act σ (Θ w) := by
  classical
  obtain ⟨Θ₀, hΘ₀⟩ := exists_n6Equiv h
  have hū' : Θ₀ ū ≠ 1 := fun h1 => hū (Θ₀.injective (by rw [h1, map_one]))
  obtain ⟨g, hgA, hg⟩ := n6_transitive a6u0 (Θ₀ ū) a6u0_ne_one hū'
  let π' : Equiv.Perm (Fin 6) →* ↥H := π.comp (MulAut.conj g).toMonoidHom
  let Θ : W ≃* N6 := Θ₀.trans (n6Act g⁻¹)
  have hΘ : ∀ (σ : Equiv.Perm (Fin 6)) (w : W), Θ (((π' σ : ↥H) : MulAut W) w) = n6Act σ (Θ w) := by
    intro σ w
    show n6Act g⁻¹ (Θ₀ (((π (g * σ * g⁻¹) : ↥H) : MulAut W) w)) = n6Act σ (n6Act g⁻¹ (Θ₀ w))
    rw [hΘ₀, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hΘū : Θ ū = a6u0 := by
    show n6Act g⁻¹ (Θ₀ ū) = a6u0
    rw [← hg, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hπ'inj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    refine n6_faithful_perm σ fun a => ?_
    obtain ⟨w, rfl⟩ := Θ.surjective a
    rw [← hΘ, hσ]
    rfl
  have hπ'surj : Function.Surjective π' := by
    intro q
    obtain ⟨τ₀, hτ⟩ := h.1 q
    have hτ' : π (show Equiv.Perm (Fin 6) from τ₀) = q := hτ
    generalize (show Equiv.Perm (Fin 6) from τ₀) = τ at hτ'
    refine ⟨g⁻¹ * τ * g, ?_⟩
    show π (g * (g⁻¹ * τ * g) * g⁻¹) = q
    have e : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rw [e, hτ']
  exact ⟨π', Θ, ⟨hπ'inj, hπ'surj⟩, hΘū, hΘ⟩

theorem a6_no_strong_normalized {W : Type} [CommGroup W] [Finite W]
    {G' : Subgroup (MulAut W)} {π' : Equiv.Perm (Fin 6) →* ↥G'} {Θ : W ≃* N6} {ū : W}
    (hπ'bij : Function.Bijective π') (hΘū : Θ ū = a6u0)
    (hΘ : ∀ (σ : Equiv.Perm (Fin 6)) (w : W), Θ (((π' σ : ↥G') : MulAut W) w) = n6Act σ (Θ w))
    {Pp Qp Ap : Subgroup (MulAut W)}
    (hPp : ∀ σ ∈ alternatingGroup (Fin 6), ((π' σ : ↥G') : MulAut W) ū = ū →
      ((π' σ : ↥G') : MulAut W) ∈ Pp)
    (hQG : Qp ≤ G') (hQ2 : ∀ q ∈ Qp, ∃ k : ℕ, q ^ 2 ^ k = 1) (hQu : ∀ q ∈ Qp, q ū = ū)
    (hQn : ∀ p ∈ Pp, ∀ q ∈ Qp, p * q * p⁻¹ ∈ Qp) (hAQ : Ap ≤ Qp) (hAne : Ap ≠ ⊥) :
    Nat.card Ap * Nat.card (fixV Ap) ≤ Nat.card W := by
  classical
  obtain ⟨hπ'inj, hπ'surj⟩ := hπ'bij
  let Q₀ : Subgroup (Equiv.Perm (Fin 6)) := (Qp.subgroupOf G').comap π'
  let B₀ : Subgroup (Equiv.Perm (Fin 6)) := (Ap.subgroupOf G').comap π'
  have hmemQ : ∀ σ, σ ∈ Q₀ ↔ ((π' σ : ↥G') : MulAut W) ∈ Qp := fun σ => Iff.rfl
  have hmemB : ∀ σ, σ ∈ B₀ ↔ ((π' σ : ↥G') : MulAut W) ∈ Ap := fun σ => Iff.rfl
  have hBQ : B₀ ≤ Q₀ := fun σ hσ => (hmemQ σ).2 (hAQ ((hmemB σ).1 hσ))
  have hQ2' : ∀ q ∈ Q₀, ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := hQ2 _ ((hmemQ q).1 hq)
    refine ⟨k, hπ'inj ?_⟩
    rw [map_pow, map_one]
    exact Subtype.ext hk
  have hQu' : ∀ q ∈ Q₀, n6Act q a6u0 = a6u0 := by
    intro q hq
    have h1 := hQu _ ((hmemQ q).1 hq)
    rw [← hΘū, ← hΘ, h1]
  have hQn' : ∀ p ∈ alternatingGroup (Fin 6), n6Act p a6u0 = a6u0 → ∀ q ∈ Q₀, p * q * p⁻¹ ∈ Q₀ := by
    intro p hp hpu q hq
    have hfix : ((π' p : ↥G') : MulAut W) ū = ū := by
      apply Θ.injective
      rw [hΘ, hΘū, hpu]
    have hpP := hPp p hp hfix
    rw [hmemQ] at hq ⊢
    have := hQn _ hpP _ hq
    simpa using this
  have hB1 : B₀ ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [eq_bot_iff]
    intro a ha
    have haG : a ∈ G' := hQG (hAQ ha)
    obtain ⟨σ, hσ⟩ := hπ'surj ⟨a, haG⟩
    have hσB : σ ∈ B₀ := (hmemB σ).2 (by rw [hσ]; exact ha)
    rw [hbot, Subgroup.mem_bot] at hσB
    subst hσB
    rw [Subgroup.mem_bot]
    have := congrArg Subtype.val hσ
    rw [map_one] at this
    exact this.symm
  have hbound := a6_card_bound hBQ hQ2' hQu' hQn' hB1
  have hcardA : Nat.card Ap = Nat.card B₀ := by
    refine (Nat.card_congr (Equiv.ofBijective (fun σ : B₀ =>
      (⟨((π' σ : ↥G') : MulAut W), (hmemB σ).1 σ.2⟩ : Ap)) ⟨?_, ?_⟩)).symm
    · intro σ τ hστ
      apply Subtype.ext
      apply hπ'inj
      apply Subtype.ext
      exact congrArg (fun z : Ap => (z : MulAut W)) hστ
    · rintro ⟨a, ha⟩
      obtain ⟨σ, hσ⟩ := hπ'surj ⟨a, hQG (hAQ ha)⟩
      refine ⟨⟨σ, (hmemB σ).2 (by rw [hσ]; exact ha)⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : ↥G' => (z : MulAut W)) hσ
  have hcardF : Nat.card (fixV Ap) = Nat.card {v : N6 // ∀ b ∈ B₀, n6Act b v = v} := by
    refine Nat.card_congr (Equiv.ofBijective (fun w : fixV Ap =>
      (⟨Θ (w : W), fun b hb => by
        rw [← hΘ]
        have := w.2 _ ((hmemB b).1 hb)
        rw [this]⟩ : {v : N6 // ∀ b ∈ B₀, n6Act b v = v})) ⟨?_, ?_⟩)
    · intro w₁ w₂ h12
      apply Subtype.ext
      exact Θ.injective (congrArg Subtype.val h12)
    · rintro ⟨v, hv⟩
      obtain ⟨w, rfl⟩ := Θ.surjective v
      refine ⟨⟨w, fun a ha => ?_⟩, rfl⟩
      obtain ⟨σ, hσ⟩ := hπ'surj ⟨a, hQG (hAQ ha)⟩
      have hσB : σ ∈ B₀ := (hmemB σ).2 (by rw [hσ]; exact ha)
      have h1 := hv σ hσB
      rw [← hΘ] at h1
      apply Θ.injective
      have haeq : a = ((π' σ : ↥G') : MulAut W) := by rw [hσ]
      rw [haeq]
      exact h1
  have hcardW : Nat.card W = 16 := by rw [Nat.card_congr Θ.toEquiv, n6_card]
  rw [hcardA, hcardF, hcardW]
  exact hbound

end CFSG.Quasithin.S1549D
