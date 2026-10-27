module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotUniqueField
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinCard

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem le_of_card_ge_E7 {X : Type*} [Group X] [Finite X] {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) = ⊥) {K : Type} [Field K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : ↥F ≃* adjointGroup .E7 K) {A : Subgroup X}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hcard : 2 ^ (27 * f) ≤ Nat.card A) : A ≤ F := by
  have hf : 1 ≤ f := SeitzReduction.F4Pilot.one_le_of_natCard_eq_two_pow hK
  have : Finite K := SeitzReduction.F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  set β : X →* MulAut (adjointGroup .E7 K) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hβdef
  have hβ : ∀ x, β x = (e.symm.trans (MulAut.conjNormal x)).trans e := fun x =>
    MulEquiv.ext fun _ => rfl
  have hβF : ∀ x, β x ∈ (MulAut.conj : adjointGroup .E7 K →* _).range → x ∈ F := by
    intro x hx
    rw [hβ, SeitzReduction.F4Pilot.conj_mem_range_conj_iff] at hx
    obtain ⟨n, hn⟩ := hx
    have hc : (n : X)⁻¹ * x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun φ : MulAut ↥F => ((φ ⟨y, hy⟩ : ↥F) : X)) hn
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc y * ((n : X)⁻¹ * x) = (n : X)⁻¹ * ((n : X) * y * (n : X)⁻¹) * x := by group
        _ = (n : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
        _ = (n : X)⁻¹ * x * y := by group
    rw [hC, Subgroup.mem_bot] at hc
    rw [← inv_mul_eq_one.1 hc]
    exact n.2
  have hβ2 : ∀ x ∈ A, β x ^ 2 = 1 := fun x hx => by rw [← map_pow, hA x hx, map_one]
  by_contra hAF
  obtain ⟨a, haA, haF⟩ := Set.not_subset.1 hAF
  have haO : β a ∉ (MulAut.conj : adjointGroup .E7 K →* _).range := fun h => haF (hβF a h)
  have hΘa : Θ (β a) ≠ 1 := fun h => haO (by rw [← hker]; exact h)
  obtain ⟨⟨e', hfe⟩, hσa⟩ := (hinv (β a) (hβ2 a haA)).resolve_left hΘa
  have hf' : f = 2 * e' := by omega
  have he' : 1 ≤ e' := by omega
  have hK' : Nat.card K = 2 ^ (2 * e') := by rw [hK, hf']
  have hσ : ∀ c, Θ (β a) c = c ^ 2 ^ e' := fun c => by
    rw [hσa c, hf', Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hdich : ∀ b ∈ A, Θ (β b) = 1 ∨ Θ (β b) = Θ (β a) := by
    intro b hb
    refine (hinv (β b) (hβ2 b hb)).imp_right fun h => RingEquiv.ext fun c => ?_
    rw [h.2 c, hσa c]
  set φ : ↥A →* (K ≃+* K) := Θ.comp (β.comp A.subtype) with hφ
  have hrange : Nat.card φ.range ≤ 2 := by
    classical
    have hinj : Function.Injective (fun r : φ.range => decide ((r : K ≃+* K) = 1)) := by
      rintro ⟨_, b, rfl⟩ ⟨_, b', rfl⟩ h
      simp only [decide_eq_decide] at h
      apply Subtype.ext
      change Θ (β b) = Θ (β b')
      rcases hdich b b.2 with h1 | h1 <;> rcases hdich b' b'.2 with h2 | h2
      · rw [h1, h2]
      · exact absurd (h.1 h1) (h2 ▸ hΘa)
      · exact absurd (h.2 h2) (h1 ▸ hΘa)
      · rw [h1, h2]
    simpa using Nat.card_le_card_of_injective _ hinj
  have hkerF : (φ.ker.map A.subtype) ≤ A ⊓ F := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, hβF _ ?_⟩
    rw [← hker]
    exact hx
  have hAker : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ F) := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ F) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective]
      exact Subgroup.card_le_of_le hkerF
    rw [← h1]
    nlinarith
  obtain ⟨ψ, hψ⟩ := SeitzReduction.E8Pilot.exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inl rfl)
    he' K hK' (Θ (β a)) hσ (hβ2 a haA) haO
  have hfix := SeitzReduction.E7Pilot.fixSubgroup_entrywiseAdjointAut_eq_range_E7 he' hK'
    (Θ (β a)) hσ
  obtain ⟨-, hk, -⟩ := even_E7_E8_canonical_field_full_centralizer .E7 (Or.inl rfl) he' K hK'
    (Θ (β a)) hσ
  set σ := Θ (β a) with hσdef
  have : Finite (fixSubfield σ) := SeitzReduction.F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP (fixSubfield σ) 2 := SeitzReduction.F4Pilot.charP_two_of_natCard_eq_two_pow hk
  set D : Subgroup (adjointGroup .E7 K) :=
    (((A ⊓ F).subgroupOf F).map e.toMonoidHom).map ψ.toMonoidHom with hD
  have hDfix : D ≤ (fixedFieldInclusion σ).range := by
    rw [← hfix]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hbA : (b : X) ∈ A := (Subgroup.mem_subgroupOf.1 hb).1
    have hinvA : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA x hx)
    have hcomm : a * (b : X) = b * a := by
      calc a * b = (a * b)⁻¹ := (hinvA _ (A.mul_mem haA hbA)).symm
        _ = (b : X)⁻¹ * a⁻¹ := mul_inv_rev a (b : X)
        _ = b * a := by rw [hinvA _ hbA, hinvA a haA]
    have hab : MulAut.conjNormal a b = b := Subtype.ext (by
      rw [MulAut.conjNormal_apply, hcomm, mul_inv_cancel_right])
    have hβab : β a (e b) = e b := by
      rw [hβ]
      change e (MulAut.conjNormal a (e.symm (e b))) = e b
      rw [MulEquiv.symm_apply_apply, hab]
    change entrywiseAdjointAut .E7 σ (ψ (e b)) = ψ (e b)
    rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      hβab]
  set A' : Subgroup (adjointGroup .E7 (fixSubfield σ)) := D.comap (fixedFieldInclusion σ)
  have hA'card : Nat.card A' = Nat.card ↥(A ⊓ F) := by
    rw [← Subgroup.card_map_of_injective (fixedFieldInclusion_injective σ),
      Subgroup.map_comap_eq_self hDfix, hD, Subgroup.card_map_of_injective ψ.injective,
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hA'2 : ∀ x ∈ A', x ^ 2 = 1 := by
    intro x hx
    apply fixedFieldInclusion_injective σ
    obtain ⟨_, ⟨b, hb, rfl⟩, hxb⟩ := hx
    have hbA : (b : X) ∈ A := (Subgroup.mem_subgroupOf.1 hb).1
    have hb2 : b ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA _ hbA)
    rw [map_pow, map_one, ← hxb]
    change (ψ (e b)) ^ 2 = 1
    rw [← map_pow, ← map_pow, hb2, map_one, map_one]
  have hbound := CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.e7_adjoint_abelian_card_bound
    (fixSubfield σ) A' hA'2
  rw [hA'card, hk, ← pow_mul] at hbound
  have h3 : 2 ^ (27 * f) ≤ 2 ^ (e' * 27 + 1) := by
    calc 2 ^ (27 * f) ≤ Nat.card A := hcard
      _ ≤ 2 * Nat.card ↥(A ⊓ F) := hAker
      _ ≤ 2 * 2 ^ (e' * 27) := by omega
      _ = 2 ^ (e' * 27 + 1) := by ring
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  omega

end CFSG.RankThree.GF2n.Smith81
