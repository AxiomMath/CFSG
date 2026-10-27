module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Refl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem eq_of_smul_eq_smul_of_ne_one {e : W} (he : e ≠ 1) {a b : S.K}
    (h : S.smul a e = S.smul b e) : a = b := by
  have hvec : S.vec e ≠ 0 := fun h0 => he (S.vec_injective (by rw [h0, S.vec_one]))
  have hex : ∃ i, S.vec e i ≠ 0 := by
    by_contra h
    push Not at h
    exact hvec (funext h)
  obtain ⟨i, hi⟩ := hex
  have h' := congrFun (congrArg S.vec h) i
  rw [S.vec_smul, S.vec_smul] at h'
  simp only [Pi.smul_apply, smul_eq_mul] at h'
  exact mul_right_cancel₀ hi h'

theorem reflection_formula {g : MulAut W}
    (hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w))
    (hiso : ∀ w : W, S.Q (g w) = S.Q w) (hg1 : g ≠ 1) {e : W} (hQ : S.Q e ≠ 0)
    (hline : ∀ w : W, ∃ a : S.K, g w * w⁻¹ = S.smul a e) :
    ∀ (w : W) (a : S.K), g w * w⁻¹ = S.smul a e → a * S.Q e = S.pol w e := by
  classical
  have he1 : e ≠ 1 := fun h => hQ (by rw [h, S.Q_one])
  let lam : W → S.K := fun w => Classical.choose (hline w)
  have hlam : ∀ w : W, g w * w⁻¹ = S.smul (lam w) e := fun w =>
    Classical.choose_spec (hline w)
  have hgw : ∀ w : W, g w = S.smul (lam w) e * w := fun w => by
    rw [← inv_mul_cancel_right (g w) w, hlam w]
  have hadd : ∀ w w' : W, lam (w * w') = lam w + lam w' := by
    intro w w'
    apply S.eq_of_smul_eq_smul_of_ne_one he1
    rw [← hlam (w * w'), map_mul, mul_inv_rev, S.smul_add_eq, ← hlam w, ← hlam w']
    ac_rfl
  have hsmulc : ∀ (c : S.K) (w : W), lam (S.smul c w) = c * lam w := by
    intro c w
    apply S.eq_of_smul_eq_smul_of_ne_one he1
    rw [← hlam (S.smul c w)]
    have hinv : (S.smul c w)⁻¹ = S.smul c w⁻¹ := by
      apply inv_eq_of_mul_eq_one_right
      rw [← S.smul_mul_eq, mul_inv_cancel, S.smul_one_elem]
    rw [hlin c w, hinv, ← S.smul_mul_eq, hlam w, S.smul_smul_eq]
  have hiso_lam : ∀ w : W, lam w * (lam w * S.Q e + S.pol w e) = 0 := by
    intro w
    have h := hiso w
    rw [hgw w, S.Q_mul, S.Q_smul, S.pol_smul_left, S.pol_comm e w] at h
    have hAB : (lam w) ^ 2 * S.Q e + lam w * S.pol w e = 0 := by
      have hcomm : (lam w) ^ 2 * S.Q e + S.Q w + lam w * S.pol w e
          = ((lam w) ^ 2 * S.Q e + lam w * S.pol w e) + S.Q w := by ring
      rw [hcomm] at h
      exact add_right_cancel (h.trans (zero_add (S.Q w)).symm)
    rw [show lam w * (lam w * S.Q e + S.pol w e)
      = (lam w) ^ 2 * S.Q e + lam w * S.pol w e by ring, hAB]
  have hmu_ne : ∀ w : W, lam w ≠ 0 → lam w * S.Q e + S.pol w e = 0 := by
    intro w hw
    rcases mul_eq_zero.1 (hiso_lam w) with h | h
    · exact absurd h hw
    · exact h
  have hmu_add : ∀ w w' : W, lam (w * w') * S.Q e + S.pol (w * w') e
      = (lam w * S.Q e + S.pol w e) + (lam w' * S.Q e + S.pol w' e) := by
    intro w w'
    rw [hadd w w', S.pol_mul_left]
    ring
  have hmu_zero : ∀ w : W, lam w * S.Q e + S.pol w e = 0 := by
    intro w
    by_cases hw : lam w = 0
    · obtain ⟨y, hy⟩ : ∃ y : W, g y ≠ y := by
        by_contra h
        push Not at h
        exact hg1 (MulEquiv.ext h)
      have hly : lam y ≠ 0 := by
        intro h0
        exact hy (by rw [hgw y, h0, S.smul_zero_eq, one_mul])
      have hwy : lam (w * y) ≠ 0 := by
        rw [hadd w y, hw, zero_add]
        exact hly
      have h1 : lam (w * y) * S.Q e + S.pol (w * y) e = 0 := hmu_ne (w * y) hwy
      rw [hmu_add w y, hmu_ne y hly] at h1
      simpa using h1
    · exact hmu_ne w hw
  intro w a ha
  have hlam_eq : lam w = a := by
    apply S.eq_of_smul_eq_smul_of_ne_one he1
    exact (hlam w).symm.trans ha
  have hfin : lam w * S.Q e = S.pol w e := CharTwo.add_eq_zero.mp (hmu_zero w)
  rw [hlam_eq] at hfin
  exact hfin

theorem card_fixed_mul_le_of_ne {g₁ g₂ : MulAut W}
    (hl₁ : ∀ (c : S.K) (w : W), g₁ (S.smul c w) = S.smul c (g₁ w))
    (hl₂ : ∀ (c : S.K) (w : W), g₂ (S.smul c w) = S.smul c (g₂ w))
    (hi₁ : ∀ w : W, S.Q (g₁ w) = S.Q w) (hi₂ : ∀ w : W, S.Q (g₂ w) = S.Q w)
    (ho₁ : g₁ * g₁ = 1) (ho₂ : g₂ * g₂ = 1) (hne₁ : g₁ ≠ 1) (hne₂ : g₂ ≠ 1) (hne : g₁ ≠ g₂)
    (hf₁ : Nat.card S.K ^ 2 < Nat.card {v : W // g₁ v = v})
    (hf₂ : Nat.card S.K ^ 2 < Nat.card {v : W // g₂ v = v}) :
    Nat.card {v : W // (g₁ * g₂) v = v} ≤ Nat.card S.K ^ 2 := by
  classical
  obtain ⟨e₁, hQ₁, -, hline₁⟩ := S.exists_line_of_card_fixed_gt hl₁ hi₁ hne₁ hf₁
  obtain ⟨e₂, hQ₂, -, hline₂⟩ := S.exists_line_of_card_fixed_gt hl₂ hi₂ hne₂ hf₂
  have he₁ : e₁ ≠ 1 := fun h => hQ₁ (by rw [h, S.Q_one])
  have he₂ : e₂ ≠ 1 := fun h => hQ₂ (by rw [h, S.Q_one])
  let lam₁ : W → S.K := fun w => Classical.choose (hline₁ w)
  let lam₂ : W → S.K := fun w => Classical.choose (hline₂ w)
  have hlam₁ : ∀ w, g₁ w * w⁻¹ = S.smul (lam₁ w) e₁ := fun w =>
    Classical.choose_spec (hline₁ w)
  have hlam₂ : ∀ w, g₂ w * w⁻¹ = S.smul (lam₂ w) e₂ := fun w =>
    Classical.choose_spec (hline₂ w)
  have hgw₁ : ∀ w, g₁ w = S.smul (lam₁ w) e₁ * w := fun w => by
    rw [← inv_mul_cancel_right (g₁ w) w, hlam₁ w]
  have hgw₂ : ∀ w, g₂ w = S.smul (lam₂ w) e₂ * w := fun w => by
    rw [← inv_mul_cancel_right (g₂ w) w, hlam₂ w]
  have hrefl₁ : ∀ w, lam₁ w * S.Q e₁ = S.pol w e₁ := fun w =>
    S.reflection_formula hl₁ hi₁ hne₁ hQ₁ hline₁ w (lam₁ w) (hlam₁ w)
  have hrefl₂ : ∀ w, lam₂ w * S.Q e₂ = S.pol w e₂ := fun w =>
    S.reflection_formula hl₂ hi₂ hne₂ hQ₂ hline₂ w (lam₂ w) (hlam₂ w)
  have indep : ∀ a b : S.K, S.smul a e₁ = S.smul b e₂ → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · refine ⟨ha, ?_⟩
      exact S.eq_of_smul_eq_smul_of_ne_one he₂
        (by rw [← hab, ha, S.smul_zero_eq, S.smul_zero_eq])
    · by_cases hb : b = 0
      · refine ⟨?_, hb⟩
        exact S.eq_of_smul_eq_smul_of_ne_one he₁
          (by rw [hab, hb, S.smul_zero_eq, S.smul_zero_eq])
      · exfalso
        let c : S.K := a * b⁻¹
        have hc : c ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
        have he₂_eq : e₂ = S.smul c e₁ := by
          have h1 : S.smul b⁻¹ (S.smul a e₁) = S.smul b⁻¹ (S.smul b e₂) := by rw [hab]
          rw [S.smul_smul_eq, S.smul_smul_eq] at h1
          have hb1 : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
          rw [hb1, S.smul_one_eq, mul_comm b⁻¹ a] at h1
          exact h1.symm
        have hstep : ∀ w, lam₂ w * c = lam₁ w := by
          intro w
          have h₂ := hrefl₂ w
          rw [he₂_eq, S.Q_smul, S.pol_smul_right, ← hrefl₁ w] at h₂
          have h₂' : (lam₂ w * c) * (c * S.Q e₁) = lam₁ w * (c * S.Q e₁) := by
            have hh : (lam₂ w * c) * (c * S.Q e₁) = lam₂ w * (c ^ 2 * S.Q e₁) := by ring
            have hh2 : lam₁ w * (c * S.Q e₁) = c * (lam₁ w * S.Q e₁) := by ring
            rw [hh, h₂, hh2]
          exact mul_right_cancel₀ (mul_ne_zero hc hQ₁) h₂'
        have hg_eq : g₂ = g₁ := by
          apply MulEquiv.ext
          intro w
          rw [hgw₂ w, hgw₁ w, he₂_eq, S.smul_smul_eq, hstep w]
        exact hne hg_eq.symm
  have hfix_iff : ∀ x : W, (g₁ * g₂) x = x ↔ (lam₁ x = 0 ∧ lam₂ x = 0) := by
    intro x
    have hiff : (g₁ * g₂) x = x ↔ g₂ x = g₁ x := by
      constructor
      · intro h
        have key : g₁ ((g₁ * g₂) x) = g₂ x := by
          rw [← MulAut.mul_apply, ← mul_assoc, ho₁, one_mul]
        rw [h] at key
        exact key.symm
      · intro h
        rw [MulAut.mul_apply, h, ← MulAut.mul_apply, ho₁, MulAut.one_apply]
    rw [hiff, hgw₁ x, hgw₂ x, mul_right_cancel_iff]
    constructor
    · intro h
      exact indep (lam₁ x) (lam₂ x) h.symm
    · rintro ⟨h1, h2⟩
      rw [h1, h2, S.smul_zero_eq, S.smul_zero_eq]
  let Ψ : W →* Multiplicative (S.K × S.K) :=
    { toFun := fun x => Multiplicative.ofAdd (S.pol x e₁, S.pol x e₂)
      map_one' := by
        rw [ofAdd_eq_one, Prod.mk_eq_zero]
        constructor <;> simp [pol, S.Q_one]
      map_mul' := by
        intro x y
        rw [← ofAdd_add]
        apply Multiplicative.ofAdd.injective
        ext <;> simp [S.pol_mul_left] }
  have hΨ : ∀ x : W, Ψ x = Multiplicative.ofAdd (S.pol x e₁, S.pol x e₂) := fun _ => rfl
  have hker : ∀ x : W, x ∈ Ψ.ker ↔ (lam₁ x = 0 ∧ lam₂ x = 0) := by
    intro x
    rw [MonoidHom.mem_ker, hΨ x, ofAdd_eq_one, Prod.mk_eq_zero,
      ← hrefl₁ x, ← hrefl₂ x, mul_eq_zero_iff_right hQ₁, mul_eq_zero_iff_right hQ₂]
  have hfix_ker : Nat.card {v : W // (g₁ * g₂) v = v} = Nat.card Ψ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hfix_iff x).trans (hker x).symm))
  let p : Submodule S.K (S.K × S.K) :=
    { carrier := {y | Multiplicative.ofAdd y ∈ Ψ.range}
      zero_mem' := by
        change Multiplicative.ofAdd (0 : S.K × S.K) ∈ Ψ.range
        rw [ofAdd_zero]
        exact Ψ.range.one_mem
      add_mem' := by
        intro y z hy hz
        change Multiplicative.ofAdd (y + z) ∈ Ψ.range
        rw [ofAdd_add]
        exact Ψ.range.mul_mem hy hz
      smul_mem' := by
        intro c y hy
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
        refine MonoidHom.mem_range.mpr ⟨S.smul c x, ?_⟩
        have hy' : y = (S.pol x e₁, S.pol x e₂) := by
          have h1 : (Ψ x).toAdd = y := congrArg Multiplicative.toAdd hx
          rw [hΨ x] at h1
          simpa using h1.symm
        rw [hy', hΨ (S.smul c x), S.pol_smul_left, S.pol_smul_left]
        simp [Prod.smul_mk, smul_eq_mul] }
  have hp_top : p = ⊤ := by
    by_contra hne_p
    have hp_lt : p < ⊤ := lt_top_iff_ne_top.mpr hne_p
    obtain ⟨F, hFne, hpF⟩ := Submodule.exists_le_ker_of_lt_top p hp_lt
    have hxmem : ∀ x : W, (S.pol x e₁, S.pol x e₂) ∈ p := by
      intro x
      show Multiplicative.ofAdd (S.pol x e₁, S.pol x e₂) ∈ Ψ.range
      rw [← hΨ x]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    have hvan : ∀ x : W, F (S.pol x e₁, S.pol x e₂) = 0 := fun x => hpF (hxmem x)
    have hF_eq : ∀ y : S.K × S.K, F y = F (1, 0) * y.1 + F (0, 1) * y.2 := by
      intro y
      have hy : y = y.1 • (1, 0) + y.2 • (0, 1) := by ext <;> simp
      conv_lhs => rw [hy]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have hfun : ∀ w' : W,
        S.pol (S.smul (F (1, 0)) e₁ * S.smul (F (0, 1)) e₂) w' = 0 := by
      intro x
      rw [S.pol_comm, S.pol_mul_right, S.pol_smul_right, S.pol_smul_right]
      have h := hF_eq (S.pol x e₁, S.pol x e₂)
      rw [hvan x] at h
      simpa using h.symm
    have hprod : S.smul (F (1, 0)) e₁ * S.smul (F (0, 1)) e₂ = 1 :=
      S.eq_one_of_pol_eq_zero hfun
    have hprod' : S.smul (F (1, 0)) e₁ = S.smul (F (0, 1)) e₂ := by
      have h1 := eq_inv_of_mul_eq_one_left hprod
      have h2 : (S.smul (F (0, 1)) e₂)⁻¹ = S.smul (F (0, 1)) e₂ := by
        apply inv_eq_of_mul_eq_one_right
        apply S.vec_injective
        rw [S.vec_mul, S.vec_one]
        exact CharTwo.add_self_eq_zero (S.vec (S.smul (F (0, 1)) e₂))
      rwa [h2] at h1
    obtain ⟨hα0, hβ0⟩ := indep (F (1, 0)) (F (0, 1)) hprod'
    have hFzero : F = 0 := by
      apply LinearMap.ext
      intro y
      rw [hF_eq y, hα0, hβ0]
      simp
    exact hFne hFzero
  have hrange : Ψ.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    have hz : Multiplicative.toAdd z ∈ p := by
      rw [hp_top]
      exact Submodule.mem_top
    exact hz
  have hcard_ker : Nat.card Ψ.ker = Nat.card S.K ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range Ψ
    rw [hrange, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      S.card_eq] at h
    have hq : Nat.card S.K * Nat.card S.K ≠ 0 :=
      mul_ne_zero (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
        (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
    have h' : Nat.card Ψ.ker * (Nat.card S.K * Nat.card S.K)
        = (Nat.card S.K * Nat.card S.K) * (Nat.card S.K * Nat.card S.K) := by
      rw [h]
      ring
    have hcancel := mul_right_cancel₀ hq h'
    simpa [pow_two] using hcancel
  exact le_of_eq (hfix_ker.trans hcard_ker)

theorem card_le_two_of_card_fixed_gt (H : Subgroup (MulAut W))
    (hN : H ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) (hord : ∀ g ∈ H, g * g = 1)
    (hfix : ∀ g ∈ H, g ≠ 1 → Nat.card S.K ^ 2 < Nat.card {v : W // g v = v}) :
    Nat.card H ≤ 2 := by
  classical
  by_contra hcon
  have hcard : 2 < Nat.card H := not_le.1 hcon
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype H := Fintype.ofFinite H
  have hcard' : 2 < Fintype.card H := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hcard'
  have hex : ∃ g₁ ∈ H, ∃ g₂ ∈ H, g₁ ≠ 1 ∧ g₂ ≠ 1 ∧ g₁ ≠ g₂ := by
    by_cases ha : (a : MulAut W) = 1
    · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
      · intro hb
        exact hab (Subtype.ext (by rw [ha, hb]))
      · intro hc
        exact hac (Subtype.ext (by rw [ha, hc]))
    · by_cases hb : (b : MulAut W) = 1
      · refine ⟨a, a.2, c, c.2, ha, ?_, fun h => hac (Subtype.ext h)⟩
        intro hc
        exact hbc (Subtype.ext (by rw [hb, hc]))
      · exact ⟨a, a.2, b, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, h1, h2, h12⟩ := hex
  have hprod : g₁ * g₂ ∈ H := H.mul_mem hg₁ hg₂
  have hprod1 : g₁ * g₂ ≠ 1 := by
    intro h
    apply h12
    have := hord g₁ hg₁
    calc g₁ = g₁ * (g₂ * g₂) := by rw [hord g₂ hg₂, mul_one]
      _ = (g₁ * g₂) * g₂ := by rw [mul_assoc]
      _ = g₂ := by rw [h, one_mul]
  obtain ⟨hl₁, hi₁⟩ := S.linear_isometry_of_card_fixed_gt (hN hg₁) (hord g₁ hg₁) (hfix g₁ hg₁ h1)
  obtain ⟨hl₂, hi₂⟩ := S.linear_isometry_of_card_fixed_gt (hN hg₂) (hord g₂ hg₂) (hfix g₂ hg₂ h2)
  exact absurd (S.card_fixed_mul_le_of_ne hl₁ hl₂ hi₁ hi₂ (hord g₁ hg₁) (hord g₂ hg₂) h1 h2 h12
    (hfix g₁ hg₁ h1) (hfix g₂ hg₂ h2)) (not_le.2 (hfix _ hprod hprod1))

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
