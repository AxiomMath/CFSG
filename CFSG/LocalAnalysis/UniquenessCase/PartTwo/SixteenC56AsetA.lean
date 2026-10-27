module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Space

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem commutator_mem_perp_fixV {A : Subgroup (MulAut W)}
    (hiso : ∀ g ∈ A, ∀ w : W, S.Q (g w) = S.Q w) {g : MulAut W} (hg : g ∈ A) (w : W) :
    g w * w⁻¹ ∈ S.perp (fixV A) := by
  rw [S.mem_perp]
  intro f hf
  have hgf : g f = f := mem_fixV.1 hf g hg
  have hww : w⁻¹ = w := by
    apply S.vec_injective
    rw [S.vec_inv, CharTwo.neg_eq]
  have hpol : S.pol (g w) f = S.pol w f := by
    calc S.pol (g w) f = S.pol (g w) (g f) := by rw [hgf]
      _ = S.pol w f := by simp only [pol, ← map_mul, hiso g hg]
  rw [S.pol_mul_left, hpol, hww, CharTwo.add_self_eq_zero]

theorem Q_commutator_eq_pol {g : MulAut W} (hg : ∀ w : W, S.Q (g w) = S.Q w) (w : W) :
    S.Q (g w * w⁻¹) = S.pol w (g w * w⁻¹) := by
  set δ : W := g w * w⁻¹ with hδ
  have hgw : g w = w * δ := by
    rw [hδ, ← mul_assoc, mul_comm w (g w), mul_assoc, mul_inv_cancel, mul_one]
  have h := hg w
  rw [hgw, S.Q_mul] at h
  rw [add_assoc] at h
  have hbc : S.Q δ + S.pol w δ = 0 := by
    have h' : S.Q w + 0 = S.Q w + (S.Q δ + S.pol w δ) := by rw [h, add_zero]
    exact (add_left_cancel h').symm
  exact CharTwo.add_eq_zero.mp hbc

theorem exists_singular_of_isotropic {F : Subgroup W} (hF : ∀ x ∈ F, ∀ y ∈ F, S.pol x y = 0)
    (hcard : Nat.card S.K < Nat.card F) : ∃ θ ∈ F, θ ≠ 1 ∧ S.Q θ = 0 := by
  classical
  let φ : F →* Multiplicative S.K :=
    { toFun := fun δ => Multiplicative.ofAdd (S.Q (δ : W))
      map_one' := by
        change Multiplicative.ofAdd (S.Q (1 : W)) = 1
        rw [S.Q_one, ofAdd_zero]
      map_mul' := fun δ δ' => by
        change Multiplicative.ofAdd (S.Q ((δ : W) * (δ' : W))) =
          Multiplicative.ofAdd (S.Q (δ : W)) * Multiplicative.ofAdd (S.Q (δ' : W))
        rw [← ofAdd_add]
        apply Multiplicative.ofAdd.injective
        rw [S.Q_mul, hF (δ : W) δ.2 (δ' : W) δ'.2, add_zero] }
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have hle : Nat.card F ≤ Nat.card (Multiplicative S.K) :=
      Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_congr Multiplicative.toAdd] at hle
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnotinj
  refine ⟨(x : W) * (y : W)⁻¹, F.mul_mem x.2 (F.inv_mem y.2), ?_, ?_⟩
  · intro h
    exact hne (Subtype.ext (by
      have h' := congrArg (· * (y : W)) h
      simpa [mul_assoc] using h'))
  · have hφ1 : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact ofAdd_eq_one.mp hφ1

theorem exists_subgroup_card_le {F : Subgroup W} (hF : S.IsSub F)
    (hiso : ∀ x ∈ F, ∀ y ∈ F, S.pol x y = 0) (hcard : Nat.card F = Nat.card S.K ^ 2) {θ : W}
    (hθF : θ ∈ F) (hθQ : S.Q θ = 0) {w : W} (hw : S.pol w θ ≠ 0) :
    ∃ N : Subgroup W, N ≤ F ∧ Nat.card N ≤ Nat.card S.K ∧
      ∀ δ ∈ F, S.Q δ = S.pol w δ → δ ∈ N := by
  classical
  have hqpos : 0 < Nat.card S.K := by have := S.four_le; omega
  let ψ : F →* Multiplicative S.K :=
    { toFun := fun δ => Multiplicative.ofAdd (S.Q (δ : W) + S.pol w (δ : W))
      map_one' := by
        change Multiplicative.ofAdd (S.Q (1 : W) + S.pol w (1 : W)) = 1
        have h1 : S.pol w (1 : W) = 0 := by simp [pol, S.Q_one]
        rw [S.Q_one, h1, zero_add, ofAdd_zero]
      map_mul' := fun δ δ' => by
        change Multiplicative.ofAdd (S.Q ((δ : W) * (δ' : W)) +
            S.pol w ((δ : W) * (δ' : W))) =
          Multiplicative.ofAdd (S.Q (δ : W) + S.pol w (δ : W)) *
            Multiplicative.ofAdd (S.Q (δ' : W) + S.pol w (δ' : W))
        rw [← ofAdd_add]
        apply Multiplicative.ofAdd.injective
        rw [S.Q_mul, hiso (δ : W) δ.2 (δ' : W) δ'.2, S.pol_mul_right]
        ring }
  have hsurj : Function.Surjective ψ := by
    intro y
    refine ⟨⟨S.smul (Multiplicative.toAdd y / S.pol w θ) θ,
      hF (Multiplicative.toAdd y / S.pol w θ) θ hθF⟩, ?_⟩
    have hc : Multiplicative.toAdd y / S.pol w θ * S.pol w θ = Multiplicative.toAdd y :=
      div_mul_cancel₀ _ hw
    show Multiplicative.ofAdd (S.Q (S.smul (Multiplicative.toAdd y / S.pol w θ) θ) +
      S.pol w (S.smul (Multiplicative.toAdd y / S.pol w θ) θ)) = y
    rw [S.Q_smul, hθQ, mul_zero, S.pol_smul_right, zero_add, hc,
      ofAdd_toAdd]
  have hrange : Nat.card ψ.range = Nat.card S.K := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd
  have hker := Subgroup.card_ker_mul_card_range ψ
  have hkercard : Nat.card ψ.ker = Nat.card S.K := by
    have hker' : Nat.card ψ.ker * Nat.card S.K = Nat.card S.K * Nat.card S.K := by
      rw [hrange, hcard, pow_two] at hker
      exact hker
    exact Nat.eq_of_mul_eq_mul_right hqpos hker'
  refine ⟨ψ.ker.map F.subtype, Subgroup.map_subtype_le ψ.ker, ?_, ?_⟩
  · have hNcard : Nat.card (ψ.ker.map F.subtype) = Nat.card S.K := by
      rw [Subgroup.card_map_of_injective F.subtype_injective, hkercard]
    exact le_of_eq hNcard
  · intro δ hδF hδQ
    rw [Subgroup.mem_map]
    refine ⟨⟨δ, hδF⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (S.Q δ + S.pol w δ) = 1
    rw [hδQ, CharTwo.add_self_eq_zero, ofAdd_zero]

theorem eq_perp_of_card_inf_gt {F : Subgroup W} (hF : S.IsSub F) (hq : 2 ≤ Nat.card S.K)
    (h : Nat.card S.K < Nat.card ↥(F ⊓ S.perp F)) :
    F = S.perp F ∧ Nat.card F = Nat.card S.K ^ 2 := by
  obtain ⟨d, hd⟩ := S.exists_card_eq_pow (S.isSub_inf hF (S.isSub_perp F))
  have hqpos : 0 < Nat.card S.K := by omega
  have hd2 : 2 ≤ d := by
    by_contra hdlt
    have hdle : d ≤ 1 := by omega
    have hpow : Nat.card S.K ^ d ≤ Nat.card S.K ^ 1 := Nat.pow_le_pow_right hqpos hdle
    rw [pow_one] at hpow
    omega
  have hEge : Nat.card S.K ^ 2 ≤ Nat.card ↥(F ⊓ S.perp F) := by
    have hpow := Nat.pow_le_pow_right hqpos hd2
    rwa [← hd] at hpow
  have hperpmul : Nat.card F * Nat.card (S.perp F) = Nat.card S.K ^ 4 := S.card_mul_card_perp hF
  have hFne : Nat.card F ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hperpmul
    have : 0 < Nat.card S.K ^ 4 := pow_pos hqpos 4
    omega
  haveI : Finite F := Nat.finite_of_card_ne_zero hFne
  have hPne : Nat.card (S.perp F) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hperpmul
    have : 0 < Nat.card S.K ^ 4 := pow_pos hqpos 4
    omega
  haveI : Finite (S.perp F) := Nat.finite_of_card_ne_zero hPne
  have hFge : Nat.card S.K ^ 2 ≤ Nat.card F :=
    le_trans hEge (Subgroup.card_le_of_le inf_le_left)
  have hPge : Nat.card S.K ^ 2 ≤ Nat.card (S.perp F) :=
    le_trans hEge (Subgroup.card_le_of_le inf_le_right)
  have ha : Nat.card F = Nat.card S.K ^ 2 := by
    refine le_antisymm ?_ hFge
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hbpos : 0 < Nat.card (S.perp F) := lt_of_lt_of_le (pow_pos hqpos 2) hPge
    have hmul : Nat.card S.K ^ 2 * Nat.card (S.perp F) <
        Nat.card F * Nat.card (S.perp F) := mul_lt_mul_of_pos_right hlt' hbpos
    rw [hperpmul] at hmul
    have hle : Nat.card S.K ^ 2 * Nat.card S.K ^ 2 ≤
        Nat.card S.K ^ 2 * Nat.card (S.perp F) := Nat.mul_le_mul (le_refl _) hPge
    have hq4 : Nat.card S.K ^ 2 * Nat.card S.K ^ 2 = Nat.card S.K ^ 4 := by ring
    omega
  have hb : Nat.card (S.perp F) = Nat.card S.K ^ 2 := by
    refine le_antisymm ?_ hPge
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hfpos : 0 < Nat.card F := lt_of_lt_of_le (pow_pos hqpos 2) hFge
    have hmul : Nat.card F * Nat.card S.K ^ 2 <
        Nat.card F * Nat.card (S.perp F) := mul_lt_mul_of_pos_left hlt' hfpos
    rw [hperpmul] at hmul
    have hle : Nat.card S.K ^ 2 * Nat.card S.K ^ 2 ≤
        Nat.card F * Nat.card S.K ^ 2 := Nat.mul_le_mul hFge (le_refl _)
    have hq4 : Nat.card S.K ^ 2 * Nat.card S.K ^ 2 = Nat.card S.K ^ 4 := by ring
    omega
  have hEF : F ⊓ S.perp F = F :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ha]; exact hEge)
  have hEP : F ⊓ S.perp F = S.perp F :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hb]; exact hEge)
  exact ⟨hEF.symm.trans hEP, ha⟩

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
