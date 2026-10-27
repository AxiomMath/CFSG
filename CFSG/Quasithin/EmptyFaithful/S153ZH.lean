module

public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem eq_of_mul_eq_of_disjoint {X Y : Subgroup Q} (hd : X ⊓ Y = ⊥) {x x' y y' : Q} (hx : x ∈ X)
    (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y) (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have h1 : x / x' = y' / y := by
    rw [div_eq_div_iff_mul_eq_mul]
    rw [mul_comm y' x', ← h, mul_comm]
  have h2 : x / x' ∈ X ⊓ Y := ⟨X.div_mem hx hx', by rw [h1]; exact Y.div_mem hy' hy⟩
  rw [hd, Subgroup.mem_bot, div_eq_one] at h2
  refine ⟨h2, ?_⟩
  rw [h2] at h
  exact mul_left_cancel h

theorem nB_index_two [Finite Q] {A A' : Subgroup Γ} {a : Γ} (haA : a ∈ A) (ha2 : a ^ 2 = 1)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA'A : A' ≤ A)
    (hsplit : ∀ x ∈ A, x ∈ A' ∨ a⁻¹ * x ∈ A') {P' : Subgroup Q} (hP' : XMod.IsInv ↥A' P')
    (hdisj : P' ⊓ a • P' = ⊥) :
    nB A (P' ⊔ a • P') = rk ↥P' + nB A' P' := by
  classical
  unfold nB
  set P := P' ⊔ a • P' with hP
  set F := XMod.fixed ↥A (⊤ : Subgroup Q) with hF
  set F' := XMod.fixed ↥A' (⊤ : Subgroup Q) with hF'
  have haa : ∀ x : Q, a • a • x = x := by
    intro x
    rw [smul_smul, ← pow_two, ha2, one_smul]
  have hcomm : ∀ b ∈ A', ∀ x : Q, b • a • x = a • b • x := by
    intro b hb x
    rw [smul_smul, smul_smul, hAc b (hA'A hb) a haA]
  have hmemsmul : ∀ {x : Q}, x ∈ a • P' ↔ ∃ y ∈ P', a • y = x := by
    intro x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
  have haP' : ∀ y ∈ P', a • y ∈ a • P' := fun y hy => Subgroup.smul_mem_pointwise_smul _ _ _ hy
  have hP'inv' : ∀ b ∈ A', ∀ y ∈ P', b • y ∈ P' := fun b hb y hy => hP' ⟨b, hb⟩ y hy
  have haP'inv : ∀ b ∈ A', ∀ y ∈ a • P', b • y ∈ a • P' := by
    intro b hb y hy
    obtain ⟨x, hx, rfl⟩ := hmemsmul.1 hy
    rw [hcomm b hb]
    exact haP' _ (hP'inv' b hb x hx)
  have hrk : rk ↥P = 2 * rk ↥P' := by
    have h1 : rk ↥P + rk ↥(P' ⊓ a • P') = rk ↥P' + rk ↥(a • P') := rk_sup_add_rk_inf P' (a • P')
    rw [hdisj, rk_bot, rk_smul] at h1
    omega
  let ι : ↥P' →* Q :=
    P'.subtype * (MulDistribMulAction.toMonoidHom Q a).comp P'.subtype
  have hι : ∀ x : ↥P', ι x = (x : Q) * a • (x : Q) := fun x => rfl
  have hιinj : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).2 fun x hx => ?_
    rw [hι] at hx
    have h1 : (x : Q) = (a • (x : Q))⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h2 : (x : Q) ∈ a • P' := by
      rw [h1]
      exact (a • P').inv_mem (haP' _ x.2)
    have h3 : (x : Q) ∈ P' ⊓ a • P' := ⟨x.2, h2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hfixeq : P ⊓ F = ((P' ⊓ F').subgroupOf P').map ι := by
    ext p
    constructor
    · rintro ⟨hpP, hpF⟩
      obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Subgroup.mem_sup.1 hpP
      have hfixb : ∀ b : ↥A, b • (p₁ * p₂) = p₁ * p₂ := fun b => (XMod.mem_fixed.1 hpF).2 b
      obtain ⟨x₂, hx₂, rfl⟩ := hmemsmul.1 hp₂
      have h1 := hfixb ⟨a, haA⟩
      change a • (p₁ * a • x₂) = p₁ * a • x₂ at h1
      rw [smul_mul', haa] at h1
      have h2 := eq_of_mul_eq_of_disjoint hdisj (x := x₂) (x' := p₁) (y := a • p₁) (y' := a • x₂)
        hx₂ hp₁ (haP' _ hp₁) (haP' _ hx₂) (by rw [mul_comm]; exact h1)
      have hp₂eq : a • x₂ = a • p₁ := by rw [h2.1]
      refine ⟨⟨p₁, hp₁⟩, ⟨hp₁, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩, ?_⟩
      · have h3 := hfixb ⟨(b : Γ), hA'A b.2⟩
        change (b : Γ) • (p₁ * a • x₂) = p₁ * a • x₂ at h3
        rw [smul_mul', hcomm (b : Γ) b.2] at h3
        have h4 := eq_of_mul_eq_of_disjoint hdisj (x := (b : Γ) • p₁) (x' := p₁)
          (y := a • (b : Γ) • x₂) (y' := a • x₂) (hP'inv' _ b.2 _ hp₁) hp₁
          (haP' _ (hP'inv' _ b.2 _ hx₂)) (haP' _ hx₂) h3
        exact h4.1
      · rw [hι]
        show p₁ * a • p₁ = p₁ * a • x₂
        rw [hp₂eq]
    · rintro ⟨x, hx, rfl⟩
      have hxP' : (x : Q) ∈ P' := x.2
      have hxF' : (x : Q) ∈ F' := (Subgroup.mem_subgroupOf.1 hx).2
      have hxfix : ∀ b : Γ, b ∈ A' → b • (x : Q) = x := fun b hb => (XMod.mem_fixed.1 hxF').2 ⟨b, hb⟩
      refine ⟨Subgroup.mul_mem_sup hxP' (haP' _ hxP'), XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩
      rw [hι]
      change (b : Γ) • ((x : Q) * a • (x : Q)) = (x : Q) * a • (x : Q)
      rcases hsplit (b : Γ) b.2 with hb | hb
      · rw [smul_mul', hcomm _ hb, hxfix _ hb]
      · set b' : Γ := a⁻¹ * (b : Γ) with hb'
        have hbeq : (b : Γ) = a * b' := by rw [hb']; group
        rw [hbeq, mul_smul, smul_mul', hcomm b' hb, hxfix b' hb, smul_mul', haa, mul_comm]
  have hrkfix : rk ↥(P ⊓ F) = rk ↥(P' ⊓ F') := by
    rw [hfixeq]
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ ι hιinj).toEquiv.symm]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  have h5 : rk ↥(P' ⊓ F') ≤ rk ↥P' := rk_mono inf_le_left
  rw [hrkfix, hrk]
  omega

end CFSG.Quasithin.Z391
