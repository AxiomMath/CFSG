module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem card_eq_inf_mul_card_projection {Γ : Type*} [Group Γ] [Finite Γ]
    {Λ N X R : Subgroup Γ} (hΛR : Λ ≤ R) (hNR : N ≤ R) (hXR : X ≤ R)
    (hN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N)
    (hRNX : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x) (hNX : N ⊓ X = ⊥) :
    Nat.card Λ = Nat.card ↥(Λ ⊓ N) * Nat.card ↥(X ⊓ (Λ ⊔ N)) := by
  have huniq : ∀ n₁ ∈ N, ∀ x₁ ∈ X, ∀ n₂ ∈ N, ∀ x₂ ∈ X,
      n₁ * x₁ = n₂ * x₂ → x₁ = x₂ := by
    intro n₁ hn₁ x₁ hx₁ n₂ hn₂ x₂ hx₂ h
    have hx : x₂ = n₂⁻¹ * (n₁ * x₁) := by rw [h, inv_mul_cancel_left]
    have hmem : x₂ * x₁⁻¹ ∈ N ⊓ X := by
      refine Subgroup.mem_inf.mpr ⟨?_, X.mul_mem hx₂ (X.inv_mem hx₁)⟩
      have hk : x₂ * x₁⁻¹ = n₂⁻¹ * n₁ := by
        rw [hx, mul_assoc, mul_inv_cancel_right]
      rw [hk]
      exact N.mul_mem (N.inv_mem hn₂) hn₁
    rw [hNX, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem.symm
  choose! nn hnn xx hxx hdec using hRNX
  have hxmul : ∀ a ∈ Λ, ∀ b ∈ Λ, xx (a * b) = xx a * xx b := by
    intro a ha b hb
    have ha' : a ∈ R := hΛR ha
    have hb' : b ∈ R := hΛR hb
    have hab : a * b ∈ R := R.mul_mem ha' hb'
    have hfac : a * b = (nn a * (xx a * nn b * (xx a)⁻¹)) * (xx a * xx b) := by
      calc a * b = (nn a * xx a) * (nn b * xx b) := by rw [← hdec a ha', ← hdec b hb']
        _ = (nn a * (xx a * nn b * (xx a)⁻¹)) * (xx a * xx b) := by group
    refine huniq (nn (a * b)) (hnn _ hab) (xx (a * b)) (hxx _ hab)
      (nn a * (xx a * nn b * (xx a)⁻¹)) ?_ (xx a * xx b)
      (X.mul_mem (hxx a ha') (hxx b hb')) ?_
    · exact N.mul_mem (hnn a ha') (hN (xx a) (hXR (hxx a ha')) (nn b) (hnn b hb'))
    · rw [← hdec (a * b) hab, hfac]
  have hmul : ∀ a b : Λ, xx ((a * b : Λ) : Γ) = xx (a : Γ) * xx (b : Γ) := by
    intro a b
    rw [Subgroup.coe_mul]
    exact hxmul _ a.2 _ b.2
  obtain ⟨proj, hproj⟩ : ∃ proj : Λ →* Γ, ∀ ℓ : Λ, proj ℓ = xx (ℓ : Γ) :=
    ⟨MonoidHom.mk' (fun ℓ : Λ => xx (ℓ : Γ)) hmul, fun _ => rfl⟩
  have hprojX : ∀ ℓ : Λ, proj ℓ ∈ X := fun ℓ => by
    rw [hproj]
    exact hxx _ (hΛR ℓ.2)
  have hprojN : ∀ ℓ : Λ, (ℓ : Γ) = nn ℓ * proj ℓ := fun ℓ => by
    rw [hproj]
    exact hdec _ (hΛR ℓ.2)
  have hker : ∀ ℓ : Λ, proj ℓ = 1 ↔ (ℓ : Γ) ∈ N := by
    intro ℓ
    constructor
    · intro h
      have h1 := hprojN ℓ
      rw [h, mul_one] at h1
      rw [h1]
      exact hnn _ (hΛR ℓ.2)
    · intro hℓ
      refine huniq (nn ℓ) (hnn _ (hΛR ℓ.2)) (proj ℓ) (hprojX ℓ)
        (ℓ : Γ) hℓ 1 X.one_mem ?_
      rw [mul_one, ← hprojN ℓ]
  have hkerCard : Nat.card proj.ker = Nat.card ↥(Λ ⊓ N) := by
    refine Nat.card_congr
      { toFun := fun ℓ => ⟨(ℓ.1 : Γ), Subgroup.mem_inf.mpr
          ⟨ℓ.1.2, (hker ℓ.1).mp (MonoidHom.mem_ker.mp ℓ.2)⟩⟩
        invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩,
          MonoidHom.mem_ker.mpr ((hker ⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩).mpr
            (Subgroup.mem_inf.mp g.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsup : ∀ g ∈ Λ ⊔ N, ∃ ℓ ∈ Λ, ∃ n ∈ N, g = ℓ * n := by
    let S : Subgroup Γ :=
      { carrier := {g | ∃ ℓ ∈ Λ, ∃ n ∈ N, g = ℓ * n}
        mul_mem' := by
          rintro _ _ ⟨ℓ, hℓ, n, hn, rfl⟩ ⟨ℓ', hℓ', n', hn', rfl⟩
          have hc : ℓ'⁻¹ * n * ℓ' ∈ N := by
            have h := hN ℓ'⁻¹ (R.inv_mem (hΛR hℓ')) n hn
            rwa [inv_inv] at h
          exact ⟨ℓ * ℓ', Λ.mul_mem hℓ hℓ', ℓ'⁻¹ * n * ℓ' * n', N.mul_mem hc hn', by group⟩
        one_mem' := ⟨1, Λ.one_mem, 1, N.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨ℓ, hℓ, n, hn, rfl⟩
          exact ⟨ℓ⁻¹, Λ.inv_mem hℓ, ℓ * n⁻¹ * ℓ⁻¹, hN ℓ (hΛR hℓ) n⁻¹ (N.inv_mem hn),
            by group⟩ }
    have hle : Λ ⊔ N ≤ S :=
      sup_le (fun ℓ hℓ => ⟨ℓ, hℓ, 1, N.one_mem, by group⟩)
        (fun n hn => ⟨1, Λ.one_mem, n, hn, by group⟩)
    intro g hg
    obtain ⟨ℓ, hℓ, n, hn, hg'⟩ := hle hg
    exact ⟨ℓ, hℓ, n, hn, hg'⟩
  have hrange : proj.range = X ⊓ (Λ ⊔ N) := by
    ext g
    rw [MonoidHom.mem_range, Subgroup.mem_inf]
    constructor
    · rintro ⟨ℓ, rfl⟩
      refine ⟨hprojX ℓ, ?_⟩
      have h1 : proj ℓ = (nn ℓ)⁻¹ * (ℓ : Γ) := eq_inv_mul_of_mul_eq (hprojN ℓ).symm
      rw [h1]
      exact (Λ ⊔ N).mul_mem (Subgroup.mem_sup_right (N.inv_mem (hnn _ (hΛR ℓ.2))))
        (Subgroup.mem_sup_left ℓ.2)
    · rintro ⟨hgX, hgM⟩
      obtain ⟨ℓ₀, hℓ₀, n₀, hn₀, hg₀⟩ := hsup g hgM
      have hℓ₀R : ℓ₀ ∈ R := hΛR hℓ₀
      have hn' : g * n₀⁻¹ * g⁻¹ ∈ N := hN g (hXR hgX) n₀⁻¹ (N.inv_mem hn₀)
      have heq : ℓ₀ = (g * n₀⁻¹ * g⁻¹) * g := by
        rw [hg₀]
        group
      have hφℓ : nn ℓ₀ * proj ⟨ℓ₀, hℓ₀⟩ = (g * n₀⁻¹ * g⁻¹) * g :=
        (hprojN ⟨ℓ₀, hℓ₀⟩).symm.trans heq
      refine ⟨⟨ℓ₀, hℓ₀⟩, ?_⟩
      exact huniq (nn ℓ₀) (hnn _ hℓ₀R) (proj ⟨ℓ₀, hℓ₀⟩) (hprojX _) _ hn' g hgX hφℓ
  have hcard := Subgroup.card_ker_mul_card_range proj
  rw [hrange] at hcard
  rw [← hcard, hkerCard]

theorem card_prod_le_card_of_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {Λ A B : Subgroup Γ}
    (hA : A ≤ Λ) (hB : B ≤ Λ) (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card Λ := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥A × ↥B => (⟨(p.1 : Γ) * (p.2 : Γ), Λ.mul_mem (hA p.1.2) (hB p.2.2)⟩ : ↥Λ)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hf
  have hf' : (a : Γ) * (b : Γ) = (a' : Γ) * (b' : Γ) := congrArg Subtype.val hf
  have hmem : (a' : Γ)⁻¹ * (a : Γ) ∈ A ⊓ B := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have hk : (a' : Γ)⁻¹ * (a : Γ) = (b' : Γ) * (b : Γ)⁻¹ := by
      calc (a' : Γ)⁻¹ * (a : Γ) = (a' : Γ)⁻¹ * ((a : Γ) * (b : Γ)) * (b : Γ)⁻¹ := by group
        _ = (a' : Γ)⁻¹ * ((a' : Γ) * (b' : Γ)) * (b : Γ)⁻¹ := by rw [hf']
        _ = (b' : Γ) * (b : Γ)⁻¹ := by group
    rw [hk]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hbb : (b : Γ) = (b' : Γ) := by
    rw [← hmem] at hf'
    exact mul_left_cancel hf'
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hbb)

theorem card_le_mul_projections {Γ : Type*} [Group Γ] [Finite Γ]
    {Λ N₁ X₁ R₁ N₂ X₂ R₂ : Subgroup Γ}
    (hΛR₁ : Λ ≤ R₁) (hNR₁ : N₁ ≤ R₁) (hXR₁ : X₁ ≤ R₁)
    (hN₁ : ∀ r ∈ R₁, ∀ n ∈ N₁, r * n * r⁻¹ ∈ N₁)
    (hRNX₁ : ∀ r ∈ R₁, ∃ n ∈ N₁, ∃ x ∈ X₁, r = n * x) (hNX₁ : N₁ ⊓ X₁ = ⊥)
    (hΛR₂ : Λ ≤ R₂) (hNR₂ : N₂ ≤ R₂) (hXR₂ : X₂ ≤ R₂)
    (hN₂ : ∀ r ∈ R₂, ∀ n ∈ N₂, r * n * r⁻¹ ∈ N₂)
    (hRNX₂ : ∀ r ∈ R₂, ∃ n ∈ N₂, ∃ x ∈ X₂, r = n * x) (hNX₂ : N₂ ⊓ X₂ = ⊥)
    (h : Λ ⊓ N₁ ⊓ N₂ = ⊥) :
    Nat.card Λ ≤ Nat.card ↥(X₁ ⊓ (Λ ⊔ N₁)) * Nat.card ↥(X₂ ⊓ (Λ ⊔ N₂)) := by
  have h1 := card_eq_inf_mul_card_projection hΛR₁ hNR₁ hXR₁ hN₁ hRNX₁ hNX₁
  have h2 := card_eq_inf_mul_card_projection hΛR₂ hNR₂ hXR₂ hN₂ hRNX₂ hNX₂
  have hAB : (Λ ⊓ N₁) ⊓ (Λ ⊓ N₂) = ⊥ := by
    rw [← h]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have h3 := card_prod_le_card_of_inf_eq_bot (inf_le_left : Λ ⊓ N₁ ≤ Λ)
    (inf_le_left : Λ ⊓ N₂ ≤ Λ) hAB
  have hpos : 0 < Nat.card Λ := Nat.card_pos
  have hsq : Nat.card Λ * Nat.card Λ ≤
      Nat.card Λ * (Nat.card ↥(X₁ ⊓ (Λ ⊔ N₁)) * Nat.card ↥(X₂ ⊓ (Λ ⊔ N₂))) := by
    calc Nat.card Λ * Nat.card Λ
        = (Nat.card ↥(Λ ⊓ N₁) * Nat.card ↥(X₁ ⊓ (Λ ⊔ N₁))) *
            (Nat.card ↥(Λ ⊓ N₂) * Nat.card ↥(X₂ ⊓ (Λ ⊔ N₂))) := by
          rw [← h1, ← h2]
      _ = (Nat.card ↥(Λ ⊓ N₁) * Nat.card ↥(Λ ⊓ N₂)) *
            (Nat.card ↥(X₁ ⊓ (Λ ⊔ N₁)) * Nat.card ↥(X₂ ⊓ (Λ ⊔ N₂))) := by ring
      _ ≤ Nat.card Λ * (Nat.card ↥(X₁ ⊓ (Λ ⊔ N₁)) * Nat.card ↥(X₂ ⊓ (Λ ⊔ N₂))) :=
          Nat.mul_le_mul_right _ h3
  exact Nat.le_of_mul_le_mul_left hsq hpos

end CFSG.RankThree.GF2n.Stroth80
