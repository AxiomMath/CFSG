module

public import CFSG.Quasithin.Vol2.Ch3E213MP2A
public import CFSG.Quasithin.H13.QRCPairedBorel

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.Blueprint

variable {A : Type*} [Group A] {K₁ K₂ : Subgroup A}

theorem exists_conj_eq_of_isPGroup {X : Subgroup A} {a : ℕ}
    {k : Type} [Field k] (ha : 1 ≤ a) (hk : Nat.card k = 2 ^ (2 * a + 1))
    (θ : X ≃* suzukiGroup a k) {P : Subgroup A} (hP : IsPGroup 2 P)
    (hPX : P ≤ normalizer (X : Set A)) {p : A} (hp : p ∈ P) :
    ∃ y ∈ X, ∀ x ∈ X, p * x * p⁻¹ = y * x * y⁻¹ := by
  set φ : normalizer (X : Set A) →* MulAut (suzukiGroup a k) :=
    (MulAut.congr θ).toMonoidHom.comp X.normalizerMonoidHom with hφ
  have hP' : IsPGroup 2 ((P.subgroupOf (normalizer (X : Set A))).map φ) :=
    hP.comap_subtype.map φ
  obtain ⟨y, hy⟩ :=
    (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
      ha hk).2 _ hP' ⟨⟨p, hPX hp⟩, mem_subgroupOf.2 hp, rfl⟩
  refine ⟨(θ.symm y : A), (θ.symm y).2, fun x hx => ?_⟩
  have h1 := congrArg (fun α : MulAut (suzukiGroup a k) => θ.symm (α (θ ⟨x, hx⟩))) hy
  simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul,
    map_inv] at h1
  have h2 := congrArg Subtype.val h1
  simp only [coe_mul, coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  exact h2.symm

theorem commute_of_conj_eq {X : Subgroup A} {p w : A} (hw : ∀ x ∈ X, w⁻¹ * x * w ∈ X)
    (h : ∀ x ∈ X, p * x * p⁻¹ = w * x * w⁻¹) : ∀ x ∈ X, p * w⁻¹ * x = x * (p * w⁻¹) := by
  intro x hx
  have h1 := h _ (hw x hx)
  rw [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at h1
  calc p * w⁻¹ * x = p * (w⁻¹ * x * w) * p⁻¹ * (p * w⁻¹) := by group
    _ = x * (p * w⁻¹) := by rw [h1]

theorem le_sup_of_isPGroup {a : ℕ} {k : Type} [Field k]
    (ha : 1 ≤ a) (hk : Nat.card k = 2 ^ (2 * a + 1)) (θ₁ : K₁ ≃* suzukiGroup a k)
    (θ₂ : K₂ ≃* suzukiGroup a k) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hCK : ∀ x : A, (∀ y ∈ K₁ ⊔ K₂, x * y = y * x) → x = 1) {P : Subgroup A}
    (hP : IsPGroup 2 P) (hP₁ : P ≤ normalizer (K₁ : Set A))
    (hP₂ : P ≤ normalizer (K₂ : Set A)) : P ≤ K₁ ⊔ K₂ := by
  intro p hp
  obtain ⟨y₁, hy₁, h₁⟩ := exists_conj_eq_of_isPGroup ha hk θ₁ hP hP₁ hp
  obtain ⟨y₂, hy₂, h₂⟩ := exists_conj_eq_of_isPGroup ha hk θ₂ hP hP₂ hp
  set w := y₁ * y₂ with hw
  have hwK : w ∈ K₁ ⊔ K₂ := mul_mem_sup hy₁ hy₂
  have hw₁ : ∀ x ∈ K₁, p * x * p⁻¹ = w * x * w⁻¹ := by
    intro x hx
    rw [h₁ x hx, hw, show y₁ * y₂ * x * (y₁ * y₂)⁻¹ = y₁ * (y₂ * x * y₂⁻¹) * y₁⁻¹ by group,
      ← hc x hx y₂ hy₂, mul_inv_cancel_right]
  have hw₂ : ∀ x ∈ K₂, p * x * p⁻¹ = w * x * w⁻¹ := by
    intro x hx
    rw [h₂ x hx, hw, show y₁ * y₂ * x * (y₁ * y₂)⁻¹ = y₁ * (y₂ * x * y₂⁻¹) * y₁⁻¹ by group,
      hc y₁ hy₁ _ (K₂.mul_mem (K₂.mul_mem hy₂ hx) (K₂.inv_mem hy₂)), mul_inv_cancel_right]
  have hwn₁ : ∀ x ∈ K₁, w⁻¹ * x * w ∈ K₁ := by
    intro x hx
    rw [hw, show (y₁ * y₂)⁻¹ * x * (y₁ * y₂) = y₂⁻¹ * (y₁⁻¹ * x * y₁) * y₂ by group,
      ← hc _ (K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hy₁) hx) hy₁) _ (K₂.inv_mem hy₂),
      inv_mul_cancel_right]
    exact K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hy₁) hx) hy₁
  have hwn₂ : ∀ x ∈ K₂, w⁻¹ * x * w ∈ K₂ := by
    intro x hx
    rw [hw, show (y₁ * y₂)⁻¹ * x * (y₁ * y₂) = y₂⁻¹ * (y₁⁻¹ * x * y₁) * y₂ by group,
      show y₁⁻¹ * x * y₁ = x by rw [hc _ (K₁.inv_mem hy₁) x hx, inv_mul_cancel_right]]
    exact K₂.mul_mem (K₂.mul_mem (K₂.inv_mem hy₂) hx) hy₂
  have hz : p * w⁻¹ = 1 := hCK _ fun _ hy =>
    commute_of_le_sup (commute_of_conj_eq hwn₁ hw₁) (commute_of_conj_eq hwn₂ hw₂) hy
  rw [show p = w by rw [← mul_inv_eq_one]; exact hz]
  exact hwK

theorem isSylowOf_inf_left [Finite A] (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    {S : Subgroup A} (hS : IsSylowOf 2 S ⊤) (hn : (K₁ ⊔ K₂).Normal) :
    IsSylowOf 2 (S ⊓ K₁) K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 (S ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    hS.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.2 hn])
  have h2 := h1.inf_of_le_normalizer (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
    (sup_le le_normalizer (H13.QRC.le_normalizer_of_commute hc))
  rwa [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)] at h2

theorem borel_inf_left [Finite A] (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hn : (K₁ ⊔ K₂).Normal) {S B : Subgroup A} {n : ℕ} {U₁ : Subgroup K₁}
    (hS2 : IsPGroup 2 S) (hU₁ : U₁ = (S ⊓ K₁).subgroupOf K₁) (hD : H13.QRC.BenderData K₁ U₁ n)
    (h₁ : IsSylowOf 2 (S ⊓ K₁) K₁) (h₂ : IsSylowOf 2 (S ⊓ K₂) K₂) (hKS : K₁ ⊔ K₂ ⊔ S = ⊤)
    {s : A} (hs : s ∈ S) (hsK : K₁.map (MulAut.conj s).toMonoidHom = K₂) (hSB : S ≤ B)
    (hBtop : B < ⊤) (hBmax : ∀ Y : Subgroup A, S ≤ Y → Y < ⊤ → Y ≤ B) :
    B ⊓ K₁ = (normalizer (U₁ : Set K₁)).map K₁.subtype := by
  set U := S ⊓ K₁ with hUdef
  set W := S ⊓ (K₁ ⊔ K₂) with hWdef
  have hUK : U ≤ K₁ := inf_le_right
  have hW : W = U ⊔ S ⊓ K₂ := inf_sup_eq_of_isSylowOf hc hd hS2 h₁ h₂
  have hNmap : (normalizer (U₁ : Set K₁)).map K₁.subtype = K₁ ⊓ normalizer (U : Set A) := by
    rw [hU₁, ← H13.QRC.inf_normalizer_subgroupOf hUK, map_subgroupOf_eq_of_le inf_le_left]
  have hSW : S ≤ normalizer (W : Set A) :=
    H13.QRC.le_normalizer_inf le_normalizer (fun x _ => by
      rw [normalizer_eq_top_iff.2 hn]; exact mem_top x)
  have hNW : K₁ ⊓ normalizer (U : Set A) ≤ normalizer (W : Set A) := by
    rintro x ⟨hx₁, hxU⟩
    rw [hW]
    exact H13.QRC.mem_normalizer_sup hxU
      (H13.QRC.mem_normalizer_of_commute fun y hy => hc x hx₁ y hy.2)
  have hNtop : normalizer (W : Set A) ≠ ⊤ := by
    intro htop
    apply hD.stronglyEmbedded.1
    rw [eq_top_iff]
    intro y _
    have hWn : W.Normal := normalizer_eq_top_iff.1 htop
    have h1 : (y : A) ∈ K₁ ⊓ normalizer (U : Set A) := by
      refine ⟨y.2, mem_normalizer_iff.2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · have h2 : (y : A) * z * (y : A)⁻¹ ∈ W := hWn.conj_mem z
          ⟨hz.1, mem_sup_left hz.2⟩ y
        exact ⟨h2.1, K₁.mul_mem (K₁.mul_mem y.2 hz.2) (K₁.inv_mem y.2)⟩
      · have h2 : (y : A)⁻¹ * ((y : A) * z * (y : A)⁻¹) * (y : A)⁻¹⁻¹ ∈ W :=
          hWn.conj_mem _ ⟨hz.1, mem_sup_left hz.2⟩ (y : A)⁻¹
        rw [show (y : A)⁻¹ * ((y : A) * z * (y : A)⁻¹) * (y : A)⁻¹⁻¹ = z by group] at h2
        refine ⟨h2.1, ?_⟩
        have h3 := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem y.2) hz.2) y.2
        rwa [show (y : A)⁻¹ * ((y : A) * z * (y : A)⁻¹) * y = z by group] at h3
    rw [← hNmap] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    rwa [← K₁.subtype_injective hzy]
  have hNB : normalizer (W : Set A) ≤ B := hBmax _ hSW (lt_top_iff_ne_top.2 hNtop)
  have hle : normalizer (U₁ : Set K₁) ≤ (B ⊓ K₁).subgroupOf K₁ := by
    intro y hy
    have h1 : (y : A) ∈ (normalizer (U₁ : Set K₁)).map K₁.subtype := ⟨y, hy, rfl⟩
    rw [hNmap] at h1
    exact ⟨hNB (hNW h1), y.2⟩
  have hne : (B ⊓ K₁).subgroupOf K₁ ≠ ⊤ := by
    intro h
    have hK₁B : K₁ ≤ B := fun y hy => by
      have : (⟨y, hy⟩ : K₁) ∈ (B ⊓ K₁).subgroupOf K₁ := h ▸ mem_top _
      exact this.1
    have hK₂B : K₂ ≤ B := by
      rw [← hsK]
      rintro _ ⟨y, hy, rfl⟩
      exact B.mul_mem (B.mul_mem (hSB hs) (hK₁B hy)) (B.inv_mem (hSB hs))
    exact hBtop.ne (eq_top_iff.2 (hKS ▸ sup_le (sup_le hK₁B hK₂B) hSB))
  have hBK : (B ⊓ K₁).subgroupOf K₁ = normalizer (U₁ : Set K₁) := by
    rcases hD.isCoatom.le_iff.1 hle with h | h
    · exact absurd h hne
    · exact h
  rw [← hBK, subgroupOf_map_subtype, inf_assoc, inf_idem]

end CFSG.Quasithin.Ch3E213M.P2
