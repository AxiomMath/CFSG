module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.H13.L829N

open Module

section Helpers

variable {S₀ : Type} [Group S₀] {M W : Type} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup W] [Module (ZMod 2) W]

private def kerM (V₁ : Submodule (ZMod 2) M) (κ : ↥V₁ →ₗ[ZMod 2] W) : Submodule (ZMod 2) M :=
  (LinearMap.ker κ).map V₁.subtype

private def resK (V₁ : Submodule (ZMod 2) M) (κ : ↥V₁ →ₗ[ZMod 2] W) {Y : Submodule (ZMod 2) M}
    (hY : Y ≤ V₁) : ↥Y →ₗ[ZMod 2] W :=
  κ.comp (Submodule.inclusion hY)

private def preK (V₁ : Submodule (ZMod 2) M) (κ : ↥V₁ →ₗ[ZMod 2] W)
    (P : Submodule (ZMod 2) W) : Submodule (ZMod 2) M :=
  (P.comap κ).map V₁.subtype

private lemma mem_kerM {V₁ : Submodule (ZMod 2) M} {κ : ↥V₁ →ₗ[ZMod 2] W} {m : M} :
    m ∈ kerM V₁ κ ↔ ∃ h : m ∈ V₁, κ ⟨m, h⟩ = 0 := by
  unfold kerM
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, LinearMap.mem_ker.1 hx⟩
  · rintro ⟨h, hm⟩
    exact ⟨⟨m, h⟩, LinearMap.mem_ker.2 hm, rfl⟩

private lemma mem_preK {V₁ : Submodule (ZMod 2) M} {κ : ↥V₁ →ₗ[ZMod 2] W}
    {P : Submodule (ZMod 2) W} {m : M} :
    m ∈ preK V₁ κ P ↔ ∃ h : m ∈ V₁, κ ⟨m, h⟩ ∈ P := by
  unfold preK
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, Submodule.mem_comap.1 hx⟩
  · rintro ⟨h, hm⟩
    exact ⟨⟨m, h⟩, Submodule.mem_comap.2 hm, rfl⟩

private lemma preK_le (V₁ : Submodule (ZMod 2) M) (κ : ↥V₁ →ₗ[ZMod 2] W)
    (P : Submodule (ZMod 2) W) : preK V₁ κ P ≤ V₁ :=
  fun _ hm => (mem_preK.1 hm).1

private lemma finrank_eq_range_add_inf_kerM [Module.Finite (ZMod 2) M]
    {V₁ : Submodule (ZMod 2) M} (κ : ↥V₁ →ₗ[ZMod 2] W)
    {Y : Submodule (ZMod 2) M} (hY : Y ≤ V₁) :
    finrank (ZMod 2) Y =
      finrank (ZMod 2) (LinearMap.range (resK V₁ κ hY)) + finrank (ZMod 2) ↥(Y ⊓ kerM V₁ κ) := by
  have h2 : (LinearMap.ker (resK V₁ κ hY)).map Y.subtype = Y ⊓ kerM V₁ κ := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Submodule.mem_inf.2 ⟨y.2, mem_kerM.2 ⟨hY y.2, LinearMap.mem_ker.1 hy⟩⟩
    · intro hm
      obtain ⟨hmY, hmK⟩ := Submodule.mem_inf.1 hm
      obtain ⟨_, hκ0⟩ := mem_kerM.1 hmK
      exact ⟨⟨m, hmY⟩, LinearMap.mem_ker.2 hκ0, rfl⟩
  have h3 : finrank (ZMod 2) ↥(Y ⊓ kerM V₁ κ) =
      finrank (ZMod 2) (LinearMap.ker (resK V₁ κ hY)) := by
    rw [← h2, Submodule.finrank_map_subtype_eq]
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (resK V₁ κ hY)
  omega

private lemma range_resK_preK {V₁ : Submodule (ZMod 2) M} (κ : ↥V₁ →ₗ[ZMod 2] W)
    {P : Submodule (ZMod 2) W} (hP : P ≤ LinearMap.range κ) :
    LinearMap.range (resK V₁ κ (preK_le V₁ κ P)) = P := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact (mem_preK.1 y.2).2
  · intro p hp
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 (hP hp)
    exact LinearMap.mem_range.2 ⟨⟨v.1, mem_preK.2 ⟨v.2, hp⟩⟩, rfl⟩

private lemma finrank_range_le_add_one [Module.Finite (ZMod 2) M]
    {V₁ : Submodule (ZMod 2) M} (κ : ↥V₁ →ₗ[ZMod 2] W)
    {B B₁ X Y : Submodule (ZMod 2) M} (hXV : X ≤ V₁) (hXB : X ≤ B) (hB₁B : B₁ ≤ B)
    (hBdim : finrank (ZMod 2) B ≤ finrank (ZMod 2) B₁ + 1) (hYdef : Y = X ⊓ B₁)
    (hYV : Y ≤ V₁) :
    finrank (ZMod 2) (LinearMap.range (resK V₁ κ hXV)) ≤
      finrank (ZMod 2) (LinearMap.range (resK V₁ κ hYV)) + 1 := by
  subst hYdef
  have hX := finrank_eq_range_add_inf_kerM κ hXV
  have hY := finrank_eq_range_add_inf_kerM κ hYV
  have hsi1 := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) X B₁
  have hsi2 := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (X ⊓ kerM V₁ κ) (X ⊓ B₁)
  have hkey : (X ⊓ kerM V₁ κ) ⊓ (X ⊓ B₁) = (X ⊓ B₁) ⊓ kerM V₁ κ := by
    ext m
    simp only [Submodule.mem_inf]
    tauto
  rw [hkey] at hsi2
  have hm1 : finrank (ZMod 2) ↥(X ⊓ B₁) ≤
      finrank (ZMod 2) ↥((X ⊓ kerM V₁ κ) ⊔ (X ⊓ B₁)) :=
    Submodule.finrank_mono le_sup_right
  have hm2 : finrank (ZMod 2) ↥(X ⊔ B₁) ≤ finrank (ZMod 2) B :=
    Submodule.finrank_mono (sup_le hXB hB₁B)
  omega

private lemma eq_zero_of_mem_kerM_sup {V₁ : Submodule (ZMod 2) M} {κ : ↥V₁ →ₗ[ZMod 2] W}
    {U : Submodule (ZMod 2) M} (hκU : ∀ v : ↥V₁, (v : M) ∈ U → κ v = 0)
    {c : M} (hcV : c ∈ V₁) (hc : c ∈ kerM V₁ κ ⊔ U) : κ ⟨c, hcV⟩ = 0 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨hyV, hy0⟩ := mem_kerM.1 hy
  have huV : u ∈ V₁ := by simpa using V₁.sub_mem hcV hyV
  have e : (⟨y + u, hcV⟩ : ↥V₁) = ⟨y, hyV⟩ + ⟨u, huV⟩ := rfl
  rw [e, map_add, hy0, hκU ⟨u, huV⟩ hu, zero_add]

private lemma kerM_inv (ρM : S₀ →* (M ≃ₗ[ZMod 2] M)) (ρW : S₀ →* (W ≃ₗ[ZMod 2] W))
    {V₁ : Submodule (ZMod 2) M} (κ : ↥V₁ →ₗ[ZMod 2] W)
    (hV₁ : ∀ s : S₀, ∀ m ∈ V₁, ρM s m ∈ V₁)
    (hκeq : ∀ (s : S₀) (v : ↥V₁) (hv : ρM s v ∈ V₁), κ ⟨ρM s v, hv⟩ = ρW s (κ v)) :
    ∀ s : S₀, ∀ m ∈ kerM V₁ κ, ρM s m ∈ kerM V₁ κ := by
  intro s m hm
  obtain ⟨hmV, hm0⟩ := mem_kerM.1 hm
  refine mem_kerM.2 ⟨hV₁ s m hmV, ?_⟩
  have h : κ ⟨ρM s m, hV₁ s m hmV⟩ = ρW s (κ ⟨m, hmV⟩) := hκeq s ⟨m, hmV⟩ (hV₁ s m hmV)
  rw [h, hm0, map_zero]

private lemma range_trichotomy [Module.Finite (ZMod 2) M]
    (ρM : S₀ →* (M ≃ₗ[ZMod 2] M)) (ρW : S₀ →* (W ≃ₗ[ZMod 2] W))
    {U B₁ V₁ : Submodule (ZMod 2) M}
    (hU : ∀ s : S₀, ∀ m ∈ U, ρM s m ∈ U) (hV₁ : ∀ s : S₀, ∀ m ∈ V₁, ρM s m ∈ V₁)
    (hUB₁ : U ≤ B₁)
    (hirr : ∀ C : Submodule (ZMod 2) M, U ≤ C → C ≤ B₁ →
      (∀ s : S₀, ∀ m ∈ C, ρM s m ∈ C) → C = U ∨ C = B₁)
    (hdim : finrank (ZMod 2) B₁ = finrank (ZMod 2) U + 4)
    (hnonab : ∃ s s' : S₀, ∃ b ∈ B₁, ρM s (ρM s' b) - ρM s' (ρM s b) ∉ U)
    {κ : ↥V₁ →ₗ[ZMod 2] W}
    (hκeq : ∀ (s : S₀) (v : ↥V₁) (hv : ρM s v ∈ V₁), κ ⟨ρM s v, hv⟩ = ρW s (κ v))
    (hκU : ∀ v : ↥V₁, (v : M) ∈ U → κ v = 0)
    {Y : Submodule (ZMod 2) M} (hYV : Y ≤ V₁) (hYB : Y ≤ B₁)
    (hYinv : ∀ s : S₀, ∀ m ∈ Y, ρM s m ∈ Y) :
    LinearMap.range (resK V₁ κ hYV) = ⊥ ∨
      (finrank (ZMod 2) (LinearMap.range (resK V₁ κ hYV)) = 4 ∧
        ∃ s s' : S₀, ∃ w ∈ LinearMap.range (resK V₁ κ hYV),
          ρW s (ρW s' w) ≠ ρW s' (ρW s w)) := by
  have hsup : ∀ A C : Submodule (ZMod 2) M, (∀ s : S₀, ∀ m ∈ A, ρM s m ∈ A) →
      (∀ s : S₀, ∀ m ∈ C, ρM s m ∈ C) → ∀ s : S₀, ∀ m ∈ A ⊔ C, ρM s m ∈ A ⊔ C := by
    intro A C hA hC s m hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hm
    rw [map_add]
    exact Submodule.add_mem_sup (hA s a ha) (hC s c hc)
  have hYK : ∀ s : S₀, ∀ m ∈ Y ⊓ kerM V₁ κ, ρM s m ∈ Y ⊓ kerM V₁ κ := fun s m hm =>
    Submodule.mem_inf.2 ⟨hYinv s m (Submodule.mem_inf.1 hm).1,
      kerM_inv ρM ρW κ hV₁ hκeq s m (Submodule.mem_inf.1 hm).2⟩
  have hYKB : Y ⊓ kerM V₁ κ ≤ B₁ := inf_le_left.trans hYB
  have hZbot : Y ≤ kerM V₁ κ ⊔ U → LinearMap.range (resK V₁ κ hYV) = ⊥ := by
    intro hYle
    rw [eq_bot_iff]
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_kerM_sup hκU (hYV y.2) (hYle y.2)
  have hA₁ := hirr ((Y ⊓ kerM V₁ κ) ⊔ U) le_sup_right (sup_le hYKB hUB₁) (hsup _ _ hYK hU)
  have hA₂ := hirr (Y ⊔ U) le_sup_right (sup_le hYB hUB₁) (hsup _ _ hYinv hU)
  by_cases hA₁B : (Y ⊓ kerM V₁ κ) ⊔ U = B₁
  · left
    apply hZbot
    intro c hc
    have hcB : c ∈ (Y ⊓ kerM V₁ κ) ⊔ U := by
      rw [hA₁B]
      exact hYB hc
    exact (sup_le_sup_right inf_le_right U) hcB
  have hA₁U : (Y ⊓ kerM V₁ κ) ⊔ U = U := hA₁.resolve_right hA₁B
  by_cases hA₂U : Y ⊔ U = U
  · left
    apply hZbot
    intro c hc
    have hcU : c ∈ U := by
      have h1 : c ∈ Y ⊔ U := Submodule.mem_sup_left hc
      rwa [hA₂U] at h1
    exact Submodule.mem_sup_right hcU
  have hA₂B : Y ⊔ U = B₁ := hA₂.resolve_left hA₂U
  right
  have hYKU : Y ⊓ kerM V₁ κ = Y ⊓ U := by
    apply le_antisymm
    · intro m hm
      have h1 : m ∈ (Y ⊓ kerM V₁ κ) ⊔ U := Submodule.mem_sup_left hm
      rw [hA₁U] at h1
      exact Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hm).1, h1⟩
    · intro m hm
      obtain ⟨hmY, hmU⟩ := Submodule.mem_inf.1 hm
      exact Submodule.mem_inf.2 ⟨hmY, mem_kerM.2 ⟨hYV hmY, hκU ⟨m, hYV hmY⟩ hmU⟩⟩
  have hfin : finrank (ZMod 2) (LinearMap.range (resK V₁ κ hYV)) = 4 := by
    have hrk := finrank_eq_range_add_inf_kerM κ hYV
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) Y U
    rw [hYKU] at hrk
    rw [hA₂B] at hsi
    omega
  refine ⟨hfin, ?_⟩
  obtain ⟨s, s', b, hb, hd⟩ := hnonab
  rw [← hA₂B] at hb
  obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.1 hb
  have hcV : c ∈ V₁ := hYV hc
  have hsc : ρM s c ∈ V₁ := hV₁ s c hcV
  have hs'c : ρM s' c ∈ V₁ := hV₁ s' c hcV
  have hss'c : ρM s (ρM s' c) ∈ V₁ := hV₁ s (ρM s' c) hs'c
  have hs'sc : ρM s' (ρM s c) ∈ V₁ := hV₁ s' (ρM s c) hsc
  have hdc : ρM s (ρM s' c) - ρM s' (ρM s c) ∉ U := by
    intro hmem
    apply hd
    have hdu : ρM s (ρM s' u) - ρM s' (ρM s u) ∈ U :=
      Submodule.sub_mem U (hU s _ (hU s' u hu)) (hU s' _ (hU s u hu))
    have e : ρM s (ρM s' (c + u)) - ρM s' (ρM s (c + u)) =
        (ρM s (ρM s' c) - ρM s' (ρM s c)) + (ρM s (ρM s' u) - ρM s' (ρM s u)) := by
      simp only [map_add]
      abel
    rw [e]
    exact Submodule.add_mem U hmem hdu
  have hdcY : ρM s (ρM s' c) - ρM s' (ρM s c) ∈ Y :=
    Submodule.sub_mem Y (hYinv s _ (hYinv s' c hc)) (hYinv s' _ (hYinv s c hc))
  have hdcV : ρM s (ρM s' c) - ρM s' (ρM s c) ∈ V₁ := hYV hdcY
  have hκd : κ ⟨ρM s (ρM s' c) - ρM s' (ρM s c), hdcV⟩ ≠ 0 := by
    intro h0
    apply hdc
    have hmem : ρM s (ρM s' c) - ρM s' (ρM s c) ∈ Y ⊓ kerM V₁ κ :=
      Submodule.mem_inf.2 ⟨hdcY, mem_kerM.2 ⟨hdcV, h0⟩⟩
    rw [hYKU] at hmem
    exact (Submodule.mem_inf.1 hmem).2
  have hκd_eq : κ ⟨ρM s (ρM s' c) - ρM s' (ρM s c), hdcV⟩ =
      ρW s (ρW s' (resK V₁ κ hYV ⟨c, hc⟩)) - ρW s' (ρW s (resK V₁ κ hYV ⟨c, hc⟩)) := by
    have e : (⟨ρM s (ρM s' c) - ρM s' (ρM s c), hdcV⟩ : ↥V₁) =
        ⟨ρM s (ρM s' c), hss'c⟩ - ⟨ρM s' (ρM s c), hs'sc⟩ := rfl
    have A1 : κ ⟨ρM s (ρM s' c), hss'c⟩ = ρW s (κ ⟨ρM s' c, hs'c⟩) :=
      hκeq s ⟨ρM s' c, hs'c⟩ hss'c
    have A2 : κ ⟨ρM s' c, hs'c⟩ = ρW s' (resK V₁ κ hYV ⟨c, hc⟩) :=
      hκeq s' ⟨c, hcV⟩ hs'c
    have A3 : κ ⟨ρM s' (ρM s c), hs'sc⟩ = ρW s' (κ ⟨ρM s c, hsc⟩) :=
      hκeq s' ⟨ρM s c, hsc⟩ hs'sc
    have A4 : κ ⟨ρM s c, hsc⟩ = ρW s (resK V₁ κ hYV ⟨c, hc⟩) :=
      hκeq s ⟨c, hcV⟩ hsc
    rw [e, map_sub, A1, A2, A3, A4]
  refine ⟨s, s', resK V₁ κ hYV ⟨c, hc⟩, LinearMap.mem_range_self _ _, ?_⟩
  intro heq
  apply hκd
  rw [hκd_eq, heq, sub_self]

private lemma exists_Z_range [Module.Finite (ZMod 2) M]
    (ρM : S₀ →* (M ≃ₗ[ZMod 2] M)) (ρW : S₀ →* (W ≃ₗ[ZMod 2] W))
    {U B₁ B V₁ : Submodule (ZMod 2) M}
    (hU : ∀ s : S₀, ∀ m ∈ U, ρM s m ∈ U) (hB₁ : ∀ s : S₀, ∀ m ∈ B₁, ρM s m ∈ B₁)
    (hV₁ : ∀ s : S₀, ∀ m ∈ V₁, ρM s m ∈ V₁)
    (hUB₁ : U ≤ B₁) (hB₁B : B₁ ≤ B) (hV₁B : V₁ ≤ B)
    (hirr : ∀ C : Submodule (ZMod 2) M, U ≤ C → C ≤ B₁ →
      (∀ s : S₀, ∀ m ∈ C, ρM s m ∈ C) → C = U ∨ C = B₁)
    (hdim : finrank (ZMod 2) B₁ = finrank (ZMod 2) U + 4)
    (hnonab : ∃ s s' : S₀, ∃ b ∈ B₁, ρM s (ρM s' b) - ρM s' (ρM s b) ∉ U)
    (hBdim : finrank (ZMod 2) B ≤ finrank (ZMod 2) B₁ + 1)
    {κ : ↥V₁ →ₗ[ZMod 2] W}
    (hκeq : ∀ (s : S₀) (v : ↥V₁) (hv : ρM s v ∈ V₁), κ ⟨ρM s v, hv⟩ = ρW s (κ v))
    (hκU : ∀ v : ↥V₁, (v : M) ∈ U → κ v = 0)
    (P : Submodule (ZMod 2) W) (hPle : P ≤ LinearMap.range κ)
    (hPinv : ∀ s : S₀, ∀ w ∈ P, ρW s w ∈ P) :
    ∃ Z : Submodule (ZMod 2) W, Z ≤ P ∧ (∀ s : S₀, ∀ w ∈ Z, ρW s w ∈ Z) ∧
      finrank (ZMod 2) P ≤ finrank (ZMod 2) Z + 1 ∧
      (Z = ⊥ ∨ (finrank (ZMod 2) Z = 4 ∧
        ∃ s s' : S₀, ∃ w ∈ Z, ρW s (ρW s' w) ≠ ρW s' (ρW s w))) := by
  have hXV : preK V₁ κ P ≤ V₁ := preK_le V₁ κ P
  have hXB : preK V₁ κ P ≤ B := hXV.trans hV₁B
  have hXinv : ∀ s : S₀, ∀ m ∈ preK V₁ κ P, ρM s m ∈ preK V₁ κ P := by
    intro s m hm
    obtain ⟨hmV, hmP⟩ := mem_preK.1 hm
    refine mem_preK.2 ⟨hV₁ s m hmV, ?_⟩
    have h : κ ⟨ρM s m, hV₁ s m hmV⟩ = ρW s (κ ⟨m, hmV⟩) := hκeq s ⟨m, hmV⟩ (hV₁ s m hmV)
    rw [h]
    exact hPinv s _ hmP
  have hYinv : ∀ s : S₀, ∀ m ∈ preK V₁ κ P ⊓ B₁, ρM s m ∈ preK V₁ κ P ⊓ B₁ := fun s m hm =>
    Submodule.mem_inf.2 ⟨hXinv s m (Submodule.mem_inf.1 hm).1, hB₁ s m (Submodule.mem_inf.1 hm).2⟩
  have hYV : preK V₁ κ P ⊓ B₁ ≤ V₁ := inf_le_left.trans hXV
  have hYB : preK V₁ κ P ⊓ B₁ ≤ B₁ := inf_le_right
  have hrange : LinearMap.range (resK V₁ κ hXV) = P := range_resK_preK κ hPle
  have hq := finrank_range_le_add_one κ hXV hXB hB₁B hBdim rfl hYV
  rw [hrange] at hq
  refine ⟨LinearMap.range (resK V₁ κ hYV), ?_, ?_, hq,
    range_trichotomy ρM ρW hU hV₁ hUB₁ hirr hdim hnonab hκeq hκU hYV hYB hYinv⟩
  · rintro _ ⟨y, rfl⟩
    exact (mem_preK.1 (Submodule.mem_inf.1 y.2).1).2
  · rintro s _ ⟨y, rfl⟩
    refine LinearMap.mem_range.2 ⟨⟨ρM s y, hYinv s _ y.2⟩, ?_⟩
    exact hκeq s ⟨y.1, hYV y.2⟩ (hV₁ s y.1 (hYV y.2))

end Helpers

theorem hb_of_subquotient
    {S₀ : Type} [Group S₀] {M W : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρM : S₀ →* (M ≃ₗ[ZMod 2] M)) (ρW : S₀ →* (W ≃ₗ[ZMod 2] W))
    (U B₁ B V₁ : Submodule (ZMod 2) M) (WB : Submodule (ZMod 2) W)
    (hU : ∀ s : S₀, ∀ m ∈ U, ρM s m ∈ U) (hB₁ : ∀ s : S₀, ∀ m ∈ B₁, ρM s m ∈ B₁)
    (hB : ∀ s : S₀, ∀ m ∈ B, ρM s m ∈ B) (hV₁ : ∀ s : S₀, ∀ m ∈ V₁, ρM s m ∈ V₁)
    (hUB₁ : U ≤ B₁) (hB₁B : B₁ ≤ B) (hV₁B : V₁ ≤ B)
    (hirr : ∀ C : Submodule (ZMod 2) M, U ≤ C → C ≤ B₁ →
      (∀ s : S₀, ∀ m ∈ C, ρM s m ∈ C) → C = U ∨ C = B₁)
    (hne : U ≠ B₁) (hdim : Module.finrank (ZMod 2) B₁ = Module.finrank (ZMod 2) U + 4)
    (hnonab : ∃ s s' : S₀, ∃ b ∈ B₁, ρM s (ρM s' b) - ρM s' (ρM s b) ∉ U)
    (hBdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) B₁ + 1)
    (κ : ↥V₁ →ₗ[ZMod 2] W) (hκ : LinearMap.range κ = WB)
    (hκeq : ∀ (s : S₀) (v : ↥V₁) (hv : ρM s v ∈ V₁), κ ⟨ρM s v, hv⟩ = ρW s (κ v))
    (hκU : ∀ v : ↥V₁, (v : M) ∈ U → κ v = 0) :
    Module.finrank (ZMod 2) WB ≤ 5 ∧
    (∀ P : Submodule (ZMod 2) W, P ≤ WB → (∀ s : S₀, ∀ w ∈ P, ρW s w = w) →
      Module.finrank (ZMod 2) P ≤ 1) ∧
    (∀ P : Submodule (ZMod 2) W, P ≤ WB → P ≠ ⊥ → (∀ s : S₀, ∀ w ∈ P, ρW s w ∈ P) →
      (∀ Q : Submodule (ZMod 2) W, Q ≤ P → (∀ s : S₀, ∀ w ∈ Q, ρW s w ∈ Q) → Q = ⊥ ∨ Q = P) →
      Module.finrank (ZMod 2) P = 1 ∨ (Module.finrank (ZMod 2) P = 4 ∧
        ∃ s s' : S₀, ∃ w ∈ P, ρW s (ρW s' w) ≠ ρW s' (ρW s w))) := by
  haveI : Module.Finite (ZMod 2) M := inferInstance
  haveI : Module.Finite (ZMod 2) W := inferInstance
  have hWBinv : ∀ s : S₀, ∀ w ∈ WB, ρW s w ∈ WB := by
    intro s w hw
    rw [← hκ] at hw ⊢
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hw
    exact LinearMap.mem_range.2 ⟨⟨ρM s (v : M), hV₁ s (v : M) v.2⟩, hκeq s v (hV₁ s (v : M) v.2)⟩
  have hWBle : WB ≤ LinearMap.range κ := hκ.symm.le
  obtain ⟨Z₀, -, -, hZ₀fin, hZ₀tri⟩ :=
    exists_Z_range ρM ρW hU hB₁ hV₁ hUB₁ hB₁B hV₁B hirr hdim hnonab hBdim hκeq hκU WB hWBle hWBinv
  refine ⟨?_, ?_, ?_⟩
  · rcases hZ₀tri with h | ⟨h4, -⟩
    · rw [h, finrank_bot] at hZ₀fin
      omega
    · omega
  · intro P hPWB hPtriv
    have hPinv : ∀ s : S₀, ∀ w ∈ P, ρW s w ∈ P := fun s w hw => by
      rw [hPtriv s w hw]
      exact hw
    obtain ⟨Z, hZP, -, hfin, htri⟩ :=
      exists_Z_range ρM ρW hU hB₁ hV₁ hUB₁ hB₁B hV₁B hirr hdim hnonab hBdim hκeq hκU P
        (hPWB.trans hWBle) hPinv
    rcases htri with h | ⟨-, s, s', w, hw, hne'⟩
    · rw [h, finrank_bot] at hfin
      omega
    · exfalso
      have hwP : w ∈ P := hZP hw
      apply hne'
      rw [hPtriv s' w hwP, hPtriv s w hwP, hPtriv s' w hwP]
  · intro P hPWB hPne hPinv hirrP
    obtain ⟨Z, hZP, hZinv, hfin, htri⟩ :=
      exists_Z_range ρM ρW hU hB₁ hV₁ hUB₁ hB₁B hV₁B hirr hdim hnonab hBdim hκeq hκU P
        (hPWB.trans hWBle) hPinv
    rcases hirrP Z hZP hZinv with hZbot | hZPeq
    · left
      rw [hZbot, finrank_bot] at hfin
      have hpos : 1 ≤ finrank (ZMod 2) P := Submodule.one_le_finrank_iff.2 hPne
      omega
    · right
      rcases htri with h | ⟨h4, s, s', w, hw, hne'⟩
      · exact absurd (hZPeq.symm.trans h) hPne
      · refine ⟨?_, s, s', w, ?_, hne'⟩
        · rw [← hZPeq]
          exact h4
        · rw [← hZPeq]
          exact hw

end CFSG.Quasithin.H13.L829N
