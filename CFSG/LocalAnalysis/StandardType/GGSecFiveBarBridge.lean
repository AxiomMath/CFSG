module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Bridge

private theorem card_fixed_mul_iff_finrank_move
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (g : V ≃ₗ[ZMod p] V) :
    Nat.card {v : V // g v = v} * p = Nat.card V ↔
      Module.finrank (ZMod p) (ggLinMove g) = 1 := by
  classical
  have hfixed : Nat.card {v : V // g v = v} =
      Nat.card (LinearMap.ker (g.toLinearMap - LinearMap.id)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact Iff.rfl)
  have hcardker : Nat.card (LinearMap.ker (g.toLinearMap - LinearMap.id)) =
      p ^ Module.finrank (ZMod p) (LinearMap.ker (g.toLinearMap - LinearMap.id)) := by
    rw [Module.natCard_eq_pow_finrank
      (K := ZMod p) (V := LinearMap.ker (g.toLinearMap - LinearMap.id)), Nat.card_zmod]
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  have hrn := LinearMap.finrank_range_add_finrank_ker (g.toLinearMap - LinearMap.id)
  rw [hfixed, hcardker, hcardV,
    show ggLinMove g = LinearMap.range (g.toLinearMap - LinearMap.id) from rfl,
    ← hrn, ← pow_succ]
  constructor
  · intro h
    have h' := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
    omega
  · intro h
    rw [h]
    congr 1
    omega

private lemma ggLin_ofMul_inv_mul
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {E : Type*} [Group E]
    (ι : Additive E ≃+ V) (φ : MulAut E) (b : E) :
    ι (Additive.ofMul (b⁻¹ * φ b)) =
      ggLin (p := p) ι φ (ι (Additive.ofMul b)) - ι (Additive.ofMul b) := by
  rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ b]
  abel

private lemma ggLin_move_fix_of_transvection
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {E : Type*} [Group E]
    (ι : Additive E ≃+ V) (φ : MulAut E)
    (htrans : ∀ b : E, φ (b⁻¹ * φ b) = b⁻¹ * φ b) (v : V) :
    ggLin (p := p) ι φ (ggLin (p := p) ι φ v - v) = ggLin (p := p) ι φ v - v := by
  set b : E := Additive.toMul (ι.symm v) with hb
  have hbv : ι (Additive.ofMul b) = v := by
    rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply]
  have h1 := congrArg (fun x : E => ι (Additive.ofMul x)) (htrans b)
  rw [← ggLin_apply_ofMul (p := p) ι φ (b⁻¹ * φ b)] at h1
  rw [ggLin_ofMul_inv_mul (p := p) ι φ b, hbv] at h1
  exact h1

end Bridge

theorem ggIsReflection_iff_ggLinRefl
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (hp2 : p ≠ 2)
    (ι : Additive ↥Bs ≃+ V) (φ : MulAut ↥Bs) :
    GGIsReflection p φ ↔ GGLinRefl (ggLin (p := p) ι φ) := by
  rw [ggIsReflection_iff ι φ]
  unfold GGLinRefl
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨by simpa [pow_two] using h,
      (card_fixed_mul_iff_finrank_move (g := ggLin (p := p) ι φ)).mp hc⟩
  · rintro ⟨h, hr⟩
    exact ⟨by simpa [pow_two] using h,
      (card_fixed_mul_iff_finrank_move (g := ggLin (p := p) ι φ)).mpr hr⟩

theorem ggIsTransvection_iff_ggLin
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (φ : MulAut ↥Bs) :
    GGIsTransvection p φ ↔ (Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι φ)) = 1 ∧
      ggLinMove (ggLin (p := p) ι φ) ≤ ggLinFix {ggLin (p := p) ι φ}) := by
  constructor
  · rintro ⟨hcard, htrans⟩
    refine ⟨(card_fixed_mul_iff_finrank_move (g := ggLin (p := p) ι φ)).mp ?_, ?_⟩
    · rw [← card_fixed_ggLin (p := p) ι φ, ← card_eq_of_ggLin ι]
      exact hcard
    ·
      intro w hw
      rw [ggLinMove, LinearMap.mem_range] at hw
      obtain ⟨v, hv⟩ := hw
      have hv' : ggLin (p := p) ι φ v - v = w := hv
      have h := ggLin_move_fix_of_transvection (p := p) ι φ htrans v
      rw [hv'] at h
      change ∀ a ∈ ({ggLin (p := p) ι φ} : Set (V ≃ₗ[ZMod p] V)), a w = w
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact h
  · rintro ⟨hrank, hle⟩
    refine ⟨?_, fun b => ?_⟩
    · rw [card_fixed_ggLin (p := p) ι φ, card_eq_of_ggLin ι]
      exact (card_fixed_mul_iff_finrank_move (g := ggLin (p := p) ι φ)).mpr hrank
    · have hmem : ι (Additive.ofMul (b⁻¹ * φ b)) ∈ ggLinMove (ggLin (p := p) ι φ) := by
        rw [ggLinMove, LinearMap.mem_range]
        refine ⟨ι (Additive.ofMul b), ?_⟩
        rw [ggLin_ofMul_inv_mul (p := p) ι φ b]
        rfl
      rw [ggLin_fix_iff (p := p) ι φ (b⁻¹ * φ b)]
      exact hle hmem (ggLin (p := p) ι φ) (Set.mem_singleton _)

theorem ggLinFix_map_eq_bot
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (hC : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → b = 1) :
    ggLinFix ((A.map (ggLin (p := p) ι) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
  rw [← le_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  set b : ↥Bs := Additive.toMul (ι.symm v) with hb
  have hb' : ι (Additive.ofMul b) = v := by
    rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply]
  have hfix : ∀ φ ∈ A, φ b = b := by
    intro φ hφ
    rw [ggLin_fix_iff (p := p) ι φ b, hb']
    exact hv (ggLin (p := p) ι φ) (Subgroup.mem_map_of_mem (ggLin (p := p) ι) hφ)
  have hb1 : b = 1 := hC b hfix
  rw [← hb', hb1]
  simp

end CFSG.StandardType

end
