module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Core
public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Quo
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.Quasithin.H13.CTK.L5

open scoped Pointwise

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
variable {Γ : Type} [Group Γ] (act : Γ →* (W ≃ₗ[K] W))

theorem ncard_orbit_le [Finite W] (hK : Nat.card K = 2) (hdim : Module.finrank K W = 5)
    (hW : Nat.card W = 32) (F : Submodule K W) (hF : Nat.card F = 2 ∨ Nat.card F = 16) :
    letI : MulAction Γ W := MulAction.compHom W (actPerm act)
    (MulAction.orbit Γ (F : Set W)).ncard ≤ 32 := by
  let _ : MulAction Γ W := MulAction.compHom W (actPerm act)
  have hsmul : ∀ (g : Γ) (w : W), g • w = act g w := fun _ _ => rfl
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rcases hF with h2 | h16
  ·
    have hF2 : (F : Set W).ncard = 2 := by rw [ncard_coe_submodule, h2]
    obtain ⟨a, b, hab, hFab⟩ := Set.ncard_eq_two.1 hF2
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, (F : Set W) = {0, w₀} := by
      have h0 : (0 : W) ∈ (F : Set W) := F.zero_mem
      rw [hFab] at h0
      rcases h0 with rfl | rfl
      · exact ⟨b, hFab⟩
      · exact ⟨a, by rw [hFab, Set.pair_comm]⟩
    have hsub : MulAction.orbit Γ (F : Set W) ⊆ Set.range (fun a : W => ({0, a} : Set W)) := by
      rintro _ ⟨g, rfl⟩
      refine ⟨g • w₀, ?_⟩
      show ({0, g • w₀} : Set W) = g • (F : Set W)
      have h0 : g • (0 : W) = 0 := by rw [hsmul, map_zero]
      rw [hw₀, Set.smul_set_insert, Set.smul_set_singleton, h0]
    calc (MulAction.orbit Γ (F : Set W)).ncard
        ≤ (Set.range (fun a : W => ({0, a} : Set W))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ((fun a : W => ({0, a} : Set W)) '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set W).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 32 := by rw [Set.ncard_univ, hW]
  ·
    have hfinD : Finite (Module.Dual K W) := Module.finite_of_finite K
    have hFne : F ≠ ⊤ := by
      intro htop
      have := Nat.card_congr (Submodule.topEquiv (R := K) (M := W)).toEquiv
      rw [htop] at h16
      rw [this, hW] at h16
      omega
    obtain ⟨l, hl0, hFl⟩ := Submodule.exists_le_ker_of_lt_top F (lt_top_iff_ne_top.2 hFne)
    obtain ⟨r, hr⟩ := card_submodule hK (LinearMap.ker l)
    have hker_ne : LinearMap.ker l ≠ ⊤ := fun h => hl0 (LinearMap.ker_eq_top.1 h)
    have hr' : Nat.card (LinearMap.ker l) ≤ 16 := by
      by_contra hgt
      push Not at hgt
      have hle : 2 ^ r ≤ 32 := by
        rw [← hr, ← hW]
        exact Nat.card_le_card_of_injective (fun a => (a : W)) Subtype.val_injective
      have hr5 : r = 5 := by
        by_contra hne5
        have : r ≤ 4 := by
          by_contra h
          have : 2 ^ 6 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
        omega
      exact hker_ne (by
        apply eq_top_iff.2
        intro w _
        exact ncard_eq_univ_of_card_eq hW _ (by rw [hr, hr5]; norm_num) w)
    have hFeq : (F : Set W) = (LinearMap.ker l : Set W) := by
      apply Set.eq_of_subset_of_ncard_le hFl _ (Set.toFinite _)
      rw [ncard_coe_submodule, ncard_coe_submodule, h16]
      exact hr'
    have hsub : MulAction.orbit Γ (F : Set W) ⊆
        Set.range (fun μ : Module.Dual K W => ((LinearMap.ker μ : Submodule K W) : Set W)) := by
      rintro _ ⟨g, rfl⟩
      refine ⟨l.comp (act g⁻¹).toLinearMap, ?_⟩
      ext a
      show a ∈ ((LinearMap.ker (l.comp (act g⁻¹).toLinearMap) : Submodule K W) : Set W) ↔
        a ∈ g • (F : Set W)
      rw [Set.mem_smul_set_iff_inv_smul_mem, hFeq]
      simp [hsmul]
    have hDual : Nat.card (Module.Dual K W) = 32 := by
      have : Fintype K := Fintype.ofFinite K
      have : Fintype (Module.Dual K W) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K),
        ← Nat.card_eq_fintype_card, hK, Subspace.dual_finrank_eq, hdim]
      norm_num
    calc (MulAction.orbit Γ (F : Set W)).ncard
        ≤ (Set.range fun μ : Module.Dual K W =>
            ((LinearMap.ker μ : Submodule K W) : Set W)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ((fun μ : Module.Dual K W => ((LinearMap.ker μ : Submodule K W) : Set W)) ''
            Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Module.Dual K W)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 32 := by rw [Set.ncard_univ, hDual]

theorem index_stabF_le [Finite W] (hK : Nat.card K = 2) (hdim : Module.finrank K W = 5)
    (hW : Nat.card W = 32) (F : Submodule K W) (hF : Nat.card F = 2 ∨ Nat.card F = 16) :
    (stabF act F).index ≤ 32 := by
  let _ : MulAction Γ W := MulAction.compHom W (actPerm act)
  have hstab : MulAction.stabilizer Γ (F : Set W) = stabF act F := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hg w
      have h1 : g • w ∈ g • (F : Set W) ↔ w ∈ (F : Set W) := Set.smul_mem_smul_set_iff
      rw [hg] at h1
      exact h1.symm
    · intro hg
      ext a
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have := hg (g⁻¹ • a)
      have h2 : act g (g⁻¹ • a) = a := act_apply_inv act g a
      rw [h2] at this
      exact this
  rw [← hstab, MulAction.index_stabilizer]
  exact ncard_orbit_le act hK hdim hW F hF

theorem l5_core [Finite W] [Finite Γ] (hK : Nat.card K = 2) (hdim : Module.finrank K W = 5)
    (hact : Function.Injective act) (hΓ : 491520 < Nat.card Γ) {V : Subgroup Γ}
    (hV : Nat.card V = 16) {x : Γ} (hx : orderOf x = 5)
    (hxN : x ∈ Subgroup.normalizer (V : Set Γ))
    (hN : Nat.card (Subgroup.normalizer (V : Set Γ)) ≤ 15360) : False := by
  have hW : Nat.card W = 32 := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    have : Fintype K := Fintype.ofFinite K
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W),
      ← Nat.card_eq_fintype_card, hK, hdim]
    norm_num
  have hx2 : ∀ v ∈ V, x⁻¹ * v * x ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) v).1 hv
    simpa using this
  obtain ⟨hFcard, hall⟩ := step_CD act hK hW hact hV hx hx2
  set F := fixV act V with hFdef
  have hVT : (V : Set Γ) ⊆ Tset act F := fun v hv => ⟨fun f hf => hf v hv, fun w => hall w v hv⟩
  have hTle := tset_ncard_le act hK hdim hact F hFcard
  have hVcard : (V : Set Γ).ncard = 16 := by rw [← hV]; exact Nat.card_coe_set_eq _ |>.symm
  have hVeq : (V : Set Γ) = Tset act F :=
    Set.eq_of_subset_of_ncard_le hVT (by rw [hVcard]; exact hTle) (Set.toFinite _)
  have hstab := stab_le_normalizer act V F hVeq
  have hstab_card : Nat.card (stabF act F) ≤ 15360 := (Subgroup.card_le_of_le hstab).trans hN
  have hidx := index_stabF_le act hK hdim hW F hFcard
  have hmul := Subgroup.card_mul_index (stabF act F)
  have : Nat.card Γ ≤ 15360 * 32 := by
    rw [← hmul]
    exact Nat.mul_le_mul hstab_card hidx
  omega

end CFSG.Quasithin.H13.CTK.L5
