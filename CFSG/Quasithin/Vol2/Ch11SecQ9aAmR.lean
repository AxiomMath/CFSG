module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Linear

variable {k : Type} [Field k]

theorem radMr_apply' (s : k) (x : Fin 4 → k) : radMr s x =
    ![x 0, x 1 + x 0 * s, x 2 + x 0 * s ^ 2, x 3 + x 0 * s ^ 3 + x 1 * s ^ 2 + x 2 * s] := rfl

theorem radSwap_apply' (x : Fin 4 → k) : radSwap x = ![x 3, x 2, x 1, x 0] := rfl

local macro "vec_coords" : tactic => `(tactic| (funext i; fin_cases i <;>
  (simp only [radMr_apply', radSwap_apply', Pi.sub_apply, Pi.add_apply, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]; all_goals grind)))

theorem radSwap_vec_three (c : k) : radSwap ![0, 0, 0, c] = ![c, 0, 0, 0] := by vec_coords

theorem radSwap_vec_zero (c : k) : radSwap ![c, 0, 0, 0] = ![0, 0, 0, c] := by vec_coords

theorem radMr_one_vec_zero (c : k) :
    radMr 1 ![c, 0, 0, 0] - ![c, 0, 0, 0] - ![0, 0, 0, c] = ![0, c, c, 0] := by vec_coords

variable {ω : k}

theorem radMr_omega_vec_zero (hω : ω ^ 2 + ω + 1 = 0) (c : k) :
    radMr ω ![c, 0, 0, 0] - ![c, 0, 0, 0] - ![0, 0, 0, c] = ![0, c * ω, c * ω ^ 2, 0] := by
  vec_coords

theorem radSwap_radMr_mid (s : k) (x : Fin 4 → k) :
    radSwap (radMr s (x - ![x 0, 0, 0, 0] - ![0, 0, 0, x 3]) -
      (x - ![x 0, 0, 0, 0] - ![0, 0, 0, x 3])) = ![x 1 * s ^ 2 + x 2 * s, 0, 0, 0] := by
  vec_coords

theorem radMr_radMr_sub [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0) (x : Fin 4 → k) :
    radMr ω (radMr 1 x - x) - (radMr 1 x - x) = ![0, 0, 0, x 0] := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  vec_coords

theorem vec_decomp [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0) (x : Fin 4 → k) :
    x = ![x 0, 0, 0, 0] + ![0, 0, 0, x 3] +
      ![0, x 1 * ω ^ 2 + x 2 * ω, x 1 * ω ^ 2 + x 2 * ω, 0] +
      ![0, (x 1 + x 2) * ω, (x 1 + x 2) * ω ^ 2, 0] := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  vec_coords

variable {W : AddSubgroup (Fin 4 → k)}

theorem vec_zero_mem [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0)
    (hR : ∀ s : k, ∀ x ∈ W, radMr s x ∈ W) (hS : ∀ x ∈ W, radSwap x ∈ W) {x : Fin 4 → k}
    (hx : x ∈ W) : ![x 0, 0, 0, 0] ∈ W := by
  have h1 : radMr 1 x - x ∈ W := W.sub_mem (hR 1 x hx) hx
  have h3 := hS _ (W.sub_mem (hR ω _ h1) h1)
  rwa [radMr_radMr_sub hω, radSwap_vec_three] at h3

theorem vec_zero_mem_three [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0)
    (hR : ∀ s : k, ∀ x ∈ W, radMr s x ∈ W) (hS : ∀ x ∈ W, radSwap x ∈ W) {x : Fin 4 → k}
    (hx : x ∈ W) : ![x 3, 0, 0, 0] ∈ W :=
  vec_zero_mem hω hR hS (hS x hx)

theorem vec_mem_of_vec_zero (hω : ω ^ 2 + ω + 1 = 0) (hR : ∀ s : k, ∀ x ∈ W, radMr s x ∈ W)
    (hS : ∀ x ∈ W, radSwap x ∈ W) {c : k} (hc : ![c, 0, 0, 0] ∈ W) :
    ![0, 0, 0, c] ∈ W ∧ ![0, c, c, 0] ∈ W ∧ ![0, c * ω, c * ω ^ 2, 0] ∈ W := by
  have h3 : ![0, 0, 0, c] ∈ W := by simpa only [radSwap_vec_zero] using hS _ hc
  refine ⟨h3, ?_, ?_⟩
  · simpa only [radMr_one_vec_zero] using W.sub_mem (W.sub_mem (hR 1 _ hc) hc) h3
  · simpa only [radMr_omega_vec_zero hω] using W.sub_mem (W.sub_mem (hR ω _ hc) hc) h3

theorem vec_zero_mem_mid [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0)
    (hR : ∀ s : k, ∀ x ∈ W, radMr s x ∈ W) (hS : ∀ x ∈ W, radSwap x ∈ W) {x : Fin 4 → k}
    (hx : x ∈ W) (s : k) : ![x 1 * s ^ 2 + x 2 * s, 0, 0, 0] ∈ W := by
  have hx' : x - ![x 0, 0, 0, 0] - ![0, 0, 0, x 3] ∈ W :=
    W.sub_mem (W.sub_mem hx (vec_zero_mem hω hR hS hx))
      (vec_mem_of_vec_zero hω hR hS (vec_zero_mem_three hω hR hS hx)).1
  simpa only [radSwap_radMr_mid] using hS _ (W.sub_mem (hR s _ hx') hx')

theorem le_of_vec_zero_mem [CharP k 2] (hω : ω ^ 2 + ω + 1 = 0)
    {W₁ W₂ : AddSubgroup (Fin 4 → k)}
    (hR₁ : ∀ s : k, ∀ x ∈ W₁, radMr s x ∈ W₁) (hS₁ : ∀ x ∈ W₁, radSwap x ∈ W₁)
    (hR₂ : ∀ s : k, ∀ x ∈ W₂, radMr s x ∈ W₂) (hS₂ : ∀ x ∈ W₂, radSwap x ∈ W₂)
    (h : ∀ c : k, ![c, 0, 0, 0] ∈ W₂ → ![c, 0, 0, 0] ∈ W₁) : W₂ ≤ W₁ := by
  intro x hx
  have ha := h _ (vec_zero_mem hω hR₂ hS₂ hx)
  have hb := (vec_mem_of_vec_zero hω hR₁ hS₁ (h _ (vec_zero_mem_three hω hR₂ hS₂ hx))).1
  have hq := (vec_mem_of_vec_zero hω hR₁ hS₁ (h _ (vec_zero_mem_mid hω hR₂ hS₂ hx ω))).2.1
  have hp := (vec_mem_of_vec_zero hω hR₁ hS₁ (h (x 1 + x 2) (by
    simpa only [one_pow, mul_one] using vec_zero_mem_mid hω hR₂ hS₂ hx 1))).2.2
  rw [vec_decomp hω x]
  exact W₁.add_mem (W₁.add_mem (W₁.add_mem ha hb) hq) hp

end Linear

section Radical

variable {k : Type} [Field k] [CharP k 2]

local notation "X" => pinnedX Tag.G2 k

@[expose] def radImage (S : Subgroup (ModGL .G2 k)) : AddSubgroup (Fin 4 → k) where
  carrier := {x | ∃ F : k, g2N 0 (x 0) (x 1) (x 2) (x 3) F ∈ S}
  add_mem' := by
    rintro x y ⟨F, hF⟩ ⟨F', hF'⟩
    refine ⟨F + y 0 * x 3 + y 1 * x 2 + F', ?_⟩
    have h := S.mul_mem hF hF'
    rwa [g2N_zero_mul_g2N_zero] at h
  zero_mem' := ⟨0, by simpa only [Pi.zero_apply, g2N_zero] using S.one_mem⟩
  neg_mem' := by
    rintro x ⟨F, hF⟩
    exact ⟨F, by simpa only [Pi.neg_apply, CharTwo.neg_eq] using hF⟩

theorem radImage_stable {S : Subgroup (ModGL .G2 k)} {l : ModGL .G2 k}
    {T : (Fin 4 → k) →ₗ[k] (Fin 4 → k)} (hl : ActsOnRadical l T)
    (hS : ∀ g ∈ S, l * g * l⁻¹ ∈ S) : ∀ x ∈ radImage S, T x ∈ radImage S := by
  rintro x ⟨F, hF⟩
  obtain ⟨F', hF'⟩ := hl.2 x F
  exact ⟨F', hF' ▸ hS _ hF⟩

theorem exists_g2N_mem_sdiff {ω : k} (hω : ω ^ 2 + ω + 1 = 0) {S₁ S₂ : Subgroup (ModGL .G2 k)}
    (h12 : S₁ ≤ S₂) (hne : S₁ ≠ S₂) (hQ : S₂ ≤ g2LongRadical k)
    (hr₁ : ∀ s : k, ∀ g ∈ S₁, X g2r s * g * (X g2r s)⁻¹ ∈ S₁)
    (hr₂ : ∀ s : k, ∀ g ∈ S₂, X g2r s * g * (X g2r s)⁻¹ ∈ S₂)
    (hn₁ : ∀ g ∈ S₁, weylElt .G2 k g2ir 1 * g * (weylElt .G2 k g2ir 1)⁻¹ ∈ S₁)
    (hn₂ : ∀ g ∈ S₂, weylElt .G2 k g2ir 1 * g * (weylElt .G2 k g2ir 1)⁻¹ ∈ S₂) :
    ∃ c F : k, g2N 0 c 0 0 0 F ∈ S₂ ∧ g2N 0 c 0 0 0 F ∉ S₁ := by
  by_contra hcon
  push Not at hcon
  have hW : radImage S₂ ≤ radImage S₁ :=
    le_of_vec_zero_mem hω (fun s => radImage_stable (actsOnRadical_pinnedX_r s) (hr₁ s))
      (radImage_stable actsOnRadical_weylElt_r hn₁)
      (fun s => radImage_stable (actsOnRadical_pinnedX_r s) (hr₂ s))
      (radImage_stable actsOnRadical_weylElt_r hn₂) fun c ⟨F, hF⟩ => ⟨F, hcon c F hF⟩
  apply hne
  refine le_antisymm h12 fun g hg => ?_
  obtain ⟨B, C, D, E, F, rfl⟩ := hQ hg
  obtain ⟨F', hF'⟩ := hW (show ![B, C, D, E] ∈ radImage S₂ from ⟨F, hg⟩)
  change g2N 0 B C D E F' ∈ S₁ at hF'
  have e : g2N 0 B C D E F' * g2N 0 0 0 0 0 (F' + F) = g2N 0 B C D E F := by
    rw [g2N_zero_mul_g2N_zero]
    refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> char2_ring
  have hz : g2N 0 0 0 0 0 (F' + F) ∈ S₂ := by
    have h := S₂.mul_mem (S₂.inv_mem (h12 hF')) hg
    rwa [← e, ← mul_assoc, inv_mul_cancel, one_mul] at h
  rw [← e]
  exact S₁.mul_mem hF' (hcon 0 _ hz)

end Radical

section Torus

variable {k : Type} [Field k]

local notation "X" => pinnedX Tag.G2 k

theorem commute_torusElt_r_g2N {t : kˣ} (ht : t ^ 3 = 1) (c F : k) :
    Commute (torusElt .G2 k g2ir t) (g2N 0 c 0 0 0 F) := by
  have h3 : t ^ (-3 : ℤ) = 1 := by
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ht, inv_one]
  have ha := torus_r_conj t isRoot_g2a (-3) (by decide) c
  have hc := torus_r_conj t isRoot_g2c 0 (by decide) F
  rw [h3, Units.val_one, one_mul] at ha
  rw [zpow_zero, Units.val_one, one_mul] at hc
  have e : g2N 0 c 0 0 0 F = X g2a c * X g2c F := by
    simp only [g2N, pinnedX_zero, one_mul, mul_one]
  have key : torusElt .G2 k g2ir t * (X g2a c * X g2c F) * (torusElt .G2 k g2ir t)⁻¹ =
      X g2a c * X g2c F := by
    calc _ = (torusElt .G2 k g2ir t * X g2a c * (torusElt .G2 k g2ir t)⁻¹) *
          (torusElt .G2 k g2ir t * X g2c F * (torusElt .G2 k g2ir t)⁻¹) := by group
      _ = _ := by rw [ha, hc]
  rw [e]
  exact mul_inv_eq_iff_eq_mul.1 key

end Torus

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
