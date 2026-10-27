module

public import CFSG.Quasithin.Vol2.Ch10SecEA5b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

theorem mul_self_eq_one_of_isL2Natural_mod {K : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (h : E2.IsL2Natural K C m) {k : MulAut W} (hk : k ∈ K) {w : W} (hw : w ∈ commV K)
    (hwC : w ∉ C) (hkw : k w * w⁻¹ ∈ C) : k * k = 1 := by
  obtain ⟨hm, F, hF, hFt, hcard, e, β, -, hker, hβ⟩ := h
  have h2 : (2 : F) = 0 :=
    SecE.two_eq_zero_of_card hm (by rw [Nat.card_eq_fintype_card, hcard])
  have hd : k w * w⁻¹ ∈ commV K := Subgroup.subset_closure ⟨k, hk, w, rfl⟩
  have hkw' : k w ∈ commV K := by
    have := (commV K).mul_mem hd hw
    rwa [inv_mul_cancel_right] at this
  have hβw : Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective h0
    have hmem : (⟨w, hw⟩ : ↥(commV K)) ∈ β.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact hwC hmem.2
  have hβd : β ⟨k w * w⁻¹, hd⟩ = 1 := by
    have hmem : (⟨k w * w⁻¹, hd⟩ : ↥(commV K)) ∈ (commV K ⊓ C).subgroupOf (commV K) :=
      ⟨hd, hkw⟩
    rw [← hker] at hmem
    exact hmem
  have hβk : β ⟨k w, hkw'⟩ = β ⟨w, hw⟩ := by
    have e1 : (⟨k w, hkw'⟩ : ↥(commV K)) = ⟨k w * w⁻¹, hd⟩ * ⟨w, hw⟩ :=
      Subtype.ext (by simp)
    rw [e1, map_mul, hβd, one_mul]
  have hfix := hβ ⟨k, hk⟩ ⟨w, hw⟩ hkw'
  have e2 : (⟨((⟨k, hk⟩ : ↥K) : MulAut W) (w : W), hkw'⟩ : ↥(commV K)) = ⟨k w, hkw'⟩ := rfl
  rw [e2, hβk] at hfix
  have hsq := SecE.mul_self_eq_one_of_mulVec_eq h2 (e ⟨k, hk⟩).2 hβw hfix.symm
  have h3 : e (⟨k, hk⟩ * ⟨k, hk⟩) = 1 := by
    rw [map_mul]
    exact Subtype.ext hsq
  have h4 : (⟨k, hk⟩ * ⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

theorem apply_mem_commV_conjAut {L : Subgroup (MulAut W)} (s : MulAut W) {v : W}
    (hv : v ∈ commV L) : s v ∈ commV (B1.conjAut s L) := by
  induction hv using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, u, rfl⟩ := hy
    have hx' : s * x * s⁻¹ ∈ B1.conjAut s L := B1.mem_conjAut.mpr (by simpa [mul_assoc] using hx)
    have h1 : (s * x * s⁻¹) (s u) * (s u)⁻¹ ∈ commV (B1.conjAut s L) :=
      Subgroup.subset_closure ⟨_, hx', s u, rfl⟩
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    rwa [map_mul, map_inv]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem mem_of_fix_one {K₀ : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (hnat : E2.IsL2Natural K₀ C m) (hspan : C ⊔ commV K₀ = ⊤) {b : MulAut W} (hb : b ∈ K₀)
    (hb2 : b * b ≠ 1) (hbC : ∀ c ∈ C, b c = c) {w : W} (hbw : b w = w) : w ∈ C := by
  have hw : w ∈ C ⊔ commV K₀ := hspan ▸ Subgroup.mem_top w
  obtain ⟨c, hc, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
  have hbv : b v = v := by
    rw [map_mul, hbC c hc] at hbw
    exact mul_left_cancel hbw
  by_contra hcv
  have hvC : v ∉ C := fun h => hcv (C.mul_mem hc h)
  have h1 : b v * v⁻¹ ∈ C := by
    rw [hbv, mul_inv_cancel]
    exact C.one_mem
  exact hb2 (mul_self_eq_one_of_isL2Natural_mod hnat hb hv hvC h1)

theorem mem_of_fix_two {K₀ K₁ : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (hnat : E2.IsL2Natural K₀ C m) (hspan : C ⊔ (commV K₀ ⊔ commV K₁) = ⊤)
    (hdir : commV K₀ ⊓ (C ⊔ commV K₁) ≤ C) {b : MulAut W} (hb : b ∈ K₀)
    (hbK : ∀ k ∈ K₁, b * k = k * b) (hb2 : b * b ≠ 1) (hbC : ∀ c ∈ C, b c = c) {s : MulAut W}
    (hsC : ∀ c ∈ C, s c ∈ C) (hs : B1.conjAut s K₁ = K₀) {w : W} (hbw : b w = w)
    (hsw : s w = w) : w ∈ C := by
  have hw : w ∈ C ⊔ (commV K₀ ⊔ commV K₁) := hspan ▸ Subgroup.mem_top w
  obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Subgroup.mem_sup.mp hu
  have hbv₁ : b v₁ ∈ commV K₁ := SecE.apply_mem_commV_of_commute hbK hv₁
  have hkey : b v₀ * v₀⁻¹ = v₁ * (b v₁)⁻¹ := by
    rw [map_mul, map_mul, hbC c hc] at hbw
    have h1 : b v₀ * b v₁ = v₀ * v₁ := mul_left_cancel hbw
    have h2 : b v₀ = v₀ * v₁ * (b v₁)⁻¹ := eq_mul_inv_of_mul_eq h1
    rw [h2, mul_comm _ v₀⁻¹, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd₀ : b v₀ * v₀⁻¹ ∈ commV K₀ := Subgroup.subset_closure ⟨b, hb, v₀, rfl⟩
  have hd₁ : v₁ * (b v₁)⁻¹ ∈ C ⊔ commV K₁ :=
    Subgroup.mem_sup_right ((commV K₁).mul_mem hv₁ ((commV K₁).inv_mem hbv₁))
  have hv₀C : v₀ ∈ C := by
    by_contra hv₀C
    exact hb2 (mul_self_eq_one_of_isL2Natural_mod hnat hb hv₀ hv₀C
      (hdir ⟨hd₀, hkey ▸ hd₁⟩))
  have hsv₁ : s v₁ ∈ commV K₀ := hs ▸ apply_mem_commV_conjAut s hv₁
  have hc' : c * v₀ ∈ C := C.mul_mem hc hv₀C
  have hsv₁' : s v₁ ∈ C ⊔ commV K₁ := by
    have e1 : s v₁ = (s (c * v₀))⁻¹ * (c * v₀) * v₁ := by
      have h2 : s (c * v₀) * s v₁ = c * (v₀ * v₁) := by rw [← map_mul, mul_assoc, hsw]
      rw [mul_assoc, mul_assoc, ← h2, inv_mul_cancel_left]
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (C.mul_mem (C.inv_mem (hsC _ hc')) hc'))
      (Subgroup.mem_sup_right hv₁)
  have hsv₁C : s v₁ ∈ C := hdir ⟨hsv₁, hsv₁'⟩
  have e2 : c * (v₀ * v₁) = s (c * v₀) * s v₁ := by rw [← map_mul, mul_assoc, hsw]
  rw [e2]
  exact C.mul_mem (hsC _ hc') hsv₁C

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
