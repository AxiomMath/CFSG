module

public import CFSG.Milestones.ASVolI.H13
public import CFSG.Quasithin.Background.HMathieuFacts22Base

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.ChH

theorem rkIdx_fixV_zpowers_of_intertwine {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (t : MulAut V) (t₀ : MulAut W) (h : ∀ v, e (t v) = t₀ (e v)) :
    rkIdx (fixV (Subgroup.zpowers t)) = rkIdx (fixV (Subgroup.zpowers t₀)) := by
  have hfix : fixV (Subgroup.zpowers t₀) = (fixV (Subgroup.zpowers t)).map e.toMonoidHom := by
    ext w
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hw
      rw [mem_fixV_zpowers_iff]
      apply e.injective
      rw [h (e.symm w), e.apply_symm_apply, (mem_fixV_zpowers_iff).mp hw]
    · intro hw
      rw [mem_fixV_zpowers_iff]
      calc t₀ w = t₀ (e (e.symm w)) := by rw [e.apply_symm_apply]
        _ = e (t (e.symm w)) := (h (e.symm w)).symm
        _ = e (e.symm w) := by rw [(mem_fixV_zpowers_iff).mp hw]
        _ = w := e.apply_symm_apply w
  rw [hfix]
  unfold rkIdx
  congr 1
  exact (Subgroup.index_map_equiv (fixV (Subgroup.zpowers t)) e).symm

theorem rkIdx_fixV_zpowers_of_masks {n : ℕ} (u : MulAut (Wn n)) (P : ℕ → Bool)
    (hP : ∀ m < 2 ^ n, u (toW n m) = toW n m ↔ P m = true) {k : ℕ}
    (hk : ((List.range (2 ^ n)).filter P).length = 2 ^ k) :
    rkIdx (fixV (Subgroup.zpowers u)) = n - k :=
  set_option backward.isDefEq.respectTransparency false in by
    have hcard : Nat.card (fixV (Subgroup.zpowers u)) =
        ((List.range (2 ^ n)).filter P).length :=
      (MaskCoords.std n).card_eq _ _ (fun m hm => by
        rw [mem_fixV_zpowers_iff]
        exact hP m hm)
    rw [(MaskCoords.std n).rkIdx_of_card hcard, hk, Nat.log_pow (by norm_num : 1 < 2)]

theorem rkIdx_fixV_zpowers_of_arr {Λ : Subgroup S24} {n : ℕ} (ρ₀ : ↥Λ →* MulAut (Wn n))
    (act : Array ℕ → ℕ → ℕ)
    (hact : ∀ (s : ↥Λ) (arr : Array ℕ), HasArr (s : S24) arr → ∀ m,
      ρ₀ s (toW n m) = toW n (act arr m))
    (hlt : ∀ arr m, act arr m < 2 ^ n) {V : Type*} [CommGroup V] (e : V ≃* Wn n) (t : MulAut V)
    (σ c s : ↥Λ) (hσ : σ = c * s * c⁻¹) (ht : ∀ v, e (t v) = ρ₀ σ (e v)) {arr : Array ℕ}
    (harr : HasArr (s : S24) arr) {k : ℕ}
    (hk : ((List.range (2 ^ n)).filter fun m => act arr m == m).length = 2 ^ k) :
    rkIdx (fixV (Subgroup.zpowers t)) = n - k :=
  set_option backward.isDefEq.respectTransparency false in by
    have hconj : ρ₀ σ = ρ₀ c * ρ₀ s * (ρ₀ c)⁻¹ := by
      rw [hσ, map_mul, map_mul, map_inv]
    have h1 : rkIdx (fixV (Subgroup.zpowers t)) = rkIdx (fixV (Subgroup.zpowers (ρ₀ σ))) :=
      rkIdx_fixV_zpowers_of_intertwine e t (ρ₀ σ) ht
    have h2 : rkIdx (fixV (Subgroup.zpowers (ρ₀ σ))) =
        rkIdx (fixV (Subgroup.zpowers (ρ₀ s))) := by
      refine (rkIdx_fixV_zpowers_of_intertwine (ρ₀ c) (ρ₀ s) (ρ₀ σ) ?_).symm
      intro w
      rw [hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    have hP : ∀ m < 2 ^ n, ρ₀ s (toW n m) = toW n m ↔ (act arr m == m) = true := by
      intro m hm
      rw [hact s arr harr m, beq_iff_eq]
      exact ⟨fun h => toW_inj (hlt arr m) hm h, fun h => by rw [h]⟩
    have h3 : rkIdx (fixV (Subgroup.zpowers (ρ₀ s))) = n - k :=
      rkIdx_fixV_zpowers_of_masks (ρ₀ s) (fun m => act arr m == m) hP hk
    rw [h1, h2, h3]

end CFSG.Quasithin.AppendixH.H14
