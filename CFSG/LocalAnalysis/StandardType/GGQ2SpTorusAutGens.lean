module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutBasic
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
  {m : ℕ}

private theorem extSwap_one {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (extSwap (1 : PlaneRaw.V m) i j hij : ↥(StatedSp m K)) = rho i j hij sl2W := by
  unfold extSwap
  rw [Pi.one_apply, Pi.one_apply, if_pos rfl]

private theorem swapVec_one {m : ℕ} {i j : Fin m} (hij : i ≠ j) (u : PlaneRaw.V m) :
    swapVec (1 : PlaneRaw.V m) i j u = PlaneRaw.swapEquiv m i j u := by
  funext k
  simp only [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases hki : k = i
  · rw [hki, swapVec_apply_fst (1 : PlaneRaw.V m) hij, Equiv.swap_apply_left]
    simp
  · by_cases hkj : k = j
    · rw [hkj, swapVec_apply_snd, Equiv.swap_apply_right]
      simp
    · rw [swapVec_apply_of_ne (1 : PlaneRaw.V m) hki hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem rho_sl2W_conj_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {i j : Fin m} (hij : i ≠ j) (u : PlaneRaw.V m) :
    rho i j hij sl2W * tau ζ m u * (rho i j hij sl2W)⁻¹ =
      tau ζ m (PlaneRaw.swapEquiv m i j u) := by
  have h := extSwap_conj_tau (e := (1 : PlaneRaw.V m)) hK hζ hij
    (by simp) (by simp) u
  rwa [extSwap_one hij, swapVec_one hij] at h

theorem swapEquiv_mem_torusAut [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {X : Subgroup ↥(StatedSp m K)} {i j : Fin m} (hij : i ≠ j)
    (hX : rho i j hij sl2W ∈ X) : PlaneRaw.swapEquiv m i j ∈ torusAut ζ m X :=
  ⟨rho i j hij sl2W, hX, fun u => rho_sl2W_conj_tau hK hζ hij u⟩

theorem lam_sl2W_conj_tau [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (i : Fin m) (u : PlaneRaw.V m) :
    lam i sl2W * tau ζ m u * (lam i sl2W)⁻¹ = tau ζ m (PlaneRaw.negEquiv m i u) := by
  set v : PlaneRaw.V m := Function.update u i 0 with hv
  have hu : u = v + Pi.single i (u i) := by
    funext k
    by_cases hk : k = i <;> simp [hv, hk]
  have hneg : PlaneRaw.negEquiv m i u = v + Pi.single i (-(u i)) := by
    funext k
    simp only [PlaneRaw.negEquiv, LinearEquiv.piCongrRight_apply]
    by_cases hk : k = i <;> simp [hv, hk, LinearEquiv.neg_apply, LinearEquiv.refl_apply]
  have hcomm : lam i sl2W * tau ζ m v = tau ζ m v * lam i sl2W := by
    refine (commute_tau_of_mem_levi (ζ := ζ) (S := {i}) (u := v) ?_ ?_).symm
    · intro k hk
      rw [Finset.mem_singleton.mp hk, hv]
      simp
    · exact lam_mem_levi (Finset.mem_singleton_self i) sl2W
  rw [hneg, tau_add, tau_single]
  conv_lhs => rw [hu]
  rw [tau_add, tau_single]
  calc lam i sl2W * (tau ζ m v * lam i (ζ (Multiplicative.ofAdd (u i)))) *
        (lam i sl2W)⁻¹
      = (lam i sl2W * tau ζ m v * (lam i sl2W)⁻¹) *
          (lam i sl2W * lam i (ζ (Multiplicative.ofAdd (u i))) * (lam i sl2W)⁻¹) := by
        group
    _ = tau ζ m v * lam i (ζ (Multiplicative.ofAdd (-(u i)))) := by
        have h1 : lam i sl2W * tau ζ m v * (lam i sl2W)⁻¹ = tau ζ m v := by
          rw [hcomm]
          group
        rw [h1, ← map_mul (lam i), ← map_inv (lam i), ← map_mul (lam i),
          sl2W_conj_zeta hK hζ]

theorem negEquiv_mem_torusAut [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {X : Subgroup ↥(StatedSp m K)} {i : Fin m}
    (hX : lam i sl2W ∈ X) : PlaneRaw.negEquiv m i ∈ torusAut ζ m X :=
  ⟨lam i sl2W, hX, fun u => lam_sl2W_conj_tau hK hζ i u⟩

theorem signedPermGroup_subset_torusAut_top [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) :
    ((PlaneRaw.signedPermGroup m : Subgroup _) : Set _) ⊆ torusAut ζ m ⊤ := by
  simp only [PlaneRaw.signedPermGroup]
  refine closure_subset_torusAut ζ m (Set.union_subset ?_ ?_)
  · rintro T ⟨i, j, rfl⟩
    by_cases hij : i = j
    · subst hij
      have h1 : PlaneRaw.swapEquiv m i i = 1 := by
        ext u
        simp [PlaneRaw.swapEquiv, Equiv.swap_self, LinearEquiv.one_eq_refl]
      rw [h1]
      exact one_mem_torusAut ζ m ⊤
    · exact swapEquiv_mem_torusAut hK hζ hij (Subgroup.mem_top _)
  · rintro T ⟨i, rfl⟩
    exact negEquiv_mem_torusAut hK hζ (Subgroup.mem_top _)

end CFSG.StandardType.GGQ2Frame.SpBlocks
