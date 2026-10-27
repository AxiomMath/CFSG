module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryVec
public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockAux
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape

public section

namespace CFSG.StandardType.SympMinus

open Matrix Multiplicative CFSG.StandardType.SpJoin CFSG.StandardType.SpCoord
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.SeitzReduction.SymplecticPilot (permSp mat_permSp mat_permSp_inv mat_conj_permSp_apply
  sumMap_bijective)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spIncl spIncl_apply)
open CFSG.StandardType.TorC (coe_spPlaneTorus)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] {p m : ℕ}

private theorem smuElt_plane_sumMap (π : Equiv.Perm (Fin m)) (r : Fin m ⊕ Fin m) :
    WitSpNs.plane (Sum.map π π r) = π (WitSpNs.plane r) := by
  rcases r with j | j <;> rfl

private theorem smuElt_side_sumMap (π : Equiv.Perm (Fin m)) (r : Fin m ⊕ Fin m) :
    WitSpNs.side (Sum.map π π r) = WitSpNs.side r := by
  rcases r with j | j <;> rfl

private theorem smuElt_planeMat_comp_perm (π : Equiv.Perm (Fin m))
    (M : Fin m → Matrix (Fin 2) (Fin 2) K) (x y : Fin m ⊕ Fin m) :
    WitSpNs.planeMat (M ∘ ⇑π.symm) (Sum.map π π x) (Sum.map π π y) = WitSpNs.planeMat M x y := by
  rw [WitSpNs.planeMat_apply, WitSpNs.planeMat_apply]
  rcases x with j | j <;> rcases y with k | k <;>
    by_cases hjk : j = k <;>
    simp [WitSpNs.plane, WitSpNs.side, Function.comp_apply, hjk, π.injective.eq_iff,
      π.symm_apply_apply]

private theorem smuElt_spIncl_mulVec_perm (π : Equiv.Perm (Fin m)) (v : Fin m ⊕ Fin m → K) :
    spIncl (K := K) (π : Fin m → Fin m) *ᵥ v = fun r => v (Sum.map π.symm π.symm r) := by
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.sum_eq_single (Sum.map π.symm π.symm r) ?_ ?_).trans ?_
  · intro s _ hs
    rw [spIncl_apply, if_neg (fun h => hs (by rw [h]; cases s <;> simp)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [spIncl_apply, if_pos (by cases r <;> simp), one_mul]

private theorem smuElt_planeMat_mulVec_eq_of_one_off {S : Finset (Fin m)}
    {M : Fin m → Matrix (Fin 2) (Fin 2) K} (hM : ∀ x ∉ S, M x = 1)
    {v : Fin m ⊕ Fin m → K} (hv : ∀ r, WitSpNs.plane r ∈ S → v r = 0) :
    WitSpNs.planeMat M *ᵥ v = v := by
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  by_cases hr : WitSpNs.plane r ∈ S
  · rw [hv r hr]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [WitSpNs.planeMat_apply]
    by_cases hps : WitSpNs.plane r = WitSpNs.plane s
    · rw [if_pos hps, hv s (hps ▸ hr), mul_zero]
    · rw [if_neg hps, zero_mul]
  · refine (Finset.sum_eq_single r ?_ ?_).trans ?_
    · intro s _ hsr
      rw [WitSpNs.planeMat_apply]
      by_cases hps : WitSpNs.plane r = WitSpNs.plane s
      · rw [if_pos hps, hM (WitSpNs.plane s) (by rwa [← hps]), Matrix.one_apply,
          if_neg (fun hside => hsr (WitSpNs.eq_of_plane_side hps hside).symm), zero_mul]
      · rw [if_neg hps, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · rw [WitSpNs.planeMat_apply, if_pos rfl, hM (WitSpNs.plane r) hr, Matrix.one_apply,
        if_pos rfl, one_mul]

private theorem smuElt_permSp_conj_lam (π : Equiv.Perm (Fin m)) (i : Fin m)
    (A : SpecialLinearGroup (Fin 2) K) :
    permSp K π * lam i A * (permSp K π)⁻¹ = lam (π i) A := by
  apply mat_injective
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply π (lam i A) x y]
  simp only [mat_apply]
  rw [coe_lam, coe_lam]
  exact (pairMat_apply_equiv (Equiv.sumCongr π π) (A : Matrix (Fin 2) (Fin 2) K) x y).symm

private theorem smuElt_sl2W_mul_self [CharP K 2] :
    (sl2W : SpecialLinearGroup (Fin 2) K) * sl2W = 1 := by
  rw [sl2W_mul_sl2W]
  have h : (-1 : Kˣ) = 1 := by
    apply Units.ext
    simpa using (CharTwo.neg_eq (1 : K))
  rw [h, map_one]

private theorem smuElt_sign_mul_swap {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1)
    {a b : Fin m} (hsab : s a * s b = 1) (i : Fin m) : s i * s (Equiv.swap a b i) = 1 := by
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, hsab]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, mul_comm, hsab]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, hs i]

theorem mat_lam_eq_planeMat (i : Fin m) (A : SpecialLinearGroup (Fin 2) K) :
    (((lam i A : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      WitSpNs.planeMat (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) i
        (A : Matrix (Fin 2) (Fin 2) K)) := by
  rw [coe_lam]
  ext a b
  rw [WitSpNs.planeMat_apply]
  rcases a with j | j <;> rcases b with k | k <;>
    by_cases hji : j = i <;> by_cases hki : k = i <;> by_cases hjk : j = k <;>
    simp_all [pairMat, Function.update_apply, Matrix.one_apply, WitSpNs.plane, WitSpNs.side]

theorem permSp_conj_spPlaneTorus {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K}
    (π : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) :
    permSp K π * spPlaneTorus m ζ f * (permSp K π)⁻¹ = spPlaneTorus m ζ (f ∘ ⇑π.symm) := by
  apply mat_injective
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply π (spPlaneTorus m ζ f) x y]
  simp only [mat_apply]
  rw [coe_spPlaneTorus m ζ f, coe_spPlaneTorus m ζ (f ∘ ⇑π.symm)]
  exact (smuElt_planeMat_comp_perm π
    (fun j => ((ζ (f j) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) x y).symm

theorem lam_sl2W_conj_spPlaneTorus {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K}
    (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (i : Fin m) (f : Fin m → Multiplicative (ZMod p)) :
    lam i sl2W * spPlaneTorus m ζ f * (lam i sl2W)⁻¹ =
      spPlaneTorus m ζ (Function.update f i (f i)⁻¹) := by
  apply mat_injective
  rw [map_mul, map_mul, ← map_inv]
  simp only [mat_apply]
  rw [mat_lam_eq_planeMat i sl2W, mat_lam_eq_planeMat i sl2W⁻¹, coe_spPlaneTorus m ζ f,
    coe_spPlaneTorus m ζ (Function.update f i (f i)⁻¹), WitSpNs.planeMat_mul, WitSpNs.planeMat_mul,
    WitSpNs.planeMat_injective.eq_iff]
  funext j
  by_cases hj : j = i
  · rw [hj]
    simp only [Function.update_self]
    have h := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
      (hζW (f i))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [h]
  · rw [Function.update_of_ne hj]
    simp [Function.update_of_ne hj]

@[expose] noncomputable def smuPlaneSwap (a b : Fin m) : StatedSp m K :=
  permSp K (Equiv.swap a b)

@[expose] noncomputable def smuPlaneSwapW (a b : Fin m) : StatedSp m K :=
  lam a sl2W * lam b sl2W * permSp K (Equiv.swap a b)

theorem smuPlaneSwap_mul_self (a b : Fin m) : smuPlaneSwap a b * smuPlaneSwap a b = (1 : StatedSp m K) := by
  rw [smuPlaneSwap]
  exact ggTBJSpB_permSp_swap_mul_self (K := K) a b

theorem smuPlaneSwapW_mul_self [CharP K 2] {a b : Fin m} (hab : a ≠ b) :
    smuPlaneSwapW a b * smuPlaneSwapW a b = (1 : StatedSp m K) := by
  have hPLa : permSp K (Equiv.swap a b) * lam a sl2W =
      lam b sl2W * permSp K (Equiv.swap a b) := by
    have h := smuElt_permSp_conj_lam (K := K) (Equiv.swap a b) a
      (sl2W : SpecialLinearGroup (Fin 2) K)
    rw [Equiv.swap_apply_left] at h
    calc permSp K (Equiv.swap a b) * lam a sl2W
        = permSp K (Equiv.swap a b) * lam a sl2W * (permSp K (Equiv.swap a b))⁻¹ *
            permSp K (Equiv.swap a b) := by group
      _ = lam b sl2W * permSp K (Equiv.swap a b) := by rw [h]
  have hPLb : permSp K (Equiv.swap a b) * lam b sl2W =
      lam a sl2W * permSp K (Equiv.swap a b) := by
    have h := smuElt_permSp_conj_lam (K := K) (Equiv.swap a b) b
      (sl2W : SpecialLinearGroup (Fin 2) K)
    rw [Equiv.swap_apply_right] at h
    calc permSp K (Equiv.swap a b) * lam b sl2W
        = permSp K (Equiv.swap a b) * lam b sl2W * (permSp K (Equiv.swap a b))⁻¹ *
            permSp K (Equiv.swap a b) := by group
      _ = lam a sl2W * permSp K (Equiv.swap a b) := by rw [h]
  have hP2 : permSp K (Equiv.swap a b) * permSp K (Equiv.swap a b) = 1 :=
    ggTBJSpB_permSp_swap_mul_self (K := K) a b
  have hLa2 : lam a (sl2W : SpecialLinearGroup (Fin 2) K) *
      lam a (sl2W : SpecialLinearGroup (Fin 2) K) = 1 := by
    rw [← map_mul, smuElt_sl2W_mul_self (K := K), map_one]
  have hLb2 : lam b (sl2W : SpecialLinearGroup (Fin 2) K) *
      lam b (sl2W : SpecialLinearGroup (Fin 2) K) = 1 := by
    rw [← map_mul, smuElt_sl2W_mul_self (K := K), map_one]
  have hcomm : lam a sl2W * lam b sl2W = lam b sl2W * lam a sl2W :=
    (commute_lam_lam hab (sl2W : SpecialLinearGroup (Fin 2) K)
      (sl2W : SpecialLinearGroup (Fin 2) K)).eq
  rw [smuPlaneSwapW]
  calc (lam a sl2W * lam b sl2W * permSp K (Equiv.swap a b)) *
        (lam a sl2W * lam b sl2W * permSp K (Equiv.swap a b))
      = lam a sl2W * lam b sl2W * (permSp K (Equiv.swap a b) * lam a sl2W) * lam b sl2W *
          permSp K (Equiv.swap a b) := by group
    _ = lam a sl2W * lam b sl2W * (lam b sl2W * permSp K (Equiv.swap a b)) * lam b sl2W *
          permSp K (Equiv.swap a b) := by rw [hPLa]
    _ = lam a sl2W * lam b sl2W * lam b sl2W * (permSp K (Equiv.swap a b) * lam b sl2W) *
          permSp K (Equiv.swap a b) := by group
    _ = lam a sl2W * lam b sl2W * lam b sl2W * (lam a sl2W * permSp K (Equiv.swap a b)) *
          permSp K (Equiv.swap a b) := by rw [hPLb]
    _ = lam a sl2W * lam b sl2W * lam b sl2W * lam a sl2W *
          (permSp K (Equiv.swap a b) * permSp K (Equiv.swap a b)) := by group
    _ = lam a sl2W * lam b sl2W * lam b sl2W * lam a sl2W * 1 := by rw [hP2]
    _ = lam a sl2W * lam b sl2W * lam b sl2W * lam a sl2W := by group
    _ = lam a sl2W * lam b sl2W * (lam b sl2W * lam a sl2W) := by group
    _ = lam a sl2W * lam b sl2W * (lam a sl2W * lam b sl2W) := by rw [← hcomm]
    _ = lam a sl2W * (lam b sl2W * lam a sl2W) * lam b sl2W := by group
    _ = lam a sl2W * (lam a sl2W * lam b sl2W) * lam b sl2W := by rw [← hcomm]
    _ = lam a sl2W * lam a sl2W * (lam b sl2W * lam b sl2W) := by group
    _ = 1 := by rw [hLa2, hLb2, mul_one]

theorem smuPlaneSwap_mulVec (a b : Fin m) {v : Fin m ⊕ Fin m → K}
    (hv : ∀ r, WitSpNs.plane r = a ∨ WitSpNs.plane r = b → v r = 0) :
    (((smuPlaneSwap a b : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v := by
  rw [smuPlaneSwap]
  change mat m K (permSp K (Equiv.swap a b)) *ᵥ v = v
  rw [mat_permSp, smuElt_spIncl_mulVec_perm]
  funext r
  by_cases hra : WitSpNs.plane r = a
  · have h1 : v r = 0 := hv r (Or.inl hra)
    have h2 : WitSpNs.plane (Sum.map (Equiv.swap a b).symm (Equiv.swap a b).symm r) = b := by
      rw [smuElt_plane_sumMap, ← Equiv.Perm.coe_inv (Equiv.swap a b), Equiv.swap_inv, hra,
        Equiv.swap_apply_left]
    have h3 : v (Sum.map (Equiv.swap a b).symm (Equiv.swap a b).symm r) = 0 := hv _ (Or.inr h2)
    simp only [h1, h3]
  · by_cases hrb : WitSpNs.plane r = b
    · have h1 : v r = 0 := hv r (Or.inr hrb)
      have h2 : WitSpNs.plane (Sum.map (Equiv.swap a b).symm (Equiv.swap a b).symm r) = a := by
        rw [smuElt_plane_sumMap, ← Equiv.Perm.coe_inv (Equiv.swap a b), Equiv.swap_inv, hrb,
          Equiv.swap_apply_right]
      have h3 : v (Sum.map (Equiv.swap a b).symm (Equiv.swap a b).symm r) = 0 := hv _ (Or.inl h2)
      simp only [h1, h3]
    · have hfix : (Equiv.swap a b) (WitSpNs.plane r) = WitSpNs.plane r :=
        Equiv.swap_apply_of_ne_of_ne hra hrb
      have hsid : Sum.map (Equiv.swap a b).symm (Equiv.swap a b).symm r = r := by
        apply WitSpNs.eq_of_plane_side
        · rw [smuElt_plane_sumMap, ← Equiv.Perm.coe_inv (Equiv.swap a b), Equiv.swap_inv, hfix]
        · rw [smuElt_side_sumMap]
      rw [hsid]

theorem smuPlaneSwapW_mulVec [CharP K 2] (a b : Fin m) {v : Fin m ⊕ Fin m → K}
    (hv : ∀ r, WitSpNs.plane r = a ∨ WitSpNs.plane r = b → v r = 0) :
    (((smuPlaneSwapW a b : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v := by
  have hσ : spIncl (K := K) (Equiv.swap a b : Fin m → Fin m) *ᵥ v = v := by
    have h := smuPlaneSwap_mulVec a b hv
    rw [smuPlaneSwap] at h
    rwa [← mat_apply, mat_permSp] at h
  have hB : WitSpNs.planeMat (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) b
      ((sl2W : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = v :=
    smuElt_planeMat_mulVec_eq_of_one_off (S := {b})
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        simp [Function.update_of_ne hx])
      (fun r hr => hv r (Or.inr (by simpa using hr)))
  have hA : WitSpNs.planeMat (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) a
      ((sl2W : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = v :=
    smuElt_planeMat_mulVec_eq_of_one_off (S := {a})
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        simp [Function.update_of_ne hx])
      (fun r hr => hv r (Or.inl (by simpa using hr)))
  change mat m K (smuPlaneSwapW a b) *ᵥ v = v
  rw [smuPlaneSwapW, map_mul, map_mul, mat_permSp]
  simp only [mat_apply]
  rw [mat_lam_eq_planeMat, mat_lam_eq_planeMat]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hσ, hB, hA]
theorem twisted_swap_apply {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1) (a b : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    ((diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ :
      MulAut (Fin m → Multiplicative (ZMod p))) f) i =
      ofAdd (s i * s (Equiv.swap a b i) * toAdd (f (Equiv.swap a b i))) := by
  have h1 : (diagAut s hs)⁻¹ f = fun j => ofAdd (s j * toAdd (f j)) := rfl
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, permAut_apply, diagAut_apply, Equiv.swap_inv]
  simp only [Function.comp_apply, toAdd_ofAdd]
  congr 1
  rw [mul_assoc]

private theorem smuElt_twisted_eq_update {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1)
    {a b : Fin m} (hab : a ≠ b) (hsab : s a * s b = -1)
    (f : Fin m → Multiplicative (ZMod p)) :
    Function.update (Function.update (f ∘ ⇑(Equiv.swap a b).symm) b
        ((f ∘ ⇑(Equiv.swap a b).symm) b)⁻¹) a
        ((f ∘ ⇑(Equiv.swap a b).symm) a)⁻¹ =
      ((diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ :
        MulAut (Fin m → Multiplicative (ZMod p))) f) := by
  funext i
  rw [twisted_swap_apply hs a b f i]
  rw [← Equiv.Perm.coe_inv (Equiv.swap a b), Equiv.swap_inv]
  by_cases hia : i = a
  · rw [hia]
    rw [Function.update_self, Function.comp_apply, Equiv.swap_apply_left, hsab, neg_one_mul,
      ofAdd_neg, ofAdd_toAdd]
  · by_cases hib : i = b
    · rw [hib]
      rw [Function.update_of_ne (Ne.symm hab), Function.update_self, Function.comp_apply,
        Equiv.swap_apply_right, mul_comm (s b) (s a), hsab, neg_one_mul, ofAdd_neg, ofAdd_toAdd]
    · rw [Function.update_of_ne hia, Function.update_of_ne hib, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hia hib, hs i, one_mul, ofAdd_toAdd]

theorem smuPlaneSwap_conj_twisted {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K}
    {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1) {a b : Fin m} (hsab : s a * s b = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    smuPlaneSwap a b * spPlaneTorus m ζ f * (smuPlaneSwap a b)⁻¹ =
      spPlaneTorus m ζ ((diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ :
        MulAut (Fin m → Multiplicative (ZMod p))) f) := by
  rw [smuPlaneSwap, permSp_conj_spPlaneTorus]
  congr 1
  funext i
  rw [twisted_swap_apply hs a b f i, smuElt_sign_mul_swap hs hsab i, Function.comp_apply,
    ← Equiv.Perm.coe_inv (Equiv.swap a b), Equiv.swap_inv, one_mul, ofAdd_toAdd]

theorem smuPlaneSwapW_conj_twisted {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K}
    (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1) {a b : Fin m} (hab : a ≠ b)
    (hsab : s a * s b = -1) (f : Fin m → Multiplicative (ZMod p)) :
    smuPlaneSwapW a b * spPlaneTorus m ζ f * (smuPlaneSwapW a b)⁻¹ =
      spPlaneTorus m ζ ((diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ :
        MulAut (Fin m → Multiplicative (ZMod p))) f) := by
  rw [smuPlaneSwapW]
  calc (lam a sl2W * lam b sl2W * permSp K (Equiv.swap a b)) * spPlaneTorus m ζ f *
        (lam a sl2W * lam b sl2W * permSp K (Equiv.swap a b))⁻¹
      = lam a sl2W * (lam b sl2W * (permSp K (Equiv.swap a b) * spPlaneTorus m ζ f *
          (permSp K (Equiv.swap a b))⁻¹) * (lam b sl2W)⁻¹) * (lam a sl2W)⁻¹ := by group
    _ = lam a sl2W * (lam b sl2W * spPlaneTorus m ζ (f ∘ ⇑(Equiv.swap a b).symm) *
          (lam b sl2W)⁻¹) * (lam a sl2W)⁻¹ := by
          rw [permSp_conj_spPlaneTorus (Equiv.swap a b) f]
    _ = lam a sl2W * spPlaneTorus m ζ
          (Function.update (f ∘ ⇑(Equiv.swap a b).symm) b
            ((f ∘ ⇑(Equiv.swap a b).symm) b)⁻¹) * (lam a sl2W)⁻¹ := by
          rw [lam_sl2W_conj_spPlaneTorus hζW b (f ∘ ⇑(Equiv.swap a b).symm)]
    _ = spPlaneTorus m ζ (Function.update (Function.update (f ∘ ⇑(Equiv.swap a b).symm) b
          ((f ∘ ⇑(Equiv.swap a b).symm) b)⁻¹) a
          ((Function.update (f ∘ ⇑(Equiv.swap a b).symm) b
            ((f ∘ ⇑(Equiv.swap a b).symm) b)⁻¹) a)⁻¹) :=
          lam_sl2W_conj_spPlaneTorus hζW a _
    _ = spPlaneTorus m ζ ((diagAut s hs * permAut (Equiv.swap a b) *
          (diagAut s hs)⁻¹ : MulAut (Fin m → Multiplicative (ZMod p))) f) := by
          rw [← smuElt_twisted_eq_update hs hab hsab f]
          simp [Function.update_self, Function.update_of_ne, hab, Ne.symm hab]

end CFSG.StandardType.SympMinus

end
