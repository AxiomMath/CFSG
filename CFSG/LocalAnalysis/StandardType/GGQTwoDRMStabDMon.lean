module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameTau
import CFSG.LocalAnalysis.StandardType.FS81.OmMonomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.StandardType.FrameRoute.FS81

private abbrev p9uRMDM_J (m : ℕ) (i₀ : Fin m) := {i : Fin m // i ≠ i₀}

private abbrev p9uRMDM_U (m : ℕ) (i₀ : Fin m) : Submodule (ZMod 3) (DVec m) :=
  Submodule.span (ZMod 3) {x : DVec m | ∃ p : Fin m, p ≠ i₀ ∧ x = dBasis m p}

private lemma p9uRMDM_dBasis_mem_U {m : ℕ} {i₀ : Fin m} {p : Fin m} (hp : p ≠ i₀) :
    dBasis m p ∈ p9uRMDM_U m i₀ :=
  Submodule.subset_span ⟨p, hp, rfl⟩

private lemma p9uRMDM_mem_U_iff {m : ℕ} {i₀ : Fin m} (v : DVec m) :
    v ∈ p9uRMDM_U m i₀ ↔ v i₀ = 0 := by
  constructor
  · intro hv
    have hker : p9uRMDM_U m i₀ ≤ LinearMap.ker (LinearMap.proj i₀) := by
      rw [Submodule.span_le]
      rintro x ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
      rw [dBasis, Pi.basisFun_apply, Pi.single_apply, if_neg (Ne.symm hp)]
    have h := hker hv
    rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h
  · intro hv
    have hsum := (dBasis m).sum_repr v
    rw [← hsum]
    refine Submodule.sum_mem _ fun p _ => ?_
    by_cases hp : p = i₀
    · subst hp
      have hrep : (dBasis m).repr v p = v p := by
        rw [dBasis, Pi.basisFun_repr]
      rw [hrep, hv, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (p9uRMDM_dBasis_mem_U hp)

private lemma p9uRMDM_card_J {m : ℕ} (i₀ : Fin m) :
    Fintype.card (p9uRMDM_J m i₀) = m - 1 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin m => i ≠ i₀) = Finset.univ.erase i₀ := by
    ext i
    simp [Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]

private lemma p9uRMDM_dTau_mem_stab {m : ℕ} {i₀ : Fin m} {p q : Fin m} (hp : p ≠ i₀)
    (hq : q ≠ i₀) (hpq : p ≠ q) (ε : Bool) :
    dTau m ε p q ∈ dEvenStab m (dBasis m i₀) :=
  ⟨dTau_mem_dEven m ε hpq, by
    rw [dTau_apply_of_ne m ε (Ne.symm hp) (Ne.symm hq)]⟩

private lemma p9uRMDM_coord_fix {m : ℕ} {i₀ : Fin m} {w : DVec m ≃ₗ[ZMod 3] DVec m}
    (hw : w ∈ dEvenStab m (dBasis m i₀)) (v : DVec m) :
    (w v) i₀ = v i₀ := by
  obtain ⟨hwEven, hwfix⟩ := hw
  obtain ⟨σ, c, hc, hprod, hact⟩ := hwEven
  have hσ0 : σ i₀ = i₀ := by
    by_contra hσ
    have h := congrFun (hact i₀) i₀
    rw [hwfix] at h
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_apply] at h
    rw [if_neg (fun hh : i₀ = σ i₀ => hσ hh.symm), smul_zero] at h
    exact absurd h (by decide)
  have hc0 : c i₀ = 1 := by
    have h := congrFun (hact i₀) i₀
    rw [hwfix, hσ0] at h
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_eq_same, mul_one] at h
    simpa using h.symm
  have hfun : (LinearMap.proj i₀ : DVec m →ₗ[ZMod 3] ZMod 3).comp w.toLinearMap =
      LinearMap.proj i₀ := by
    refine (dBasis m).ext fun j => ?_
    change (w (dBasis m j)) i₀ = (dBasis m j) i₀
    rw [hact j]
    by_cases hj : j = i₀
    · subst hj
      rw [hσ0, hc0]
      simp
    · have hσj : σ j ≠ i₀ := fun h => hj (σ.injective (h.trans hσ0.symm))
      simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_apply]
      rw [if_neg (fun h : i₀ = σ j => hσj h.symm), smul_zero,
        if_neg (fun h : i₀ = j => hj h.symm)]
  have h := congrArg (fun (f : DVec m →ₗ[ZMod 3] ZMod 3) => f v) hfun
  change (w v) i₀ = v i₀
  simpa only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_toLinearMap] using h

private lemma p9uRMDM_U_eq_comm (m : ℕ) (i₀ : Fin m) (hm : 3 ≤ m) :
    p9uRMDM_U m i₀ =
      Submodule.span (ZMod 3) {x : DVec m | ∃ (w : DVec m ≃ₗ[ZMod 3] DVec m),
        w ∈ dEvenStab m (dBasis m i₀) ∧ ∃ v : DVec m, x = w v - v} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨p, hp, rfl⟩
    have hcard : 1 < Fintype.card (p9uRMDM_J m i₀) := by
      rw [p9uRMDM_card_J]
      omega
    obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card hcard (⟨p, hp⟩ : p9uRMDM_J m i₀)
    have hqp : q.1 ≠ p := fun h => hq (Subtype.ext h)
    have hpq : p ≠ q.1 := Ne.symm hqp
    have hmem : dBasis m p = (dTau m true p q.1 (dBasis m p) - dBasis m p) +
        (dTau m false p q.1 (dBasis m p) - dBasis m p) := by
      rw [dTau_apply_left m true hpq, dTau_apply_left m false hpq,
        show (if true then (-1 : ZMod 3) else 1) = -1 from by decide,
        show (if false then (-1 : ZMod 3) else 1) = 1 from by decide]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, dBasis,
        Pi.basisFun_apply, Pi.single_apply, neg_one_smul, one_smul]
      split_ifs <;> simp_all <;> decide +kernel
    rw [hmem]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.subset_span
        ⟨dTau m true p q.1, p9uRMDM_dTau_mem_stab hp q.2 hpq true, dBasis m p, rfl⟩
    · exact Submodule.subset_span
        ⟨dTau m false p q.1, p9uRMDM_dTau_mem_stab hp q.2 hpq false, dBasis m p, rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨w, hw, v, rfl⟩
    exact (p9uRMDM_mem_U_iff (w v - v)).mpr (by
      rw [Pi.sub_apply, p9uRMDM_coord_fix hw v, sub_self])

private lemma p9uRMDM_map_U {m : ℕ} (hm : 3 ≤ m) {i₀ : Fin m}
    {a : DVec m ≃ₗ[ZMod 3] DVec m} (hfix : a (dBasis m i₀) = dBasis m i₀)
    (hnorm : ∀ w ∈ dEvenStab m (dBasis m i₀), a * w * a⁻¹ ∈ dEvenStab m (dBasis m i₀)) :
    Submodule.map (a : DVec m →ₗ[ZMod 3] DVec m) (p9uRMDM_U m i₀) = p9uRMDM_U m i₀ := by
  have hle : Submodule.map (a : DVec m →ₗ[ZMod 3] DVec m) (p9uRMDM_U m i₀) ≤
      p9uRMDM_U m i₀ := by
    rw [p9uRMDM_U_eq_comm m i₀ hm, Submodule.map_span, Submodule.span_le]
    rintro x ⟨y, ⟨w, hw, v, rfl⟩, rfl⟩
    have hkey : a (w v - v) = (a * w * a⁻¹) (a v) - a v := by
      simp only [map_sub, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.symm_apply_apply]
    change a (w v - v) ∈ Submodule.span (ZMod 3) {x : DVec m |
      ∃ (w : DVec m ≃ₗ[ZMod 3] DVec m),
        w ∈ dEvenStab m (dBasis m i₀) ∧ ∃ v : DVec m, x = w v - v}
    rw [hkey]
    exact Submodule.subset_span ⟨a * w * a⁻¹, hnorm w hw, a v, rfl⟩
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq a _)

private noncomputable def p9uRMDM_extPerm {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  σ.extendDomain (finSuccAboveEquiv i₀)
private lemma p9uRMDM_extPerm_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (l : Fin n) :
    p9uRMDM_extPerm i₀ σ (i₀.succAbove l) = i₀.succAbove (σ l) :=
  Equiv.Perm.extendDomain_apply_image σ (finSuccAboveEquiv i₀) l
private lemma p9uRMDM_extPerm_self {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) : p9uRMDM_extPerm i₀ σ i₀ = i₀ :=
  Equiv.Perm.extendDomain_apply_not_subtype σ (finSuccAboveEquiv i₀) (fun h => h rfl)
private noncomputable def p9uRMDM_lift {n : ℕ} (i₀ : Fin (n + 1))
    (u : Fin n → (ZMod 3)ˣ) : Fin (n + 1) → (ZMod 3)ˣ :=
  fun k => if hk : k = i₀ then 1 else u ((finSuccAboveEquiv i₀).symm ⟨k, hk⟩)
private lemma p9uRMDM_lift_self {n : ℕ} (i₀ : Fin (n + 1)) (u : Fin n → (ZMod 3)ˣ) :
    p9uRMDM_lift i₀ u i₀ = 1 :=
  dif_pos rfl
private lemma p9uRMDM_lift_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (u : Fin n → (ZMod 3)ˣ) (l : Fin n) :
    p9uRMDM_lift i₀ u (i₀.succAbove l) = u l := by
  rw [p9uRMDM_lift, dif_neg (Fin.succAbove_ne i₀ l)]
  congr 1
  rw [show (⟨i₀.succAbove l, Fin.succAbove_ne i₀ l⟩ : {i : Fin (n + 1) // i ≠ i₀}) =
      finSuccAboveEquiv i₀ l from Subtype.ext rfl, Equiv.symm_apply_apply]
private lemma p9uRMDM_prod_lift {n : ℕ} (i₀ : Fin (n + 1)) (u : Fin n → (ZMod 3)ˣ)
    (t : Fin n → ZMod 3) (hu : ∀ l, (u l : ZMod 3) = t l) :
    (∏ k, (p9uRMDM_lift i₀ u k : ZMod 3)) = ∏ l, t l := by
  rw [Fin.prod_univ_succAbove (fun k => (p9uRMDM_lift i₀ u k : ZMod 3)) i₀]
  change (p9uRMDM_lift i₀ u i₀ : ZMod 3) *
      (∏ l, (p9uRMDM_lift i₀ u (i₀.succAbove l) : ZMod 3)) = ∏ l, t l
  rw [p9uRMDM_lift_self, Units.val_one, one_mul]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [p9uRMDM_lift_succAbove, hu l]
private noncomputable def p9uRMDM_liftVal {n : ℕ} (i₀ : Fin (n + 1))
    (t : Fin n → ZMod 3) : Fin (n + 1) → ZMod 3 :=
  fun k => if hk : k = i₀ then 1 else t ((finSuccAboveEquiv i₀).symm ⟨k, hk⟩)
private lemma p9uRMDM_liftVal_self {n : ℕ} (i₀ : Fin (n + 1)) (t : Fin n → ZMod 3) :
    p9uRMDM_liftVal i₀ t i₀ = 1 :=
  dif_pos rfl
private lemma p9uRMDM_liftVal_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (t : Fin n → ZMod 3) (l : Fin n) :
    p9uRMDM_liftVal i₀ t (i₀.succAbove l) = t l := by
  rw [p9uRMDM_liftVal, dif_neg (Fin.succAbove_ne i₀ l)]
  congr 1
  rw [show (⟨i₀.succAbove l, Fin.succAbove_ne i₀ l⟩ : {i : Fin (n + 1) // i ≠ i₀}) =
      finSuccAboveEquiv i₀ l from Subtype.ext rfl, Equiv.symm_apply_apply]
private lemma p9uRMDM_unitOfSign_val {x : ZMod 3} (hx : x = 1 ∨ x = -1) :
    (((if x = -1 then (-1 : (ZMod 3)ˣ) else 1) : (ZMod 3)ˣ) : ZMod 3) = x := by
  rcases hx with h | h
  · rw [h, if_neg (by decide : ¬ ((1 : ZMod 3) = -1))]
    rfl
  · rw [h, if_pos rfl]
    rfl
private lemma p9uRMDM_unitOfSign_or (x : ZMod 3) :
    (((if x = -1 then (-1 : (ZMod 3)ˣ) else 1) : (ZMod 3)ˣ) : ZMod 3) = 1 ∨
      (((if x = -1 then (-1 : (ZMod 3)ˣ) else 1) : (ZMod 3)ˣ) : ZMod 3) = -1 := by
  by_cases h : x = -1
  · right; rw [if_pos h]; rfl
  · left; rw [if_neg h]; rfl
private noncomputable def p9uRMDM_monEquiv {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod 3)ˣ) :
    DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1) :=
  dPerm (n + 1) (p9uRMDM_extPerm i₀ σ) * ZS.diagMap 3 (dBasis (n + 1)) (p9uRMDM_lift i₀ u)
private lemma p9uRMDM_monEquiv_apply {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod 3)ˣ) (k : Fin (n + 1)) :
    p9uRMDM_monEquiv i₀ σ u (dBasis (n + 1) k) =
      (p9uRMDM_lift i₀ u k : ZMod 3) •
        dBasis (n + 1) (p9uRMDM_extPerm i₀ σ k) := by
  rw [p9uRMDM_monEquiv, LinearEquiv.mul_apply, ZS.diagMap_apply_basis, map_smul, dPerm_apply]
private lemma p9uRMDM_monEquiv_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod 3)ˣ) (l : Fin n) :
    p9uRMDM_monEquiv i₀ σ u (dBasis (n + 1) (i₀.succAbove l)) =
      (u l : ZMod 3) • dBasis (n + 1) (i₀.succAbove (σ l)) := by
  rw [p9uRMDM_monEquiv_apply, p9uRMDM_lift_succAbove, p9uRMDM_extPerm_succAbove]
private lemma p9uRMDM_monEquiv_self {n : ℕ} (i₀ : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod 3)ˣ) :
    p9uRMDM_monEquiv i₀ σ u (dBasis (n + 1) i₀) = dBasis (n + 1) i₀ := by
  rw [p9uRMDM_monEquiv_apply, p9uRMDM_extPerm_self, p9uRMDM_lift_self, Units.val_one,
    one_smul]
private lemma p9uRMDM_sigma_fix {m : ℕ} {i₀ : Fin m} {σ : Equiv.Perm (Fin m)}
    {c : Fin m → ZMod 3} (h : c i₀ • dBasis m (σ i₀) = dBasis m i₀) :
    σ i₀ = i₀ ∧ c i₀ = 1 := by
  by_cases hσ : σ i₀ = i₀
  · refine ⟨hσ, ?_⟩
    have h1 := congrFun h i₀
    rw [hσ] at h1
    simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_eq_same,
      mul_one] at h1
    exact h1
  · exfalso
    have h1 := congrFun h i₀
    simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_apply] at h1
    rw [if_neg (fun hh : i₀ = σ i₀ => hσ hh.symm)] at h1
    simp at h1
private lemma p9uRMDM_sum_repr {n : ℕ} {i₀ : Fin (n + 1)} {v : DVec (n + 1)}
    (hv : v i₀ = 0) :
    v = ∑ l : Fin n, v (i₀.succAbove l) • dBasis (n + 1) (i₀.succAbove l) := by
  have hrepr : ∀ k, (dBasis (n + 1)).repr v k = v k := by
    intro k; rw [dBasis, Pi.basisFun_repr]
  conv_lhs => rw [← (dBasis (n + 1)).sum_repr v]
  rw [Fin.sum_univ_succAbove (fun k => (dBasis (n + 1)).repr v k • dBasis (n + 1) k) i₀]
  simp only [hrepr, hv, zero_smul, zero_add]
theorem qtwoDRMStab_D_monomial {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m)
    (a : DVec m ≃ₗ[ZMod 3] DVec m) (hfix : a (Pi.single i₀ 1) = Pi.single i₀ 1)
    (hnorm : ∀ w ∈ dEvenStab m (Pi.single i₀ 1),
      a * w * a⁻¹ ∈ dEvenStab m (Pi.single i₀ 1)) :
    ∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ σ i₀ = i₀ ∧ c i₀ = 1 ∧
      ∀ i, a (dBasis m i) = c i • dBasis m (σ i) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 5 ≤ n := by omega
  haveI : Fintype (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) :=
    Fintype.ofInjective (fun e : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1) =>
      (e : DVec (n + 1) → DVec (n + 1))) (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hfix' : a (dBasis (n + 1) i₀) = dBasis (n + 1) i₀ := by
    simpa [dBasis] using hfix
  have hnorm' : ∀ w ∈ dEvenStab (n + 1) (dBasis (n + 1) i₀),
      a * w * a⁻¹ ∈ dEvenStab (n + 1) (dBasis (n + 1) i₀) := by
    intro w hw
    simpa [dBasis] using hnorm w (by simpa [dBasis] using hw)
  have hmapU : Submodule.map (a : DVec (n + 1) →ₗ[ZMod 3] DVec (n + 1))
      (p9uRMDM_U (n + 1) i₀) = p9uRMDM_U (n + 1) i₀ :=
    p9uRMDM_map_U (by omega) hfix' hnorm'
  have hmemU : ∀ x ∈ p9uRMDM_U (n + 1) i₀, a⁻¹ x ∈ p9uRMDM_U (n + 1) i₀ := by
    intro x hx
    have hx' : x ∈ Submodule.map (a : DVec (n + 1) →ₗ[ZMod 3] DVec (n + 1))
        (p9uRMDM_U (n + 1) i₀) := by rw [hmapU]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have h1 : a⁻¹ x = y := by
      rw [← hyx]
      exact LinearEquiv.symm_apply_apply a y
    rw [h1]
    exact hy
  have hnorm_inv : ∀ w ∈ dEvenStab (n + 1) (dBasis (n + 1) i₀),
      a⁻¹ * w * a ∈ dEvenStab (n + 1) (dBasis (n + 1) i₀) := by
    intro w hw
    have hinj : Function.Injective (fun u : dEvenStab (n + 1) (dBasis (n + 1) i₀) =>
        (⟨a * u.1 * a⁻¹, hnorm' u.1 u.2⟩ :
          dEvenStab (n + 1) (dBasis (n + 1) i₀))) := by
      intro u v huv
      apply Subtype.ext
      have h := congrArg Subtype.val huv
      simp only [Subtype.coe_mk] at h
      exact mul_right_cancel (mul_left_cancel h)
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
    have hval : a * u.1 * a⁻¹ = w := congrArg Subtype.val hu
    have hrew : a⁻¹ * w * a = u.1 := by
      rw [← hval]
      group
    rw [hrew]
    exact u.2
  let P : Matrix (Fin n) (Fin n) (ZMod 3) :=
    fun k l => a (dBasis (n + 1) (i₀.succAbove l)) (i₀.succAbove k)
  have hPcol : ∀ l, a (dBasis (n + 1) (i₀.succAbove l)) =
      ∑ j, P j l • dBasis (n + 1) (i₀.succAbove j) := by
    intro l
    refine p9uRMDM_sum_repr ?_
    have hmem : a (dBasis (n + 1) (i₀.succAbove l)) ∈ p9uRMDM_U (n + 1) i₀ := by
      have h0 : dBasis (n + 1) (i₀.succAbove l) ∈ p9uRMDM_U (n + 1) i₀ :=
        p9uRMDM_dBasis_mem_U (Fin.succAbove_ne i₀ l)
      have h1 : a (dBasis (n + 1) (i₀.succAbove l)) ∈
          Submodule.map (a : DVec (n + 1) →ₗ[ZMod 3] DVec (n + 1))
            (p9uRMDM_U (n + 1) i₀) :=
        Submodule.mem_map_of_mem (f := (a : DVec (n + 1) →ₗ[ZMod 3] DVec (n + 1))) h0
      rwa [hmapU] at h1
    exact (p9uRMDM_mem_U_iff _).mp hmem
  have hPdet : IsUnit P.det := by
    refine Matrix.isUnit_det_of_left_inverse
      (B := (show Matrix (Fin n) (Fin n) (ZMod 3) from
        fun k j => (a⁻¹ (dBasis (n + 1) (i₀.succAbove j))) (i₀.succAbove k))) ?_
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := congrArg (fun v : DVec (n + 1) => v (i₀.succAbove k))
        (LinearEquiv.symm_apply_apply a (dBasis (n + 1) (i₀.succAbove l)))
    rw [hPcol l, map_sum] at h
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul] at h
    rw [show (∑ j, (a⁻¹ (dBasis (n + 1) (i₀.succAbove j))) (i₀.succAbove k) * P j l) =
        ∑ j, P j l * (a⁻¹ (dBasis (n + 1) (i₀.succAbove j))) (i₀.succAbove k) from
      Finset.sum_congr rfl fun j _ => mul_comm _ _]
    change (∑ j, P j l * a.symm ((dBasis (n + 1) (i₀.succAbove j))) (i₀.succAbove k)) =
      if k = l then 1 else 0
    rw [h]
    simp [dBasis, Pi.single_apply, Fin.succAbove_right_inj]
  have hconj : ∀ (σ : Equiv.Perm (Fin n)) (t : Fin n → ZMod 3), IsSign t →
      ∏ i, t i = 1 →
      ∃ (σ' : Equiv.Perm (Fin n)) (t' : Fin n → ZMod 3), IsSign t' ∧ ∏ i, t' i = 1 ∧
        spMat σ t * P = P * spMat σ' t' := by
    intro σ t ht hprod
    let u : Fin n → (ZMod 3)ˣ := fun l => if t l = -1 then -1 else 1
    have hu : ∀ l, (u l : ZMod 3) = t l := fun l => p9uRMDM_unitOfSign_val (ht l)
    have hmon_fix : p9uRMDM_monEquiv i₀ σ u (dBasis (n + 1) i₀) = dBasis (n + 1) i₀ :=
      p9uRMDM_monEquiv_self i₀ σ u
    have hmon_mem : p9uRMDM_monEquiv i₀ σ u ∈ dEven (n + 1) := by
      refine ⟨p9uRMDM_extPerm i₀ σ, fun k => (p9uRMDM_lift i₀ u k : ZMod 3), ?_, ?_,
        p9uRMDM_monEquiv_apply i₀ σ u⟩
      · intro k
        change ((p9uRMDM_lift i₀ u k : ZMod 3) = 1 ∨ (p9uRMDM_lift i₀ u k : ZMod 3) = -1)
        by_cases hk : k = i₀
        · subst hk; rw [p9uRMDM_lift_self]; exact Or.inl rfl
        · rw [p9uRMDM_lift, dif_neg hk]
          exact p9uRMDM_unitOfSign_or _
      · change (∏ k, (p9uRMDM_lift i₀ u k : ZMod 3)) = 1
        rw [p9uRMDM_prod_lift i₀ u t hu]
        exact hprod
    have hmon_stab : p9uRMDM_monEquiv i₀ σ u ∈ dEvenStab (n + 1) (dBasis (n + 1) i₀) :=
      ⟨hmon_mem, hmon_fix⟩
    have hwtilde : a⁻¹ * p9uRMDM_monEquiv i₀ σ u * a ∈
        dEvenStab (n + 1) (dBasis (n + 1) i₀) :=
      hnorm_inv _ hmon_stab
    obtain ⟨σw, cw, hcw, hprodw, hactw⟩ := hwtilde.1
    have hwtilde_fix : (a⁻¹ * p9uRMDM_monEquiv i₀ σ u * a) (dBasis (n + 1) i₀) =
        dBasis (n + 1) i₀ := hwtilde.2
    have hfixdata : cw i₀ • dBasis (n + 1) (σw i₀) = dBasis (n + 1) i₀ := by
      rw [← hactw i₀]; exact hwtilde_fix
    have hcw0 : cw i₀ = 1 := (p9uRMDM_sigma_fix hfixdata).2
    have hs_not : ∀ l, σw (i₀.succAbove l) ≠ i₀ := by
      intro l hσl
      have hcoord := p9uRMDM_coord_fix hwtilde (dBasis (n + 1) (i₀.succAbove l))
      have hcoord0 : (cw (i₀.succAbove l) •
          dBasis (n + 1) (σw (i₀.succAbove l))) i₀ = 0 := by
        rw [← hactw (i₀.succAbove l), hcoord]
        rw [dBasis, Pi.basisFun_apply,
          Pi.single_eq_of_ne (Ne.symm (Fin.succAbove_ne i₀ l))]
      rw [hσl, dBasis, Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one] at hcoord0
      rcases hcw (i₀.succAbove l) with h | h
      · rw [h] at hcoord0; exact absurd hcoord0 (by decide)
      · rw [h] at hcoord0; exact absurd hcoord0 (by decide)
    let fσ : Fin n → Fin n := fun l =>
      (finSuccAboveEquiv i₀).symm ⟨σw (i₀.succAbove l), hs_not l⟩
    have hfσ_inj : Function.Injective fσ := by
      intro l l' h
      have h1 : (⟨σw (i₀.succAbove l), hs_not l⟩ : {i : Fin (n + 1) // i ≠ i₀}) =
          ⟨σw (i₀.succAbove l'), hs_not l'⟩ := (finSuccAboveEquiv i₀).symm.injective h
      have h2 : σw (i₀.succAbove l) = σw (i₀.succAbove l') := congrArg Subtype.val h1
      exact Fin.succAbove_right_injective (σw.injective h2)
    let σ' : Equiv.Perm (Fin n) :=
      Equiv.ofBijective fσ (Finite.injective_iff_bijective.mp hfσ_inj)
    let t' : Fin n → ZMod 3 := fun l => cw (i₀.succAbove l)
    have hσ' : ∀ l, σw (i₀.succAbove l) = i₀.succAbove (σ' l) := by
      intro l
      have h1 : (finSuccAboveEquiv i₀) (σ' l) = ⟨σw (i₀.succAbove l), hs_not l⟩ :=
        (finSuccAboveEquiv i₀).apply_symm_apply _
      exact (congrArg Subtype.val h1).symm
    have hA : ∀ k l, (spMat σ t * P) k l =
        (p9uRMDM_monEquiv i₀ σ u (a (dBasis (n + 1) (i₀.succAbove l))))
          (i₀.succAbove k) := by
      intro k l
      rw [Matrix.mul_apply, hPcol l, map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [p9uRMDM_monEquiv_succAbove i₀ σ u j, hu j, Pi.smul_apply, smul_eq_mul]
      rw [spMat]
      simp only [dBasis, Pi.basisFun_apply, Pi.single_apply, Fin.succAbove_right_inj]
      by_cases h : k = σ j
      · simp [h, mul_comm, mul_assoc]
      · simp [h]
    have hB : ∀ k l, (P * spMat σ' t') k l =
        (a ((a⁻¹ * p9uRMDM_monEquiv i₀ σ u * a)
          (dBasis (n + 1) (i₀.succAbove l)))) (i₀.succAbove k) := by
      intro k l
      rw [Matrix.mul_apply, hactw (i₀.succAbove l), hσ' l, map_smul, Pi.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single (σ' l)]
      · rw [spMat, if_pos rfl]
        change (a (dBasis (n + 1) (i₀.succAbove (σ' l)))) (i₀.succAbove k) * t' l =
          t' l * (a (dBasis (n + 1) (i₀.succAbove (σ' l)))) (i₀.succAbove k)
        ring
      · intro j _ hj
        rw [spMat]
        simp [hj]
      · intro hmem
        exact absurd (Finset.mem_univ (σ' l)) hmem
    have hmat : spMat σ t * P = P * spMat σ' t' := by
      ext k l
      rw [hA k l, hB k l]
      have hact : a ((a⁻¹ * p9uRMDM_monEquiv i₀ σ u * a)
          (dBasis (n + 1) (i₀.succAbove l))) =
          p9uRMDM_monEquiv i₀ σ u (a (dBasis (n + 1) (i₀.succAbove l))) := by
        simp
      rw [hact]
    refine ⟨σ', t', ?_, ?_, ?_⟩
    · intro l; exact hcw (i₀.succAbove l)
    · have hprod' : ∏ l, cw (i₀.succAbove l) = 1 := by
        have h := hprodw
        rw [Fin.prod_univ_succAbove (fun k => cw k) i₀, hcw0, one_mul] at h
        exact h
      simpa [t'] using hprod'
    · exact hmat
  obtain ⟨σ₁, t₁, ht₁, hPσ₁⟩ := monomial_of_conj_even hn P hPdet hconj
  have hact₁ : ∀ l, a (dBasis (n + 1) (i₀.succAbove l)) =
      t₁ l • dBasis (n + 1) (i₀.succAbove (σ₁ l)) := by
    intro l
    rw [hPcol l, hPσ₁]
    rw [Finset.sum_eq_single (σ₁ l)]
    · rw [spMat, if_pos rfl]
    · intro j _ hj
      rw [spMat, if_neg hj]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ (σ₁ l)) hmem
  refine ⟨p9uRMDM_extPerm i₀ σ₁, p9uRMDM_liftVal i₀ t₁, ?_, p9uRMDM_extPerm_self i₀ σ₁,
    p9uRMDM_liftVal_self i₀ t₁, ?_⟩
  · intro k
    by_cases hk : k = i₀
    · subst hk; rw [p9uRMDM_liftVal_self]; exact Or.inl rfl
    · rw [p9uRMDM_liftVal, dif_neg hk]
      exact ht₁ _
  · intro k
    by_cases hk : k = i₀
    · subst hk
      rw [p9uRMDM_liftVal_self, p9uRMDM_extPerm_self, one_smul]
      exact hfix'
    · set l : Fin n := (finSuccAboveEquiv i₀).symm ⟨k, hk⟩ with hl
      have hkl : i₀.succAbove l = k := by
        have h := (finSuccAboveEquiv i₀).apply_symm_apply (⟨k, hk⟩ : {i : Fin (n + 1) // i ≠ i₀})
        exact congrArg Subtype.val h
      rw [← hkl, p9uRMDM_liftVal_succAbove, p9uRMDM_extPerm_succAbove]
      exact hact₁ l

end CFSG.StandardType.QTwo

end
