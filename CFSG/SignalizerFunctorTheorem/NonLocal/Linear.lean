module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.LinearData
public import CFSG.SignalizerFunctorTheorem.NonLocal.LinearHeisenberg
public import CFSG.SignalizerFunctorTheorem.NonLocal.TwoDim
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement

local notation "SL" => Matrix.SpecialLinearGroup

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem two_pow_ge (n : ℕ) (hn : 4 ≤ n) : n ≤ 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : n + 1 - 2 = (n - 2) + 1 := by omega
    rw [h1, pow_succ]
    omega

theorem two_pow_gt (n : ℕ) (hn : 5 ≤ n) : n + 3 ≤ 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : n + 1 - 2 = (n - 2) + 1 := by omega
    rw [h1, pow_succ]
    omega

theorem two_pow_lin (n : ℕ) (hn : 5 ≤ n) : 2 * n ≤ 2 ^ (n - 2) + 5 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : n + 1 - 2 = (n - 2) + 1 := by omega
    have h2 : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1, pow_succ]
    omega

theorem linear_numerics {n q0 s L m j : ℕ} (hn : 3 ≤ n) (hq : 2 ≤ q0) (hs : 2 ≤ s)
    (hq2 : q0 = 2 → s ≠ 2) (hL : L = q0 ^ (n - 2)) (hLm : L ≤ m)
    (h : m ≤ n - 1 ∨ (s ^ j ≤ n ∧ m ≤ 2 * j)) : n = 3 ∧ q0 = 2 ∧ m = 2 := by
  have hL2 : 2 ^ (n - 2) ≤ L := hL ▸ Nat.pow_le_pow_left hq _
  rcases h with h | ⟨hsj, hmj⟩
  ·
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · have hn3 : n = 3 := by omega
      subst hn3
      have hLq : L = q0 := by simp [hL]
      refine ⟨rfl, by omega, by omega⟩
    · have := two_pow_ge n h4
      omega
  · have hj : 2 ^ j ≤ n := (Nat.pow_le_pow_left hs j).trans hsj
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · interval_cases n
      ·
        have hj1 : j ≤ 1 := by
          by_contra hcon
          have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hLq : L = q0 := by simp [hL]
        exact ⟨rfl, by omega, by omega⟩
      ·
        exfalso
        have hj2 : j ≤ 2 := by
          by_contra hcon
          have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hLq : L = q0 ^ 2 := by simp [hL]
        have hq4 : q0 * q0 ≤ 4 := by nlinarith
        have hq2' : q0 = 2 := by nlinarith
        have hs3 : 3 ≤ s := by
          have := hq2 hq2'
          omega
        have hj1 : j ≤ 1 := by
          by_contra hcon
          have : 3 ^ 2 ≤ s ^ j :=
            (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hs3 j)
          omega
        have : L = 4 := by simp [hL, hq2']
        omega
    · exfalso
      have hjn : j + 3 ≤ n := by
        by_contra hcon
        have h1 : 2 ^ (n - 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := two_pow_gt n h5
        omega
      have := two_pow_lin n h5
      omega

section Heisenberg

variable {n : ℕ} {K : Type*} [Field K] (k : Subfield K) (hn : 3 ≤ n)


theorem coe_map_rowElt (β : Fin n → k) (hβ : β (i0 hn) = 0) :
    ((Matrix.SpecialLinearGroup.map k.subtype (rowElt hn β hβ) : SL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec (Pi.single (i0 hn) (1 : K)) (fun j => (β j : K)) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  simp [rowElt, rowMat, vecMulVec_apply, Pi.single_apply]
  simp only [Matrix.one_apply]
  split_ifs <;> simp_all


theorem proj_map_rowElt_eq_one_iff (β : Fin n → k) (hβ : β (i0 hn) = 0) :
    proj n K (Matrix.SpecialLinearGroup.map k.subtype (rowElt hn β hβ)) = 1 ↔ β = 0 := by
  rw [proj_eq_one_iff, mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    rw [coe_map_rowElt k hn β hβ] at hc
    funext j
    by_cases hj : j = i0 hn
    · rw [hj]; exact hβ
    · have := congrFun (congrFun hc (i0 hn)) j
      have h2 : (β j : K) = 0 := by
        simpa [Matrix.one_apply, vecMulVec_apply, Pi.single_apply, hj, scalar_apply,
          diagonal_apply, Ne.symm hj] using this
      exact Subtype.ext h2
  · rintro rfl
    refine ⟨1, one_pow n, ?_⟩
    have h1 : rowElt hn (0 : Fin n → k) hβ = 1 := rowElt_zero hn
    rw [h1]
    simp


theorem zElt_mem_zSub (c : k) : zElt hn c ∈ (zSub hn : Subgroup (SL (Fin n) k)) := ⟨c, rfl⟩

theorem heis_comm (v : Mid hn → k) :
    ∀ a ∈ (rowSub hn : Subgroup (SL (Fin n) k)), ⁅(yElt hn v)⁻¹, a⁆ ∈ (zSub hn) := by
  rintro _ ⟨β, hβ, rfl⟩
  have := comm_elt hn β (extZero hn v) hβ (extZero_iL hn v)
  refine ⟨β ⬝ᵥ extZero hn v, ?_⟩
  exact this

theorem heis_nt : ∃ z ∈ (zSub hn : Subgroup (SL (Fin n) k)),
    proj n K (Matrix.SpecialLinearGroup.map k.subtype z) ≠ 1 := by
  refine ⟨zElt hn 1, zElt_mem_zSub k hn 1, fun h => ?_⟩
  have h1 := (proj_map_rowElt_eq_one_iff k hn _ (by simp [single_iL_apply_i0 hn])).mp h
  have h2 := congrFun h1 (iL hn)
  simp at h2


theorem heis_dist {F : Type*} [Field F] (ξ : SL (Fin n) k → F)
    (hmul : ∀ z ∈ (zSub hn : Subgroup (SL (Fin n) k)), ∀ z' ∈ (zSub hn : Subgroup (SL (Fin n) k)),
      ξ (z * z') = ξ z * ξ z')
    (hne0 : ∀ z ∈ (zSub hn : Subgroup (SL (Fin n) k)), ξ z ≠ 0)
    (hnt : ∃ z ∈ (zSub hn : Subgroup (SL (Fin n) k)), ξ z ≠ 1)
    (v v' : Mid hn → k) (hvv : v ≠ v') :
    ∃ a ∈ (rowSub hn : Subgroup (SL (Fin n) k)),
      ξ ⁅(yElt hn v)⁻¹, a⁆ ≠ ξ ⁅(yElt hn v')⁻¹, a⁆ := by
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ v' m := by
    by_contra h
    push Not at h
    exact hvv (funext h)
  let ψ : k → F := fun c => ξ (zElt hn c)
  have hψmul : ∀ c c', ψ (c + c') = ψ c * ψ c' := fun c c' => by
    show ξ (zElt hn (c + c')) = ξ (zElt hn c) * ξ (zElt hn c')
    rw [← zElt_mul, hmul _ (zElt_mem_zSub k hn c) _ (zElt_mem_zSub k hn c')]
  have hψne : ∀ c, ψ c ≠ 0 := fun c => hne0 _ (zElt_mem_zSub k hn c)
  have hψ0 : ψ 0 = 1 := by
    have h1 := hψmul 0 0
    rw [add_zero] at h1
    have h2 := hψne 0
    have : ψ 0 * (ψ 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  have hψnt : ∃ c, ψ c ≠ 1 := by
    obtain ⟨z, ⟨c, rfl⟩, hz⟩ := hnt
    exact ⟨c, hz⟩
  by_contra hcon
  push Not at hcon
  have hmi0 : m.1 ≠ i0 hn := m.2.1
  have hβ : ∀ t : k, (t • (Pi.single m.1 (1 : k) : Fin n → k)) (i0 hn) = 0 := by
    intro t
    simp [hmi0.symm]
  have hcomm_t : ∀ (w : Mid hn → k) (t : k),
      ⁅(yElt hn w)⁻¹, rowElt hn (t • (Pi.single m.1 (1 : k) : Fin n → k)) (hβ t)⁆ =
        zElt hn (t * w m) := by
    intro w t
    have := comm_elt hn (t • (Pi.single m.1 (1 : k) : Fin n → k)) (extZero hn w) (hβ t)
      (extZero_iL hn w)
    have h2 : ((t • (Pi.single m.1 (1 : k) : Fin n → k)) ⬝ᵥ extZero hn w) = t * w m := by
      simp [extZero_mid hn w m]
    have h3 : ⁅(yElt hn w)⁻¹, rowElt hn (t • (Pi.single m.1 (1 : k) : Fin n → k)) (hβ t)⁆ =
        zElt hn ((t • (Pi.single m.1 (1 : k) : Fin n → k)) ⬝ᵥ extZero hn w) := this
    rw [h3, h2]
  have hall : ∀ t : k, ψ (t * (v m - v' m)) = 1 := by
    intro t
    have h1 := hcon (rowElt hn (t • (Pi.single m.1 (1 : k) : Fin n → k)) (hβ t)) ⟨_, hβ t, rfl⟩
    rw [hcomm_t, hcomm_t] at h1
    have h2 : ψ (t * v m) = ψ (t * v' m) := h1
    have h3 : t * (v m - v' m) = t * v m + -(t * v' m) := by ring
    rw [h3, hψmul]
    have h4 : ψ (t * v' m) * ψ (-(t * v' m)) = 1 := by
      rw [← hψmul, add_neg_cancel, hψ0]
    rw [h2, h4]
  obtain ⟨c, hc⟩ := hψnt
  apply hc
  have hd : v m - v' m ≠ 0 := sub_ne_zero.mpr hm
  have := hall (c * (v m - v' m)⁻¹)
  rwa [mul_assoc, inv_mul_cancel₀ hd, mul_one] at this


theorem linear_special_case [Finite K] (hn : 3 ≤ n) (k : Subfield K) (hk2 : Nat.card k = 2)
    {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2)
    (hsimple : IsSimpleGroup ((linearProjData n K).π.comp
      (Matrix.SpecialLinearGroup.map k.subtype)).range)
    (hnonab : ∃ a b : ((linearProjData n K).π.comp
      (Matrix.SpecialLinearGroup.map k.subtype)).range, a * b ≠ b * a)
    (V : Subgroup (projectiveSL n K)) [Finite V] [IsMulCommutative V]
    (hVexp : ∀ v ∈ V, v ^ s = 1)
    (hVnorm : ∀ g : SL (Fin n) k, ∀ v ∈ V,
      (linearProjData n K).π (Matrix.SpecialLinearGroup.map k.subtype g) * v *
        ((linearProjData n K).π (Matrix.SpecialLinearGroup.map k.subtype g))⁻¹ ∈ V)
    (hfaith : ∀ g : SL (Fin n) k, (∀ v ∈ V,
      (linearProjData n K).π (Matrix.SpecialLinearGroup.map k.subtype g) * v *
        ((linearProjData n K).π (Matrix.SpecialLinearGroup.map k.subtype g))⁻¹ = v) →
      (linearProjData n K).π (Matrix.SpecialLinearGroup.map k.subtype g) = 1)
    (hV2 : Nat.card V = s ^ 2) : False := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  let Ψ : SL (Fin n) k →* projectiveSL n K :=
    (linearProjData n K).π.comp (Matrix.SpecialLinearGroup.map k.subtype)
  let C₀ : Subgroup (projectiveSL n K) := Ψ.range
  have hC₀norm : ∀ c ∈ C₀, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    rintro c ⟨g, rfl⟩ v hv
    exact hVnorm g v hv
  have hfaithC : ∀ c : C₀, (∀ v ∈ V, (c : projectiveSL n K) * v * (c : projectiveSL n K)⁻¹ = v) →
      c = 1 := by
    rintro ⟨_, g, rfl⟩ h
    exact Subtype.ext (hfaith g h)
  let F := AlgebraicClosure (ZMod s)
  obtain ⟨m, ρ, hcard, hρ1⟩ := exists_rep_of_elementary_abelian (C₀.subtype) V hs hVexp
    (fun c v hv => hC₀norm c.1 c.2 v hv) F
  have hm : m = 2 := by
    have : s ^ m = s ^ 2 := by rw [← hcard, hV2]
    exact Nat.pow_right_injective hs.two_le this
  subst hm
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact hfaithC c (hρ1 c hc)
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have : s ∣ 2 := by
      rw [← CharP.cast_eq_zero_iff F s 2]
      exact_mod_cast h
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp this)
  have h2k : (2 : k) = 0 := by
    have h1 : Nat.card k • (1 : k) = 0 := card_nsmul_eq_zero'
    rw [hk2] at h1
    simpa using h1
  have hdbl : ∀ β : Fin n → k, β + β = 0 := by
    intro β
    ext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← two_mul, h2k, zero_mul]
  have hsq : ∀ (β : Fin n → k) (hβ : β (i0 hn) = 0), rowElt hn β hβ ^ 2 = 1 := by
    intro β hβ
    have h1 : rowElt hn β hβ ^ 2 = rowElt hn (β + β) (by simp [hβ]) := by
      rw [pow_two, rowElt_mul]
    rw [h1]
    have h2 : rowElt hn (β + β) (by simp [hβ]) = rowElt hn (0 : Fin n → k) (by simp) := by
      congr 1
      exact hdbl β
    rw [h2]
    exact rowElt_zero hn
  let m₀ : Fin n := ⟨1, by omega⟩
  have hm₀0 : m₀ ≠ i0 hn := by simp [m₀, i0, Fin.ext_iff]
  have hm₀L : m₀ ≠ iL hn := by simp [m₀, iL, Fin.ext_iff]; omega
  have hβ₁ : (Pi.single (iL hn) (1 : k) : Fin n → k) (i0 hn) = 0 := single_iL_apply_i0 hn
  have hβ₂ : (Pi.single m₀ (1 : k) : Fin n → k) (i0 hn) = 0 := by
    simp [hm₀0.symm]
  let g₁ := rowElt hn (Pi.single (iL hn) (1 : k) : Fin n → k) hβ₁
  let g₂ := rowElt hn (Pi.single m₀ (1 : k) : Fin n → k) hβ₂
  have hne1 : ∀ (β : Fin n → k) (hβ : β (i0 hn) = 0), β ≠ 0 →
      Ψ (rowElt hn β hβ) ≠ 1 := fun β hβ hβ0 h => hβ0
        ((proj_map_rowElt_eq_one_iff k hn β hβ).mp h)
  let u₁ : C₀ := ⟨Ψ g₁, g₁, rfl⟩
  let u₂ : C₀ := ⟨Ψ g₂, g₂, rfl⟩
  have hu₁ : u₁ ^ 2 = 1 := Subtype.ext (by
    show Ψ g₁ ^ 2 = 1
    rw [← map_pow, hsq, map_one])
  have hu₂ : u₂ ^ 2 = 1 := Subtype.ext (by
    show Ψ g₂ ^ 2 = 1
    rw [← map_pow, hsq, map_one])
  have hu₁1 : u₁ ≠ 1 := fun h => hne1 _ hβ₁ (fun h' => by
    have := congrFun h' (iL hn); simp at this) (congrArg Subtype.val h)
  have hu₂1 : u₂ ≠ 1 := fun h => hne1 _ hβ₂ (fun h' => by
    have := congrFun h' m₀; simp at this) (congrArg Subtype.val h)
  have hu₁₂ : u₁ ≠ u₂ := by
    intro h
    have h1 : Ψ g₁ = Ψ g₂ := congrArg Subtype.val h
    have h2 : Ψ (g₁⁻¹ * g₂) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : g₁⁻¹ * g₂ = rowElt hn (-(Pi.single (iL hn) (1 : k) : Fin n → k) +
        (Pi.single m₀ (1 : k) : Fin n → k)) (by simp [hβ₁, hβ₂]) := by
      rw [rowElt_inv hn _ hβ₁, rowElt_mul]
    rw [h3] at h2
    have h4 := (proj_map_rowElt_eq_one_iff k hn _ (by simp [hβ₁, hβ₂])).mp h2
    have h5 := congrFun h4 (iL hn)
    simp [hm₀L.symm] at h5
  have := hsimple
  exact not_faithful_dim_two hnonab h2F ρ hρinj u₁ u₂ hu₁ hu₂ hu₁1 hu₂1 hu₁₂


end Heisenberg

end CFSG.SignalizerFunctorTheorem.NonLocal
