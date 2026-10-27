module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCA
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType
open CFSG CFSG.Assembly Module QTwoLin

private noncomputable def P {n : ℕ} (σ : Equiv.Perm (Fin n)) : GGBCV n ≃ₗ[ZMod 3] GGBCV n where
  toFun v := v ∘ σ.symm
  invFun v := v ∘ σ
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

private lemma P_mul {n} (σ τ : Equiv.Perm (Fin n)) : P (σ * τ) = P σ * P τ := by
  ext v i
  simp only [P, LinearEquiv.mul_apply, Function.comp_apply]
  congr 1

private lemma P_swap_apply {n} (a b : Fin n) (v : GGBCV n) (i : Fin n) :
    P (Equiv.swap a b) v i = v (Equiv.swap a b i) := by
  change v ((Equiv.swap a b).symm i) = v (Equiv.swap a b i)
  rw [Equiv.symm_swap]

private lemma ggBCDot_apply {n} (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp only [ggBCDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  rfl

private lemma ggBCRefl_apply {n} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v - (2 / (c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  erw [ggBCRefl, Module.reflection_apply]
  erw [LinearMap.smul_apply, ggBCDot_apply, smul_eq_mul]
  rfl

private lemma dot_single {n} (a : Fin n) (x : ZMod 3) (v : GGBCV n) :
    (Pi.single a x) ⬝ᵥ v = x * v a := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma dot_sub_single {n} (a b : Fin n) (v : GGBCV n) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n)) ⬝ᵥ v =
      v a - v b := by
  rw [sub_dotProduct, dot_single, dot_single]
  ring

private lemma hcc_ab {n} (a b : Fin n) (hab : a ≠ b) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n)) ⬝ᵥ
      ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n)) =
        (2 : ZMod 3) := by
  rw [dot_sub_single]
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
    Pi.single_eq_of_ne (Ne.symm hab), sub_zero, zero_sub]
  decide

private lemma refl_sub_single {n} (a b : Fin n) (hab : a ≠ b) :
    ggBCRefl ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n))
      (by rw [hcc_ab a b hab]; decide +kernel) = P (Equiv.swap a b) := by
  ext v i
  rw [ggBCRefl_apply, P_swap_apply]
  have hcv : ((Pi.single a (1:ZMod 3) : GGBCV n) -
      (Pi.single b (1:ZMod 3) : GGBCV n)) ⬝ᵥ v = v a - v b := dot_sub_single a b v
  rw [hcc_ab a b hab, hcv]
  have htwo : (2 : ZMod 3) / 2 = 1 := by decide +kernel
  rw [htwo, one_mul]
  by_cases hia : i = a
  · subst hia
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      Equiv.swap_apply_left, smul_eq_mul, sub_zero]
    ring
  · by_cases hib : i = b
    · subst hib
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hab),
        Pi.single_eq_same, Equiv.swap_apply_right, smul_eq_mul, zero_sub]
      ring
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib,
        Equiv.swap_apply_of_ne_of_ne hia hib, smul_eq_mul, sub_zero, mul_zero, sub_zero]
      ring

end CFSG.StandardType

namespace CFSG.StandardType
open CFSG CFSG.Assembly Module QTwoLin

private lemma two_mul (x : ZMod 3) : (2 : ZMod 3) * x = -x := by
  revert x
  decide +kernel

private lemma sub_neg_self (x : ZMod 3) : x - -x = -x := by
  revert x
  decide +kernel

private lemma dot_single_self {n} (a : Fin n) :
    (Pi.single a (1:ZMod 3) : GGBCV n) ⬝ᵥ (Pi.single a (1:ZMod 3) : GGBCV n) = 1 := by
  rw [dot_single, Pi.single_eq_same]; ring

private lemma hc_single {n} (a : Fin n) :
    (Pi.single a (1:ZMod 3) : GGBCV n) ⬝ᵥ (Pi.single a (1:ZMod 3) : GGBCV n) ≠ 0 := by
  rw [dot_single_self]; decide +kernel

private noncomputable def negLin {n} (a : Fin n) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (Pi.single a (1:ZMod 3)) (hc_single a)

private lemma negLin_apply {n} (a : Fin n) (v : GGBCV n) (i : Fin n) :
    negLin a v i = if i = a then -v i else v i := by
  rw [negLin, ggBCRefl_apply]
  have hcv : (Pi.single a (1:ZMod 3) : GGBCV n) ⬝ᵥ v = v a := by
    rw [dot_single]; ring
  rw [dot_single_self, hcv]
  have h2 : (2 : ZMod 3) / 1 = 2 := by ring
  rw [h2]
  by_cases hia : i = a
  · subst hia
    rw [if_pos rfl, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      two_mul, sub_neg_self]
  · rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hia, smul_eq_mul, mul_zero]
    simp [hia]

end CFSG.StandardType

namespace CFSG.StandardType
open CFSG CFSG.Assembly Module QTwoLin

private lemma coroot_chain {n : ℕ} (i : Fin n) (h : (i:ℕ) + 1 < n) (ε : ZMod 3) :
    ggBCCoroot n ε i =
      (Pi.single i (1:ZMod 3) : GGBCV n) - Pi.single ⟨(i:ℕ)+1, h⟩ (1:ZMod 3) := by
  have hne1 : i ≠ (⟨(i:ℕ)+1, h⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp at this
  have hne2 : (⟨(i:ℕ)+1, h⟩ : Fin n) ≠ i := hne1.symm
  funext j
  rw [ggBCCoroot, if_pos h, Pi.sub_apply]
  by_cases hji : (j:ℕ) = (i:ℕ)
  · rw [if_pos hji]
    have hji' : j = i := Fin.ext hji
    subst hji'
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne1]
    decide +kernel
  · rw [if_neg hji]
    by_cases hj : (j:ℕ) = (i:ℕ) + 1
    · rw [if_pos hj]
      have hj' : j = (⟨(i:ℕ)+1, h⟩ : Fin n) := Fin.ext hj
      subst hj'
      rw [Pi.single_eq_of_ne hne2, Pi.single_eq_same]
      decide +kernel
    · rw [if_neg hj]
      rw [Pi.single_eq_of_ne (fun hh => hji (by rw [hh])),
        Pi.single_eq_of_ne (fun hh => hj (by rw [hh]))]
      simp

private lemma coroot_last {n : ℕ} (i : Fin n) (h : ¬((i:ℕ) + 1 < n)) (ε : ZMod 3) :
    ggBCCoroot n ε i = (Pi.single i ε : GGBCV n) := by
  funext j
  rw [ggBCCoroot, if_neg h]
  by_cases hj : (j:ℕ) + 1 = n
  · rw [if_pos hj]
    have : j = i := by
      apply Fin.ext
      omega
    subst this
    rw [Pi.single_eq_same]
  · rw [if_neg hj]
    rw [Pi.single_eq_of_ne]
    intro hh
    exact hj (by rw [hh]; omega)

private lemma hc_sub {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b (1:ZMod 3)) ⬝ᵥ
      ((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b (1:ZMod 3)) ≠ 0 := by
  rw [hcc_ab a b hab]
  decide +kernel

private lemma coroot_hc {n : ℕ} (i : Fin n) :
    ggBCCoroot n 1 i ⬝ᵥ ggBCCoroot n 1 i ≠ 0 := by
  by_cases h : (i:ℕ) + 1 < n
  · rw [coroot_chain i h 1]
    rw [hcc_ab i (⟨(i:ℕ)+1, h⟩ : Fin n) (by
      intro hh; have := congrArg Fin.val hh; simp at this)]
    decide +kernel
  · rw [coroot_last i h 1, dot_single_self]
    decide +kernel

private noncomputable def rS {n : ℕ} (i : Fin n) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (ggBCCoroot n 1 i) (coroot_hc i)

noncomputable def ggQ2x_SimpleGp (n : ℕ) : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  Subgroup.closure (Set.range fun i : Fin n => ggBCRefl (ggBCCoroot n 1 i) (coroot_hc i))

private lemma ggQ2x_SimpleGp_eq_closure_range_rS (n : ℕ) :
    ggQ2x_SimpleGp n = Subgroup.closure (Set.range rS) := rfl

private noncomputable def Phom {n : ℕ} :
    Equiv.Perm (Fin n) →* (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  toFun := P
  map_one' := by ext v i; rfl
  map_mul' := P_mul

private lemma adjacent_mem {m : ℕ} (i : Fin m) :
    P (Equiv.swap i.castSucc i.succ) ∈ ggQ2x_SimpleGp (m+1) := by
  have hne : i.castSucc ≠ i.succ := by simp [Fin.ext_iff, Fin.castSucc, Fin.succ]
  have hlt : ((i.castSucc : Fin (m+1)) : ℕ) + 1 < m+1 := by
    simp [Fin.castSucc, Fin.succ]
  have hnext : (⟨((i.castSucc : Fin (m+1)) : ℕ)+1, hlt⟩ : Fin (m+1)) = i.succ := by
    apply Fin.ext; simp [Fin.castSucc, Fin.succ]
  have hv : (Pi.single i.castSucc (1:ZMod 3) : GGBCV (m+1)) - Pi.single i.succ 1
      = ggBCCoroot (m+1) 1 i.castSucc := by
    rw [coroot_chain i.castSucc hlt 1, hnext]
  have key : ggBCRefl ((Pi.single i.castSucc (1:ZMod 3) : GGBCV (m+1)) - Pi.single i.succ 1)
      (hc_sub i.castSucc i.succ hne) =
      ggBCRefl (ggBCCoroot (m+1) 1 i.castSucc) (coroot_hc i.castSucc) := by
    ext v k
    rw [ggBCRefl_apply, ggBCRefl_apply, hv]
  rw [← refl_sub_single i.castSucc i.succ hne, key]
  exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩

private lemma swap_mem {n : ℕ} (hn : 1 ≤ n) (a b : Fin n) :
    P (Equiv.swap a b) ∈ ggQ2x_SimpleGp n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let K : Subgroup (Equiv.Perm (Fin (m+1))) := (ggQ2x_SimpleGp (m+1)).comap Phom
  have hgen : ∀ i : Fin m, Equiv.swap i.castSucc i.succ ∈ K := by
    intro i
    rw [Subgroup.mem_comap]
    exact adjacent_mem i
  have htop : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid :=
    Submonoid.closure_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ m] at htop
  exact Subgroup.mem_comap.mp (htop (Submonoid.mem_top (Equiv.swap a b)))

end CFSG.StandardType

namespace CFSG.StandardType
open CFSG CFSG.Assembly Module QTwoLin

private lemma ggBCRefl_eq_of_eq {n} {c1 c2 : GGBCV n} (hv : c1 = c2)
    (h1 : c1 ⬝ᵥ c1 ≠ 0) (h2 : c2 ⬝ᵥ c2 ≠ 0) :
    ggBCRefl c1 h1 = ggBCRefl c2 h2 := by
  ext v k
  rw [ggBCRefl_apply, ggBCRefl_apply, hv]

private lemma negLin_conj {n} (a b : Fin n) (hab : a ≠ b) :
    P (Equiv.swap a b) * negLin b * (P (Equiv.swap a b))⁻¹ = negLin a := by
  have hq : (P (Equiv.swap a b))⁻¹ = P (Equiv.swap a b) := by
    rw [inv_eq_iff_mul_eq_one, ← P_mul, Equiv.swap_mul_self]
    exact map_one Phom
  rw [hq]
  ext v i
  simp only [LinearEquiv.mul_apply, P_swap_apply, negLin_apply]
  have hswap : (Equiv.swap a b) ((Equiv.swap a b) i) = i := by
    rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]
  rw [hswap]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, if_pos rfl, if_pos rfl]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, if_neg hab, if_neg (Ne.symm hab)]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, if_neg hib, if_neg hia]

private lemma negLin_last_mem {m : ℕ} : negLin (Fin.last m) ∈ ggQ2x_SimpleGp (m+1) := by
  have hgen : ggBCRefl (ggBCCoroot (m+1) 1 (Fin.last m)) (coroot_hc (Fin.last m)) ∈
      ggQ2x_SimpleGp (m+1) := Subgroup.subset_closure ⟨Fin.last m, rfl⟩
  have hv : ggBCCoroot (m+1) 1 (Fin.last m) = (Pi.single (Fin.last m) (1:ZMod 3) : GGBCV (m+1)) :=
    coroot_last (Fin.last m) (by simp [Fin.last]) 1
  change ggBCRefl (Pi.single (Fin.last m) (1:ZMod 3)) (hc_single (Fin.last m)) ∈
    ggQ2x_SimpleGp (m+1)
  rw [show ggBCRefl (Pi.single (Fin.last m) (1:ZMod 3)) (hc_single (Fin.last m)) =
      ggBCRefl (ggBCCoroot (m+1) 1 (Fin.last m)) (coroot_hc (Fin.last m)) from
    ggBCRefl_eq_of_eq hv.symm (hc_single _) (coroot_hc _)]
  exact hgen

private lemma negLin_mem {n : ℕ} (hn : 1 ≤ n) (a : Fin n) : negLin a ∈ ggQ2x_SimpleGp n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases ha : a = Fin.last m
  · subst ha; exact negLin_last_mem
  · have hconj := negLin_conj a (Fin.last m) ha
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (swap_mem (by omega) a (Fin.last m))
      negLin_last_mem) (Subgroup.inv_mem _ (swap_mem (by omega) a (Fin.last m)))

end CFSG.StandardType

namespace CFSG.StandardType
open CFSG CFSG.Assembly Module QTwoLin

private lemma dot_add_single {n} (a b : Fin n) (hab : a ≠ b) (v : GGBCV n) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) ⬝ᵥ v = v a + v b := by
  rw [add_dotProduct, dot_single, dot_single]
  ring

private lemma hcc_add {n} (a b : Fin n) (hab : a ≠ b) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) ⬝ᵥ
      ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) = 2 := by
  rw [dot_add_single a b hab]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
    Pi.single_eq_of_ne (Ne.symm hab), add_zero, zero_add]
  decide +kernel

private lemma hc_add {n} (a b : Fin n) (hab : a ≠ b) :
    ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) ⬝ᵥ
      ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) ≠ 0 := by
  rw [hcc_add a b hab]
  decide +kernel

private lemma refl_add_single {n} (a b : Fin n) (hab : a ≠ b) :
    ggBCRefl ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3))
      (hc_add a b hab) = negLin a * negLin b * P (Equiv.swap a b) := by
  ext v i
  rw [ggBCRefl_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    negLin_apply, negLin_apply, P_swap_apply]
  have hcv : ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3)) ⬝ᵥ v =
      v a + v b := dot_add_single a b hab v
  rw [hcc_add a b hab, hcv]
  have h2 : (2 : ZMod 3) / 2 = 1 := by decide +kernel
  rw [h2, one_mul]
  by_cases hia : i = a
  · subst hia
    rw [if_pos rfl, if_neg hab, Equiv.swap_apply_left]
    rw [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hab, add_zero, smul_eq_mul, mul_one]
    abel
  · by_cases hib : i = b
    · subst hib
      rw [if_neg (Ne.symm hab), if_pos rfl, Equiv.swap_apply_right]
      rw [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hab),
        Pi.single_eq_same, zero_add, smul_eq_mul, mul_one]
      abel
    · rw [if_neg hib, if_neg hia, Equiv.swap_apply_of_ne_of_ne hia hib]
      rw [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne hia,
        Pi.single_eq_of_ne hib, add_zero, smul_eq_mul, mul_zero]
      abel

private lemma sswap_mem {n : ℕ} (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    ggBCRefl ((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b (1:ZMod 3))
      (hc_add a b hab) ∈ ggQ2x_SimpleGp n := by
  rw [refl_add_single a b hab]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (negLin_mem hn a) (negLin_mem hn b))
    (swap_mem hn a b)

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_eq_one_or_neg_one (l : ZMod 3) (hl : l ≠ 0) : l = 1 ∨ l = -1 := by
  revert l; decide +kernel

private lemma ggQ2x_neg_mul_neg (x : ZMod 3) : -x * -x = x * x := by
  revert x; decide +kernel

private lemma ggQ2x_two_div_eq_neg (x : ZMod 3) (hx : x ≠ 0) : (2 : ZMod 3) / x = -x := by
  revert x; decide +kernel

private lemma ggQ2x_neg_dot_self {n} (c : GGBCV n) : (-c) ⬝ᵥ (-c) = c ⬝ᵥ c := by
  simp only [dotProduct, Pi.neg_apply]
  exact Finset.sum_congr rfl (fun i _ => ggQ2x_neg_mul_neg (c i))

private lemma ggQ2x_neg_dot {n} (c v : GGBCV n) : (-c) ⬝ᵥ v = -(c ⬝ᵥ v) := by
  simp only [dotProduct, Pi.neg_apply]
  rw [Finset.sum_congr rfl
    (fun i _ => (by decide +kernel : ∀ a b : ZMod 3, -a * b = -(a * b)) (c i) (v i))]
  exact Finset.sum_neg_distrib (s := Finset.univ) (f := fun i : Fin n => c i * v i)

private lemma ggQ2x_smul_hc {n} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) : (l • c) ⬝ᵥ (l • c) ≠ 0 := by
  rw [smul_dotProduct, dotProduct_smul]
  exact mul_ne_zero hl (mul_ne_zero hl hc)

private lemma ggQ2x_scalar_neg_mul_neg (A B x : ZMod 3) : (A * -B) * -x = (A * B) * x := by
  revert A B x; decide +kernel

private lemma ggQ2x_smul_neg_neg {n} (A B : ZMod 3) (c : GGBCV n) :
    (A * (-B)) • (-c) = (A * B) • c := by
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2x_scalar_neg_mul_neg A B (c i)

private lemma ggQ2xB_scalar_refl (vi ci A B : ZMod 3) :
    vi - (-A * B) * ci = vi + (A * B) * ci := by
  revert vi ci A B; decide +kernel

private lemma ggQ2x_refl_apply {n} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  rw [ggBCRefl_apply, ggQ2x_two_div_eq_neg (c ⬝ᵥ c) hc]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2xB_scalar_refl (v i) (c i) (c ⬝ᵥ c) (c ⬝ᵥ v)

private lemma ggQ2x_neg_hc {n} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    (-c) ⬝ᵥ (-c) ≠ 0 := by
  rw [ggQ2x_neg_dot_self]; exact hc

private lemma ggQ2x_refl_neg {n} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl (-c) (ggQ2x_neg_hc c hc) = ggBCRefl c hc := by
  ext v i
  rw [ggQ2x_refl_apply, ggQ2x_refl_apply]
  rw [ggQ2x_neg_dot_self, ggQ2x_neg_dot]
  simp only [ggQ2x_smul_neg_neg]

private lemma ggQ2x_refl_smul {n} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hlc : (l • c) ⬝ᵥ (l • c) ≠ 0) :
    ggBCRefl (l • c) hlc = ggBCRefl c hc := by
  rcases ggQ2x_eq_one_or_neg_one l hl with rfl | rfl
  · exact ggBCRefl_eq_of_eq (one_smul (ZMod 3) c) hlc hc
  · exact (ggBCRefl_eq_of_eq (neg_one_smul (ZMod 3) c) hlc (ggQ2x_neg_hc c hc)).trans
      (ggQ2x_refl_neg c hc)

private lemma ggQ2x_Wt_single {n} (i : Fin n) (x : ZMod 3) (hx : x ≠ 0) :
    ggBCWt (Pi.single i x : GGBCV n) = 1 := by
  unfold ggBCWt
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases hji : j = i
  · subst hji; simp [Pi.single_eq_same, hx]
  · simp [Pi.single_eq_of_ne hji, hji]

private lemma ggQ2x_Wt_sub_single {n} (a b : Fin n) (hab : a ≠ b) :
    ggBCWt ((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1) = 2 := by
  unfold ggBCWt
  rw [Finset.card_eq_two]
  refine ⟨a, b, hab, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hja : j = a
  · subst hja
    simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), hab] <;>
      decide +kernel
  · by_cases hjb : j = b
    · subst hjb
      simp [Pi.sub_apply, Pi.single_eq_of_ne hab, Pi.single_eq_same, hab] <;>
        decide +kernel
    · simp [Pi.sub_apply, Pi.single_eq_of_ne hja, Pi.single_eq_of_ne hjb, hja, hjb]

private lemma ggQ2x_Wt_coroot {n} (i : Fin n) :
    ggBCWt (ggBCCoroot n 1 i) = if (i:ℕ)+1 < n then 2 else 1 := by
  by_cases h : (i:ℕ)+1 < n
  · rw [coroot_chain i h 1, if_pos h]
    exact ggQ2x_Wt_sub_single i ⟨(i:ℕ)+1, h⟩ (by
      intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega)
  · rw [coroot_last i h 1, if_neg h]
    exact ggQ2x_Wt_single i 1 one_ne_zero

private lemma ggQ2x_coroot_mem_roots {n} (i : Fin n) : ggBCCoroot n 1 i ∈ ggBCRoots n := by
  rw [ggBCRoots, Set.mem_setOf_eq, ggQ2x_Wt_coroot i]
  split <;> omega

private lemma ggQ2x_Wt_eq_one {n : ℕ} {v : GGBCV n} (h : ggBCWt v = 1) :
    ∃ a : Fin n, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • Pi.single a 1 := by
  unfold ggBCWt at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  refine ⟨a, v a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
    simpa using hm
  · funext i
    by_cases hia : i = a
    · subst hia; simp
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, hvi]

private lemma ggQ2x_Wt_eq_two {n : ℕ} {v : GGBCV n} (h : ggBCWt v = 2) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ c d : ZMod 3, c ≠ 0 ∧ d ≠ 0 ∧
      v = c • Pi.single a 1 + d • Pi.single b 1 := by
  unfold ggBCWt at h
  obtain ⟨a, b, hab, ha⟩ : ∃ a b : Fin n, a ≠ b ∧
      Finset.univ.filter (fun i => v i ≠ 0) = {a, b} := Finset.card_eq_two.mp h
  have hma : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hmb : b ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hva : v a ≠ 0 := by simpa using hma
  have hvb : v b ≠ 0 := by simpa using hmb
  refine ⟨a, b, hab, v a, v b, hva, hvb, ?_⟩
  funext i
  by_cases hia : i = a
  · subst hia
    simp [Pi.single_eq_of_ne (Ne.symm hab), hab]
  · by_cases hib : i = b
    · subst hib
      simp [Pi.single_eq_of_ne hab, hab]
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia, hib]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, hvi]

theorem ggQ2x_W_eq_simple (n : ℕ) (hn : 1 ≤ n) : ggBCW n = ggQ2x_SimpleGp n := by
  apply le_antisymm
  · rw [ggBCW, Subgroup.closure_le]
    rintro t ⟨c, hcroot, hc, rfl⟩
    rcases hcroot with ⟨h1, h2⟩
    have hw : ggBCWt c = 1 ∨ ggBCWt c = 2 := by omega
    rcases hw with hw | hw
    · obtain ⟨a, l, hl, hcl⟩ := ggQ2x_Wt_eq_one hw
      have hlc : (l • (Pi.single a (1:ZMod 3) : GGBCV n)) ⬝ᵥ
          (l • (Pi.single a (1:ZMod 3) : GGBCV n)) ≠ 0 :=
        ggQ2x_smul_hc l hl (Pi.single a (1:ZMod 3)) (hc_single a)
      rw [ggBCRefl_eq_of_eq hcl hc hlc]
      rw [ggQ2x_refl_smul l hl (Pi.single a (1:ZMod 3)) (hc_single a) hlc]
      exact negLin_mem hn a
    · obtain ⟨a, b, hab, l, m, hl, hm, hcl⟩ := ggQ2x_Wt_eq_two hw
      rcases ggQ2x_eq_one_or_neg_one l hl with rfl | rfl <;>
        rcases ggQ2x_eq_one_or_neg_one m hm with rfl | rfl
      · have hv : c = (Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b 1 := by
          rw [hcl]; ext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          split_ifs <;> decide +kernel
        rw [ggBCRefl_eq_of_eq hv hc (hc_add a b hab)]
        exact sswap_mem hn a b hab
      · have hv : c = (Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1 := by
          rw [hcl]; ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
            smul_eq_mul]
          split_ifs <;> decide +kernel
        rw [ggBCRefl_eq_of_eq hv hc (hc_sub a b hab), refl_sub_single a b hab]
        exact swap_mem hn a b
      · have hv : c = -((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1) := by
          rw [hcl]; ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
            smul_eq_mul]
          split_ifs <;> decide +kernel
        rw [ggBCRefl_eq_of_eq hv hc (ggQ2x_neg_hc _ (hc_sub a b hab))]
        rw [ggQ2x_refl_neg _ (hc_sub a b hab), refl_sub_single a b hab]
        exact swap_mem hn a b
      · have hv : c = -((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b 1) := by
          rw [hcl]; ext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply, smul_eq_mul]
          split_ifs <;> decide +kernel
        rw [ggBCRefl_eq_of_eq hv hc (ggQ2x_neg_hc _ (hc_add a b hab))]
        rw [ggQ2x_refl_neg _ (hc_add a b hab)]
        exact sswap_mem hn a b hab
  · rw [ggQ2x_SimpleGp, Subgroup.closure_le]
    rintro t ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨ggBCCoroot n 1 i, ggQ2x_coroot_mem_roots i, coroot_hc i, rfl⟩

private noncomputable def ggQ2x_A1 (n : ℕ) [NeZero n] :
    Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  Subgroup.closure (rS '' {i : Fin n | i ≠ 0})

private noncomputable def ggQ2x_AN (n : ℕ) (last : Fin n) :
    Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  Subgroup.closure (rS '' {i : Fin n | i ≠ last})

private lemma ggQ2x_sum_single_one {n : ℕ} (i : Fin n) :
    ∑ j, (Pi.single i (1:ZMod 3) : GGBCV n) j = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2x_sum_smul_single {n : ℕ} (i : Fin n) (x : ZMod 3) :
    ∑ j, (x • (Pi.single i (1:ZMod 3) : GGBCV n)) j = x := by
  rw [Finset.sum_eq_single i]
  · simp [Pi.smul_apply, smul_eq_mul]
  · intro j _ hj; simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2x_rS_eq_swap {n : ℕ} (i : Fin n) (h : (i:ℕ)+1 < n) :
    rS i = P (Equiv.swap i ⟨(i:ℕ)+1, h⟩) := by
  have hne : i ≠ (⟨(i:ℕ)+1, h⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  rw [rS, ggBCRefl_eq_of_eq (coroot_chain i h 1) (coroot_hc i)
    (hc_sub i (⟨(i:ℕ)+1, h⟩ : Fin n) hne)]
  exact refl_sub_single i (⟨(i:ℕ)+1, h⟩ : Fin n) hne

private lemma ggQ2x_rS_last_eq_negLin {n : ℕ} (hn : 1 ≤ n) :
    rS (⟨n-1, by omega⟩ : Fin n) = negLin (⟨n-1, by omega⟩ : Fin n) := by
  have h : ¬(((⟨n-1, by omega⟩ : Fin n):ℕ) + 1 < n) := by
    simp only [Fin.val_mk]; omega
  rw [rS, negLin]
  exact ggBCRefl_eq_of_eq (coroot_last (⟨n-1, by omega⟩ : Fin n) h 1) _ _

private lemma ggQ2x_swap_lam1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (a b : Fin n)
    (ha : a ≠ 0) (hb : b ≠ 0) : P (Equiv.swap a b) ∈ ggQ2x_A1 n := by
  have key : ∀ k : ℕ, ∀ a b : Fin n, a.val ≤ b.val → max a.val b.val = k → a ≠ 0 →
      b ≠ 0 → P (Equiv.swap a b) ∈ ggQ2x_A1 n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hle hk ha hb
      have ha' : (a : ℕ) ≠ 0 := fun hh => ha (Fin.ext hh)
      have hb' : (b : ℕ) ≠ 0 := fun hh => hb (Fin.ext hh)
      rcases lt_or_eq_of_le hle with hlt | heq
      · let c : Fin n := ⟨b.val - 1, by omega⟩
        have hcval : c.val = b.val - 1 := rfl
        have hc0 : c ≠ 0 := by
          intro hh
          have hv : c.val = 0 := congrArg Fin.val hh
          omega
        by_cases hac : a.val = c.val
        · have hac' : a = c := Fin.ext hac
          rw [hac']
          have hb_eq : b = (⟨c.val + 1, by omega⟩ : Fin n) := by
            apply Fin.ext; simp only [Fin.val_mk]; omega
          have hltc : (c.val) + 1 < n := by omega
          rw [hb_eq, ← ggQ2x_rS_eq_swap c hltc]
          exact Subgroup.subset_closure ⟨c, hc0, rfl⟩
        · have haltc : a.val < c.val := by omega
          have hc_lt_b : c.val < b.val := by omega
          have ih_ac : P (Equiv.swap a c) ∈ ggQ2x_A1 n :=
            ih (max a.val c.val) (by omega) a c (by omega) rfl ha hc0
          have hcb_adj : P (Equiv.swap c b) ∈ ggQ2x_A1 n := by
            have hb_eq : b = (⟨c.val + 1, by omega⟩ : Fin n) := by
              apply Fin.ext; simp only [Fin.val_mk]; omega
            have hltc : (c.val) + 1 < n := by omega
            rw [hb_eq, ← ggQ2x_rS_eq_swap c hltc]
            exact Subgroup.subset_closure ⟨c, hc0, rfl⟩
          have hne_ac : a ≠ c := by intro hh; rw [hh] at haltc; omega
          have hne_ab : a ≠ b := by intro hh; rw [hh] at hlt; omega
          have hswap : Equiv.swap a b =
              Equiv.swap c b * Equiv.swap a c * Equiv.swap c b := by
            rw [Equiv.swap_comm a b, ← Equiv.swap_mul_swap_mul_swap hne_ac hne_ab]
          rw [hswap, P_mul, P_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcb_adj ih_ac) hcb_adj
      · have hab : a = b := Fin.ext heq
        rw [hab, Equiv.swap_self]
        show Phom (1 : Equiv.Perm (Fin n)) ∈ ggQ2x_A1 n
        rw [map_one]
        exact Subgroup.one_mem _
  rcases le_total a.val b.val with hle | hle
  · exact key (max a.val b.val) a b hle rfl ha hb
  · have h := key (max b.val a.val) b a hle rfl hb ha
    rwa [← Equiv.swap_comm a b] at h

private lemma ggQ2x_negLin_mem_lam1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (a : Fin n)
    (ha : a ≠ 0) : negLin a ∈ ggQ2x_A1 n := by
  by_cases ha_last : a = (⟨n-1, by omega⟩ : Fin n)
  · subst ha_last
    rw [← ggQ2x_rS_last_eq_negLin (n := n) (by omega)]
    exact Subgroup.subset_closure ⟨(⟨n-1, by omega⟩ : Fin n), ha, rfl⟩
  · have hconj := negLin_conj a (⟨n-1, by omega⟩ : Fin n) ha_last
    rw [← hconj]
    have h1 : P (Equiv.swap a (⟨n-1, by omega⟩ : Fin n)) ∈ ggQ2x_A1 n :=
      ggQ2x_swap_lam1 hn a _ ha (by
        intro hh
        have hv : ((⟨n-1, by omega⟩ : Fin n) : ℕ) = 0 := congrArg Fin.val hh
        simp only [Fin.val_mk] at hv
        omega)
    have h2 : negLin (⟨n-1, by omega⟩ : Fin n) ∈ ggQ2x_A1 n := by
      rw [← ggQ2x_rS_last_eq_negLin (n := n) (by omega)]
      exact Subgroup.subset_closure
        ⟨(⟨n-1, by omega⟩ : Fin n), by
          intro hh; have := congrArg Fin.val hh
          simp only [Fin.val_mk, Fin.val_zero] at this; omega, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)

private lemma ggQ2x_refl_mem_lam1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (c : GGBCV n)
    (hc : c ∈ ggBCRootsLam1 n) (hcc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hcc ∈ ggQ2x_A1 n := by
  rcases hc with ⟨hcroot, hc0⟩
  have hw : ggBCWt c = 1 ∨ ggBCWt c = 2 := by
    rcases hcroot with ⟨h1, h2⟩; omega
  rcases hw with hw | hw
  · obtain ⟨a, l, hl, hcl⟩ := ggQ2x_Wt_eq_one hw
    have ha : a ≠ 0 := by
      intro ha0
      have h0 : (l • (Pi.single a (1:ZMod 3) : GGBCV n)) 0 = 0 := by
        rw [← hcl]; exact hc0
      rw [ha0] at h0
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at h0
      exact hl h0
    rw [ggBCRefl_eq_of_eq hcl hcc (ggQ2x_smul_hc l hl _ (hc_single a))]
    have h1 : ggBCRefl (l • (Pi.single a (1:ZMod 3) : GGBCV n))
        (ggQ2x_smul_hc l hl _ (hc_single a)) = ggBCRefl (Pi.single a 1) (hc_single a) :=
      ggQ2x_refl_smul l hl _ (hc_single a) _
    rw [h1]
    exact ggQ2x_negLin_mem_lam1 hn a ha
  · obtain ⟨a, b, hab, l, k, hl, hk, hcl⟩ := ggQ2x_Wt_eq_two hw
    have ha : a ≠ 0 := by
      intro ha0
      have h0 : (l • (Pi.single a (1:ZMod 3) : GGBCV n) +
          k • (Pi.single b (1:ZMod 3) : GGBCV n)) 0 = 0 := by
        rw [← hcl]; exact hc0
      rw [ha0] at h0
      have hb0 : b ≠ 0 := by rintro rfl; exact hab ha0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hb0)] at h0
      simp at h0
      exact hl h0
    have hb : b ≠ 0 := by
      intro hb0
      have h0 : (l • (Pi.single a (1:ZMod 3) : GGBCV n) +
          k • (Pi.single b (1:ZMod 3) : GGBCV n)) 0 = 0 := by
        rw [← hcl]; exact hc0
      rw [hb0] at h0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
      rw [Pi.single_eq_of_ne (Ne.symm ha), Pi.single_eq_same] at h0
      simp at h0
      exact hk h0
    rcases ggQ2x_eq_one_or_neg_one l hl with rfl | rfl <;>
      rcases ggQ2x_eq_one_or_neg_one k hk with rfl | rfl
    · have hv : c = (Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b 1 := by
        rw [hcl]; ext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> decide +kernel
      rw [ggBCRefl_eq_of_eq hv hcc (hc_add a b hab), refl_add_single a b hab]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ggQ2x_negLin_mem_lam1 hn a ha)
        (ggQ2x_negLin_mem_lam1 hn b hb)) (ggQ2x_swap_lam1 hn a b ha hb)
    · have hv : c = (Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1 := by
        rw [hcl]; ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
          smul_eq_mul]
        split_ifs <;> decide +kernel
      rw [ggBCRefl_eq_of_eq hv hcc (hc_sub a b hab), refl_sub_single a b hab]
      exact ggQ2x_swap_lam1 hn a b ha hb
    · have hv : c = -((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1) := by
        rw [hcl]; ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
          smul_eq_mul]
        split_ifs <;> decide +kernel
      rw [ggBCRefl_eq_of_eq hv hcc (ggQ2x_neg_hc _ (hc_sub a b hab))]
      rw [ggQ2x_refl_neg _ (hc_sub a b hab), refl_sub_single a b hab]
      exact ggQ2x_swap_lam1 hn a b ha hb
    · have hv : c = -((Pi.single a (1:ZMod 3) : GGBCV n) + Pi.single b 1) := by
        rw [hcl]; ext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> decide +kernel
      rw [ggBCRefl_eq_of_eq hv hcc (ggQ2x_neg_hc _ (hc_add a b hab))]
      rw [ggQ2x_refl_neg _ (hc_add a b hab), refl_add_single a b hab]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ggQ2x_negLin_mem_lam1 hn a ha)
        (ggQ2x_negLin_mem_lam1 hn b hb)) (ggQ2x_swap_lam1 hn a b ha hb)

private lemma ggQ2x_swap_lamN {m : ℕ} (a b : Fin (m+1)) :
    P (Equiv.swap a b) ∈ ggQ2x_AN (m+1) (Fin.last m) := by
  let K : Subgroup (Equiv.Perm (Fin (m+1))) := (ggQ2x_AN (m+1) (Fin.last m)).comap Phom
  have hgen : ∀ i : Fin m, Equiv.swap i.castSucc i.succ ∈ K := by
    intro i
    rw [Subgroup.mem_comap]
    have hne : i.castSucc ≠ (Fin.last m : Fin (m+1)) := by
      intro hh; have := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
    have hlt : ((i.castSucc : Fin (m+1)) : ℕ) + 1 < m+1 := by
      simp only [Fin.val_castSucc]; omega
    have hnext : (⟨((i.castSucc : Fin (m+1)) : ℕ)+1, hlt⟩ : Fin (m+1)) = i.succ := by
      apply Fin.ext; simp only [Fin.val_mk, Fin.val_succ, Fin.val_castSucc]
    have hrw : rS i.castSucc = P (Equiv.swap i.castSucc i.succ) := by
      rw [ggQ2x_rS_eq_swap i.castSucc hlt, hnext]
    change P (Equiv.swap i.castSucc i.succ) ∈ ggQ2x_AN (m+1) (Fin.last m)
    rw [← hrw]
    exact Subgroup.subset_closure ⟨i.castSucc, hne, rfl⟩
  have htop : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid :=
    Submonoid.closure_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ m] at htop
  exact Subgroup.mem_comap.mp (htop (Submonoid.mem_top (Equiv.swap a b)))

private lemma ggQ2x_refl_mem_lamN {m : ℕ} (c : GGBCV (m+1))
    (hc : c ∈ ggBCRootsLamN (m+1)) (hcc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hcc ∈ ggQ2x_AN (m+1) (Fin.last m) := by
  obtain ⟨hwt, hsum⟩ := hc
  obtain ⟨a, b, hab, l, k, hl, hk, hcl⟩ := ggQ2x_Wt_eq_two hwt
  have hlk : l + k = 0 := by
    rw [hcl] at hsum
    simp only [Pi.add_apply] at hsum
    rw [Finset.sum_add_distrib, ggQ2x_sum_smul_single a l,
      ggQ2x_sum_smul_single b k] at hsum
    exact hsum
  rcases ggQ2x_eq_one_or_neg_one l hl with rfl | rfl
  · have hk1 : k = -1 := by
      have hh : ∀ k : ZMod 3, (1:ZMod 3) + k = 0 → k = -1 := by decide +kernel
      exact hh k hlk
    rw [hk1] at hcl
    have hv : c = (Pi.single a (1:ZMod 3) : GGBCV (m+1)) - Pi.single b 1 := by
      rw [hcl]; ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> decide +kernel
    rw [ggBCRefl_eq_of_eq hv hcc (hc_sub a b hab), refl_sub_single a b hab]
    exact ggQ2x_swap_lamN a b
  · have hk1 : k = 1 := by
      have hh : ∀ k : ZMod 3, (-1:ZMod 3) + k = 0 → k = 1 := by decide +kernel
      exact hh k hlk
    rw [hk1] at hcl
    have hv : c = -((Pi.single a (1:ZMod 3) : GGBCV (m+1)) - Pi.single b 1) := by
      rw [hcl]; ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_apply,
        smul_eq_mul]
      split_ifs <;> decide +kernel
    rw [ggBCRefl_eq_of_eq hv hcc (ggQ2x_neg_hc _ (hc_sub a b hab))]
    rw [ggQ2x_refl_neg _ (hc_sub a b hab), refl_sub_single a b hab]
    exact ggQ2x_swap_lamN a b

private lemma ggQ2x_coroot_mem_lam1 {n : ℕ} [NeZero n] (i : Fin n) (hi : i ≠ 0) :
    ggBCCoroot n 1 i ∈ ggBCRootsLam1 n := by
  refine ⟨ggQ2x_coroot_mem_roots i, ?_⟩
  by_cases h : (i:ℕ)+1 < n
  · rw [coroot_chain i h 1]
    simp only [Pi.sub_apply]
    rw [Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (by
      intro hh; have := congrArg Fin.val hh
      simp only [Fin.val_zero, Fin.val_mk] at this; omega)]
    simp
  · rw [coroot_last i h 1, Pi.single_eq_of_ne (Ne.symm hi)]

private lemma ggQ2x_coroot_mem_lamN {n : ℕ} (hn : 5 ≤ n) (i : Fin n)
    (hi : i ≠ (⟨n-1, by omega⟩ : Fin n)) :
    ggBCCoroot n 1 i ∈ ggBCRootsLamN n := by
  have hlt : (i:ℕ)+1 < n := by
    have hiv : (i:ℕ) ≠ n-1 := by
      intro hh; exact hi (Fin.ext hh)
    omega
  refine ⟨?_, ?_⟩
  · rw [ggQ2x_Wt_coroot i, if_pos hlt]
  · calc ∑ j, (ggBCCoroot n 1 i) j
        = ∑ j, ((Pi.single i (1:ZMod 3) : GGBCV n) j -
            (Pi.single (⟨(i:ℕ)+1, hlt⟩ : Fin n) (1:ZMod 3) : GGBCV n) j) := by
          rw [coroot_chain i hlt 1]
          simp only [Pi.sub_apply]
      _ = (∑ j, (Pi.single i (1:ZMod 3) : GGBCV n) j)
            - (∑ j, (Pi.single (⟨(i:ℕ)+1, hlt⟩ : Fin n) (1:ZMod 3) : GGBCV n) j) :=
          Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun j => (Pi.single i (1:ZMod 3) : GGBCV n) j)
            (g := fun j => (Pi.single (⟨(i:ℕ)+1, hlt⟩ : Fin n) (1:ZMod 3) : GGBCV n) j)
      _ = 1 - 1 := by
          rw [ggQ2x_sum_single_one i,
            ggQ2x_sum_single_one (⟨(i:ℕ)+1, hlt⟩ : Fin n)]
      _ = 0 := by simp

private theorem ggQ2x_parab_lam1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    Subgroup.closure (rS '' {i : Fin n | i ≠ 0}) =
      Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro t ⟨i, hi, rfl⟩
    exact Subgroup.subset_closure
      ⟨ggBCCoroot n 1 i, ggQ2x_coroot_mem_lam1 i hi, coroot_hc i, rfl⟩
  · rw [Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    exact ggQ2x_refl_mem_lam1 hn c hc hcc

private theorem ggQ2x_parab_lamN {n : ℕ} (hn : 5 ≤ n) :
    Subgroup.closure (rS '' {i : Fin n | i ≠ ⟨n - 1, by omega⟩}) =
      Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro t ⟨i, hi, rfl⟩
    exact Subgroup.subset_closure
      ⟨ggBCCoroot n 1 i, ggQ2x_coroot_mem_lamN hn i hi, coroot_hc i, rfl⟩
  · rw [Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ggQ2x_refl_mem_lamN c hc hcc

noncomputable def ggQ2x_T {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n) :
    (D.V ≃ₗ[ZMod 3] D.V) ≃* (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  toFun g := τ.symm.trans (g.trans τ)
  invFun g := τ.trans (g.trans τ.symm)
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp [LinearEquiv.mul_apply]

noncomputable def ggQ2x_Tm {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n) :
    (D.V ≃ₗ[ZMod 3] D.V) →* (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  (ggQ2x_T D τ).toMonoidHom

theorem ggQ2x_Tm_injective {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n) :
    Function.Injective (ggQ2x_Tm D τ) :=
  (ggQ2x_T D τ).injective

private lemma ggQ2xT_rootFun_eq_single {n : ℕ} (ε : ZMod 3) (i : Fin n)
    (hi : (i:ℕ)+1 < n) :
    ggBCRootFun n ε i =
      ((Pi.single i (1:ZMod 3) : GGBCV n) - Pi.single ⟨(i:ℕ)+1, hi⟩ (1:ZMod 3)) := by
  funext j
  by_cases h1 : j = i
  · subst h1
    have hne : j ≠ (⟨(j:ℕ)+1, hi⟩ : Fin n) := by
      intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
    simp [ggBCRootFun, hi, Pi.single_apply, hne]
    norm_num
  · by_cases h2 : j = (⟨(i:ℕ)+1, hi⟩ : Fin n)
    · subst h2
      have hne' : i ≠ (⟨(i:ℕ)+1, hi⟩ : Fin n) := by
        intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega
      simp [ggBCRootFun, hi, Pi.single_apply, h1, hne']
      rfl
    · have hj1 : (j:ℕ) ≠ i := fun h => h1 (Fin.ext h)
      have hj2 : (j:ℕ) ≠ (i:ℕ)+1 := fun h => h2 (Fin.ext h)
      simp [ggBCRootFun, hi, Pi.single_apply, h1, h2, hj1, hj2]

private lemma ggQ2xT_rootFun_last {n : ℕ} (ε : ZMod 3) (i : Fin n)
    (hi : ¬ ((i:ℕ)+1 < n)) :
    ggBCRootFun n ε i = (Pi.single i (2/ε) : GGBCV n) := by
  funext j
  rw [ggBCRootFun, if_neg hi]
  by_cases hj : (j:ℕ) + 1 = n
  · rw [if_pos hj]
    have hji : j = i := by
      apply Fin.ext
      omega
    subst hji
    rw [Pi.single_eq_same]
  · rw [if_neg hj]
    rw [Pi.single_eq_of_ne]
    intro hh
    exact hj (by rw [hh]; omega)

private lemma ggQ2xT_scalar_case2 (ε x : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    (2/ε) * x * ε = -x := by
  rcases hε with rfl | rfl <;> revert x <;> decide +kernel

private lemma ggQ2xT_neg_two_mul (a : ZMod 3) : -(2 * a) = a := by
  revert a; decide +kernel

private lemma ggQ2xT_neg_smul {n : ℕ} (a : ZMod 3) (x : GGBCV n) :
    (-a) • x = -(a • x) := by
  ext j
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact neg_mul a (x j)

private lemma ggQ2xT_smul_coroot_eq {n : ℕ} (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (i : Fin n) (v : GGBCV n) :
    (∑ j, ggBCRootFun n ε i j * v j) • ggBCCoroot n ε i =
      (-((ggBCCoroot n 1 i ⬝ᵥ ggBCCoroot n 1 i) * (ggBCCoroot n 1 i ⬝ᵥ v))) •
        ggBCCoroot n 1 i := by
  by_cases h : (i:ℕ)+1 < n
  · set u : GGBCV n := (Pi.single i (1:ZMod 3) : GGBCV n) -
        Pi.single ⟨(i:ℕ)+1, h⟩ (1:ZMod 3) with hu
    have hne : i ≠ (⟨(i:ℕ)+1, h⟩ : Fin n) := by
      intro hh; have := congrArg Fin.val hh; simp at this
    have hrf : ggBCRootFun n ε i = u := by
      rw [hu]; exact ggQ2xT_rootFun_eq_single ε i h
    have hcε : ggBCCoroot n ε i = u := by
      rw [hu]; exact coroot_chain i h ε
    have hc1 : ggBCCoroot n 1 i = u := by
      rw [hu]; exact coroot_chain i h 1
    rw [hrf, hcε, hc1]
    rw [show (∑ j, u j * v j) = u ⬝ᵥ v from rfl]
    rw [show u ⬝ᵥ u = (2 : ZMod 3) from by
      rw [hu]; exact hcc_ab i ⟨(i:ℕ)+1, h⟩ hne]
    have hscalar : -(2 * (u ⬝ᵥ v)) = u ⬝ᵥ v := ggQ2xT_neg_two_mul (u ⬝ᵥ v)
    exact (congrArg (fun a : ZMod 3 => a • u) hscalar).symm
  · have hrf : ggBCRootFun n ε i = (Pi.single i (2/ε) : GGBCV n) :=
      ggQ2xT_rootFun_last ε i h
    have hcε : ggBCCoroot n ε i = (Pi.single i ε : GGBCV n) := coroot_last i h ε
    have hc1 : ggBCCoroot n 1 i = (Pi.single i 1 : GGBCV n) := coroot_last i h 1
    rw [hrf, hcε, hc1]
    rw [show (∑ j, (Pi.single i (2/ε) : GGBCV n) j * v j) =
        (Pi.single i (2/ε) : GGBCV n) ⬝ᵥ v from rfl]
    simp only [dot_single, Pi.single_eq_same, one_mul]
    funext j
    by_cases hj : j = i
    · rw [hj]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact ggQ2xT_scalar_case2 ε (v i) hε
    · simp [Pi.single_eq_of_ne hj]

private lemma ggQ2xT_simpleRefl_eq {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (i : Fin n) :
    ggQ2x_T D τ (D.simpleRefl (e i)) = rS i := by
  refine LinearEquiv.ext fun v => ?_
  change τ (D.simpleRefl (e i) (τ.symm v)) = rS i v
  set w : D.V := τ.symm v with hw
  have hv : v = τ w := by rw [hw]; simp
  rw [hv]
  have hsimple : D.simpleRefl (e i) w = w - D.root (e i) w • D.coroot (e i) := by
    rw [GGQ2Lin.simpleRefl]
    exact Module.reflection_apply w (D.root_coroot_self (e i))
  rw [hsimple, map_sub, map_smul, hcor i, hroot i w]
  rw [rS, ggQ2x_refl_apply]
  rw [ggQ2xT_smul_coroot_eq ε hε i (τ w), ggQ2xT_neg_smul, sub_neg_eq_add]
  rfl

theorem ggQ2x_map_weyl {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j) :
    Subgroup.map (ggQ2x_Tm D τ) D.weyl = ggQ2x_SimpleGp n := by
  have hset : (ggQ2x_Tm D τ) '' (D.simpleRefl '' Set.univ) = Set.range rS := by
    ext g
    constructor
    · rintro ⟨φ, ⟨k, -, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      exact ⟨i, (ggQ2xT_simpleRefl_eq D e τ ε hε hcor hroot i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨D.simpleRefl (e i), ⟨e i, trivial, rfl⟩,
        ggQ2xT_simpleRefl_eq D e τ ε hε hcor hroot i⟩
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, MonoidHom.map_closure, hset,
    ggQ2x_SimpleGp_eq_closure_range_rS]

private theorem ggQ2x_map_parab {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (S : Set D.ι) :
    Subgroup.map (ggQ2x_Tm D τ) (D.parab S) = Subgroup.closure (rS '' (e ⁻¹' S)) := by
  have hset : (ggQ2x_Tm D τ) '' (D.simpleRefl '' S) = rS '' (e ⁻¹' S) := by
    ext g
    constructor
    · rintro ⟨φ, ⟨k, hkS, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      exact ⟨i, hkS, (ggQ2xT_simpleRefl_eq D e τ ε hε hcor hroot i).symm⟩
    · rintro ⟨i, hiS, rfl⟩
      exact ⟨D.simpleRefl (e i), ⟨e i, hiS, rfl⟩,
        ggQ2xT_simpleRefl_eq D e τ ε hε hcor hroot i⟩
  rw [GGQ2Lin.parab, MonoidHom.map_closure, hset]

private lemma ggQ2x_B_apply (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i:ℕ) = n-1 ∧ (j:ℕ) = n-2) ∨ ((j:ℕ) = n-1 ∧ (i:ℕ) = n-2) then 4
        else if ((j:ℕ)+1 = (i:ℕ)) ∨ ((i:ℕ)+1 = (j:ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]

private lemma ggQ2x_cartan_ne_of_coxeter_ne_two {Γ : Type*} {M : CoxeterMatrix Γ}
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) {i j : Γ} (hij : i ≠ j) (h : M i j ≠ 2) :
    C i j ≠ 0 := by
  rcases hC.2 i j hij with ⟨hm, h1, _⟩ | ⟨hm, h1, _⟩ | ⟨hm, _, h1, _⟩ | ⟨hm, _, h1, _⟩
  · exact absurd hm h
  · rw [h1]; decide
  · exact ne_of_lt h1
  · exact ne_of_lt h1

private lemma ggQ2x_B_succ_ne_two {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (h : (i:ℕ)+1 < n) :
    (CoxeterMatrix.B n) i (⟨(i:ℕ)+1, h⟩ : Fin n) ≠ 2 := by
  rw [ggQ2x_B_apply]
  have hne : i ≠ (⟨(i:ℕ)+1, h⟩ : Fin n) := by
    intro hh; have h' := congrArg Fin.val hh; change (i:ℕ) = (i:ℕ)+1 at h'; omega
  rw [if_neg hne]
  by_cases hd : ((i:ℕ) = n-1 ∧ ((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ) = n-2) ∨
      (((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ) = n-1 ∧ (i:ℕ) = n-2)
  · rw [if_pos hd]; decide
  · rw [if_neg hd]
    by_cases ha : (((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ)+1 = (i:ℕ)) ∨
        ((i:ℕ)+1 = ((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ))
    · rw [if_pos ha]; decide
    · exfalso
      apply ha; right
      simp only [Fin.val_mk]

private lemma ggQ2x_B_pred_ne_two {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (h : 0 < (i:ℕ)) :
    (CoxeterMatrix.B n) i (⟨(i:ℕ)-1, by omega⟩ : Fin n) ≠ 2 := by
  rw [ggQ2x_B_apply]
  have hne : i ≠ (⟨(i:ℕ)-1, by omega⟩ : Fin n) := by
    intro hh; have h' := congrArg Fin.val hh; change (i:ℕ) = (i:ℕ)-1 at h'; omega
  rw [if_neg hne]
  by_cases hd : ((i:ℕ) = n-1 ∧ ((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ) = n-2) ∨
      (((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ) = n-1 ∧ (i:ℕ) = n-2)
  · rw [if_pos hd]; decide
  · rw [if_neg hd]
    by_cases ha : (((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ)+1 = (i:ℕ)) ∨
        ((i:ℕ)+1 = ((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ))
    · rw [if_pos ha]; decide
    · exfalso
      apply ha; left
      simp only [Fin.val_mk]
      omega

private lemma ggQ2x_sum_sub_single {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ∑ i, ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n)) i = 0 := by
  have ha : ∑ i, (Pi.single a (1:ZMod 3) : GGBCV n) i = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Pi.single_eq_of_ne hc]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hb : ∑ i, (Pi.single b (1:ZMod 3) : GGBCV n) i = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [Pi.single_eq_of_ne hc]
    · intro h; exact absurd (Finset.mem_univ b) h
  have hsum : (∑ i,
        ((Pi.single a (1:ZMod 3) : GGBCV n) - (Pi.single b (1:ZMod 3) : GGBCV n)) i)
      = (∑ i, (Pi.single a (1:ZMod 3) : GGBCV n) i) -
        (∑ i, (Pi.single b (1:ZMod 3) : GGBCV n) i) :=
    Finset.sum_sub_distrib (s := Finset.univ) _ _
  rw [hsum, ha, hb]; ring

private lemma ggQ2x_neg_eq_self_zero (x : ZMod 3) (h : -x = x) : x = 0 := by
  revert x; decide +kernel

private theorem ggQ2x_leaf {n : ℕ} [NeZero n] (hn : 5 ≤ n) (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) :
    D.a = e 0 ∨ D.a = e ⟨n - 1, by omega⟩ := by
  have hn3 : 3 ≤ n := by omega
  let k : Fin n := e.symm D.a
  have hk : e k = D.a := e.apply_symm_apply D.a
  have hcoe : ∀ j : Fin n, D.coxeter (e k) (e j) = (CoxeterMatrix.B n) k j := by
    intro j
    rw [hB, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hk0 : (k:ℕ) = 0
  · left
    rw [← hk]; congr 1; exact Fin.ext hk0
  · right
    have hkpos : 0 < (k:ℕ) := by omega
    have hklast : (k:ℕ) = n - 1 := by
      by_contra hne
      have hklt' : (k:ℕ) < n - 1 := by have := k.isLt; omega
      obtain ⟨c0, -, huniq⟩ := D.a_leaf
      let j1 : Fin n := ⟨(k:ℕ)-1, by omega⟩
      let j2 : Fin n := ⟨(k:ℕ)+1, by omega⟩
      have hj1k : j1 ≠ k := by
        intro hh; have h := congrArg Fin.val hh; change (k:ℕ)-1 = (k:ℕ) at h; omega
      have hj2k : j2 ≠ k := by
        intro hh; have h := congrArg Fin.val hh; change (k:ℕ)+1 = (k:ℕ) at h; omega
      have hcart1 : D.cartan (e k) (e j1) ≠ 0 := by
        apply ggQ2x_cartan_ne_of_coxeter_ne_two D.isCartan
        · intro hh; exact hj1k (e.injective hh).symm
        · rw [hcoe j1]; exact ggQ2x_B_pred_ne_two hn3 k hkpos
      have hcart2 : D.cartan (e k) (e j2) ≠ 0 := by
        apply ggQ2x_cartan_ne_of_coxeter_ne_two D.isCartan
        · intro hh; exact hj2k (e.injective hh).symm
        · rw [hcoe j2]; exact ggQ2x_B_succ_ne_two hn3 k (by omega)
      have hcart1' : D.cartan D.a (e j1) ≠ 0 := by rwa [hk] at hcart1
      have hcart2' : D.cartan D.a (e j2) ≠ 0 := by rwa [hk] at hcart2
      have hne1 : e j1 ≠ D.a := by
        intro hh; exact hj1k (e.injective (hh.trans hk.symm))
      have hne2 : e j2 ≠ D.a := by
        intro hh; exact hj2k (e.injective (hh.trans hk.symm))
      have hu1 : e j1 = c0 := huniq (e j1) ⟨hne1, hcart1'⟩
      have hu2 : e j2 = c0 := huniq (e j2) ⟨hne2, hcart2'⟩
      have hjj : j1 = j2 := e.injective (hu1.trans hu2.symm)
      have hval : (j1:ℕ) = (j2:ℕ) := congrArg Fin.val hjj
      change (k:ℕ)-1 = (k:ℕ)+1 at hval
      omega
    rw [← hk]; congr 1; exact Fin.ext hklast

private theorem ggQ2x_fixed_lam1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (v : GGBCV n) :
    (∀ g ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)), g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {(Pi.single 0 (1:ZMod 3) : GGBCV n)} := by
  constructor
  · intro hv
    have hsingle_mem : ∀ j : Fin n, j ≠ 0 →
        (Pi.single j (1:ZMod 3) : GGBCV n) ∈ ggBCRootsLam1 n := by
      intro j hj
      refine ⟨?_, ?_⟩
      · rw [ggBCRoots, Set.mem_setOf_eq, ggQ2x_Wt_single j 1 one_ne_zero]
        omega
      · rw [Pi.single_eq_of_ne (Ne.symm hj)]
    have hzero : ∀ j : Fin n, j ≠ 0 → v j = 0 := by
      intro j hj
      have hmem : negLin j ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) := by
        apply Subgroup.subset_closure
        exact ⟨Pi.single j (1:ZMod 3), hsingle_mem j hj, hc_single j, rfl⟩
      have hfixv := hv (negLin j) hmem
      have hval := congrArg (fun w : GGBCV n => w j) hfixv
      rw [negLin_apply, if_pos rfl] at hval
      exact ggQ2x_neg_eq_self_zero (v j) hval
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · rw [hzero i hi]
      simp [Pi.single_eq_of_ne hi]
  · rintro hvsp
    rw [Submodule.mem_span_singleton] at hvsp
    obtain ⟨a, rfl⟩ := hvsp
    have hbase : ∀ t ∈ ggBCReflSet (ggBCRootsLam1 n),
        t (Pi.single 0 (1:ZMod 3) : GGBCV n) = Pi.single 0 (1:ZMod 3) := by
      rintro t ⟨c, hcroot, hc, rfl⟩
      rw [ggQ2x_refl_apply]
      have hc0 : c 0 = 0 := hcroot.2
      have hdot : c ⬝ᵥ (Pi.single 0 (1:ZMod 3) : GGBCV n) = 0 := by
        rw [dotProduct_single, hc0, mul_one]
      rw [hdot, mul_zero, zero_smul, add_zero]
    have hfix : ∀ g ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)),
        g (Pi.single 0 (1:ZMod 3) : GGBCV n) = Pi.single 0 (1:ZMod 3) := by
      intro g hg
      refine Subgroup.closure_induction (fun x hx => hbase x hx) ?_ ?_ ?_ hg
      · rfl
      · intro x y hx hy ihx ihy
        rw [LinearEquiv.mul_apply, ihy, ihx]
      · intro x hx ihx
        change x.symm (Pi.single 0 (1:ZMod 3) : GGBCV n) = Pi.single 0 (1:ZMod 3)
        have h := congrArg (fun w => x.symm w) ihx
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm
    intro g hg
    rw [map_smul, hfix g hg]

private theorem ggQ2x_fixed_lamN {n : ℕ} (hn : 5 ≤ n) (v : GGBCV n) :
    (∀ g ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)), g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {(fun _ : Fin n => (1:ZMod 3))} := by
  haveI : NeZero n := ⟨by omega⟩
  constructor
  · intro hv
    have hdiff_mem : ∀ a b : Fin n, a ≠ b →
        ((Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1) ∈ ggBCRootsLamN n := by
      intro a b hab
      rw [ggBCRootsLamN, Set.mem_setOf_eq]
      exact ⟨ggQ2x_Wt_sub_single a b hab, ggQ2x_sum_sub_single a b hab⟩
    have hconst : ∀ a b : Fin n, v a = v b := by
      intro a b
      by_cases hab : a = b
      · subst hab; rfl
      · have hmem : P (Equiv.swap a b) ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) := by
          apply Subgroup.subset_closure
          exact ⟨(Pi.single a (1:ZMod 3) : GGBCV n) - Pi.single b 1, hdiff_mem a b hab,
            hc_sub a b hab, (refl_sub_single a b hab).symm⟩
        have hfixv := hv (P (Equiv.swap a b)) hmem
        have hval := congrArg (fun w : GGBCV n => w a) hfixv
        rw [P_swap_apply] at hval
        simpa [Equiv.swap_apply_left] using hval.symm
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0, ?_⟩
    funext i
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact hconst 0 i
  · rintro hvsp
    rw [Submodule.mem_span_singleton] at hvsp
    obtain ⟨a, rfl⟩ := hvsp
    have hbase : ∀ t ∈ ggBCReflSet (ggBCRootsLamN n),
        t (fun _ : Fin n => (1:ZMod 3)) = (fun _ : Fin n => (1:ZMod 3)) := by
      rintro t ⟨c, hcroot, hc, rfl⟩
      rw [ggQ2x_refl_apply]
      have hcsum : ∑ i, c i = 0 := hcroot.2
      have hdot : c ⬝ᵥ (fun _ : Fin n => (1:ZMod 3)) = 0 := by
        rw [show c ⬝ᵥ (fun _ : Fin n => (1:ZMod 3)) = ∑ i, c i by
          simp only [dotProduct, Pi.one_apply, mul_one]]
        exact hcsum
      rw [hdot, mul_zero, zero_smul, add_zero]
    have hfix : ∀ g ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)),
        g (fun _ : Fin n => (1:ZMod 3)) = (fun _ : Fin n => (1:ZMod 3)) := by
      intro g hg
      refine Subgroup.closure_induction (fun x hx => hbase x hx) ?_ ?_ ?_ hg
      · rfl
      · intro x y hx hy ihx ihy
        rw [LinearEquiv.mul_apply, ihy, ihx]
      · intro x hx ihx
        change x.symm (fun _ : Fin n => (1:ZMod 3)) = (fun _ : Fin n => (1:ZMod 3))
        have h := congrArg (fun w => x.symm w) ihx
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm
    intro g hg
    rw [map_smul, hfix g hg]

private lemma ggQ2xF_simplePair_mem (D : GGQ2Lin 3) (k : D.ι) :
    (D.root k, D.coroot k) ∈ D.rootPairs :=
  ⟨k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2xF_rootFun_eq_coroot {n : ℕ} (i : Fin n) (h : (i:ℕ)+1 < n) (ε : ZMod 3) :
    ggBCRootFun n ε i = ggBCCoroot n ε i := by
  funext j
  simp only [ggBCRootFun, ggBCCoroot, if_pos h]

private lemma ggQ2xF_rootFun_last {n : ℕ} (i : Fin n) (h : ¬ (i:ℕ)+1 < n) (ε : ZMod 3) :
    ggBCRootFun n ε i = (Pi.single i (2/ε) : GGBCV n) := by
  funext j
  rw [ggBCRootFun, if_neg h]
  by_cases hj : (j:ℕ)+1 = n
  · rw [if_pos hj]
    have hji : j = i := by apply Fin.ext; omega
    subst hji
    rw [Pi.single_eq_same]
  · rw [if_neg hj, Pi.single_eq_of_ne]
    intro hh
    exact hj (by rw [hh]; omega)

private lemma ggQ2xF_pairing {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j) :
    ∀ i j, ggBCRootFun n ε i ⬝ᵥ ggBCCoroot n ε j = (D.cartan (e i) (e j) : ZMod 3) := by
  intro i j
  have h := hroot i (D.coroot (e j))
  rw [hcor j, D.pairing (e i) (e j)] at h
  simp only [dotProduct]
  rw [← h]

private lemma ggQ2xF_dot_chain {n : ℕ} (k : Fin n) (h : (k:ℕ)+2 < n) (ε : ZMod 3) :
    ggBCRootFun n ε k ⬝ᵥ ggBCCoroot n ε (⟨(k:ℕ)+1, by omega⟩ : Fin n) = -1 := by
  have hk1 : (k:ℕ)+1 < n := by omega
  have hne1 : k ≠ (⟨(k:ℕ)+1, hk1⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hne2 : k ≠ (⟨(k:ℕ)+2, h⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hne3 : (⟨(k:ℕ)+1, hk1⟩ : Fin n) ≠ (⟨(k:ℕ)+2, h⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  rw [ggQ2xF_rootFun_eq_coroot k hk1 ε, coroot_chain k hk1 ε,
    coroot_chain (⟨(k:ℕ)+1, by omega⟩ : Fin n) h ε, dot_sub_single]
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2,
    Pi.single_eq_of_ne hne3]
  decide

private lemma ggQ2xF_dot_chain' {n : ℕ} (k : Fin n) (h : (k:ℕ)+2 < n) (ε : ZMod 3) :
    ggBCRootFun n ε (⟨(k:ℕ)+1, by omega⟩ : Fin n) ⬝ᵥ ggBCCoroot n ε k = -1 := by
  have hc := ggQ2xF_dot_chain k h ε
  rw [ggQ2xF_rootFun_eq_coroot k (by omega : (k:ℕ)+1 < n) ε] at hc
  rw [ggQ2xF_rootFun_eq_coroot (⟨(k:ℕ)+1, by omega⟩ : Fin n) h ε, dotProduct_comm]
  exact hc

private lemma ggQ2xF_dot_last {n : ℕ} (hn : 5 ≤ n) (ε : ZMod 3) :
    ggBCRootFun n ε (⟨n-2, by omega⟩ : Fin n) ⬝ᵥ
      ggBCCoroot n ε (⟨n-1, by omega⟩ : Fin n) = -ε := by
  have h1 : ((⟨n-2, by omega⟩ : Fin n):ℕ)+1 < n := by simp only [Fin.val_mk]; omega
  have h2 : ¬ ((⟨n-1, by omega⟩ : Fin n):ℕ)+1 < n := by simp only [Fin.val_mk]; omega
  have hne : (⟨n-2, by omega⟩ : Fin n) ≠ (⟨n-1, by omega⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hpos : (⟨((⟨n-2, by omega⟩ : Fin n):ℕ)+1, h1⟩ : Fin n) =
      (⟨n-1, by omega⟩ : Fin n) := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [ggQ2xF_rootFun_eq_coroot (⟨n-2, by omega⟩ : Fin n) h1 ε,
    coroot_chain (⟨n-2, by omega⟩ : Fin n) h1 ε,
    coroot_last (⟨n-1, by omega⟩ : Fin n) h2 ε, dot_sub_single]
  rw [Pi.single_eq_of_ne hne, hpos, Pi.single_eq_same, zero_sub]
  rfl

private lemma ggQ2xF_dot_last' {n : ℕ} (hn : 5 ≤ n) (ε : ZMod 3) :
    ggBCRootFun n ε (⟨n-1, by omega⟩ : Fin n) ⬝ᵥ
      ggBCCoroot n ε (⟨n-2, by omega⟩ : Fin n) = -(2/ε) := by
  have h1 : ((⟨n-2, by omega⟩ : Fin n):ℕ)+1 < n := by simp only [Fin.val_mk]; omega
  have h2 : ¬ ((⟨n-1, by omega⟩ : Fin n):ℕ)+1 < n := by simp only [Fin.val_mk]; omega
  have hne : (⟨n-2, by omega⟩ : Fin n) ≠ (⟨n-1, by omega⟩ : Fin n) := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hpos : (⟨((⟨n-2, by omega⟩ : Fin n):ℕ)+1, h1⟩ : Fin n) =
      (⟨n-1, by omega⟩ : Fin n) := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [ggQ2xF_rootFun_last (⟨n-1, by omega⟩ : Fin n) h2 ε,
    coroot_chain (⟨n-2, by omega⟩ : Fin n) h1 ε, dotProduct_sub, dotProduct_single,
    dotProduct_single]
  rw [Pi.single_eq_of_ne hne, hpos, Pi.single_eq_same]
  simp only [zero_mul, mul_one, zero_sub]
  rfl

private lemma ggQ2xF_mul_neg_eq (a b : ZMod 3) : a * (-b) = (-a) * b := by
  revert a b; decide +kernel

private lemma ggQ2xF_scalar_last (l x ε : ZMod 3) : (-l) * ((2/ε) * x) = l * (ε * x) := by
  revert l x ε; decide +kernel

private lemma ggQ2xF_neg_two_div (ε : ZMod 3) : -(2/ε) = ε := by
  revert ε; decide +kernel

private theorem ggQ2x_form_eq {n : ℕ} (hn : 5 ≤ n) (D : GGQ2Lin 3) (hbas : D.Basis)
    (e : Fin n ≃ D.ι) (τ : D.V ≃ₗ[ZMod 3] GGBCV n)
    (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (β : LinearMap.BilinForm (ZMod 3) D.V) (hβ : β.IsSymm)
    (d : ↥D.rootPairs → ZMod 3) (hd : ∀ γ, d γ ≠ 0)
    (hβh : ∀ γ v, β γ.1.2 v = d γ * γ.1.1 v) :
    ∃ lam : ZMod 3, lam ≠ 0 ∧ ∀ u v : GGBCV n, β (τ.symm u) (τ.symm v) = lam * (u ⬝ᵥ v) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let pair : Fin n → ↥D.rootPairs :=
    fun i => ⟨(D.root (e i), D.coroot (e i)), ggQ2xF_simplePair_mem D (e i)⟩
  let di : Fin n → ZMod 3 := fun i => d (pair i)
  have hdi_ne : ∀ i, di i ≠ 0 := fun i => hd (pair i)
  have hβhi : ∀ i v, β (D.coroot (e i)) v = di i * D.root (e i) v :=
    fun i v => hβh (pair i) v
  have hpair := ggQ2xF_pairing D e τ ε hcor hroot
  have hsym : ∀ i j, di i * (D.cartan (e i) (e j) : ZMod 3) =
      di j * (D.cartan (e j) (e i) : ZMod 3) := by
    intro i j
    have h1 : β (D.coroot (e i)) (D.coroot (e j)) =
        di i * (D.cartan (e i) (e j) : ZMod 3) := by
      rw [hβhi i (D.coroot (e j)), D.pairing]
    have h2 : β (D.coroot (e i)) (D.coroot (e j)) = β (D.coroot (e j)) (D.coroot (e i)) :=
      hβ.eq _ _
    have h3 : β (D.coroot (e j)) (D.coroot (e i)) =
        di j * (D.cartan (e j) (e i) : ZMod 3) := by
      rw [hβhi j (D.coroot (e i)), D.pairing]
    rw [← h1, h2, h3]
  have hstep : ∀ (k : Fin n) (hk : (k:ℕ)+2 < n),
      di k = di (⟨(k:ℕ)+1, by omega⟩ : Fin n) := by
    intro k hk
    have hC := hsym k (⟨(k:ℕ)+1, by omega⟩ : Fin n)
    rw [← hpair k (⟨(k:ℕ)+1, by omega⟩ : Fin n),
      ← hpair (⟨(k:ℕ)+1, by omega⟩ : Fin n) k,
      ggQ2xF_dot_chain k hk ε, ggQ2xF_dot_chain' k hk ε] at hC
    exact mul_right_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0) hC
  let lam : ZMod 3 := di ⟨0, by omega⟩
  let Dd : ℕ → ZMod 3 := fun k => if hk : k < n then di ⟨k, hk⟩ else 0
  have hDd0 : Dd 0 = lam := by
    simp only [Dd, dif_pos (show (0:ℕ) < n by omega)]
    rfl
  have hDdstep : ∀ k, k+2 < n → Dd k = Dd (k+1) := by
    intro k hk
    have hk1 : k < n := by omega
    have hk2 : k+1 < n := by omega
    simp only [Dd, dif_pos hk1, dif_pos hk2]
    exact hstep ⟨k, hk1⟩ hk
  have hDd_chain : ∀ k, k+1 < n → Dd k = lam := by
    intro k
    induction k with
    | zero => intro _; exact hDd0
    | succ k ih =>
        intro hk
        have hk' : k+2 < n := by omega
        rw [← hDdstep k hk']
        exact ih (by omega)
  have hdi_chain : ∀ i : Fin n, (i:ℕ)+1 < n → di i = lam := by
    intro i hi
    have h1 := hDd_chain i.val hi
    have h2 : Dd i.val = di i := by simp only [Dd, dif_pos i.isLt]
    rwa [h2] at h1
  have hlast : di (⟨n-1, by omega⟩ : Fin n) = -lam := by
    have hC := hsym (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n)
    rw [← hpair (⟨n-2, by omega⟩ : Fin n) (⟨n-1, by omega⟩ : Fin n),
      ← hpair (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n),
      ggQ2xF_dot_last hn ε, ggQ2xF_dot_last' hn ε] at hC
    have h2 : ((⟨n-2, by omega⟩ : Fin n):ℕ)+1 < n := by simp only [Fin.val_mk]; omega
    rw [hdi_chain (⟨n-2, by omega⟩ : Fin n) h2] at hC
    have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> decide
    rw [ggQ2xF_neg_two_div ε, ggQ2xF_mul_neg_eq lam ε] at hC
    exact (mul_right_cancel₀ hε0 hC).symm
  have hli_cor : LinearIndependent (ZMod 3) (fun i : Fin n => D.coroot (e i)) :=
    hbas.1.comp e e.injective
  have hli : LinearIndependent (ZMod 3) (ggBCCoroot n ε) := by
    have hfun : (fun i : Fin n => τ (D.coroot (e i))) = ggBCCoroot n ε := by
      funext i; exact hcor i
    rw [← hfun]
    exact hli_cor.map' (τ : D.V →ₗ[ZMod 3] GGBCV n) (LinearEquiv.ker τ)
  have hcard : Fintype.card (Fin n) = finrank (ZMod 3) (GGBCV n) := by
    change Fintype.card (Fin n) = finrank (ZMod 3) (Fin n → ZMod 3)
    rw [Module.finrank_pi]
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let bu : Basis (Fin n) (ZMod 3) (GGBCV n) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbu : ⇑bu = ggBCCoroot n ε := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨lam, hdi_ne ⟨0, by omega⟩, ?_⟩
  intro u v
  have hkey : ∀ i : Fin n,
      β (τ.symm v) (τ.symm (ggBCCoroot n ε i)) = lam * (ggBCCoroot n ε i ⬝ᵥ v) := by
    intro i
    rw [hβ.eq (τ.symm v) (τ.symm (ggBCCoroot n ε i))]
    have hτ : τ.symm (ggBCCoroot n ε i) = D.coroot (e i) := by
      rw [← hcor i, LinearEquiv.symm_apply_apply]
    have hrootv : D.root (e i) (τ.symm v) = ggBCRootFun n ε i ⬝ᵥ v := by
      rw [hroot i (τ.symm v)]
      simp only [LinearEquiv.apply_symm_apply]
      rfl
    rw [hτ, hβhi i (τ.symm v), hrootv]
    by_cases hi : (i:ℕ)+1 < n
    · rw [ggQ2xF_rootFun_eq_coroot i hi ε, hdi_chain i hi]
    · have hilast : i = (⟨n-1, by omega⟩ : Fin n) := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      have hi' : ¬ ((⟨n-1, by omega⟩ : Fin n):ℕ)+1 < n := by
        rw [← hilast]; exact hi
      rw [hilast]
      rw [ggQ2xF_rootFun_last _ hi' ε, coroot_last _ hi' ε, hlast, dot_single, dot_single]
      exact ggQ2xF_scalar_last lam (v (⟨n-1, by omega⟩ : Fin n)) ε
  let Fv : GGBCV n →ₗ[ZMod 3] ZMod 3 :=
    (β (τ.symm v)).comp (τ.symm : GGBCV n →ₗ[ZMod 3] D.V)
  let Gv : GGBCV n →ₗ[ZMod 3] ZMod 3 := lam • ggBCDot v
  have hGv : ∀ u, Gv u = lam * (u ⬝ᵥ v) := by
    intro u
    change (lam • ggBCDot v) u = lam * (u ⬝ᵥ v)
    rw [LinearMap.smul_apply, smul_eq_mul, ggBCDot_apply, dotProduct_comm]
  have hFG : Fv = Gv := by
    apply Basis.ext bu
    intro i
    rw [congrFun hbu i]
    change β (τ.symm v) (τ.symm (ggBCCoroot n ε i)) = Gv (ggBCCoroot n ε i)
    rw [hGv (ggBCCoroot n ε i), hkey i]
  calc β (τ.symm u) (τ.symm v) = β (τ.symm v) (τ.symm u) := hβ.eq _ _
    _ = Fv u := rfl
    _ = Gv u := by rw [hFG]
    _ = lam * (u ⬝ᵥ v) := hGv u

private theorem ggQ2x_S1 {n : ℕ} (hn : 5 ≤ n) (D : GGQ2Lin 3) (hbas : D.Basis)
    (e : Fin n ≃ D.ι) (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (h4 : 4 ≤ Fintype.card D.ι)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ (c : GGBCV n) (φ : Module.Dual (ZMod 3) (GGBCV n)) (h : φ c = 2),
      Module.reflection h ∈ Subgroup.map (ggQ2x_Tm D τ) A → ∃ ε' : ZMod 3,
        (ε' = 1 ∨ ε' = -1) ∧ ∀ v, φ v = ε' * (c ⬝ᵥ v) := by
  intro cc φ h ht
  obtain ⟨β, d, hβ, hd, hβh⟩ := ggQ2_exists_invariantForm (p := 3) rfl D hbas h4
  obtain ⟨lam, hlam_ne, hlam⟩ :=
    ggQ2x_form_eq hn D hbas e τ ε hε hcor hroot β hβ d hd hβh
  obtain ⟨g, hgA, hg_eq⟩ := Subgroup.mem_map.mp ht
  let h' : Module.Dual (ZMod 3) D.V := φ.comp (τ : D.V →ₗ[ZMod 3] GGBCV n)
  have hh' : h' (τ.symm cc) = 2 := by
    change φ (τ (τ.symm cc)) = 2
    rw [LinearEquiv.apply_symm_apply]
    exact h
  have hg_refl : g = Module.reflection hh' := by
    ext w
    apply τ.injective
    have h1 : τ (g w) = Module.reflection h (τ w) := by
      have hh : (ggQ2x_Tm D τ g) (τ w) = (Module.reflection h) (τ w) :=
        DFunLike.congr_fun hg_eq (τ w)
      simpa [ggQ2x_Tm, ggQ2x_T, LinearEquiv.trans_apply] using hh
    rw [h1, Module.reflection_apply (τ w) h, Module.reflection_apply w hh',
      map_sub, map_smul, LinearEquiv.apply_symm_apply]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    rfl
  have hgA' : Module.reflection hh' ∈ A := by rw [← hg_refl]; exact hgA
  obtain ⟨ε'', hε'', hφ''⟩ :=
    ggQ2_refl_orthogonal (p := 3) rfl D hbas h4 β hβ d hd hβh A hW hTF
      (c := τ.symm cc) (φ := h') hh' hgA'
  refine ⟨ε'' * lam, ?_, ?_⟩
  · rcases hε'' with h1 | h1 <;> rcases ggQ2x_eq_one_or_neg_one lam hlam_ne with h2 | h2 <;>
      rw [h1, h2] <;> decide +kernel
  · intro v
    have h1 := hφ'' (τ.symm v)
    have h2 : h' (τ.symm v) = φ v := by
      change φ (τ (τ.symm v)) = φ v
      rw [LinearEquiv.apply_symm_apply]
    rw [h2, hlam cc v] at h1
    rw [h1, mul_assoc]

private lemma ggQ2xH_T_apply {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n)
    (g : D.V ≃ₗ[ZMod 3] D.V) (v : GGBCV n) :
    ggQ2x_Tm D τ g v = τ (g (τ.symm v)) := by
  rfl

private theorem ggQ2xH_HL_transport {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (f0 : GGBCV n) (C : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hP : Subgroup.map (ggQ2x_Tm D τ) (D.parab {k | k ≠ D.a}) = C)
    (hfix : ∀ v : GGBCV n, (∀ g ∈ C, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {f0}) :
    ∀ φ ∈ Subgroup.map (ggQ2x_Tm D τ) A,
      φ f0 ∈ Submodule.span (ZMod 3) {f0} →
      φ ∈ Subgroup.normalizer (C : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
  intro φ hφ hφf
  obtain ⟨φ', hφ'A, hφ'eq⟩ := Subgroup.mem_map.mp hφ
  have hxmem : x ∈ Submodule.span (ZMod 3) {x} := Submodule.mem_span_singleton_self x
  have hfixP : ∀ g ∈ D.parab {k | k ≠ D.a}, g x = x := (hx x).mpr hxmem
  have hτx : τ x ∈ Submodule.span (ZMod 3) {f0} := by
    rw [← hfix (τ x)]
    intro g hg
    rw [← hP] at hg
    obtain ⟨g', hg'P, rfl⟩ := Subgroup.mem_map.mp hg
    rw [ggQ2xH_T_apply, LinearEquiv.symm_apply_apply, hfixP g' hg'P]
  have hf0fixC : ∀ g ∈ C, g f0 = f0 :=
    (hfix f0).mpr (Submodule.mem_span_singleton_self f0)
  have hfixP' : ∀ g ∈ D.parab {k | k ≠ D.a}, g (τ.symm f0) = τ.symm f0 := by
    intro g hg
    have hmemC : ggQ2x_Tm D τ g ∈ C := by
      rw [← hP]
      exact Subgroup.mem_map_of_mem (ggQ2x_Tm D τ) hg
    have h := hf0fixC (ggQ2x_Tm D τ g) hmemC
    rw [ggQ2xH_T_apply] at h
    exact τ.injective (h.trans (LinearEquiv.apply_symm_apply τ f0).symm)
  have hτsymm : τ.symm f0 ∈ Submodule.span (ZMod 3) {x} :=
    (hx (τ.symm f0)).mp hfixP'
  have hf0_span : f0 ∈ Submodule.span (ZMod 3) {τ x} := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hτsymm
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    have h := congrArg τ ha
    rw [map_smul, LinearEquiv.apply_symm_apply] at h
    exact h
  have hspan : Submodule.span (ZMod 3) {τ x} = Submodule.span (ZMod 3) {f0} :=
    le_antisymm (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hτx))
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hf0_span))
  have hφf' : φ f0 ∈ Submodule.span (ZMod 3) {τ x} := by rw [hspan]; exact hφf
  have hτφx : φ (τ x) ∈ Submodule.span (ZMod 3) {τ x} := by
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hτx
    have hd' : φ (τ x) = d • φ f0 := by rw [← hd, map_smul]
    rw [hd']
    exact Submodule.smul_mem _ d hφf'
  have hτφ'x : τ (φ' x) = φ (τ x) := by
    have h1 : ggQ2x_Tm D τ φ' (τ x) = τ (φ' x) := by
      rw [ggQ2xH_T_apply, LinearEquiv.symm_apply_apply]
    rw [hφ'eq] at h1
    exact h1.symm
  have hmapspan : Submodule.map (τ : D.V →ₗ[ZMod 3] GGBCV n)
      (Submodule.span (ZMod 3) {x}) = Submodule.span (ZMod 3) {τ x} := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have hx' : φ' x ∈ Submodule.span (ZMod 3) {x} := by
    have hmem : τ (φ' x) ∈ Submodule.map (τ : D.V →ₗ[ZMod 3] GGBCV n)
        (Submodule.span (ZMod 3) {x}) := by
      rw [hmapspan, hτφ'x]
      exact hτφx
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.mp hmem
    have hy' : y = φ' x := τ.injective hyeq
    rw [hy'] at hy
    exact hy
  have hnorm' : φ' ∈ Subgroup.normalizer
      (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)) := hHL φ' hφ'A hx'
  have hmem : φ ∈ Subgroup.normalizer (C : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
    have hthis : ggQ2x_Tm D τ φ' ∈ Subgroup.map (ggQ2x_Tm D τ)
        (Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :=
      Subgroup.mem_map_of_mem (ggQ2x_Tm D τ) hnorm'
    rw [hφ'eq] at hthis
    rw [show ggQ2x_Tm D τ = (ggQ2x_T D τ).toMonoidHom from rfl] at hthis
    rw [Subgroup.map_equiv_normalizer_eq] at hthis
    rw [show Subgroup.map (ggQ2x_T D τ).toMonoidHom (D.parab {k | k ≠ D.a}) = C from hP]
      at hthis
    exact hthis
  exact hmem

private theorem ggQ2x_HL_a1 {n : ℕ} [NeZero n] (hn : 5 ≤ n) (D : GGQ2Lin 3) (hbas : D.Basis)
    (e : Fin n ≃ D.ι) (hB : D.coxeter = (CoxeterMatrix.B n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (x : D.V) (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {x})
    (ha : D.a = e 0)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hHL : ∀ φ ∈ A,
      φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ Subgroup.map (ggQ2x_Tm D τ) A,
      φ (Pi.single 0 (1:ZMod 3)) ∈ Submodule.span (ZMod 3) {(Pi.single 0 (1:ZMod 3) : GGBCV n)} →
      φ ∈ Subgroup.normalizer
        (Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) :
          Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
  have hP : Subgroup.map (ggQ2x_Tm D τ) (D.parab {k | k ≠ D.a}) =
      Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) := by
    rw [ggQ2x_map_parab D e τ ε hε hcor hroot {k | k ≠ D.a}]
    have hpre : e ⁻¹' {k : D.ι | k ≠ D.a} = {i : Fin n | i ≠ 0} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [ha]
      exact ⟨fun h hi => h (by rw [hi]), fun hi hei => hi (e.injective hei)⟩
    rw [hpre, ggQ2x_parab_lam1 hn]
  exact ggQ2xH_HL_transport D τ x hx A hHL (Pi.single 0 (1:ZMod 3))
    (Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n))) hP (ggQ2x_fixed_lam1 hn)

private theorem ggQ2x_HL_aN {n : ℕ} (hn : 5 ≤ n) (D : GGQ2Lin 3) (hbas : D.Basis)
    (e : Fin n ≃ D.ι) (hB : D.coxeter = (CoxeterMatrix.B n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV n) (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggBCCoroot n ε i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggBCRootFun n ε i j * τ v j)
    (x : D.V) (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {x})
    (ha : D.a = e ⟨n - 1, by omega⟩)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hHL : ∀ φ ∈ A,
      φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ Subgroup.map (ggQ2x_Tm D τ) A,
      φ (fun _ => (1:ZMod 3)) ∈
        Submodule.span (ZMod 3) {(fun _ : Fin n => (1:ZMod 3))} →
      φ ∈ Subgroup.normalizer
        (Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) :
          Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
  have hP : Subgroup.map (ggQ2x_Tm D τ) (D.parab {k | k ≠ D.a}) =
      Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) := by
    rw [ggQ2x_map_parab D e τ ε hε hcor hroot {k | k ≠ D.a}]
    have hpre : e ⁻¹' {k : D.ι | k ≠ D.a} =
        {i : Fin n | i ≠ ⟨n - 1, by omega⟩} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [ha]
      exact ⟨fun h hi => h ((congrArg e hi).trans (congrArg e (Fin.ext rfl))),
        fun hi hei => hi ((e.injective hei).trans (Fin.ext rfl).symm)⟩
    rw [hpre, ggQ2x_parab_lamN hn]
  exact ggQ2xH_HL_transport D τ x hx A hHL (fun _ : Fin n => (1:ZMod 3))
    (Subgroup.closure (ggBCReflSet (ggBCRootsLamN n))) hP (ggQ2x_fixed_lamN hn)

private lemma ggQ2x_isTransvectionLin_conj {K V W : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (g : V ≃ₗ[K] V) :
    IsTransvectionLin (e.symm.trans (g.trans e)) ↔ IsTransvectionLin g := by
  constructor
  · rintro ⟨u, ψ, hu, hψ, hψu, hg⟩
    refine ⟨e.symm u, ψ.comp e.toLinearMap, ?_, ?_, ?_, fun v => ?_⟩
    · intro h
      exact hu (by simpa using congrArg (⇑e) h)
    · intro h
      apply hψ
      ext y
      have := congrArg (fun f : V →ₗ[K] K => f (e.symm y)) h
      simpa using this
    · simpa using hψu
    · have h := hg (e v)
      have h2 : e (g v) = e v + ψ (e v) • u := by
        simpa [LinearEquiv.trans_apply] using h
      have h3 := congrArg (⇑e.symm) h2
      simpa [map_add, map_smul, LinearMap.comp_apply] using h3
  · rintro ⟨u, ψ, hu, hψ, hψu, hg⟩
    refine ⟨e u, ψ.comp e.symm.toLinearMap, ?_, ?_, ?_, fun v => ?_⟩
    · intro h
      exact hu (by simpa using congrArg (⇑e.symm) h)
    · intro h
      apply hψ
      ext y
      have := congrArg (fun f : W →ₗ[K] K => f (e y)) h
      simpa using this
    · simpa using hψu
    · have h := hg (e.symm v)
      have h2 := congrArg (⇑e) h
      simpa [LinearEquiv.trans_apply, map_add, map_smul, LinearMap.comp_apply] using h2

private theorem ggQ2x_transvectionFree {n : ℕ} (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] GGBCV n)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hTF : TransvectionFree A) :
    TransvectionFree (Subgroup.map (ggQ2x_Tm D τ) A) := by
  intro g' hg' htv
  obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hg'
  exact hTF g hgA ((ggQ2x_isTransvectionLin_conj τ g).mp htv)

end CFSG.StandardType
namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_thmB_BC {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ D.ι) (hB : D.coxeter = (CoxeterMatrix.B n).reindex e)
    (x : D.V) (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod p) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod p] D.V))) :
    A ≤ D.weyl := by
  subst hp
  have hn1 : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  obtain ⟨τ, ε, hε, hcor, hroot⟩ := ggQ2_BC_coordinates D hbas (by omega) e hB
  let T := ggQ2x_Tm D τ
  have hmapW : Subgroup.map T D.weyl = ggQ2x_SimpleGp n := ggQ2x_map_weyl D e τ ε hε hcor hroot
  have hTF' : TransvectionFree (Subgroup.map T A) := ggQ2x_transvectionFree D τ A hTF
  have hS1 := ggQ2x_S1 hn D hbas e τ ε hε hcor hroot h4 A hW hTF
  have hW' : ggBCW n ≤ Subgroup.map T A := by
    rw [ggQ2x_W_eq_simple n hn1, ← hmapW]
    exact Subgroup.map_mono hW
  rcases ggQ2x_leaf hn D e hB with ha | ha
  · have hHL' := ggQ2x_HL_a1 hn D hbas e hB τ ε hε hcor hroot x hx ha A hHL
    have hle : Subgroup.map T A ≤ ggBCW n :=
      ggQ2_bc_A_le_W_a1 n hn (Subgroup.map T A) hW' hTF' hS1 hHL'
    have h2 : Subgroup.map T A ≤ Subgroup.map T D.weyl := by
      rw [hmapW, ← ggQ2x_W_eq_simple n hn1]
      exact hle
    exact (Subgroup.map_le_map_iff_of_injective (ggQ2x_Tm_injective D τ)).mp h2
  · have hHL' := ggQ2x_HL_aN hn D hbas e hB τ ε hε hcor hroot x hx ha A hHL
    have hle : Subgroup.map T A ≤ ggBCW n :=
      ggQ2_bc_A_le_W_aN n hn (Subgroup.map T A) hW' hTF' hS1 hHL'
    have h2 : Subgroup.map T A ≤ Subgroup.map T D.weyl := by
      rw [hmapW, ← ggQ2x_W_eq_simple n hn1]
      exact hle
    exact (Subgroup.map_le_map_iff_of_injective (ggQ2x_Tm_injective D τ)).mp h2

end CFSG.StandardType

end
