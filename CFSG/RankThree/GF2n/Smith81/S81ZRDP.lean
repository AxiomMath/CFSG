module

public import CFSG.RankThree.GF2n.Smith81.S81ZRDU
public import CFSG.RankThree.GF2n.Smith81.S81ZLinNorm

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem conj_uN_of_single (g : Gp K) (φ : NU K →ₗ[K] NU K)
    (h : ∀ (β : ↥(Phi a7)) (b : K), uN (φ (Pi.single β b)) = g * uN (Pi.single β b) * g⁻¹)
    (m : NU K) : uN (φ m) = g * uN m * g⁻¹ := by
  have hm : m = ∑ β : ↥(Phi a7), Pi.single β (m β) := (Finset.univ_sum_single m).symm
  rw [hm]
  refine Finset.sum_induction (fun β : ↥(Phi a7) => (Pi.single β (m β) : NU K))
    (fun x : NU K => uN (φ x) = g * uN x * g⁻¹) ?_ ?_ ?_
  · intro x y hx hy
    rw [map_add, uN_add, uN_add, hx, hy]
    group
  · rw [map_zero, uN_zero]
    group
  · intro β _
    exact h β (m β)

theorem pr_add (a : Fin e7Data.d) (γ δ : Rt) : pr a (γ + δ) = pr a γ + pr a δ := by
  unfold pr
  exact dotProduct_add _ _ _

theorem add_ne_zero_of_pr {γ β : Rt} (hγ : pr a7 γ = 0 ∨ pr a7 γ = 1) (hβ : β ∈ Phi a7) :
    γ + β ≠ 0 := by
  intro h
  have h1 : pr a7 (γ + β) = pr a7 (0 : Rt) := by rw [h]
  have h2 : pr a7 (0 : Rt) = 0 := by unfold pr; simp
  have h3 : pr a7 β = 1 := (mem_Phi.1 hβ).2
  rw [pr_add, h2, h3] at h1
  rcases hγ with h | h <;> omega

theorem isRoot_add_iff_mem {γ β : Rt} (hγ : pr a7 γ = 0 ∨ pr a7 γ = 1) (hβ : β ∈ Phi a7) :
    IsRoot .E7 (γ + β) ↔ γ + β ∈ Phi a7 := by
  constructor
  · intro hr
    rw [mem_Phi]
    refine ⟨hr, ?_⟩
    have h3 : pr a7 β = 1 := (mem_Phi.1 hβ).2
    rw [pr_add, h3]
    rcases pr_mem hr a7 with h | h | h <;> rw [pr_add, h3] at h <;> rcases hγ with h' | h' <;> omega
  · intro h
    exact (mem_Phi.1 h).1

open _root_.Classical in
@[expose] def shiftFun (γ : Rt) (n : NU K) (δ : ↥(Phi a7)) : K :=
  if h : δ.1 - γ ∈ Phi a7 then n ⟨δ.1 - γ, h⟩ else 0

@[expose] def shiftN (γ : Rt) : NU K →ₗ[K] NU K where
  toFun n := fun δ => shiftFun γ n δ
  map_add' n m := by
    funext δ
    unfold shiftFun
    by_cases h : δ.1 - γ ∈ Phi a7 <;> simp [h]
  map_smul' c n := by
    funext δ
    unfold shiftFun
    by_cases h : δ.1 - γ ∈ Phi a7 <;> simp [h]

theorem shiftN_apply (γ : Rt) (n : NU K) (δ : ↥(Phi a7)) :
    shiftN γ n δ = shiftFun γ n δ := by
  simp only [shiftN, LinearMap.coe_mk, AddHom.coe_mk]

open _root_.Classical in
theorem shiftN_single (γ : Rt) (β : ↥(Phi a7)) (b : K) :
    shiftN γ (Pi.single β b) =
      if h : β.1 + γ ∈ Phi a7 then Pi.single ⟨β.1 + γ, h⟩ b else 0 := by
  funext δ
  rw [shiftN_apply]
  unfold shiftFun
  have hiff : ∀ (h3 : δ.1 - γ ∈ Phi a7), (⟨δ.1 - γ, h3⟩ : ↥(Phi a7)) = β ↔ δ.1 = β.1 + γ := by
    intro h3
    rw [Subtype.ext_iff]
    exact sub_eq_iff_eq_add
  by_cases h1 : β.1 + γ ∈ Phi a7
  · rw [dif_pos h1]
    by_cases h3 : δ.1 - γ ∈ Phi a7
    · rw [dif_pos h3]
      by_cases e : δ.1 = β.1 + γ
      · have h4 : (⟨δ.1 - γ, h3⟩ : ↥(Phi a7)) = β := (hiff h3).2 e
        have h2 : δ = ⟨β.1 + γ, h1⟩ := Subtype.ext e
        rw [h4, h2]
        simp
      · have h4 : ¬ (⟨δ.1 - γ, h3⟩ : ↥(Phi a7)) = β := fun h => e ((hiff h3).1 h)
        have h5 : ¬ δ = ⟨β.1 + γ, h1⟩ := fun h => e (by rw [h])
        simp [Pi.single_apply, h4, h5]
    · rw [dif_neg h3]
      have h5 : ¬ δ = ⟨β.1 + γ, h1⟩ := by
        intro h
        apply h3
        have : δ.1 = β.1 + γ := by rw [h]
        rw [this, add_sub_cancel_right]
        exact β.2
      simp [Pi.single_apply, h5]
  · rw [dif_neg h1]
    by_cases h3 : δ.1 - γ ∈ Phi a7
    · rw [dif_pos h3]
      have h4 : ¬ (⟨δ.1 - γ, h3⟩ : ↥(Phi a7)) = β := by
        intro h
        apply h1
        have := (hiff h3).1 h
        rw [← this]
        exact δ.2
      simp [Pi.single_apply, h4]
    · rw [dif_neg h3]
      rfl

@[expose] def adjN (γ : Rt) (a : K) : NU K →ₗ[K] NU K := LinearMap.id + a • shiftN γ

theorem adjN_apply (γ : Rt) (a : K) (n : NU K) : adjN γ a n = n + a • shiftN γ n := by
  simp [adjN]

theorem xE_conj_single {γ : Rt} (hγ : IsRoot .E7 γ) (hpr : pr a7 γ = 0 ∨ pr a7 γ = 1) (a : K)
    (β : ↥(Phi a7)) (b : K) :
    uN (adjN γ a (Pi.single β b)) = xE γ a * uN (Pi.single β b) * (xE γ a)⁻¹ := by
  classical
  have hβ : β.1 ∈ Phi a7 := β.2
  have hne : γ + β.1 ≠ 0 := add_ne_zero_of_pr hpr hβ
  have hcomm := comm_xE hγ (mem_Phi.1 hβ).1 hne a b
  have hconj : xE γ a * xE β.1 b * (xE γ a)⁻¹ = ⁅xE γ a, xE β.1 b⁆ * xE β.1 b := by
    rw [commutatorElement_def]
    group
  rw [uN_single, hconj, hcomm, adjN_apply, shiftN_single, uN_add, uN_single]
  by_cases hr : IsRoot .E7 (γ + β.1)
  · have hmem : γ + β.1 ∈ Phi a7 := (isRoot_add_iff_mem hpr hβ).1 hr
    have hmem' : β.1 + γ ∈ Phi a7 := by rwa [add_comm]
    rw [if_pos hr, dif_pos hmem']
    have h1 : a • (Pi.single ⟨β.1 + γ, hmem'⟩ b : NU K) = Pi.single ⟨β.1 + γ, hmem'⟩ (a * b) := by
      funext δ
      by_cases h : δ = ⟨β.1 + γ, hmem'⟩ <;> simp [Pi.single_apply, h]
    rw [h1, uN_single, add_comm γ β.1]
    exact xE_comm_of_mem_Phi hβ hmem' b (a * b)
  · have hno : ¬ β.1 + γ ∈ Phi a7 := by
      intro h
      apply hr
      rw [add_comm]
      exact (mem_Phi.1 h).1
    rw [if_neg hr, dif_neg hno, smul_zero, uN_zero, mul_one, one_mul]

theorem xE_conj_uN {γ : Rt} (hγ : IsRoot .E7 γ) (hpr : pr a7 γ = 0 ∨ pr a7 γ = 1) (a : K)
    (m : NU K) : uN (adjN γ a m) = xE γ a * uN m * (xE γ a)⁻¹ :=
  conj_uN_of_single (xE γ a) (adjN γ a) (fun β b => xE_conj_single hγ hpr a β b) m

theorem xE_mem_linNorm {γ : Rt} (hγ : IsRoot .E7 γ) (hpr : pr a7 γ = 0 ∨ pr a7 γ = 1) (a : K) :
    xE γ a ∈ linNorm (K := K) uN uN_injective :=
  ⟨adjN γ a, xE_conj_uN hγ hpr a⟩

theorem linAd_xE {γ : Rt} (hγ : IsRoot .E7 γ) (hpr : pr a7 γ = 0 ∨ pr a7 γ = 1) (a : K)
    (n : NU K) :
    linAd (K := K) uN uN_injective ⟨xE γ a, xE_mem_linNorm hγ hpr a⟩ n = n + a • shiftN γ n := by
  rw [linAd_eq uN uN_injective (xE_mem_linNorm hγ hpr a) (xE_conj_uN hγ hpr a) n, adjN_apply]

@[expose] def diagN (j : Fin (Tag.rank .E7)) (c : Kˣ) : NU K →ₗ[K] NU K where
  toFun n := fun β => ((c ^ MinData.toWeight β.1 j : Kˣ) : K) * n β
  map_add' n m := by
    funext β
    simp [mul_add]
  map_smul' t n := by
    funext β
    simp [mul_left_comm]

theorem diagN_apply (j : Fin (Tag.rank .E7)) (c : Kˣ) (n : NU K) (β : ↥(Phi a7)) :
    diagN j c n β = ((c ^ MinData.toWeight β.1 j : Kˣ) : K) * n β := by
  simp [diagN]

theorem diagN_single (j : Fin (Tag.rank .E7)) (c : Kˣ) (β : ↥(Phi a7)) (b : K) :
    diagN j c (Pi.single β b) = Pi.single β (((c ^ MinData.toWeight β.1 j : Kˣ) : K) * b) := by
  classical
  funext δ
  rw [diagN_apply]
  by_cases h : δ = β
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem hm_conj_uN (j : Fin (Tag.rank .E7)) (c : Kˣ) (m : NU K) :
    uN (diagN j c m) = (e7Data_valid.hm K j c : Gp K) * uN m * (e7Data_valid.hm K j c : Gp K)⁻¹ := by
  refine conj_uN_of_single (e7Data_valid.hm K j c) (diagN j c) (fun β b => ?_) m
  rw [diagN_single, uN_single, uN_single]
  exact (e7Data_valid.hm_conj_xm K (mem_Phi.1 β.2).1 j c b).symm

theorem hm_mem_linNorm (j : Fin (Tag.rank .E7)) (c : Kˣ) :
    (e7Data_valid.hm K j c : Gp K) ∈ linNorm (K := K) uN uN_injective :=
  ⟨diagN j c, hm_conj_uN j c⟩

theorem linAd_hm (j : Fin (Tag.rank .E7)) (c : Kˣ) (n : NU K) :
    linAd (K := K) uN uN_injective ⟨e7Data_valid.hm K j c, hm_mem_linNorm j c⟩ n = diagN j c n :=
  linAd_eq uN uN_injective (hm_mem_linNorm j c) (hm_conj_uN j c) n

end CFSG.RankThree.GF2n.Smith81.S81Z
