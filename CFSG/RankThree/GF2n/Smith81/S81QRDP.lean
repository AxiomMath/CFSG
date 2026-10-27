module

public import CFSG.RankThree.GF2n.Smith81.S81QRDU
public import CFSG.RankThree.GF2n.Smith81.S81ZLinNorm

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem conj_uD_of_single (g : Gp K) (φ : ND K →ₗ[K] ND K)
    (h : ∀ (β : ↥Psi0) (b : K), uD (φ (Pi.single β b)) = g * uD (Pi.single β b) * g⁻¹)
    (m : ND K) : uD (φ m) = g * uD m * g⁻¹ := by
  have hm : m = ∑ β : ↥Psi0, Pi.single β (m β) := (Finset.univ_sum_single m).symm
  rw [hm]
  refine Finset.sum_induction (fun β : ↥Psi0 => (Pi.single β (m β) : ND K))
    (fun x : ND K => uD (φ x) = g * uD x * g⁻¹) ?_ ?_ ?_
  · intro x y hx hy
    rw [map_add, uD_add, uD_add, hx, hy]
    group
  · rw [map_zero, uD_zero]
    group
  · intro β _
    exact h β (m β)

theorem pr_add0 (a : Fin e7Data.d) (γ δ : Rt) : pr a (γ + δ) = pr a γ + pr a δ := by
  unfold pr
  exact dotProduct_add _ _ _

theorem pr_a0_Psi0 {β : Rt} (hβ : β ∈ Psi0) : pr (a0 : Fin e7Data.d) β = 1 := by
  rw [pr_a0_eq (mem_Psi0.1 hβ).1]
  exact (mem_Psi0.1 hβ).2

theorem add_ne_zero_of_pr0 {γ β : Rt} (hγ : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1)
    (hβ : β ∈ Psi0) : γ + β ≠ 0 := by
  intro h
  have h1 : pr (a0 : Fin e7Data.d) (γ + β) = pr (a0 : Fin e7Data.d) (0 : Rt) := by rw [h]
  have h2 : pr (a0 : Fin e7Data.d) (0 : Rt) = 0 := by unfold pr; simp
  rw [pr_add0, h2, pr_a0_Psi0 hβ] at h1
  rcases hγ with h | h <;> omega

theorem isRoot_add_iff_mem0 {γ β : Rt} (hγP : γ ∈ Perp)
    (hγ : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1) (hβ : β ∈ Psi0) :
    IsRoot .E7 (γ + β) ↔ γ + β ∈ Psi0 := by
  constructor
  · intro hr
    have hβP := (mem_Psi0.1 hβ).1
    have hsP : γ + β ∈ Perp := by
      rw [perp_iff]
      refine ⟨hr, ?_⟩
      have h1 := (perp_iff.1 hγP).2
      have h2 := (perp_iff.1 hβP).2
      simp [Pi.add_apply, h1, h2]
    refine mem_Psi0.2 ⟨hsP, ?_⟩
    rw [← pr_a0_eq hsP, pr_add0, pr_a0_Psi0 hβ]
    have hmem := pr_mem hr (a0 : Fin e7Data.d)
    rw [pr_add0, pr_a0_Psi0 hβ] at hmem
    rcases hγ with h | h <;> rw [h] at hmem ⊢ <;> omega
  · intro h
    exact (perp_iff.1 (mem_Psi0.1 h).1).1

open _root_.Classical in
@[expose] def shiftFunD (γ : Rt) (n : ND K) (δ : ↥Psi0) : K :=
  if h : δ.1 - γ ∈ Psi0 then n ⟨δ.1 - γ, h⟩ else 0

@[expose] def shiftD (γ : Rt) : ND K →ₗ[K] ND K where
  toFun n := fun δ => shiftFunD γ n δ
  map_add' n m := by
    funext δ
    unfold shiftFunD
    by_cases h : δ.1 - γ ∈ Psi0 <;> simp [h]
  map_smul' c n := by
    funext δ
    unfold shiftFunD
    by_cases h : δ.1 - γ ∈ Psi0 <;> simp [h]

theorem shiftD_apply (γ : Rt) (n : ND K) (δ : ↥Psi0) :
    shiftD γ n δ = shiftFunD γ n δ := by
  simp only [shiftD, LinearMap.coe_mk, AddHom.coe_mk]

open _root_.Classical in
theorem shiftD_single (γ : Rt) (β : ↥Psi0) (b : K) :
    shiftD γ (Pi.single β b) =
      if h : β.1 + γ ∈ Psi0 then Pi.single ⟨β.1 + γ, h⟩ b else 0 := by
  funext δ
  rw [shiftD_apply]
  unfold shiftFunD
  have hiff : ∀ (h3 : δ.1 - γ ∈ Psi0), (⟨δ.1 - γ, h3⟩ : ↥Psi0) = β ↔ δ.1 = β.1 + γ := by
    intro h3
    rw [Subtype.ext_iff]
    exact sub_eq_iff_eq_add
  by_cases h1 : β.1 + γ ∈ Psi0
  · rw [dif_pos h1]
    by_cases h3 : δ.1 - γ ∈ Psi0
    · rw [dif_pos h3]
      by_cases e : δ.1 = β.1 + γ
      · have h4 : (⟨δ.1 - γ, h3⟩ : ↥Psi0) = β := (hiff h3).2 e
        have h2 : δ = ⟨β.1 + γ, h1⟩ := Subtype.ext e
        rw [h4, h2]
        simp
      · have h4 : ¬ (⟨δ.1 - γ, h3⟩ : ↥Psi0) = β := fun h => e ((hiff h3).1 h)
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
    by_cases h3 : δ.1 - γ ∈ Psi0
    · rw [dif_pos h3]
      have h4 : ¬ (⟨δ.1 - γ, h3⟩ : ↥Psi0) = β := by
        intro h
        apply h1
        have := (hiff h3).1 h
        rw [← this]
        exact δ.2
      simp [Pi.single_apply, h4]
    · rw [dif_neg h3]
      rfl

@[expose] def adjD (γ : Rt) (a : K) : ND K →ₗ[K] ND K := LinearMap.id + a • shiftD γ

theorem adjD_apply (γ : Rt) (a : K) (n : ND K) : adjD γ a n = n + a • shiftD γ n := by
  simp [adjD]

theorem xE_conj_single0 {γ : Rt} (hγP : γ ∈ Perp)
    (hpr : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1) (a : K)
    (β : ↥Psi0) (b : K) :
    uD (adjD γ a (Pi.single β b)) = xE γ a * uD (Pi.single β b) * (xE γ a)⁻¹ := by
  classical
  have hβ : β.1 ∈ Psi0 := β.2
  have hγR : IsRoot .E7 γ := (perp_iff.1 hγP).1
  have hβR : IsRoot .E7 β.1 := (perp_iff.1 (mem_Psi0.1 hβ).1).1
  have hne : γ + β.1 ≠ 0 := add_ne_zero_of_pr0 hpr hβ
  have hcomm := comm_xE hγR hβR hne a b
  have hconj : xE γ a * xE β.1 b * (xE γ a)⁻¹ = ⁅xE γ a, xE β.1 b⁆ * xE β.1 b := by
    rw [commutatorElement_def]
    group
  rw [uD_single, hconj, hcomm, adjD_apply, shiftD_single, uD_add, uD_single]
  by_cases hr : IsRoot .E7 (γ + β.1)
  · have hmem : γ + β.1 ∈ Psi0 := (isRoot_add_iff_mem0 hγP hpr hβ).1 hr
    have hmem' : β.1 + γ ∈ Psi0 := by rwa [add_comm]
    rw [if_pos hr, dif_pos hmem']
    have h1 : a • (Pi.single ⟨β.1 + γ, hmem'⟩ b : ND K) = Pi.single ⟨β.1 + γ, hmem'⟩ (a * b) := by
      funext δ
      by_cases h : δ = ⟨β.1 + γ, hmem'⟩ <;> simp [Pi.single_apply, h]
    rw [h1, uD_single, add_comm γ β.1]
    exact xE_comm_of_mem_Phi (Psi0_subset_Phi hβ) (Psi0_subset_Phi hmem') b (a * b)
  · have hno : ¬ β.1 + γ ∈ Psi0 := by
      intro h
      apply hr
      rw [add_comm]
      exact (perp_iff.1 (mem_Psi0.1 h).1).1
    rw [if_neg hr, dif_neg hno, smul_zero, uD_zero, mul_one, one_mul]

theorem xE_conj_uD {γ : Rt} (hγP : γ ∈ Perp)
    (hpr : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1) (a : K) (m : ND K) :
    uD (adjD γ a m) = xE γ a * uD m * (xE γ a)⁻¹ :=
  conj_uD_of_single (xE γ a) (adjD γ a) (fun β b => xE_conj_single0 hγP hpr a β b) m

theorem xE_mem_linNorm0 {γ : Rt} (hγP : γ ∈ Perp)
    (hpr : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1) (a : K) :
    xE γ a ∈ linNorm (K := K) (uD : ND K → Gp K) uD_injective :=
  ⟨adjD γ a, xE_conj_uD hγP hpr a⟩

theorem linAd_xE0 {γ : Rt} (hγP : γ ∈ Perp)
    (hpr : pr (a0 : Fin e7Data.d) γ = 0 ∨ pr (a0 : Fin e7Data.d) γ = 1) (a : K) (n : ND K) :
    linAd (K := K) uD uD_injective ⟨xE γ a, xE_mem_linNorm0 hγP hpr a⟩ n = n + a • shiftD γ n := by
  rw [linAd_eq uD uD_injective (xE_mem_linNorm0 hγP hpr a) (xE_conj_uD hγP hpr a) n, adjD_apply]

@[expose] def diagD (j : Fin (Tag.rank .E7)) (c : Kˣ) : ND K →ₗ[K] ND K where
  toFun n := fun β => ((c ^ MinData.toWeight β.1 j : Kˣ) : K) * n β
  map_add' n m := by
    funext β
    simp [mul_add]
  map_smul' t n := by
    funext β
    simp [mul_left_comm]

theorem diagD_apply (j : Fin (Tag.rank .E7)) (c : Kˣ) (n : ND K) (β : ↥Psi0) :
    diagD j c n β = ((c ^ MinData.toWeight β.1 j : Kˣ) : K) * n β := by
  simp [diagD]

theorem diagD_single (j : Fin (Tag.rank .E7)) (c : Kˣ) (β : ↥Psi0) (b : K) :
    diagD j c (Pi.single β b) = Pi.single β (((c ^ MinData.toWeight β.1 j : Kˣ) : K) * b) := by
  classical
  funext δ
  rw [diagD_apply]
  by_cases h : δ = β
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem hm_conj_uD (j : Fin (Tag.rank .E7)) (c : Kˣ) (m : ND K) :
    uD (diagD j c m) = (e7Data_valid.hm K j c : Gp K) * uD m * (e7Data_valid.hm K j c : Gp K)⁻¹ := by
  refine conj_uD_of_single (e7Data_valid.hm K j c) (diagD j c) (fun β b => ?_) m
  rw [diagD_single, uD_single, uD_single]
  exact (e7Data_valid.hm_conj_xm K (perp_iff.1 (mem_Psi0.1 β.2).1).1 j c b).symm

theorem hm_mem_linNorm0 (j : Fin (Tag.rank .E7)) (c : Kˣ) :
    (e7Data_valid.hm K j c : Gp K) ∈ linNorm (K := K) (uD : ND K → Gp K) uD_injective :=
  ⟨diagD j c, hm_conj_uD j c⟩

theorem linAd_hm0 (j : Fin (Tag.rank .E7)) (c : Kˣ) (n : ND K) :
    linAd (K := K) uD uD_injective ⟨e7Data_valid.hm K j c, hm_mem_linNorm0 j c⟩ n = diagD j c n :=
  linAd_eq uD uD_injective (hm_mem_linNorm0 j c) (hm_conj_uD j c) n

end CFSG.RankThree.GF2n.Smith81.D6Spin
