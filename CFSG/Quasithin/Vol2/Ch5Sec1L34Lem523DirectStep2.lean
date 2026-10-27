module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectZero

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem exists_noncomm_V₂_U (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)))) :
    ∃ u ∈ conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G)),
      ∃ v ∈ conjClosure Z₁ D₃, u * v ≠ v * u := by
  by_contra hcon
  push Not at hcon
  have hbot : ⁅conjClosure Z₁ D₃, conjClosure (conjClosure Z₁ D₃)
      (Subgroup.centralizer (Z₁ : Set G))⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcon u hu v hv
  have h1 := s.commutator_V₂_U_eq h5114 hF hU
  rw [hbot] at h1
  have h2 := s.card_Z₁
  rw [← h1] at h2
  simp at h2

theorem conj_Z₁_eq_id {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {z : G} (hzN : z ∈ N)
    {h : Subgroup.normalizer (N : Set G)} (hZ : (h : G) = 1 ∨ (h : G) = z) (w : Fin 2 → D.K) :
    D.conj h w = w := by
  obtain ⟨x, rfl⟩ : ∃ x : ↥N, Multiplicative.toAdd (D.E x) = w :=
    ⟨D.E.symm (Multiplicative.ofAdd w), by simp⟩
  rw [NatL2Data.conj_apply]
  have key : conjAct N h x = x := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    rcases hZ with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      have hc := hNab z hzN x x.2
      calc z * (x : G) * z⁻¹ = ((x : G) * z) * z⁻¹ := by rw [← hc]
        _ = (x : G) := by group
  rw [key]

theorem false_of_n4 (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))
    {N : Subgroup G} (D : NatL2Data L N 4) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N)
    (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
      coordN D v hv = μ • coordN D z hzN) : False := by
  have hfin : Nat.card D.K = 16 := by rw [D.card]; norm_num
  haveI : CharP D.K 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D.card
  obtain ⟨u, hu, v, hv, huv⟩ := exists_noncomm_V₂_U s h5114 hF hU
  have huT : u ∈ T := s.U_le_T h5114 hF hu
  have huN : u ∈ Subgroup.normalizer (N : Set G) := hTN huT
  have huL : u ∈ Subgroup.normalizer (L : Set G) := (s.hyp.hyp.toHyp5_0_1.T_le.trans
    s.hyp.hyp.toHyp5_0_1.normal) huT
  set g : Subgroup.normalizer (N : Set G) := ⟨u, huN⟩ with hg
  obtain ⟨σ, hσ⟩ := D.exists_semilinear g huL
  have huz : u * z * u⁻¹ = z := by
    have hC : u ∈ Subgroup.centralizer (Z₁ : Set G) := s.U_le_G₁ hu
    have hc := Subgroup.mem_centralizer_iff.mp hC z hz
    calc u * z * u⁻¹ = (z * u) * u⁻¹ := by rw [hc]
      _ = z := by group
  have hgw : D.conj g (coordN D z hzN) = coordN D z hzN := by
    unfold coordN
    rw [NatL2Data.conj_apply]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact huz
  have hu2 : (u * u) ∈ Z₁ := by
    rw [← sq]
    exact s.sq_mem_Z₁ h5114 hF hu
  have hgg : ∀ w, D.conj (g * g) w = D.conj g (D.conj g w) := fun w => NatL2Data.conj_mul D g g w
  have hw : coordN D z hzN ≠ 0 := by
    intro h0
    apply hz1
    have h1 : (⟨z, hzN⟩ : ↥N) = 1 := by
      apply D.E.injective
      apply Multiplicative.toAdd.injective
      have : Multiplicative.toAdd (D.E ⟨z, hzN⟩) = 0 := h0
      rw [this]
      simp
    exact congrArg Subtype.val h1
  have hZg : ((g * g : Subgroup.normalizer (N : Set G)) : G) = 1 ∨
      ((g * g : Subgroup.normalizer (N : Set G)) : G) = z := by
    have : ((g * g : Subgroup.normalizer (N : Set G)) : G) = u * u := rfl
    rw [this]
    exact s.eq_one_or_eq hz hz1 hu2
  have hsq : ∀ a : D.K, σ (σ a) = a := by
    intro a
    have h1 : D.conj (g * g) (a • coordN D z hzN) = a • coordN D z hzN :=
      conj_Z₁_eq_id D hNab hzN hZg _
    have h2 : D.conj g (D.conj g (a • coordN D z hzN)) = σ (σ a) • coordN D z hzN := by
      calc D.conj g (D.conj g (a • coordN D z hzN)) = D.conj g (σ a • coordN D z hzN) := by
            rw [hσ, hgw]
        _ = σ (σ a) • coordN D z hzN := by rw [hσ, hgw]
    have h3 : σ (σ a) • coordN D z hzN = a • coordN D z hzN := by
      rw [← h2, ← hgg, h1]
    exact smul_left_injective D.K hw h3
  have hF4 := Direct523Gal.fix_F4_of_sq hfin σ hsq
  obtain ⟨hvN, μ, hμ, hcoord⟩ := hV2 v hv
  have hfix : D.conj g (coordN D v hvN) = coordN D v hvN := by
    rw [hcoord, hσ, hgw, hF4 μ hμ]
  apply huv
  have hconj : conjAct N g ⟨v, hvN⟩ = ⟨v, hvN⟩ := by
    apply D.E.injective
    apply Multiplicative.toAdd.injective
    rw [← NatL2Data.conj_apply]
    exact hfix
  have h2 := congrArg (fun x : ↥N => (x : G)) hconj
  simp only [conjAct_apply_coe] at h2
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = v * u := by rw [h2]

end CFSG.Quasithin.H13
