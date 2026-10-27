module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DGeo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open Module
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_B_sup_Z95 (hc : Ctx M Q Z B) : Nat.card ↥(B ⊔ Z) = Nat.card Z ^ 2 := by
  obtain ⟨k, hk⟩ := hc.conj
  have hBcard : Nat.card B = Nat.card Z := by rw [hk, card_conjSubgroup]
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hx))
  have h := card_sup_mul_card_inf_of_le_normalizer (L := Z) (E := B) hBN
  rw [hc.inf_eq_bot, Subgroup.card_bot, mul_one, hBcard] at h
  rw [sup_comm, h, pow_two]

theorem exists_mem_inf_conj_not_BZ95 (hc : Ctx M Q Z B) {t z : G} (h5 : Five95 hc t z) :
    ∃ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t), u ∉ B ⊔ Z := by
  by_contra hcon
  push Not at hcon
  have hle : Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ≤ B ⊔ Z :=
    fun u hu => hcon u hu
  have hcard := Subgroup.card_le_of_le hle
  rw [h5.1, card_B_sup_Z95 hc] at hcard
  have hq1 : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have := (Nat.pow_le_pow_iff_right hq1).mp hcard
  omega

theorem pi_eq_of_mul_inv_mem95 {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {u a : G} (hu : u ∈ Q) (ha : a ∈ Q) (h : u * a⁻¹ ∈ Z) :
    M₀.π u = M₀.π a := by
  have h2 : M₀.π (u * a⁻¹) = 0 := (M₀.π_ker _ (Q.mul_mem hu (Q.inv_mem ha))).mpr h
  have h3 := M₀.π_mul _ (Q.mul_mem hu (Q.inv_mem ha)) _ ha
  rw [h2, inv_mul_cancel_right, zero_add] at h3
  exact h3

theorem exists_point_pair95 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {z : G}
    (hzM : z ∈ M) (h5 : Five95 hc t z) :
    ∃ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t), ∃ c ∈ Rt M (LB M Q B) t,
      conjSubgroup ρ B ⊔ Z = conjSubgroup c B ⊔ Z ∧
      conjSubgroup ρ B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ∧
      ¬ conjSubgroup ρ B ≤ B ⊔ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨u, huD, huBZ⟩ := exists_mem_inf_conj_not_BZ95 hc h5
  obtain ⟨ρ, hρz, b, hbB, hu1⟩ := h5.2.2.2.1 u huD
  obtain ⟨c, hcR, b₁, hb₁B, hu2⟩ := h5.2.2.1 u huD
  have hρR : z⁻¹ * ρ * z ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp hρz
  have hρM : ρ ∈ M := by
    have h := hc.Rt_le_M t hρR
    have e : ρ = z * (z⁻¹ * ρ * z) * z⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hzM h) (M.inv_mem hzM)
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  obtain ⟨K', fK', finK', chK', γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hCρ : Ctx M Q Z (conjSubgroup ρ B) := hc.conj_of_mem hρM
  have hCc : Ctx M Q Z (conjSubgroup c B) := hc.conj_of_mem hcM
  have huQ : u ∈ Q := hc.Vt_le_Q t (Subgroup.mem_inf.mp huD).1
  have haC : ρ * b * ρ⁻¹ ∈ conjSubgroup ρ B := conj_mem95 ρ hbB
  have ha'C : c * b₁ * c⁻¹ ∈ conjSubgroup c B := conj_mem95 c hb₁B
  have hpiρ : M₀.π u = M₀.π (ρ * b * ρ⁻¹) := pi_eq_of_mul_inv_mem95 huQ (hCρ.le haC) hu1
  have hpic : M₀.π u = M₀.π (c * b₁ * c⁻¹) := pi_eq_of_mul_inv_mem95 huQ (hCc.le ha'C) hu2
  have hne : M₀.π u ≠ 0 := fun h0 => huBZ (Subgroup.mem_sup_right ((M₀.π_ker _ huQ).mp h0))
  have h1 : conjSubgroup c B ≤ Z ⊔ conjSubgroup ρ B :=
    le_sup_of_common_pi95 h hCρ hCc haC ha'C (hpiρ.symm.trans hpic) (hpiρ ▸ hne)
  have h2 : conjSubgroup ρ B ≤ Z ⊔ conjSubgroup c B :=
    le_sup_of_common_pi95 h hCc hCρ ha'C haC (hpic.symm.trans hpiρ) (hpic ▸ hne)
  refine ⟨ρ, hρz, c, hcR, le_antisymm (sup_le (h2.trans (le_of_eq (sup_comm _ _)))
    le_sup_right) (sup_le (h1.trans (le_of_eq (sup_comm _ _))) le_sup_right), ?_, ?_⟩
  · refine le_inf ?_ ?_
    · have hCcV : conjSubgroup c B ≤ Vt M (LB M Q B) B Z t := by
        intro y hy
        have hb' : c⁻¹ * y * c ∈ B := mem_conjSubgroup.mp hy
        have hbV : c⁻¹ * y * c ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb'
        have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hcR)
          (c⁻¹ * y * c)).mp hbV
        simpa [mul_assoc] using this
      exact h2.trans (sup_le sec39_Z_le_Vt hCcV)
    · intro y hy
      have hb' : ρ⁻¹ * y * ρ ∈ B := mem_conjSubgroup.mp hy
      have hbVz : ρ⁻¹ * y * ρ ∈ conjSubgroup z (Vt M (LB M Q B) B Z t) := (h5.2.1 hb').2
      rw [mem_conjSubgroup]
      have hx : z⁻¹ * (ρ⁻¹ * y * ρ) * z ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hbVz
      have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρR) _).mp hx
      have e : (z⁻¹ * ρ * z) * (z⁻¹ * (ρ⁻¹ * y * ρ) * z) * (z⁻¹ * ρ * z)⁻¹ = z⁻¹ * y * z := by
        group
      rwa [e] at this
  · intro hle
    apply huBZ
    have e : u = (u * (ρ * b * ρ⁻¹)⁻¹) * (ρ * b * ρ⁻¹) := by group
    rw [e]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right hu1) (hle haC)

theorem Z0_le_LB_conj95 {hc : Ctx M Q Z B} {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : Centre95 hc t Z0) {ρ c : G}
    (hρM : ρ ∈ M) (hcR : c ∈ Rt M (LB M Q B) t)
    (hEq : conjSubgroup ρ B ⊔ Z = conjSubgroup c B ⊔ Z) :
    Z0 ≤ LB M Q (conjSubgroup ρ B) := by
  have hcM : c ∈ M := hc.Rt_le_M t hcR
  rw [hc.LB_conj hρM, hc.conj_LB_eq_of_conj_BZ hρM hcM hEq]
  intro x hx
  rw [mem_conjSubgroup]
  have hxL : x ∈ LB M Q B := (hcen.1 hx).1
  have hQ : ⁅x⁻¹, c⁻¹⁆ ∈ Q := ((hZ0 _).mp (Z0.inv_mem hx)).2 c⁻¹ ((Rt M (LB M Q B) t).inv_mem hcR)
  have e : c⁻¹ * x * c = x * ⁅x⁻¹, c⁻¹⁆ := by simp only [commutatorElement_def]; group
  rw [e]
  have hQL : ⁅x⁻¹, c⁻¹⁆ ∈ LB M Q B := (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)) hQ
  exact (LB M Q B).mul_mem hxL hQL

end HS9

end CFSG.RankThree.GF2n.Stroth80
