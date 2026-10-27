module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel3

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

theorem rho_pow_three {ρ : G} (hρ : ρ ∈ S.T1) (hz : z * ρ * z⁻¹ = ρ⁻¹) : ρ ^ 3 = 1 := by
  by_contra h3
  have hdvd : orderOf ρ ∣ 9 := by
    have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : ↥S.T1)
    rw [Subgroup.orderOf_mk, S.card_T1] at this
    exact this
  have hord : orderOf ρ = 9 := by
    have hdiv : orderOf ρ ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [this] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with h | h | h
    · exact absurd (by rw [orderOf_eq_one_iff.mp h]; simp) h3
    · exact absurd (by rw [← h]; exact pow_orderOf_eq_one ρ) h3
    · exact h
  have hz9 : Nat.card (Subgroup.zpowers ρ) = 9 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers ρ ≤ S.T1 := Subgroup.zpowers_le.mpr hρ
  have heq : Subgroup.zpowers ρ = S.T1 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hz9, S.card_T1])
  have hsig : S.sig ∈ Subgroup.zpowers ρ := by
    rw [heq]
    exact S.sig_mem_T1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsig
  have hconj : z * S.sig * z⁻¹ = S.sig := by
    calc z * S.sig * z⁻¹ = (S.sig * z) * z⁻¹ := by rw [S.sig_comm_z]
      _ = S.sig := by group
  have hconj' : z * S.sig * z⁻¹ = S.sig⁻¹ := by
    rw [← hk]
    have : z * ρ ^ k * z⁻¹ = (z * ρ * z⁻¹) ^ k := by
      simp
    rw [this, hz, inv_zpow]
  have h1 : S.sig = S.sig⁻¹ := hconj.symm.trans hconj'
  have h2 : S.sig * S.sig = 1 := mul_eq_one_iff_eq_inv.mpr h1
  apply S.sig_ne_one
  calc S.sig = S.sig ^ 3 * (S.sig * S.sig)⁻¹ := by rw [pow_three', ← pow_three']; group
    _ = 1 := by rw [S.sig_pow_three, h2]; simp

theorem commute_rho {ρ : G} (hρ : ρ ∈ S.T1) (hz : z * ρ * z⁻¹ = ρ⁻¹) :
    ρ * S.rho2 ρ = S.rho2 ρ * ρ := by
  have hρM := S.T1_le_Mg hρ
  have hρ2M := S.rho2_mem_Mg hρM
  set ρ₂ := S.rho2 ρ with hρ₂
  set c := ρ⁻¹ * ρ₂⁻¹ * ρ * ρ₂ with hc
  have hcT : c ∈ S.Tg := S.comm_mem_Tg hρM hρ2M
  have hcen : ∀ m ∈ S.Mg, c * m = m * c := fun m hm =>
    (S.mem_Cg).1 (S.Mg_le_Cg hm) c hcT
  have h1 : (S.v : G)⁻¹ * ρ * S.v = ρ₂ := rfl
  have h2 : (S.v : G)⁻¹ * ρ₂ * S.v = ρ⁻¹ := S.v_rho2 hz
  have h3 : (S.v : G)⁻¹ * c * S.v = ρ₂⁻¹ * ρ * ρ₂ * ρ⁻¹ := by
    calc (S.v : G)⁻¹ * c * S.v = ((S.v : G)⁻¹ * ρ * S.v)⁻¹ * ((S.v : G)⁻¹ * ρ₂ * S.v)⁻¹ *
          ((S.v : G)⁻¹ * ρ * S.v) * ((S.v : G)⁻¹ * ρ₂ * S.v) := by rw [hc]; group
      _ = ρ₂⁻¹ * ρ * ρ₂ * ρ⁻¹ := by rw [h1, h2]; group
  have h4 : ρ₂⁻¹ * ρ * ρ₂ * ρ⁻¹ = c := by
    have e : ρ₂⁻¹ * ρ * ρ₂ = ρ * c := by rw [hc]; group
    calc ρ₂⁻¹ * ρ * ρ₂ * ρ⁻¹ = ρ * c * ρ⁻¹ := by rw [e]
      _ = c := by rw [← hcen ρ hρM]; group
  have h5 : (S.v : G)⁻¹ * c * S.v = c⁻¹ := S.v_inv_Tg hcT
  have h6 : c = c⁻¹ := (h3.trans h4).symm.trans h5
  have hc2 : c * c = 1 := mul_eq_one_iff_eq_inv.mpr h6
  have hc3 : c ^ 3 = 1 := S.pow_three_Tg hcT
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by rw [pow_three', ← pow_three']; group
      _ = 1 := by rw [hc3, hc2]; simp
  exact comm_of_form hc1

theorem exists_gens : ∃ ρ ρ₂ : G, ρ ∈ S.T1 ∧ ρ₂ ∈ S.T2 ∧ ρ * ρ₂ = ρ₂ * ρ ∧ ρ ^ 3 = 1 ∧
    ρ₂ ^ 3 = 1 ∧ S.Mg = Subgroup.closure ((S.Tg : Set G) ∪ {ρ, ρ₂}) := by
  obtain ⟨ρ, hρ, hρ1, hρz⟩ := S.exists_rho
  have hρM := S.T1_le_Mg hρ
  have hρ2T : S.rho2 ρ ∈ S.T2 := S.rho2_mem_T2 hρ
  have hρ2M := S.T2_le_Mg hρ2T
  have hρ2z : z * S.rho2 ρ * z⁻¹ = (S.rho2 ρ)⁻¹ := S.z_rho2 hρz
  have hρ21 : S.rho2 ρ ≠ 1 := by
    intro h
    apply hρ1
    have : ρ = S.v * S.rho2 ρ * (S.v : G)⁻¹ := by
      unfold rho2
      group
    rw [this, h]
    group
  have hT1 := eq_closure_of_card_nine S.card_T1 S.sig_mem_T1 hρ S.sig_pow_three S.sig_ne_one
    (S.not_mem_zpowers_sig hρM hρ1 hρz)
  have hT2 := eq_closure_of_card_nine S.card_T2 S.sig_mem_T2 hρ2T S.sig_pow_three S.sig_ne_one
    (S.not_mem_zpowers_sig hρ2M hρ21 hρ2z)
  have hρ3 := S.rho_pow_three hρ hρz
  refine ⟨ρ, S.rho2 ρ, hρ, hρ2T, S.commute_rho hρ hρz, hρ3, ?_, ?_⟩
  · have e : S.rho2 ρ = (S.v : G)⁻¹ * ρ * ((S.v : G)⁻¹)⁻¹ := by simp [rho2]
    rw [e, conj_pow, hρ3]
    group
  · have hσ : S.sig ∈ ((S.Tg : Set G) ∪ {ρ, S.rho2 ρ}) := Or.inl S.sig_mem_Tg
    apply le_antisymm
    · rw [← S.Mg_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        exact Subgroup.subset_closure (Or.inl hx)
      · rw [hT1]
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact Subgroup.subset_closure hσ
        · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      · rw [hT2]
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact Subgroup.subset_closure hσ
        · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    · rw [Subgroup.closure_le]
      rintro x (hx | rfl | rfl)
      · exact S.Tg_le_Mg hx
      · exact hρM
      · exact hρ2M

theorem abelian_Mg : ∀ x ∈ S.Mg, ∀ y ∈ S.Mg, x * y = y * x := by
  obtain ⟨ρ, ρ₂, hρ, hρ2, hcomm, -, -, hcl⟩ := S.exists_gens
  have hρM := S.T1_le_Mg hρ
  have hρ2M := S.T2_le_Mg hρ2
  have hTc : ∀ t ∈ S.Tg, ∀ m ∈ S.Mg, t * m = m * t := fun t ht m hm =>
    (S.mem_Cg).1 (S.Mg_le_Cg hm) t ht
  have h1 : ∀ m ∈ S.Mg, ρ * m = m * ρ := by
    intro m hm
    have hle : S.Mg ≤ Subgroup.centralizer ({ρ} : Set G) := by
      rw [hcl, Subgroup.closure_le]
      rintro g (hg | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hTc g hg ρ hρM)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hm)).symm
  have h2 : ∀ m ∈ S.Mg, ρ₂ * m = m * ρ₂ := by
    intro m hm
    have hle : S.Mg ≤ Subgroup.centralizer ({ρ₂} : Set G) := by
      rw [hcl, Subgroup.closure_le]
      rintro g (hg | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hTc g hg ρ₂ hρ2M)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hm)).symm
  have hgen : S.Mg ≤ Subgroup.centralizer (S.Mg : Set G) := by
    calc S.Mg = Subgroup.closure ((S.Tg : Set G) ∪ {ρ, ρ₂}) := hcl
      _ ≤ Subgroup.centralizer (S.Mg : Set G) := by
        rw [Subgroup.closure_le]
        rintro g (hg | rfl | rfl)
        · exact Subgroup.mem_centralizer_iff.mpr fun m hm => (hTc g hg m hm).symm
        · exact Subgroup.mem_centralizer_iff.mpr fun m hm => (h1 m hm).symm
        · exact Subgroup.mem_centralizer_iff.mpr fun m hm => (h2 m hm).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hgen hx) y hy).symm

theorem pow_three_Mg : ∀ x ∈ S.Mg, x ^ 3 = 1 := by
  obtain ⟨ρ, ρ₂, hρ, hρ2, -, hρ3, hρ23, hcl⟩ := S.exists_gens
  intro x hx
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | rfl | rfl
    · exact S.pow_three_Tg hg
    · exact hρ3
    · exact hρ23
  | one => simp
  | mul a b ha hb iha ihb =>
    have haM : a ∈ S.Mg := by rw [hcl]; exact ha
    have hbM : b ∈ S.Mg := by rw [hcl]; exact hb
    have hab : Commute a b := S.abelian_Mg a haM b hbM
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha =>
    rw [inv_pow, iha, inv_one]

end JWSetup

end CFSG.Quasithin.H13.U43
