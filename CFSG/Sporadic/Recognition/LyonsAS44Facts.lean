module

public import CFSG.Sporadic.Recognition.LyonsAS44Setup
public import CFSG.Sporadic.Recognition.LyonsAS44Collinear
public import CFSG.Sporadic.Recognition.LyonsLocalA3Cert

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Facts

variable {G : Type} [Group G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

structure LyAFacts (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (R T A : Subgroup (CentQuot (x₁ : G))) (Y : Fin 10 → CentQuot (x₁ : G)) : Prop where
  mcl : McLFacts (CentQuot (x₁ : G)) (D.x₂Q S) (D.x₃Q S) R T A Y
  classes : ∀ u : CentQuot (x₁ : G), orderOf u = 3 →
    IsConj u (D.x₂Q S) ∨ IsConj u (D.x₂Q S * D.x₃Q S)
  card_M : Nat.card ↥(centralizer ({(x₁ : G)} : Set G)) = 2 ^ 7 * 3 ^ 7 * 5 ^ 3 * 7 * 11
  inv : ∃ s : G, s * s = 1 ∧ s ∈ NormX (x₁ : G) ∧ s * (x₁ : G) * s⁻¹ = (x₁ : G)⁻¹ ∧
    ∀ a ∈ preimQ (x₁ : G) A, s * a * s⁻¹ = a⁻¹
  sylowQ3 : ∃ A₀ : Subgroup G, SylowQ3 (x₁ : G) (x₂ : G) (x₃ : G) t A₀

end Facts

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem exists_lyAFacts (hnrm : nrmCheck = true) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ R T A Y, LyAFacts D S R T A Y := by
  obtain ⟨R, T, A, Y, hF⟩ := D.exists_mclFacts_of_lyData hnrm S
  refine ⟨R, T, A, Y, hF, ?_, D.card_centralizer_x1 S.pow₁ S.rho₁,
    D.exists_inverting_involution S hF, D.exists_sylowQ3_of_certificate S⟩
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hy2 := D.orderOf_x₂Q S
  have hy3 := D.orderOf_x₃Q S
  have hc2 : Nat.card ↥(centralizer ({D.x₂Q S} : Set (CentQuot (x₁ : G)))) = 29160 :=
    hF.card_cent
  obtain ⟨r₁, r₂, o₁, -, c₁, c₂, hall⟩ := exists_two_classes_of_mulEquiv e
  have hcomm := D.x₂Q_mul_x₃Q S
  have hconj : IsConj (D.x₂Q S) (D.x₃Q S) := by
    obtain ⟨u, hu₂, -, hu₁, -⟩ := D.exists_swap23 S
    have hu₁G : (u : G) * (x₁ : G) = (x₁ : G) * (u : G) := by
      have := congrArg Subtype.val hu₁
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    let uM : ↥(centralizer ({(x₁ : G)} : Set G)) :=
      ⟨(u : G), mem_centralizer_singleton_iff.2 hu₁G⟩
    refine isConj_iff.2 ⟨QuotientGroup.mk uM, ?_⟩
    rw [LyData.x₂Q, LyData.x₃Q, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val hu₂
    simpa [uM, LyData.x₂M, LyData.x₃M] using this
  have hmul3 : orderOf (D.x₂Q S * D.x₃Q S) = 3 := by
    have h2 : D.x₂Q S ^ 3 = 1 := by simpa [hy2] using pow_orderOf_eq_one (D.x₂Q S)
    have h2' : D.x₃Q S ^ 3 = 1 := by simpa [hy3] using pow_orderOf_eq_one (D.x₃Q S)
    have h3 : (D.x₂Q S * D.x₃Q S) ^ 3 = 1 := by
      rw [Commute.mul_pow hcomm, h2, h2', one_mul]
    have hne : D.x₂Q S * D.x₃Q S ≠ 1 := by
      intro h1
      apply D.x₃Q_notMem_zpowers S
      have : D.x₃Q S = (D.x₂Q S)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact Subgroup.inv_mem _ (mem_zpowers _)
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3 hne
  have hc3 : Nat.card ↥(centralizer ({D.x₃Q S} : Set (CentQuot (x₁ : G)))) = 29160 := by
    rw [← card_centralizer_eq_of_isConj hconj]; exact hc2
  have hcmul : Nat.card ↥(centralizer ({D.x₂Q S * D.x₃Q S} : Set (CentQuot (x₁ : G)))) = 972 := by
    rcases card_centralizer_eq_or e hmul3 with h | h
    · exfalso
      have := hF.A_elem
      have hconj' : IsConj (D.x₂Q S * D.x₃Q S) (D.x₂Q S) :=
        isConj_of_card_eq_aux c₂ hall hmul3 hy2 h hc2
      exact hF.norm.not_isConj_mul hF.z_mem hconj (D.x₃Q_notMem_zpowers S) hconj'.symm
    · exact h
  have hy2r : IsConj (D.x₂Q S) r₁ := isConj_of_card_eq_aux c₂ hall hy2 o₁ hc2 c₁
  intro u hu
  rcases hall u hu with h | h
  · left
    exact h.trans hy2r.symm
  · right
    have hw : IsConj (D.x₂Q S * D.x₃Q S) r₂ := by
      rcases hall _ hmul3 with h' | h'
      · exfalso
        rw [card_centralizer_eq_of_isConj h', c₁] at hcmul
        omega
      · exact h'
    exact h.trans hw.symm

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
