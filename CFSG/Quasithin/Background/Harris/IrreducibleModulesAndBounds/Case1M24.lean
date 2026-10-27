module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M24Dim
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M24Form
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M24End
public import CFSG.Quasithin.Background.SmithB45MatIndM24
import CFSG.Quasithin.Background.G9GolayM22
import CFSG.Quasithin.Background.G9GolayM24
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint
  CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case1_M24_core_dimensionOnly
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M24)) :
    G93Case1DimensionOnly L m := by
  obtain ⟨e⟩ := hM
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* S24 := e
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover h.L_comp.2.2 h.H_irr e'
    (fun E _ _ _ π hπ hC hodd => CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd)
  have hAut : ∀ φ : S24 ≃* S24, ∃ s : S24, ∀ x, φ x = s * x * s⁻¹ :=
    autInner_of_card_le m24_center_eq_bot' m24_mulAut_card
  have hm6 : m ≤ 6 := m_le_of_autInner h e' hAut (r := 6) m24_rank_le
  have hb := h.bound
  have hcard : Nat.card (Multiplicative V) ≤ 2 ^ 36 := by
    rw [natCard_multiplicative]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod := mathieuSmallIrr24_holds (Multiplicative V) mul_self_eq_one_multiplicative
    (toMulSub L) ⟨(toMulSubEquiv L).symm.trans f⟩ (isIrrOn_toMulSub h.H_irr).2 hcard
  have hd : Module.finrank (ZMod 2) V = 11 := by
    have h1 := natCard_of_mathieu24 hmod
    rw [natCard_multiplicative] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  have hm5 : 5 ≤ m := by omega
  have h23 : 23 ∣ Nat.card L := by
    have h1 : 23 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
      rw [Nat.card_congr e'.toEquiv, m24_card_eq]
      norm_num
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have htop : Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2 x x.2)
    have hidx : (Subgroup.center ↥L).index = Nat.card S24 :=
      (Subgroup.index_eq_card _).trans (Nat.card_congr e'.toEquiv)
    rw [htop, Subgroup.index_top, m24_card_eq] at hidx
    omega
  refine ⟨Or.inr ⟨⟨f⟩, hd, hm5, hm6⟩, ?_, ?_⟩
  · exact endIsField_one_of_prime_finrank h.H_irr (by rw [hd]; norm_num) hnc
  · rintro ⟨B, hBnd, hBinv⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 23 h23
    let eT : V ≃ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V) := Submodule.topEquiv.symm
    let B' : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 := B.compl₁₂ eT.toLinearMap eT.toLinearMap
    refine Case1M24Form.false_of_invariant_form hd (g := (x : GLV V))
      (by rw [Subgroup.orderOf_coe]; exact hx) B' ?_ ?_
    · intro y hy
      have h0 : eT y = 0 := hBnd.2 _ fun i => by
        have h1 : B (eT (Submodule.topEquiv i)) (eT y) = 0 := hy (Submodule.topEquiv i)
        have h2 : eT (Submodule.topEquiv i) = i := LinearEquiv.symm_apply_apply _ _
        rwa [h2] at h1
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · intro u v
      exact hBinv (x : GLV V) x.2 (eT u) (eT v) (eT ((x : GLV V) u)) (eT ((x : GLV V) v)) rfl rfl


theorem case1_M24_core
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M24)) :
    G93Case1 L m := by
  have partialResult := case1_M24_core_dimensionOnly h hM
  rcases partialResult with ⟨cases, endField, notSelfDual⟩
  rcases cases with left | right
  · rcases left with ⟨group, dimension, lower, upper⟩
    exact ⟨Or.inl ⟨group, dimension, lower, upper,
      mathieu22_golay_realization h.H_irr group dimension⟩, endField, notSelfDual⟩
  · rcases right with ⟨group, dimension, lower, upper⟩
    exact ⟨Or.inr ⟨group, dimension, lower, upper,
      mathieu24_golay_realization h.H_irr group dimension⟩, endField, notSelfDual⟩

theorem case1_M24
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M24)) :
    G93Concl Γ L m :=
  Or.inr (Or.inl (case1_M24_core h hM))

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
