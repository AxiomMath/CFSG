module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

theorem two_le_of_admissible_G2 {n f : ℕ} (h : StatedLieAdmissible .G2 n 2 f) : 2 ≤ f := by
  have h1 : 1 ≤ f := h.2.1
  have h3 : 3 ≤ 2 ^ f := h.2.2.2
  by_contra hlt
  have : f = 1 := by omega
  subst this
  norm_num at h3

theorem admissible_G2 {f : ℕ} (hf : 2 ≤ f) : StatedLieAdmissible .G2 0 2 f :=
  CFSG.Open.StatedAPI.statedLieAdmissible_G2_two hf

theorem untwistedTag_G2 : untwistedTag .G2 = some Tag.G2 := rfl

@[expose] def G2SubfieldCaseExcluded : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LieModel T .G2 0 2 p →
    ∀ (α : MulAut T) (q : T) (U : Subgroup T), orderOf α = p → α ∉ innerAut T → q ≠ 1 →
      q ^ p = 1 → α q = q → U ≠ ⊥ → IsPGroup 2 ↥U → (∀ u ∈ U, α u ∈ U) →
      (∀ u ∈ U, q * u * q⁻¹ ∈ U) → (∃ u ∈ U, α u ≠ u ∨ q * u * q⁻¹ ≠ u) → False

theorem sec66T_K2_G2 :
    Sec66T_K2 .G2 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have hf : 2 ≤ f := two_le_of_admissible_G2 hadm
  obtain ⟨-, Θ, -, -, hΘker, -⟩ := even_G2_exact_automorphism_normal_form hf K hKcard
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut (by omega) hKcard
  refine no_plane_of_cyclic_quotient hp (Θ.comp (MulAut.congr e).toMonoidHom) ?_ E hE hcard hEinn
  intro x hx _
  have hx' : Θ (MulAut.congr e x) = 1 := hx
  have hmem : MulAut.congr e x ∈ Θ.ker := hx'
  rw [hΘker] at hmem
  exact (mem_innerAut_congr e x).mp hmem

theorem sec66T_K1_G2
    (hdeg
    : G2SubfieldCaseExcluded) : Sec66T_K1 .G2 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_G2).mp hM).1
  subst hn0
  have hf2 : 2 ≤ f := two_le_of_admissible_G2 hadmf
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  set α' : MulAut (adjointGroup .G2 K) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hKcard
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨h0, hh0⟩, -⟩ :=
    even_G2_noninner_prime_local_core_trivial hf2 hKcard hp ⊤ le_top ⟨α', Subgroup.mem_top _⟩
      hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  obtain ⟨f', hff'⟩ := hpf
  by_cases hf'1 : f' = 1
  ·
    exfalso
    subst hf'1
    rw [mul_one] at hff'
    subst hff'
    exact hdeg T f hp hp5 hM α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv
  · have hf'pos : 1 ≤ f' := one_le_of_mul_eq (by omega) hff'
    have hf'2 : 2 ≤ f' := by omega
    obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf2 hKcard σ
    have hk4 : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hkcard, hσord, hff', Nat.mul_div_cancel_left f' hp.pos]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf'2
    have hq' : CFSG.IsQuasisimple ↥(adjointGroup .G2 (fixSubfield σ)) :=
      CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card _ hk4
    obtain ⟨hsimple, hnc⟩ := fixedFieldImage_simple_of_quasisimple σ hq'
    exact fieldAutT_of_conj_entrywise untwistedTag_G2 hp (admissible_G2 hf'2) (by omega) hKcard e
      hM α σ hσord hff' (MulAut.conj h0) hh0 hJC1 hsimple hnc

end CFSG.RankThree.PartOne.Sec66T
