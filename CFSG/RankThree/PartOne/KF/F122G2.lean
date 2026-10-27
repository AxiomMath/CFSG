module

public import CFSG.RankThree.PartOne.KF.F122ExcEngine
public import CFSG.RankThree.PartOne.S11c.Sec66G2
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
public import CFSG.RankThree.PartOne.KF.F122Sp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)
open CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.RankThreeEven (localRank)

theorem two_le_localRank_adjoint_G2
    {k : Type} [Field k] [Finite k] [CharP k 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ Nat.card k - 1) : 2 ≤ localRank p ↥(adjointGroup .G2 k) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨ι, hι, hcomm⟩ := CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2
    (K := k) .G2 ![![1, 0], ![1, 2]] (by decide +kernel)
  exact CFSG.RankThree.PartTwo.Census.Exceptional.le_localRank_of_commuting_SL2_even
    (ringChar.eq k 2) hp hp2 (by rwa [← Nat.card_eq_fintype_card]) (by norm_num) ι hι hcomm

theorem kf122Row2_holds
    : KF122Row 2 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, hf1, hpq, hM⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f = 1 := by omega
    subst this
    have h1 : p ∣ 1 := by simpa using hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
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
  obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf2 hKcard σ
  have hk : Nat.card (fixSubfield σ) = 2 ^ f' := by
    rw [hkcard, hσord, hff', Nat.mul_div_cancel_left f' hp.pos]
  have hpk : p ∣ 2 ^ f' - 1 := dvd_two_pow_sub_one_of_mul hp (hff' ▸ hpq)
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have : CharP (fixSubfield σ) 2 :=
    charP_of_card_eq_prime_pow (f := f') (by rw [← Nat.card_eq_fintype_card, hk])
  have hlow := two_le_localRank_adjoint_G2 (k := fixSubfield σ) hp (by omega) (by rw [hk]; exact hpk)
  let e3 : ↥(fixSub (entrywiseAdjointAut .G2 σ)) ≃* ↥(fixedFieldImage .G2 σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup .G2 K).subtype
      (adjointGroup .G2 K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  exact false_of_conj_fixed hp e hαp hαinn (MulAut.conj h0) (entrywiseAdjointAut .G2 σ)
    (by rw [hh0]) (e3.trans (fixedFieldImageEquiv σ).symm) hlow hLRA

end CFSG.RankThree.PartOne
