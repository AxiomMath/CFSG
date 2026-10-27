module

public import CFSG.RankThree.PartOne.F106.OddRadG2
public import CFSG.RankThree.PartOne.S11c.Sec66G2
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyG2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.RankThree.Native.DerivedGenerators

public section


attribute [-instance] CFSG.RankThree.Native.fact_prime_five
namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.Sec66T
  CFSG.SignalizerFunctorTheorem.CatalogBridge
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)
open CFSG.Open (signalizerFixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2 g2Two_derived)

set_option linter.unusedSectionVars false

theorem oddRadConcl_G2_entrywise {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ}
    (hd : 1 ≤ d) (hk : Nat.card (fixSubfield σ) = 2 ^ d) :
    OddRadConcl (adjointGroup .G2 K) (entrywiseAdjointAut .G2 σ) := by
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_fixedGroup_G2 σ
  have hfix : ((entrywiseAdjointAut .G2 σ : MulAut (adjointGroup .G2 K)) :
      adjointGroup .G2 K →* adjointGroup .G2 K).eqLocus (MonoidHom.id _) =
      signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ) := by
    ext y
    exact Iff.rfl
  unfold OddRadConcl
  rw [hfix, card_solvableRadical_perfectResidual_eq e]
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Finite (ModGL .G2 (fixSubfield σ)) := finite_modGL
  rcases Nat.lt_or_ge 1 d with hd2 | hd1
  · have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd2
    have := isSimpleGroup_adjointGroup_g2 hk3
    rw [card_radical_residual_of_simple_perfect
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card (fixSubfield σ) hk3)]
    exact odd_one
  · have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hk, le_antisymm hd1 hd, pow_one]
    obtain ⟨hs, -⟩ := g2Two_derived hk2
    have hnc := g2Two_derived_nonabelian hk2
    have _ := hs
    have hper : Group.IsPerfect ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))) :=
      isPerfect_of_simple_nonabelian hnc
    rw [card_radical_residual_of_simple_commutator hs hper]
    exact odd_one

theorem five_dvd_sub_or_add_of_dvd_ordG2 {q : ℕ} (hq : 1 ≤ q) (h5 : ¬ 5 ∣ q)
    (h : 5 ∣ CFSG.Open.ordG2 q) : 5 ∣ q - 1 ∨ 5 ∣ q + 1 := by
  have hz : ((CFSG.Open.ordG2 q : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  unfold CFSG.Open.ordG2 at hz
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hz
  have hx : (q : ZMod 5) ≠ 0 := fun h0 => h5 ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have key : ∀ x : ZMod 5, x ≠ 0 → x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) = 0 → x = 1 ∨ x = -1 := by
    decide
  rcases key _ hx hz with h1 | h1
  · left
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1]
    simp
  · right
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h1]
    simp

theorem oddRadConcl_G2 {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) (β : MulAut (adjointGroup .G2 K)) (hβ : orderOf β = 5) :
    OddRadConcl (adjointGroup .G2 K) β := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hk3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp5 : (5 : ℕ).Prime := by norm_num
  by_cases hinn : β ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range
  · obtain ⟨t, rfl⟩ := hinn
    have hsimple : IsSimpleGroup (adjointGroup .G2 K) := isSimpleGroup_adjointGroup_g2 hk3
    have hnc : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a :=
      exists_noncomm_of_perfect
        (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K hk3)
    have hc := center_eq_bot_of_simple_nonabelian hnc
    have htord : orderOf t = 5 := by rw [← orderOf_conj_eq hc t]; exact hβ
    have h5 : 5 ∣ Nat.card (adjointGroup .G2 K) := htord ▸ orderOf_dvd_natCard t
    rw [card_adjointGroup_G2] at h5
    have h5K : ¬ 5 ∣ Nat.card K := by
      rw [hK]
      intro h
      have := (Nat.prime_five.dvd_of_dvd_pow h)
      omega
    unfold OddRadConcl
    rw [eqLocus_conj_eq_centralizer t]
    rcases five_dvd_sub_or_add_of_dvd_ordG2 Nat.card_pos h5K h5 with h | h
    · exact oddRad_G2_split h t htord
    · exact oddRad_G2_qplus h t htord
  · obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hm K hK
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF β
    have hβeq : β = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_entrywiseAdjointAut]
    obtain ⟨hσord, hpm, ⟨h0, hh0⟩, -⟩ :=
      even_G2_noninner_prime_local_core_trivial hm hK hp5 ⊤ le_top ⟨β, Subgroup.mem_top _⟩
        hinn (by rw [Subgroup.orderOf_mk]; exact hβ) x σ hβeq
    obtain ⟨-, hkcard, -, -, -⟩ := even_G2_canonical_field_centralizer_all_orders hm hK σ
    obtain ⟨f₀, hf₀⟩ := hpm
    have hkcard' : Nat.card (fixSubfield σ) = 2 ^ f₀ := by
      rw [hkcard, hσord, hf₀, Nat.mul_div_cancel_left f₀ hp5.pos]
    have hf₀1 : 1 ≤ f₀ := by omega
    have hcg : MulAut.congr (MulAut.conj h0 : adjointGroup .G2 K ≃* adjointGroup .G2 K) β =
        entrywiseAdjointAut .G2 σ := hh0
    rw [← oddRadConcl_congr (MulAut.conj h0 : adjointGroup .G2 K ≃* adjointGroup .G2 K) β, hcg]
    exact oddRadConcl_G2_entrywise σ hf₀1 hkcard'

theorem oddRadAt_smallModel_g2 : OddRadAt (SmallModel .G2) := by
  intro T _ _ _ hS β hβ
  obtain ⟨n, f, hadm, hM, -⟩ := hS
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have hf : 2 ≤ f := two_le_of_admissible_G2 hadm
  exact oddRadConcl_of_mulEquiv e (fun β' hβ' => oddRadConcl_G2 hf hKcard β' hβ') β hβ

end CFSG.RankThree.PartOne.F106
