module

public import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPSL
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLin
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSp
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinFixedOmega

public section
namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.ClassicalPosition
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial


theorem card_eq_two_of_guarded_component_of_linearBlock
    {G E : Type} [Group G] [Field E] [Finite E] [CharP E 2]
    {H C : Subgroup G} {m : ℕ} (e : H ≃* GL (Fin m) E)
    (hC : IsComponentOf C H)
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    Nat.card E = 2 := by
  obtain ⟨f, hf, hcard, hlabel, -⟩ :=
    exists_linear_label_of_isComponentOf_iso_generalLinear e hC
  have hm : 2 ≤ m := by
    have hr : 1 ≤ m - 1 := hlabel.2.1
    omega
  have hmf : m = 2 → 2 ≤ f := by
    intro hm2
    subst m
    exact hlabel.2.2 rfl
  have hadm : StatedLieAdmissible .PSL m 2 f := by
    refine ⟨Nat.prime_two, hf, hm, ?_, ?_⟩
    · intro heq
      have hm2 : m = 2 := (Prod.mk.inj heq).1
      have hpow : 2 ^ f = 2 := (Prod.mk.inj heq).2
      have h4 : 4 ≤ 2 ^ f := by
        exact (show 4 = 2 ^ 2 by norm_num).le.trans
          (Nat.pow_le_pow_right (by norm_num) (hmf hm2))
      omega
    · intro heq
      have hpow : 2 ^ f = 3 := (Prod.mk.inj heq).2
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      rw [hpow] at h2
      norm_num at h2
  let ec : C ≃* Matrix.SpecialLinearGroup (Fin m) E :=
    (componentEquivStatedSLOfMulEquiv e hC).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm
  have hmodel : LieModel (C ⧸ Subgroup.center C) .PSL m 2 f :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.lieModel_centerQuotient_of_equiv_SL_c2
      hadm hcard ec
  obtain ⟨lab, -, R, _, I, F0, theta, -, -, hguard, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hmark
  have hmarkedC : MarkedModel lab (C ⧸ Subgroup.center C) :=
    MarkedModel.of_mulEquiv theta.symm hmarked
  have hf1 : f = 1 := (guarded_lieModel_PSL hguard hmarkedC hmodel).1
  simpa [hf1] using hcard

theorem false_of_guarded_component_of_pairedOmegaBlock
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ CFSG.Open.StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε e e' : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e')
    {C : Subgroup ↥(CFSG.Open.StatedOmega ⇑Φ)}
    (hC : IsComponentOf C
      ⁅glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε,
        glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε⁆)
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    False := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε
  have hcomm : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hCH : C ≤ H := hC.1.trans hcomm
  have hCo : IsComponentOf (C.subgroupOf H) ⊤ :=
    RCKRP.rckIsComponentOf_top_of_commutator hC
  have hmark' : LargeEvenMarking (C.subgroupOf H)
      (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
    largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCH) hmark
  obtain ⟨d, m, E, hfield, hfin, hd, hcardE, -, hdeg, ⟨eH⟩⟩ :=
    blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hε he he' hne hεe
  letI : Field E := hfield
  letI : Fintype E := hfin
  obtain ⟨f, -, hcardK⟩ := FiniteField.card K 2
  have hcardE2 : Fintype.card E = 2 ^ ((f : ℕ) * d) := by
    rw [hcardE, hcardK, ← pow_mul]
  letI : CharP E 2 := charP_of_card_eq_prime_pow hcardE2
  have hE2 : Fintype.card E = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      card_eq_two_of_guarded_component_of_linearBlock
        ((Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).trans eH) hCo hmark'
  have hK2 : Fintype.card K = 2 := by
    have hle : Fintype.card K ≤ Fintype.card K ^ d := Nat.le_self_pow (by omega) _
    have hlt : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  have hd1 : d = 1 := by
    have hp : 2 ^ d = 2 := by simpa [hK2, hE2] using hcardE.symm
    by_contra h
    have hge : 2 ≤ d := by omega
    have h4 : 4 ≤ 2 ^ d := by
      exact (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by norm_num) hge)
    omega
  let x := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b
  have hx : OddOrderIsometry Φ (orderOf b) x := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hsq : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b]
    exact hx.squarefree_minpoly
  obtain ⟨a, ha, hae⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq he
  obtain ⟨a', ha', ha'e⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq he'
  have hax : a ∈ primaryFactors x.toLinearMap := by
    simpa [x, ggOmegaBlk_toLinEquiv_toLinearMap] using ha
  have ha'x : a' ∈ primaryFactors x.toLinearMap := by
    simpa [x, ggOmegaBlk_toLinEquiv_toLinearMap] using ha'
  have haex : Matrix.toLinAlgEquiv' e = primaryProjection x.toLinearMap a := by
    simpa [x, ggOmegaBlk_toLinEquiv_toLinearMap] using hae
  have ha'ex : Matrix.toLinAlgEquiv' e' = primaryProjection x.toLinearMap a' := by
    simpa [x, ggOmegaBlk_toLinEquiv_toLinearMap] using ha'e
  have hrec := paired_prim_idem_primary_reciprocal Φ hΦ b hx hax ha'x haex ha'ex
    hεe hne hε he he'
  have ha1 : a.natDegree = 1 := by
    have heqa := blockDegree_eq_natDegree_of_primaryProjection b hsq ha hae
    omega
  have hcoef : a.coeff 0 = 1 := by
    simpa [hK2] using FiniteField.pow_card_sub_one_eq_one (a.coeff 0) (hx.coeff_zero_ne hax)
  have hneg : (-1 : K) = 1 := by
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [one_add_one_eq_two] using htwo
  have haX : a = X - 1 := by
    rw [(monic_of_mem_primaryFactors ha).eq_X_add_C ha1, hcoef]
    calc
      (X : K[X]) + Polynomial.C (1 : K) = X - Polynomial.C (-1 : K) := by
        rw [C_neg, sub_neg_eq_add]
      _ = X - (1 : K[X]) := by rw [hneg, C_1]
  apply hrec.2
  rw [haX, reciprocalPolynomial_X_sub_one]


theorem fixed_omega_block_of_guarded_component
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ CFSG.Open.StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {C : Subgroup ↥(CFSG.Open.StatedOmega ⇑Φ)}
    (hC : IsComponentOf C
      ⁅glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε,
        glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε⁆)
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    (b : Matrix ι ι K) * ε = ε := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hM : IsUnit M.det := TableC.polarGram_isUnit_det Φ hΦ
  have hMt : Matrix.transpose M = M := TableC.polarGram_transpose Φ
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    have hs0 := Set.mem_singleton_iff.mp hs
    have hs1 := Set.mem_singleton_iff.mp hs'
    subst s
    subst s'
    exact Commute.refl b
  have hSU : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (s : Matrix ι ι K) * M * (s : Matrix ι ι K) = M := by
    intro s hs
    have hs0 := Set.mem_singleton_iff.mp hs
    subst s
    have hg : ∀ v : ι → K, Φ (Matrix.mulVec (b : Matrix ι ι K) v) = Φ v :=
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega hb
    have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
    simpa [M, Matrix.map_id,
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h
  have hSUmap : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * M *
        (s : Matrix ι ι K) = M := by
    simpa [Matrix.map_id] using hSU
  obtain ⟨e, he, heε, hcases⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn
    (RingHom.id K) (fun _ => rfl) hM (by simpa [Matrix.map_id] using hMt) hS hSUmap hε
  rcases hcases with heq | ⟨hneε, -, -⟩
  · subst e
    by_contra h1
    let H := glBlockCentralizer (CFSG.Open.StatedOmega ⇑Φ).subtype {b} ε
    have hcomm : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb =>
      H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    have hCH : C ≤ H := hC.1.trans hcomm
    have hCo : IsComponentOf (C.subgroupOf H) ⊤ :=
      RCKRP.rckIsComponentOf_top_of_commutator hC
    have hmark' : LargeEvenMarking (C.subgroupOf H)
        (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
      largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCH) hmark
    obtain ⟨d, m, E, hfield, hfin, -, hcardE, -, -, ⟨eH⟩⟩ :=
      blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hε he h1
    letI : Field E := hfield
    letI : Fintype E := hfin
    obtain ⟨f, -, hcardK⟩ := FiniteField.card K 2
    have hEpow : Fintype.card E = 2 ^ ((f : ℕ) * d * 2) := by
      simpa only [hcardK, ← pow_mul, Nat.mul_assoc] using hcardE
    letI : CharP E 2 := charP_of_card_eq_prime_pow hEpow
    have hEnat : Nat.card E = (Fintype.card K ^ d) ^ 2 := by
      rw [Nat.card_eq_fintype_card]
      exact hcardE
    obtain ⟨lab, hΛ, hh, R, _, I, F0, theta, hguard⟩ :=
      largeEvenMarking_exists_hasLabel hmark'
    exact hguard.false_of_component_iso_unitaryFull hΛ hh hEnat
      ((Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).trans eH) hCo
  · rcases TableC.isPrimIdemIn_cases hM hMt hS hSU hε he heε with
      heq | ⟨-, e', he', hne, hεe⟩
    · exact (hneε heq).elim
    · exact (false_of_guarded_component_of_pairedOmegaBlock Φ hΦ h8 b hb hodd
        hε he he' hne hεe hC hmark).elim

theorem omega_block_facts_of_guarded_component
    {U ι K : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (j : U →* GL ι K) (hj : Function.Injective j) (hr : j.range = CFSG.Open.StatedOmega ⇑Φ)
    (z : U) (hodd : Odd (orderOf z)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({j z} : Set (GL ι K)))) ε)
    {C : Subgroup U}
    (hC : IsComponentOf C ⁅glBlockCentralizer j {j z} ε, glBlockCentralizer j {j z} ε⁆)
    (hmark : LargeEvenMarking C (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({j z} : Set (GL ι K)))) ε ∧
      (j z : Matrix ι ι K) * ε = ε ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({j z} : Set (GL ι K)))) ε = 1 ∧
      8 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
  classical
  let Ω := CFSG.Open.StatedOmega ⇑Φ
  let phi : U →* Ω := j.codRestrict Ω (by
    intro u
    change j u ∈ CFSG.Open.StatedOmega ⇑Φ
    rw [← hr]
    exact ⟨u, rfl⟩)
  have hphi : Function.Injective phi := by
    intro u v huv
    exact hj (congrArg Subtype.val huv)
  have hsurj : Function.Surjective phi := by
    intro y
    have hy : (y : GL ι K) ∈ j.range := hr.symm ▸ y.2
    obtain ⟨u, hu⟩ := hy
    exact ⟨u, Subtype.ext hu⟩
  have hcomp : Ω.subtype.comp phi = j := by
    ext u
    rfl
  let H := glBlockCentralizer j {j z} ε
  let H' := glBlockCentralizer Ω.subtype {j z} ε
  have hcomap : H'.comap phi = H := by
    change ((Subgroup.centralizer {j z} ⊓ glFixing (1 - ε)).comap Ω.subtype).comap phi =
      (Subgroup.centralizer {j z} ⊓ glFixing (1 - ε)).comap j
    rw [Subgroup.comap_comap, hcomp]
  have hmap : H.map phi = H' := by
    rw [← hcomap, Subgroup.map_comap_eq, MonoidHom.range_eq_top.2 hsurj]
    simp
  have hC' : IsComponentOf (C.map phi) ⁅H', H'⁆ := by
    have hm := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hphi).2 hC
    rwa [Subgroup.map_commutator, hmap] at hm
  have hmark' : LargeEvenMarking (C.map phi)
      (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
    largeEvenMarking_of_mulEquiv (Subgroup.equivMapOfInjective C phi hphi).symm hmark
  have hb : j z ∈ CFSG.Open.StatedOmega ⇑Φ := hr ▸ (show j z ∈ j.range from ⟨z, rfl⟩)
  have hodd' : Odd (orderOf (j z)) := by
    simpa only [orderOf_injective j hj z] using hodd
  have hfix := fixed_omega_block_of_guarded_component Φ hΦ h8 (j z) hb hodd' hε hC' hmark'
  have hdim := eight_le_finrank_of_guarded_fixed_omega_block Φ hΦ h8 (j z) hb hodd'
    hε hfix hC' hmark'
  obtain ⟨hprim, hdegree⟩ := isPrimIdemIn_and_blockDegree_eq_one_of_mul_eq_self (j z)
    hε.1 hε.2.1 hε.2.2.1 hfix
  exact ⟨hprim, hfix, hdegree, hdim⟩

end CFSG.StandardType.ClassicalBlocks
