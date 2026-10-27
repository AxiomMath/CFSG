module

public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cat
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8026Base
public import Certificates.Certificate9

public section

namespace CFSG.Quasithin

namespace F6

section Action

@[expose] noncomputable def mulAutQuotCenter (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun α := QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem mulAutQuotCenter_mk {G : Type*} [Group G] (α : MulAut G) (g : G) :
    mulAutQuotCenter G α (QuotientGroup.mk g) = QuotientGroup.mk (α g) :=
  rfl

@[expose] noncomputable def conjQuotHom (D : Type) [Group D] : D →* MulAut (TwoResidualQuot D) :=
  have := twoResidual_top_normal (D := D)
  (mulAutQuotCenter ↥(twoResidual (⊤ : Subgroup D))).comp MulAut.conjNormal

theorem conjQuotHom_mk {D : Type} [Group D] (x : D) (l : ↥(twoResidual (⊤ : Subgroup D))) :
    ((conjQuotHom D x (QuotientGroup.mk l) : TwoResidualQuot D)) =
      QuotientGroup.mk ⟨x * l * x⁻¹, twoResidual_top_normal.conj_mem _ l.2 x⟩ :=
  rfl

variable {D : Type} [Group D] [Finite D]

theorem ker_conjQuotHom (hS : F618RecogSetting D) :
    (conjQuotHom D).ker = (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))).map
      (twoResidual (⊤ : Subgroup D)).subtype := by
  have := twoResidual_top_normal (D := D)
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  apply le_antisymm
  · intro x hx
    have hcen : ∀ l : ↥L, (⟨x * l * x⁻¹, twoResidual_top_normal.conj_mem _ l.2 x⟩ : ↥L) * l⁻¹ ∈
        Subgroup.center ↥L := by
      intro l
      have h1 := congrArg (fun f : MulAut (TwoResidualQuot D) => f (QuotientGroup.mk l))
        (MonoidHom.mem_ker.mp hx)
      simp only [conjQuotHom_mk, MulAut.one_apply] at h1
      have h2 := QuotientGroup.eq.mp h1
      have h3 : (⟨x * l * x⁻¹, twoResidual_top_normal.conj_mem _ l.2 x⟩ : ↥L) * l⁻¹ =
          l * ((⟨x * l * x⁻¹, twoResidual_top_normal.conj_mem _ l.2 x⟩ : ↥L)⁻¹ * l)⁻¹ * l⁻¹ := by
        group
      rw [h3]
      exact (inferInstance : (Subgroup.center ↥L).Normal).conj_mem _ (Subgroup.inv_mem _ h2) l
    let δ : ↥L →* ↥(Subgroup.center ↥L) :=
      { toFun := fun l => ⟨_, hcen l⟩
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          apply Subtype.ext
          have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen b) a⁻¹)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
          calc x * (↑a * ↑b) * x⁻¹ * (↑a * ↑b)⁻¹
              = x * ↑a * x⁻¹ * ((x * ↑b * x⁻¹ * (↑b)⁻¹) * (↑a)⁻¹) := by group
            _ = x * ↑a * x⁻¹ * ((↑a)⁻¹ * (x * ↑b * x⁻¹ * (↑b)⁻¹)) := by rw [hc]
            _ = x * ↑a * x⁻¹ * (↑a)⁻¹ * (x * ↑b * x⁻¹ * (↑b)⁻¹) := by group }
    have hδ : δ.ker = ⊤ := by
      rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ↥L)]
      exact Abelianization.commutator_subset_ker δ
    have hxC : x ∈ Subgroup.centralizer (L : Set D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : δ ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hδ]
        exact Subgroup.mem_top _
      have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : D)) h1
      simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
        OneMemClass.coe_one] at h2
      calc l * x = x * l * x⁻¹ * l⁻¹ * l * x := by rw [h2, one_mul]
        _ = x * l := by group
    have hxL : x ∈ L := by
      have h := CFSG.centralizer_generalizedFitting_le D
      rw [hS.fitting] at h
      exact h hxC
    refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) l l.2)
  · rintro _ ⟨z, hz, rfl⟩
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [conjQuotHom_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz l)
      simp only [Subgroup.coe_mul] at this
      change (z : D) * l * (z : D)⁻¹ = l
      rw [← this]
      group

theorem card_range_conjQuotHom (hS : F618RecogSetting D) :
    Nat.card (conjQuotHom D).range =
      Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
  have := twoResidual_top_normal (D := D)
  have h1 := (conjQuotHom D).ker.card_mul_index
  rw [Subgroup.index_ker, ker_conjQuotHom hS,
    ← Nat.card_congr ((Subgroup.center ↥(twoResidual (⊤ : Subgroup D))).equivMapOfInjective _
      (twoResidual (⊤ : Subgroup D)).subtype_injective).toEquiv] at h1
  have h2 := (twoResidual (⊤ : Subgroup D)).card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(twoResidual (⊤ : Subgroup D)))
  rw [h3] at h2
  have hpos : 0 < Nat.card ↥(Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) := Nat.card_pos
  have : Nat.card ↥(Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) *
      Nat.card (conjQuotHom D).range = Nat.card ↥(Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) *
      (Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index) := by
    rw [h1, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem card_mul_index_dvd_card_mulAut (hS : F618RecogSetting D) :
    Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index ∣
      Nat.card (MulAut (TwoResidualQuot D)) := by
  rw [← card_range_conjQuotHom hS]
  exact Subgroup.card_subgroup_dvd_card _

theorem index_dvd_of_card_mulAut (hS : F618RecogSetting D) {c : ℕ}
    (hc : Nat.card (MulAut (TwoResidualQuot D)) = c * Nat.card (TwoResidualQuot D)) :
    (twoResidual (⊤ : Subgroup D)).index ∣ c := by
  have h := card_mul_index_dvd_card_mulAut hS
  rw [hc, mul_comm c] at h
  exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp h

theorem nonempty_quotient_mulEquiv_mulAut (hS : F618RecogSetting D)
    (hc : Nat.card (MulAut (TwoResidualQuot D)) =
      Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index) :
    Nonempty (D ⧸ (conjQuotHom D).ker ≃* MulAut (TwoResidualQuot D)) := by
  have hsurj : Function.Surjective (conjQuotHom D) := by
    rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top, card_range_conjQuotHom hS, hc]
  exact ⟨QuotientGroup.quotientKerEquivOfSurjective _ hsurj⟩

end Action

section Aut

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

theorem card_mulAut_alternating_seven :
    Nat.card (MulAut ↥(alternatingGroup (Fin 7))) = 2 * Nat.card ↥(alternatingGroup (Fin 7)) := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num))).toEquiv,
    card_alternating_seven, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem two_mul_card_psl2 (K : Type) [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K)) :
    2 * Nat.card (PSL2 K) = Nat.card (PGL2 K) := by
  rw [psl2_card_formula K hodd, pgl2_card_formula K]
  obtain ⟨p, n, -, hpodd, -, hK⟩ := hodd
  have h2 : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hq : Odd (Nat.card K) := hK ▸ hpodd.pow
    obtain ⟨m, hm⟩ := hq
    rw [hm]
    exact Dvd.dvd.mul_left ⟨2 * m * m + 2 * m, by rw [Nat.sub_eq_of_eq_add]; ring⟩ _
  rw [mul_comm, Nat.div_mul_cancel h2]

theorem card_mulAut_psl2 (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hodd : IsOddPrimePower (Nat.card K)) (h3 : 3 < Nat.card K) :
    Nat.card (MulAut (PSL2 K)) = Nat.card (PGL2 K) * Nat.card (K ≃+* K) := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _ ⟨pGammaL2ToMulAutPSL2_injective K hodd h3,
    pGammaL2ToMulAutPSL2_surjective K hK hodd h3⟩).toEquiv, SemidirectProduct.card]

theorem card_mulAut_psl_two_prime (K : Type) [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hK : Nat.card K = p) :
    Nat.card (MulAut (StatedProj (StatedSL 2 K))) = 2 * Nat.card (StatedProj (StatedSL 2 K)) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have : Subsingleton (K ≃+* K) := CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK
  have : Unique (K ≃+* K) := uniqueOfSubsingleton 1
  have h1 : Nat.card (K ≃+* K) = 1 := Nat.card_unique
  let ε := projectiveSpecialLinearGroupEquivStatedProj 2 K
  rw [← Nat.card_congr (MulAut.congr ε).toEquiv, ← Nat.card_congr ε.toEquiv,
    card_mulAut_psl2 K (p := p) (f := 1) (by rw [hK, pow_one]) hodd (by omega), h1, mul_one,
    two_mul_card_psl2 K hodd]

theorem card_mulAut_psl_two_sq (K : Type) [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) :
    Nat.card (MulAut (StatedProj (StatedSL 2 K))) = 4 * Nat.card (StatedProj (StatedSL 2 K)) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp.out, hp.out.odd_of_ne_two hp2, by norm_num, hK⟩
  have h3 : 3 < Nat.card K := by
    rw [hK]
    have := hp.out.two_le
    nlinarith
  have : Fintype K := Fintype.ofFinite K
  have hAut := (CFSG.Quasithin.EmptyFaithfulMultiple.L15422.card_ringEquiv_eq_two
    (K := K) (p := p) (by rw [← Nat.card_eq_fintype_card, hK])).1
  let ε := projectiveSpecialLinearGroupEquivStatedProj 2 K
  rw [← Nat.card_congr (MulAut.congr ε).toEquiv, ← Nat.card_congr ε.toEquiv,
    card_mulAut_psl2 K hK hodd h3, hAut, ← two_mul_card_psl2 K hodd]
  ring

end Aut

end F6

end CFSG.Quasithin
