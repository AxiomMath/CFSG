module

public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.RankThree.PartOne.S11d.OutOrthogonal
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec19.Step1919O2

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)

namespace Step1919EndProof

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_pCoreOf {K : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hx : x ∈ CFSG.Open.pCoreOf 2 K) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x, hx⟩
  exact eq_one_of_pow_two_pow_of_pow_three_pow (j := j) (k := 1)
    (by simpa using congrArg Subtype.val hj) (by rw [pow_one]; exact hx3)

theorem not_three_dvd_card_pCore (K : Subgroup G) : ¬ 3 ∣ Nat.card (CFSG.pCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  rw [hk]
  intro h
  have := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at this

omit [Finite G] in
theorem mk_mem_center_of {K : Subgroup G} (x : K)
    (h : ∀ k : K, (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    (x : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  induction g using QuotientGroup.induction_on with
  | H k =>
    have h1 : x * k * x⁻¹ * k⁻¹ ∈ CFSG.pCore 2 K := by
      rw [Step1911EndProof.mem_pCore_iff]
      exact h k
    have h2 : ((x * k * x⁻¹ * k⁻¹ : K) : K ⧸ CFSG.pCore 2 K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (by rw [commutatorElement_def]; exact h2)).symm

theorem card_starIm {K E : Subgroup G} (hE3 : IsPGroup 3 E) (hEK : E ≤ K) :
    Nat.card (starIm K E) = Nat.card E := by
  have h3 : IsPGroup 3 (E.subgroupOf K) := hE3.comap_subtype
  rw [starIm, Step198DProof.card_map_of_injOn _
      (Sec12.injOn_mk_of_coprime _ (not_three_dvd_card_pCore K) h3),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]

omit [Finite G] in
theorem isElemAbelian_starIm {K E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (starIm K E) :=
  CFSG.SectionRank.isElemAbelian_map (Step198DProof.isElemAbelian_subgroupOf hE K) _

end Quotient

section Ranks

theorem card_le_nine_of_SL {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hexp : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F) :=
    Matrix.SpecialLinearGroup.toGL_injective
  set B' := B.map (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F) with hB'
  have : Finite B' := Finite.of_equiv B (B.equivMapOfInjective _ hinj).toEquiv
  have h3' : ((3 : ℕ) : F) ≠ 0 := by exact_mod_cast h3
  have h := CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl Nat.prime_three h3' (by simp) B'
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact x.2)
  rwa [hB', Subgroup.card_map_of_injective hinj] at h

theorem pRank_three_SL_le {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) fun B _ hB => ?_
  exact card_le_nine_of_SL h3 B
    (fun x hx y hy => congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hB.2 x hx)

theorem three_ne_zero_of_charTwo {F : Type} [Field F] [CharP F 2] : (3 : F) ≠ 0 := by
  have h := CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo (F := F) Nat.prime_three
    (by norm_num)
  exact_mod_cast h

theorem center_eq_bot_of_isList194
    {X : Type} [Group X] [Finite X] (hX : IsList194 X) (hperf : Group.IsPerfect X)
    (h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  obtain ⟨n, -, ⟨e⟩⟩ := Step1911EndProof.exists_mulEquiv_SL_of_isList194 hX hperf hz hz1
  have h2 := pRank_three_SL_le (F := GaloisField 2 n) three_ne_zero_of_charTwo
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h2
  omega

theorem center_eq_bot_of_isList194_wide
    {X : Type} [Group X] [Finite X] (hX : IsList194 X ∨ IsSmall194 X) (hperf : Group.IsPerfect X)
    (h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : Subgroup.center X = ⊥ := by
  rcases hX with hX | hX
  · exact center_eq_bot_of_isList194 hX hperf h3
  · exact Step1911EndProof.center_eq_bot_of_isSmall194 hX hperf

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem pRank_three_le_of_mulEquiv_projSU {X : Type} [Group X] [Finite X]
    (e : X ≃* projSU 3 3 1) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hF' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [hF]
    norm_num
  let e₀ : X ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 3 (GaloisField 3 (2 * 1))) :=
    e.trans ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSU_eq_projSU 3 3 1))).symm
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 3 (GaloisField 3 (2 * 1))))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₀
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 3 (GaloisField 3 (2 * 1))))) =
      CFSG.Open.pRank 3
        (⊤ : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 3 (GaloisField 3 (2 * 1)))) :=
    CFSG.SectionRank.pRank_quotient_eq _ (by
      rw [LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF,
        Subgroup.card_bot]
      norm_num)
  have h3 : CFSG.Open.pRank 3
        (⊤ : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 3 (GaloisField 3 (2 * 1)))) =
      CFSG.Open.pRank 3
        (⊤ : Subgroup (SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3)) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (equivStatedSU hF' 3)).symm
  rw [h1, h2, h3]
  exact CFSG.RankThree.PartTwo.Census.pRank_three_SU_three_le hF

theorem false_of_isSmall194 {X : Type} [Group X] [Finite X] (hX : IsSmall194 X)
    (h27 : 27 ∣ Nat.card X) (h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : False := by
  rcases hX with h | h <;> obtain ⟨e⟩ := h
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h27
    exact absurd h27 (by decide)
  · have h2 := pRank_three_le_of_mulEquiv_projSU e
    omega

end Ranks

section Count

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem {M K E : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (hEK : E ≤ K)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEne : E ≠ ⊥)
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) {x : G} (hxM : x ∈ M)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hKx := Sec18.map_conj_mem_oTwoComponentsIn hK hxM
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hey : x⁻¹ * e * x ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hxE (x⁻¹ * e * x)).mpr
      (by rw [show x * (x⁻¹ * e * x) * x⁻¹ = e by group]; exact he)
  have heKx : e ∈ K.map (MulAut.conj x).toMonoidHom :=
    ⟨x⁻¹ * e * x, hEK hey, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hc : ((⟨e, hEK he⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    refine mk_mem_center_of _ fun k => ?_
    have h1 := Step1910Proof.commutator_mem_pCoreOf hKx hK hne heKx k.2
    have h2 : e * k * e⁻¹ * (k : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (hEK he) k.2) (K.inv_mem (hEK he))) (K.inv_mem k.2)
    exact Step1910Proof.inf_pCoreOf_le hK ⟨h2, h1⟩
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Step1911EndProof.mem_pCore_iff] at hc
  exact he1' (eq_one_of_mem_pCoreOf (hE3 e he) hc)

theorem card_mul_card_range_dvd {K E Y : Subgroup G} (hEK : E ≤ K) (hEY : E ≤ Y)
    (hYE : Y ≤ Subgroup.normalizer (E : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hEc : IsMulCommutative E) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) :
    Nat.card E * Nat.card (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range ∣
      Nat.card (Step1910Proof.quotAct hYK).range := by
  set ψ := E.normalizerMonoidHom.comp (Subgroup.inclusion hYE) with hψ
  set ρ := Step1910Proof.quotAct hYK with hρ
  have hψapp : ∀ (y : Y) (e : E), ((ψ y e : E) : G) = y * e * (y : G)⁻¹ := fun y e => rfl
  have hker : ρ.ker ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hψapp, MulAut.one_apply]
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hYK y ⟨e, hEK e.2⟩
    rw [hy, MulAut.one_apply] at hact
    have h1 : j'⁻¹ * ⟨e, hEK e.2⟩ ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hact.symm
    rw [Step1911EndProof.mem_pCore_iff] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hj'] at h1
    have hyeE : (y : G) * e * (y : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hYE y.2) e).mp e.2
    have h2 := eq_one_of_mem_pCoreOf (hE3 _ (E.mul_mem (E.inv_mem hyeE) e.2)) h1
    rw [inv_mul_eq_one] at h2
    exact h2
  have hEker : E.subgroupOf Y ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hψapp, MulAut.one_apply]
    have h1 : (y : G) * e = e * y :=
      congrArg Subtype.val (hEc.is_comm.comm ⟨y, Subgroup.mem_subgroupOf.mp hy⟩ e)
    rw [h1, mul_inv_cancel_right]
  have hdisj : ρ.ker ⊓ E.subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hyy
    obtain ⟨hy, hyE⟩ := Subgroup.mem_inf.mp hyy
    rw [MonoidHom.mem_ker] at hy
    have hyE' : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hyE
    have hc : ((⟨y, hEK hyE'⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈
        Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hYK y k
        rw [hy, MulAut.one_apply] at hact
        have hj'eq : j' = ⟨y, hEK hyE'⟩ * k * (⟨y, hEK hyE'⟩ : K)⁻¹ :=
          Subtype.ext (by rw [hj']; rfl)
        rw [hj'eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          eq_mul_inv_iff_mul_eq] at hact
        exact hact
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Step1911EndProof.mem_pCore_iff] at hc
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_pCoreOf (hE3 _ hyE') hc)
  have hsup := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer
    (N := ρ.ker) (H := E.subgroupOf Y)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker ρ)]; exact le_top) hdisj
  have hEY' : Nat.card (E.subgroupOf Y) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv
  have hdvd : Nat.card ρ.ker * Nat.card E ∣ Nat.card ψ.ker := by
    rw [← hEY', ← hsup]
    exact Subgroup.card_dvd_of_le (sup_le hker hEker)
  have h1 : Nat.card ρ.ker * Nat.card ρ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ρ.ker)) ?_⟩
  rw [h1, ← h2, hm]
  ring

end Count

section Orders

theorem not_pow_six_dvd_mul {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : ¬ 3 ^ 2 ∣ a)
    (hb : ¬ 3 ^ 5 ∣ b) : ¬ 3 ^ 6 ∣ a * b := by
  intro h
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (mul_ne_zero ha0 hb0),
    Nat.factorization_mul ha0 hb0, Finsupp.add_apply] at h
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three ha0] at ha
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hb0] at hb
  omega

theorem not_dvd_card_mulAut {X : Type} [Group X] [Finite X] (hX : ¬ 3 ^ 5 ∣ Nat.card X)
    (hOut : ¬ 9 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    ¬ 3 ^ 6 ∣ Nat.card (MulAut X) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)]
  exact not_pow_six_dvd_mul Nat.card_pos.ne' Nat.card_pos.ne' hOut
    fun h => hX (h.trans (Subgroup.card_range_dvd (MulAut.conj : X →* MulAut X)))

theorem not_dvd_card_mulAut_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y] (e : Y ≃* X)
    (hX : ¬ 3 ^ 5 ∣ Nat.card X)
    (hOut : ¬ 9 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    ¬ 3 ^ 6 ∣ Nat.card (MulAut Y) :=
  not_dvd_card_mulAut (by rwa [Nat.card_congr e.toEquiv]) (by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv])

theorem two_hundred_sixteen_dvd_card {V : Type*} [Group V] {X : Subgroup V}
    (h : Sec4.IsExtOf (oUpperThreePrime X) (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) : 216 ∣ Nat.card X := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcard : Nat.card (oUpperThreePrime X) = 216 := by
    rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eN.toEquiv, Nat.card_prod, hSL]
    simp
  rw [← hcard]
  exact Subgroup.card_dvd_of_le ((Subgroup.closure_le _).mpr fun σ hσ => hσ.1)

end Orders

section Outer

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal)
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem card_ringEquiv_le (K : Type) [Field K] [Finite K] :
    Nat.card (K ≃+* K) ≤ Nat.card K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine Nat.card_le_card_of_injective (fun φ : K ≃+* K => φ (g : K)) fun φ ψ h => ?_
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 x hx))
    have hxk : x = (g : K) ^ k := by
      rw [← Units.val_zpow_eq_zpow_val, hk, Units.val_mk0]
    have h' : φ (g : K) = ψ (g : K) := h
    rw [hxk, map_zpow₀, map_zpow₀, h']

theorem finite_ringEquiv (K : Type) [Field K] [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem conjAut_scalar {n : ℕ} {K : Type} [Field K] (u : Kˣ) :
    LinearFlag.conjAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) u) = 1 := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K x
  rw [LinearFlag.conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  have hcomm := Subgroup.mem_center_iff.mp hc (Matrix.SpecialLinearGroup.toGL g)
  rw [LinearFlag.coe_slConjugation, ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix g,
    ← Units.val_mul, ← Units.val_mul, ← hcomm, mul_inv_cancel_right]

theorem conjAut_mem_inner {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : (Nat.card Kˣ).Coprime n) (A : GL (Fin n) K) :
    LinearFlag.conjAut n K A ∈ inner (LinearFlag.projectiveSL n K) := by
  set u := (powCoprime hn).symm (Matrix.GeneralLinearGroup.det A) with hu
  have hun : u ^ n = Matrix.GeneralLinearGroup.det A := by
    rw [← powCoprime_apply hn, hu, Equiv.apply_symm_apply]
  set B := A * Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹ with hB
  have hdet : Matrix.GeneralLinearGroup.det B = 1 := by
    have hs : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹ : GL (Fin n) K) = u⁻¹ ^ n := by
      ext
      simp
    rw [hB, map_mul, hs, inv_pow, hun, mul_inv_cancel]
  have hdet' : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg Units.val hdet
    simpa using this
  set g : Matrix.SpecialLinearGroup (Fin n) K := ⟨(B : Matrix (Fin n) (Fin n) K), hdet'⟩ with hg
  have hBA : A = Matrix.SpecialLinearGroup.toGL g * Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    have h1 : Matrix.SpecialLinearGroup.toGL g = B := by
      ext
      rfl
    rw [h1, hB, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  refine ⟨LinearFlag.proj n K g, ?_⟩
  rw [KFacts.conj_proj_eq_conjAut, hBA, map_mul, conjAut_scalar, mul_one]

theorem card_outer_projectiveSL_le {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (hinn : ∀ A : GL (Fin n) K, LinearFlag.conjAut n K A ∈ inner (LinearFlag.projectiveSL n K)) :
    Nat.card (Outer (LinearFlag.projectiveSL n K)) ≤ Nat.card (K ≃+* K) * 2 := by
  have := finite_ringEquiv K
  have hsurj : Function.Surjective fun p : (K ≃+* K) × Fin 2 =>
      ((LinearFlag.fieldAut n K p.1 * LinearFlag.dualAut n K ^ (p.2 : ℕ) :
        MulAut (LinearFlag.projectiveSL n K)) : Outer (LinearFlag.projectiveSL n K)) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, σ, ε, hε, hα⟩ := (LinearFlag.automorphism_generation hn).2 α
    refine ⟨(σ, ⟨ε, by omega⟩), ?_⟩
    rw [hα]
    refine QuotientGroup.eq.mpr ?_
    have := (inner_normal _).conj_mem _ (hinn A)
      (LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K ^ ε)⁻¹
    convert this using 1
    group
  calc Nat.card (Outer (LinearFlag.projectiveSL n K)) ≤ Nat.card ((K ≃+* K) × Fin 2) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card (K ≃+* K) * 2 := by rw [Nat.card_prod, Nat.card_fin]

theorem not_nine_dvd_card_outer_projSL {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hcop : (2 ^ e - 1).Coprime n) :
    ¬ 9 ∣ Nat.card (Outer (projSL n (GaloisField 2 e))) := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (Sec4.projSLEquivProjectiveSL n (GaloisField 2 e))).toEquiv]
  have hcK : Nat.card (GaloisField 2 e)ˣ = 2 ^ e - 1 := by
    rw [Nat.card_units, GaloisField.card 2 e (by omega)]
  have h1 := card_outer_projectiveSL_le hn fun A => conjAut_mem_inner (hcK ▸ hcop) A
  have h2 := card_ringEquiv_le (GaloisField 2 e)
  rw [GaloisField.card 2 e (by omega)] at h2
  have h3 : 2 ^ e ≤ 4 := (Nat.pow_le_pow_right (by norm_num) he2).trans (by norm_num)
  have hpos : 0 < Nat.card (Outer (LinearFlag.projectiveSL n (GaloisField 2 e))) := Nat.card_pos
  intro h9
  have h4 := Nat.le_of_dvd hpos h9
  omega

theorem conjAut_sp_mem_inner {r : ℕ} [NeZero r] {K : Type} [Field K]
    (A : SymplecticHigher.gsp r K) (hm : SymplecticHigher.multiplier r K A = 1) :
    SymplecticHigher.conjAut r K A ∈ inner (StatedProj (StatedSp r K)) := by
  have hA : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    have h1 : A ∈ (SymplecticHigher.multiplier r K).ker := hm
    rw [SymplecticHigher.ker_multiplier] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨SymplecticFlag.proj r K ⟨A, hA⟩, ?_⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) x
  rw [MulAut.conj_apply, SymplecticHigher.conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem card_outer_statedSp_le {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r)
    (hK : Nat.card Kˣ = 1) :
    Nat.card (Outer (StatedProj (StatedSp r K))) ≤ Nat.card (K ≃+* K) := by
  have : NeZero r := ⟨by omega⟩
  have := finite_ringEquiv K
  refine Nat.card_le_card_of_surjective (fun σ : K ≃+* K =>
    ((SymplecticHigher.fieldAut r K σ : MulAut (StatedProj (StatedSp r K))) :
      Outer (StatedProj (StatedSp r K)))) fun x => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨A, σ, hα⟩ := (SymplecticHigher.automorphism_generation hr).2 α
  refine ⟨σ, ?_⟩
  rw [hα]
  refine QuotientGroup.eq.mpr ?_
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hK).1
  have := (inner_normal _).conj_mem _ (conjAut_sp_mem_inner A (Subsingleton.elim _ _))
    (SymplecticHigher.fieldAut r K σ)⁻¹
  convert this using 1
  group

theorem not_nine_dvd_card_outer_projSp :
    ¬ 9 ∣ Nat.card (Outer (projSp 3 (GaloisField 2 1))) := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (Sec4.projSpEquivStatedProj 3 (GaloisField 2 1))).toEquiv]
  have hK : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, GaloisField.card 2 1 one_ne_zero]
    norm_num
  have h1 := card_outer_statedSp_le (r := 3) le_rfl hK
  have h2 := card_ringEquiv_le (GaloisField 2 1)
  rw [GaloisField.card 2 1 one_ne_zero] at h2
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp 3 (GaloisField 2 1)))) := Nat.card_pos
  intro h9
  have h4 := Nat.le_of_dvd hpos h9
  omega

theorem card_outer_psp_two_le {K : Type} [Field K] [Finite K] (hodd : ringChar K ≠ 2) :
    Nat.card (Outer (StatedProj (StatedSp 2 K))) ≤ Nat.card Kˣ * Nat.card (K ≃+* K) := by
  classical
  have := finite_ringEquiv K
  let rep : Kˣ → SymplecticHigher.gsp 2 K := Function.invFun (SymplecticHigher.multiplier 2 K)
  have hsurj : Function.Surjective fun p : Kˣ × (K ≃+* K) =>
      ((SymplecticHigher.conjAut 2 K (rep p.1) * SymplecticHigher.fieldAut 2 K p.2 :
        MulAut (StatedProj (StatedSp 2 K))) : Outer (StatedProj (StatedSp 2 K))) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, σ, hα⟩ := KFacts.psp4_odd_automorphism_normal_form hodd α
    refine ⟨(SymplecticHigher.multiplier 2 K A, σ), ?_⟩
    have hrep : SymplecticHigher.multiplier 2 K (rep (SymplecticHigher.multiplier 2 K A)) =
        SymplecticHigher.multiplier 2 K A := Function.invFun_eq ⟨A, rfl⟩
    have hm : SymplecticHigher.multiplier 2 K
        ((rep (SymplecticHigher.multiplier 2 K A))⁻¹ * A) = 1 := by
      rw [map_mul, map_inv, hrep, inv_mul_cancel]
    have hinn := (inner_normal _).conj_mem _ (conjAut_sp_mem_inner _ hm)
      (SymplecticHigher.fieldAut 2 K σ)⁻¹
    rw [hα]
    refine QuotientGroup.eq.mpr ?_
    convert hinn using 1
    rw [map_mul, map_inv]
    group
  calc Nat.card (Outer (StatedProj (StatedSp 2 K))) ≤ Nat.card (Kˣ × (K ≃+* K)) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card Kˣ * Nat.card (K ≃+* K) := Nat.card_prod _ _

theorem ringChar_ne_two_of_card_eq_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    ringChar K ≠ 2 := by
  intro h2
  have h0 : ((2 : ℕ) : K) = 0 := (ringChar.spec K 2).mpr (by rw [h2])
  have h1 : addOrderOf (1 : K) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by
    rw [nsmul_eq_mul, mul_one]
    exact_mod_cast h0)
  have h3 : addOrderOf (1 : K) ∣ 3 := hK ▸ addOrderOf_dvd_natCard (1 : K)
  have h4 : addOrderOf (1 : K) = 1 := Nat.dvd_one.mp (by
    have := Nat.dvd_gcd h1 h3
    rwa [show Nat.gcd 2 3 = 1 by norm_num] at this)
  exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h4)

theorem not_nine_dvd_card_outer_projSU_four_two :
    ¬ 9 ∣ Nat.card (Outer (projSU 4 2 1)) := by
  have e₀ : projSU 4 2 1 ≃* StatedProj (StatedSU 4 (2 ^ 1) (GaloisField 2 (2 * 1))) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 2 1))).symm
  have hSU : StatedClassicalModel (projSU 4 2 1) .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, GaloisField 2 (2 * 1), inferInstance,
      inferInstance, by rw [GaloisField.card 2 (2 * 1) (by norm_num)]; norm_num, ⟨e₀⟩⟩
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hSU
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e₁).toEquiv]
  have h1 := card_outer_psp_two_le (ringChar_ne_two_of_card_eq_three hK3)
  have h2 := card_ringEquiv_le K
  rw [Nat.card_units, hK3] at h1
  rw [hK3] at h2
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp 2 K))) := Nat.card_pos
  intro h9
  have h4 := Nat.le_of_dvd hpos h9
  have h5 : Nat.card (Outer (StatedProj (StatedSp 2 K))) ≤ 6 :=
    h1.trans (by simpa using Nat.mul_le_mul_left 2 h2)
  omega

theorem subsingleton_ringEquiv_of_card_units {K : Type} [Field K] (hK : Nat.card Kˣ = 1) :
    Subsingleton (K ≃+* K) := by
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hK).1
  refine ⟨fun φ ψ => RingEquiv.ext fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have hx1 : x = 1 := by
      simpa using congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)
    rw [hx1, map_one, map_one]

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData in
theorem not_nine_dvd_card_outer_projOmegaMinus {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ¬ 9 ∣ Nat.card (Outer (projOmegaMinus 3 (GaloisField 2 1) b c)) := by
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have e₀ : projOmegaMinus 3 (GaloisField 2 1) b c ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) b c)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c))).symm
  have hmod : StatedClassicalModel (projOmegaMinus 3 (GaloisField 2 1) b c) .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, GaloisField 2 1, inferInstance, inferInstance, hK, b, c, hbc,
      ⟨e₀⟩⟩
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hmod (GaloisField 2 1) hK b c hbc e₀
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus
    (GaloisField 2 1) 4 le_rfl b c hbc
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hsub : Subsingleton (GaloisField 2 1 ≃+* GaloisField 2 1) :=
    subsingleton_ringEquiv_of_card_units (by rw [Nat.card_units, hK]; norm_num)
  have hsq : ∀ α : MulAut (matrixProjectiveDerived
      (coordinateQuadMinus 4 (GaloisField 2 1) (by omega) b c)),
      α ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
    intro α
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ α).mp (htop ▸ Subgroup.mem_top α)
    have hlin : g ∈ linearSimilarityPairs _ := by
      rw [mem_linearSimilarityPairs_iff]
      exact Subsingleton.elim _ _
    exact CFSG.RankThree.PartOne.OutStructure.orthD_sq_mem_inner _ hQ hnd hT
      ((CFSG.RankThree.PartOne.OutStructure.mem_orthD_iff _ α).mpr ⟨⟨g, hlin⟩, hg⟩)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (coordinateMinusWitnessEquiv (GaloisField 2 1) (by omega) b c e₀)).toEquiv]
  intro h9
  have h3 : 3 ∣ Nat.card (Outer (matrixProjectiveDerived
      (coordinateQuadMinus 4 (GaloisField 2 1) (by omega) b c))) :=
    (by norm_num : 3 ∣ 9).trans h9
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  have hx2 : ((α : Outer (matrixProjectiveDerived
      (coordinateQuadMinus 4 (GaloisField 2 1) (by omega) b c)))) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq α
  have h1 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h1
  norm_num at h1

end Outer

end Step1919EndProof

@[expose] def KS1919U48 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 4 2 3) →
    ∀ P : Subgroup X, IsProperParabolic P → ∀ B : Subgroup X, B ≤ P →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) → Nat.card B ≤ 9

@[expose] def KS1919G2P : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Sec8.IsoGTwoEven X n →
    ∀ P : Subgroup X, IsProperParabolic P → ∀ B : Subgroup X, B ≤ P →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) → Nat.card B ≤ 9

end CFSG.RankThree.PartTwo.Sec19
