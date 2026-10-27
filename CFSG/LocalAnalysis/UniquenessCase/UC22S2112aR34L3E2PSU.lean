module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Mat
import CFSG.ClassicalInvolution.Q3.Q3URClose
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddSubfield
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU3Cube
import CFSG.GH74.Orders.LieType
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

private theorem uc22s2112r34_psu_ordTwistedA_ne_one {q n : ℕ} (hq : 3 ≤ q)
    (hodd : Odd q) (hn : 3 ≤ n) : ordTwistedA (n - 1) q ≠ ordA 1 q := by
  have hdvd : q ^ 2 ∣ ordTwistedA (n - 1) q := by
    let C : ℕ := ∏ j ∈ Finset.Icc 2 n, (q ^ j - (-1 : ℤ) ^ j).toNat
    let d : ℕ := Nat.gcd n (q + 1)
    have hterm : (q ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
      simpa using
        CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (q := q) (i := 2)
          (by omega) even_two
    have hdvdC : d ∣ C := by
      have h1 : d ∣ q + 1 := Nat.gcd_dvd_right _ _
      have h2 : q + 1 ∣ q ^ 2 - 1 := by
        have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
          simpa using Nat.sq_sub_sq q 1
        rw [h]
        exact dvd_mul_right _ _
      have h3 : q ^ 2 - 1 ∣ C := by
        rw [← hterm]
        exact Finset.dvd_prod_of_mem (fun j => (q ^ j - (-1 : ℤ) ^ j).toNat)
          (by simp only [Finset.mem_Icc]; omega)
      exact h1.trans (h2.trans h3)
    have hdvdnum : d ∣ q ^ ((n - 1) * n / 2) * C :=
      dvd_mul_of_dvd_right hdvdC _
    have hmul : ordTwistedA (n - 1) q * d = q ^ ((n - 1) * n / 2) * C := by
      rw [CFSG.Open.ordTwistedA]
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Nat.div_mul_cancel hdvdnum
    have hexp : 2 ≤ (n - 1) * n / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h : 2 * 2 ≤ (n - 1) * n := by
        have hn2 : 2 ≤ n - 1 := by omega
        calc 2 * 2 = 4 := by norm_num
          _ ≤ 2 * 3 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul hn2 hn
      omega
    have hdvdq : q ^ 2 ∣ q ^ ((n - 1) * n / 2) := Nat.pow_dvd_pow q hexp
    have hcopq : Nat.Coprime q (q + 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd q (q + 1) ∣ (q + 1) - q :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      rw [show q + 1 - q = 1 by omega] at hd
      exact Nat.dvd_one.mp hd
    have hcop : Nat.Coprime (q ^ 2) d :=
      (hcopq.pow_left 2).of_dvd_right (Nat.gcd_dvd_right _ _)
    have hdiv : q ^ 2 ∣ ordTwistedA (n - 1) q * d := by
      rw [hmul]
      exact hdvdq.trans (dvd_mul_right _ _)
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv
  have hnot : ¬ q ^ 2 ∣ ordA 1 q := by
    have htwo : 2 * ordA 1 q = q * (q ^ 2 - 1) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd
    intro h
    have h1 : q ^ 2 ∣ q * (q ^ 2 - 1) := by
      have h2 := h.mul_right 2
      rwa [mul_comm (ordA 1 q) 2, htwo] at h2
    have h1' : q * q ∣ q * (q ^ 2 - 1) := by
      rwa [show q * q = q ^ 2 from (pow_two q).symm]
    have h2 : q ∣ q ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left (k := q) (by omega) h1'
    have h3 : q ∣ 1 := by
      have hq2dvd : q ∣ q ^ 2 := dvd_pow_self q (by norm_num : 2 ≠ 0)
      have h4 := Nat.dvd_sub hq2dvd h2
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      rwa [Nat.sub_sub_eq_min, min_eq_right hq2pos] at h4
    have := Nat.dvd_one.mp h3
    omega
  intro heq
  exact hnot (heq ▸ hdvd)

private theorem uc22s2112r34_diag_block_comm {F : Type} [Field F] (μ ν : F)
    (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix.diagonal ![μ, μ, ν] * CFSG.ClassicalInvolution.Phan.blockMat 3 0 A =
      CFSG.ClassicalInvolution.Phan.blockMat 3 0 A * Matrix.diagonal ![μ, μ, ν] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply,
      Matrix.mul_apply, Fin.sum_univ_three, mul_comm]


theorem uc22s2112r34_l3E2_trichotomy_psu {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ∣ p ^ f + 1)
    (hadm : StatedLieAdmissible .PSU 3 p f) (hX : CFSG.Blueprint.LieModel X .PSU 3 p f)
    (θ : MulAut X) (hθ3 : θ ^ 3 = 1)
    {K : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) {x : X} (hxK : x ∈ K)
    (hxr : (orderOf x).Prime) (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) (hθx : θ x = x) :
    θ ∈ (MulAut.conj : X →* MulAut X).range ∨
      (∃ K' : Subgroup X, IsFundamentalOver (p ^ f) K' ∧ K' ≤ signalizerFixedSubgroup θ) ∨
      ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  classical
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf1 : 1 ≤ f := hadm.2.1
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
  have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hL2 : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL2Over17
      (X ⧸ Subgroup.center X) (p ^ f) := by
    rintro ⟨r, f', hr, hr2, hq, hf', hm2⟩
    have hcardX : Nat.card X = ordTwistedA 2 (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSU (by norm_num) hp2 hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA 1 (r ^ f') := by
      simpa using CFSG.GH74.card_of_lieModel_PSL (n := 2) (p := r) (f := f')
        (by norm_num) hm2
    have hZbot : Subgroup.center X = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
      · exact hbot
      · exfalso
        have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
          rw [htop]
          exact QuotientGroup.subsingleton_quotient_top
        have hcard1 : Nat.card (X ⧸ Subgroup.center X) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨(1 : X ⧸ Subgroup.center X)⟩⟩
        have hq1 : ordA 1 (r ^ f') = 1 := by
          rw [← hcardQ, hcard1]
        have hr3 : 3 ≤ r := by
          have := hr.two_le
          omega
        have hq3' : 3 ≤ r ^ f' :=
          hr3.trans (Nat.le_self_pow (by omega : f' ≠ 0) r)
        have htwo : 2 * ordA 1 (r ^ f') = r ^ f' * ((r ^ f') ^ 2 - 1) :=
          CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one
            ((hr.odd_of_ne_two hr2).pow)
        have h2 : 2 = r ^ f' * ((r ^ f') ^ 2 - 1) := by
          rw [← htwo, hq1, mul_one]
        have h9 : 9 ≤ (r ^ f') ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (r ^ f') ^ 2 := Nat.pow_le_pow_left hq3' 2
        have hq2pos : 8 ≤ (r ^ f') ^ 2 - 1 := by omega
        have hprod : 24 ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := by
          calc 24 = 3 * 8 := by norm_num
            _ ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := Nat.mul_le_mul hq3' hq2pos
        omega
    have heq : ordTwistedA 2 (p ^ f) = ordA 1 (p ^ f) := by
      calc ordTwistedA 2 (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := by
            rw [hZbot]
            exact (Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv).symm
        _ = ordA 1 (r ^ f') := hcardQ
        _ = ordA 1 (p ^ f) := by rw [← hq]
    exact uc22s2112r34_psu_ordTwistedA_ne_one (n := 3) hq3 hoddq (by norm_num) heq
  have : Fact p.Prime := ⟨hp⟩
  have hU := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 3 p f hp (by trivial) hadm
  obtain ⟨Ecover⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique hp2 (by trivial) hX hU.2
  let M := CFSG.ClassicalInvolution.Generic.modelUniv .PSU 3 p f hp
  let ψ : M.K →* X := Ecover.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center M.K))
  have hψ : Function.Surjective ψ :=
    Ecover.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center M.K := by
    ext x
    constructor
    · intro hx
      have h2 : QuotientGroup.mk' (Subgroup.center M.K) x = 1 := by
        apply Ecover.symm.injective
        simpa [ψ] using hx
      exact (QuotientGroup.eq_one_iff x).mp h2
    · intro hx
      have h2 : QuotientGroup.mk' (Subgroup.center M.K) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      simpa [ψ, h2] using hx
  obtain ⟨R, hR, hRK, hRker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp hp2 hadm hX (by trivial) (by simp) hL2 ψ hψ (le_of_eq hker) hK
  obtain ⟨e, he⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨i, hi⟩ := (he R).mp hR
  let F := GaloisField p (2 * f)
  have hFcard : Nat.card F = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf1
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    ⟨hp, hf1, by rw [hFcard, ← pow_mul, mul_comm f 2]⟩
  have : CharP F p := h.charP
  have : Finite F := h.finite
  have hSU : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) =
      CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution F p f) 3 := by
    change CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      (1 : Matrix (Fin 3) (Fin 3) F) = _
    rw [← CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h 3]
    exact (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFcard 3).symm
  let sc : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) ≃*
      CFSG.ClassicalInvolution.Phan.Su F p f 3 :=
    MulEquiv.subgroupCongr hSU
  let π : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) →* X :=
    ψ.comp (e.symm.toMonoidHom.comp sc.toMonoidHom)
  have hπs : Function.Surjective π :=
    hψ.comp (e.symm.surjective.comp sc.surjective)
  have hqne2 : p ^ f ≠ 2 :=
    CFSG.ClassicalInvolution.Models.prime_pow_ne_two_of_ne_two hp2 f
  have hπker : π.ker = CFSG.ClassicalGroups.UnitaryFlag.normOneScalars h
      (CFSG.ClassicalGroups.UnitaryFlag.gramSU h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) 3 := by
    apply le_antisymm
    · intro x hx
      have hx' : sc x ∈ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3) := by
        have hmem : e.symm (sc x) ∈ ψ.ker := by
          rw [MonoidHom.mem_ker]
          simpa [π, MonoidHom.comp_apply] using hx
        rw [hker] at hmem
        have hmem' : sc x ∈ (Subgroup.center M.K).map e.toMonoidHom :=
          ⟨e.symm (sc x), hmem, by simp⟩
        have hcenter : (Subgroup.center M.K).map e.toMonoidHom =
            Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3) :=
          Subgroup.map_center_eq e
        rwa [hcenter] at hmem'
      obtain ⟨c, hc⟩ :=
        CFSG.ClassicalInvolution.Q3.Q3W.exists_scalar_of_mem_center_su3
          (K := F) (p := p) (f := f) hFcard hqne2 (by norm_num : 3 ≤ 3) hx'
      have hmats : (((sc x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
          Matrix.scalar (Fin 3) c := by
        simpa [CFSG.ClassicalInvolution.Models.suMat] using hc
      have hc0 : c ≠ 0 := by
        intro h0
        have hdet : (((sc x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
          (sc x).2.1
        rw [hmats, h0] at hdet
        simp at hdet
      have hnorm : h.norm c = 1 := by
        have hxmat : (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
            Matrix.scalar (Fin 3) c := by
          have hsame : (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
              (((sc x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) :=
            congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
              (MulEquiv.subgroupCongr_apply hSU x).symm
          rw [hsame, hmats]
        have hEq := x.2.1
        rw [hxmat] at hEq
        have hsc :=
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_barTranspose_mul_mul
            h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) c
        rw [hsc] at hEq
        have h00 := congrFun (congrFun hEq 0) 0
        simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Matrix.smul_apply,
          Matrix.one_apply] using h00
      have hcu3 : (Units.mk0 c hc0) ^ 3 = 1 := by
        apply Units.ext
        have hdet : (((sc x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
          (sc x).2.1
        rw [hmats] at hdet
        simpa [pow_three] using hdet
      refine ⟨Units.mk0 c hc0, hnorm, hcu3, ?_⟩
      · apply Units.ext
        rw [show (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
            (((sc x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) from
          congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
            (MulEquiv.subgroupCongr_apply hSU x).symm]
        exact hmats
    · rintro x ⟨c, hcN, hc3, hcx⟩
      have hxc : (sc x : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
        apply Units.ext
        have hxm := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F))) hcx
        simpa [sc] using hxm
      have hcent : sc x ∈ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3) := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hxc]
        exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (y : GL (Fin 3) F)).eq
      have hmem : e.symm (sc x) ∈ Subgroup.center M.K := by
        have hmem' : e.symm (sc x) ∈
            (Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3)).map e.symm.toMonoidHom :=
          ⟨sc x, hcent, by simp⟩
        have hcenter : (Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3)).map
            e.symm.toMonoidHom = Subgroup.center M.K :=
          Subgroup.map_center_eq e.symm
        rwa [hcenter] at hmem'
      have hψ1 : ψ (e.symm (sc x)) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hmem
      simpa [π, MonoidHom.comp_apply] using hψ1
  let E : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  have hEmk : ∀ x, E (QuotientGroup.mk x) = π x := by
    intro x
    change (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs) (QuotientGroup.mk x) = π x
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    change QuotientGroup.kerLift π (QuotientGroup.mk x) = π x
    exact QuotientGroup.kerLift_mk π x
  let θ' : MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) := MulAut.congr E.symm θ
  have hθE : θ = MulAut.congr E θ' := by
    ext y
    simp [θ', MulAut.congr_apply]
  have hθ'3 : θ' ^ 3 = 1 := by
    calc θ' ^ 3 = (MulAut.congr E.symm θ) ^ 3 := rfl
      _ = MulAut.congr E.symm (θ ^ 3) := by rw [map_pow]
      _ = MulAut.congr E.symm 1 := by rw [hθ3]
      _ = 1 := map_one _
  have hne : ¬(3 = 3 ∧ p ^ f = 2) := by simp [hqne2]
  let σ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
    (by norm_num : 3 ≤ 3) hne θ'
  by_cases hσ1 : σ = 1
  · have hD : θ' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := by
      have h1 : θ' ∈ (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
          (by norm_num : 3 ≤ 3) hne).ker := by
        rw [MonoidHom.mem_ker]
        exact hσ1
      have h2 := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.ker_primeFormFieldFactor h
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
        (by norm_num : 3 ≤ 3) hne
      rwa [h2] at h1
    have hD' : θ' ∈ (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)).range := by
      simpa [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD] using hD
    obtain ⟨A, hA⟩ := hD'
    have hA3one : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) (A ^ 3) = 1 := by
      rw [map_pow, hA, hθ'3]
    have hA3ker : A ^ 3 ∈ CFSG.RankThree.PartOne.KCUnitaryModel.idScalarKernel h 3 :=
      (CFSG.RankThree.PartOne.KCUnitaryModel.primeFormConjHom_eq_one_iff_of_ne
        (by norm_num : 3 ≤ 3) hne (A ^ 3)).mp hA3one
    rw [CFSG.RankThree.PartOne.KCUnitaryModel.mem_idScalarKernel] at hA3ker
    obtain ⟨cA, -, hA3c⟩ := hA3ker
    have hA3 : ((A : GL (Fin 3) F) ^ 3) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) cA := by
      simpa [Subgroup.coe_pow] using hA3c
    have hxKmap : x ∈ R.map ψ := by rw [← hRK]; exact hxK
    obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp hxKmap
    have ha_r : a ^ orderOf x = 1 := by
      have hmem : a ^ orderOf x ∈ R ⊓ ψ.ker := by
        refine ⟨R.pow_mem haR _, ?_⟩
        change ψ (a ^ orderOf x) = 1
        rw [map_pow, hψa, pow_orderOf_eq_one]
      rw [hRker] at hmem
      simpa using hmem
    have ha_ne : a ≠ 1 := by
      intro ha1
      have hx1 : x = 1 := by rw [← hψa, ha1, map_one]
      exact hxr.ne_one (by rw [hx1, orderOf_one])
    have ha_order : orderOf a = orderOf x := by
      refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ha_r) ?_
      rw [← hψa]
      exact orderOf_map_dvd ψ a
    obtain ⟨i, hi⟩ := (he R).mp hR
    obtain ⟨gconj, hL, -⟩ := hi
    have hea_mem : e a ∈ (CFSG.ClassicalInvolution.Models.rootSU2 F p f
        (by norm_num : 2 ≤ 3)).map (MulAut.conj gconj).toMonoidHom := by
      have h1 : e a ∈ R.map e.toMonoidHom := ⟨a, haR, rfl⟩
      rwa [hL] at h1
    obtain ⟨k, hkroot, hk_eq⟩ := Subgroup.mem_map.mp hea_mem
    obtain ⟨B, hB⟩ := hkroot
    have hea_eq : e a = gconj * CFSG.ClassicalInvolution.Phan.blockEmb F p f 3 2 0
        (by norm_num) B * gconj⁻¹ := by
      rw [← hk_eq, ← hB]
      rfl
    have hB_ne : B ≠ 1 := by
      intro hB1
      have hea1 : e a = 1 := by rw [hea_eq, hB1, map_one]; group
      have ha1 : a = 1 := e.injective (by simpa using hea1)
      exact ha_ne ha1
    have hB_r : B ^ orderOf x = 1 := by
      have h1 : (e a) ^ orderOf x = 1 := by rw [← map_pow, ha_r, map_one]
      have h1' : (CFSG.ClassicalInvolution.Phan.blockEmb F p f 3 2 0 (by norm_num) B) ^
          orderOf x = 1 := by
        have h := congrArg (MulAut.conj gconj⁻¹) h1
        rw [map_pow, map_one] at h
        have heq : MulAut.conj gconj⁻¹ (e a) =
            CFSG.ClassicalInvolution.Phan.blockEmb F p f 3 2 0 (by norm_num) B := by
          rw [hea_eq, MulAut.conj_apply]
          group
        rwa [heq] at h
      have h2 : CFSG.ClassicalInvolution.Phan.blockEmb F p f 3 2 0 (by norm_num) (B ^ orderOf x) =
          CFSG.ClassicalInvolution.Phan.blockEmb F p f 3 2 0 (by norm_num) 1 := by
        simpa [map_pow] using h1'
      exact CFSG.ClassicalInvolution.Phan.blockEmb_injective
        (K := F) (p := p) (f := f) (m := 3) (k := 2) (i := 0) (by norm_num) h2
    have hBmat_r : (CFSG.ClassicalInvolution.Models.suMat B) ^ orderOf x = 1 := by
      have h := congrArg (CFSG.ClassicalInvolution.Models.suMatHom F p f 2) hB_r
      simpa [map_pow] using h
    have hBmat_det : (CFSG.ClassicalInvolution.Models.suMat B).det = 1 :=
      CFSG.ClassicalInvolution.Models.det_suMat B
    have hBmat_ne : CFSG.ClassicalInvolution.Models.suMat B ≠ 1 := by
      intro hsm
      exact hB_ne (CFSG.ClassicalInvolution.Models.suMat_injective hsm)
    have hrF : ((orderOf x : ℕ) : F) ≠ 0 := by
      intro h0
      have hdvd : p ∣ orderOf x := (CharP.cast_eq_zero_iff F p (orderOf x)).mp h0
      have hp_eq : p = orderOf x := (Nat.prime_dvd_prime_iff_eq hp hxr).mp hdvd
      exact hxp hp_eq.symm
    have hA1mat : (CFSG.ClassicalInvolution.Models.suMat B - 1).det ≠ 0 :=
      uc22s2112r34_det_sub_one_ne_zero (K := F) hBmat_det hrF hBmat_r hBmat_ne
    let sA : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := sc.symm (e a)
    have hsA_su : sc sA = e a := sc.apply_symm_apply _
    have hE_sA : E (QuotientGroup.mk sA) = x := by
      rw [hEmk]
      simp [π, sA, hsA_su, hψa]
    have hfixθ' : θ' (QuotientGroup.mk sA) = QuotientGroup.mk sA := by
      apply E.injective
      have h1 : E (θ' (QuotientGroup.mk sA)) = θ (E (QuotientGroup.mk sA)) := by
        rw [hθE]
        simp [MulAut.congr_apply]
      rw [h1, hE_sA, hθx]
    have hconj : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) A
        (QuotientGroup.mk sA) = QuotientGroup.mk sA := by
      rw [hA, hfixθ']
    have hconj' : ((⟨A * sA * (A : GL (Fin 3) F)⁻¹,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.conj_mem_gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) A.2 sA.2⟩ :
          CFSG.ClassicalGroups.UnitaryFlag.gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) :
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) = QuotientGroup.mk sA := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom_mk]
      exact hconj
    have hζmem : ((⟨A * sA * (A : GL (Fin 3) F)⁻¹,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.conj_mem_gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) A.2 sA.2⟩ :
          CFSG.ClassicalGroups.UnitaryFlag.gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) / sA) ∈
        CFSG.ClassicalGroups.UnitaryFlag.normOneScalars h
          (CFSG.ClassicalGroups.UnitaryFlag.gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3)) 3 :=
      (QuotientGroup.eq_iff_div_mem).mp hconj'
    obtain ⟨cζ, hcζN, hcζ3, hcζ_eq⟩ := hζmem
    have hrel : (A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) cζ * (sA : GL (Fin 3) F) := by
      have h := hcζ_eq
      simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc (A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹
          = ((A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ *
              (sA : GL (Fin 3) F)⁻¹) * (sA : GL (Fin 3) F) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) cζ * (sA : GL (Fin 3) F) := by rw [h]
    have hsA_order : orderOf sA = orderOf x := by
      rw [show sA = sc.symm (e a) from rfl, MulEquiv.orderOf_eq sc.symm (e a),
        MulEquiv.orderOf_eq e a, ha_order]
    have hsA_r : ((sA : GL (Fin 3) F) ^ orderOf x) = 1 := by
      have hpwr : sA ^ orderOf x = 1 := by
        have h0 : sA ^ orderOf sA = 1 := pow_orderOf_eq_one sA
        rwa [hsA_order] at h0
      have h' := congrArg (fun g : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) => (g : GL (Fin 3) F)) hpwr
      simpa using h'
    have hζr : (Matrix.GeneralLinearGroup.scalar (Fin 3) cζ) ^ orderOf x = 1 := by
      have hconj_r : ((A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹) ^
          orderOf x = 1 := by
        rw [show (A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
            MulAut.conj (A : GL (Fin 3) F) (sA : GL (Fin 3) F) from rfl,
          ← map_pow, hsA_r, map_one]
      rw [hrel] at hconj_r
      have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) cζ)
          (sA : GL (Fin 3) F) :=
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar cζ (sA : GL (Fin 3) F)).symm
      rw [hcomm.mul_pow, hsA_r, mul_one] at hconj_r
      exact hconj_r
    have hζ3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) cζ) ^ 3 = 1 := by
      simpa using congrArg (Matrix.GeneralLinearGroup.scalar (Fin 3)) hcζ3
    have hcop : Nat.Coprime 3 (orderOf x) :=
      (Nat.coprime_primes Nat.prime_three hxr).mpr (Ne.symm hx3)
    have hζ1 : Matrix.GeneralLinearGroup.scalar (Fin 3) cζ = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨hζ3, hζr⟩
    have hAsA : (A : GL (Fin 3) F) * (sA : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
        (sA : GL (Fin 3) F) := by
      rw [hrel, hζ1, one_mul]
    let Igl : GL (Fin 3) F := (gconj : GL (Fin 3) F)
    let Agl : GL (Fin 3) F := (A : GL (Fin 3) F)
    let Kgl : GL (Fin 3) F := CFSG.ClassicalInvolution.Phan.blockGL 3 0
      (by norm_num : 2 + 0 ≤ 3) (B : GL (Fin 2) F)
    let ggl : GL (Fin 3) F := Igl⁻¹ * Agl * Igl
    let gmat : Matrix (Fin 3) (Fin 3) F := (ggl : Matrix (Fin 3) (Fin 3) F)
    have hea_gl : (e a : GL (Fin 3) F) = Igl * Kgl * Igl⁻¹ := by
      have h := congrArg (fun z : CFSG.ClassicalInvolution.Phan.Su F p f 3 =>
        (z : GL (Fin 3) F)) hea_eq
      simpa [Igl, Kgl, CFSG.ClassicalInvolution.Models.suMat,
        CFSG.ClassicalInvolution.Phan.coe_blockEmb, Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hsA_gl : (sA : GL (Fin 3) F) = Igl * Kgl * Igl⁻¹ := by
      have hsame : (sA : GL (Fin 3) F) = (e a : GL (Fin 3) F) := rfl
      rw [hsame, hea_gl]
    have hcommg : ggl * Kgl * ggl⁻¹ = Kgl := by
      have h := hAsA
      rw [hsA_gl] at h
      calc ggl * Kgl * ggl⁻¹
          = Igl⁻¹ * (Agl * (Igl * Kgl * Igl⁻¹) * Agl⁻¹) * Igl := by
            simp only [ggl]; group
        _ = Igl⁻¹ * (Igl * Kgl * Igl⁻¹) * Igl := by rw [h]
        _ = Kgl := by group
    have hcommg' : ggl * Kgl = Kgl * ggl := by
      calc ggl * Kgl = (ggl * Kgl * ggl⁻¹) * ggl := by group
        _ = Kgl * ggl := by rw [hcommg]
    have hKmat : ((Kgl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        CFSG.ClassicalInvolution.Phan.blockMat 3 0 (CFSG.ClassicalInvolution.Models.suMat B) := by
      rw [show Kgl = CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
          (B : GL (Fin 2) F) from rfl]
      rw [CFSG.ClassicalInvolution.Phan.coe_blockGL]
      rfl
    have hgA : gmat * CFSG.ClassicalInvolution.Phan.blockMat 3 0
          (CFSG.ClassicalInvolution.Models.suMat B) =
        CFSG.ClassicalInvolution.Phan.blockMat 3 0
          (CFSG.ClassicalInvolution.Models.suMat B) * gmat := by
      have h := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) hcommg'
      simpa [gmat, hKmat] using h
    have hblock : CFSG.ClassicalInvolution.Phan.blockMat 3 0
        (CFSG.ClassicalInvolution.Models.suMat B) =
        !![CFSG.ClassicalInvolution.Models.suMat B 0 0,
          CFSG.ClassicalInvolution.Models.suMat B 0 1, 0;
          CFSG.ClassicalInvolution.Models.suMat B 1 0,
          CFSG.ClassicalInvolution.Models.suMat B 1 1, 0; 0, 0, 1] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]
    have hgA' : gmat * !![CFSG.ClassicalInvolution.Models.suMat B 0 0,
          CFSG.ClassicalInvolution.Models.suMat B 0 1, 0;
          CFSG.ClassicalInvolution.Models.suMat B 1 0,
          CFSG.ClassicalInvolution.Models.suMat B 1 1, 0; 0, 0, 1] =
        !![CFSG.ClassicalInvolution.Models.suMat B 0 0,
          CFSG.ClassicalInvolution.Models.suMat B 0 1, 0;
          CFSG.ClassicalInvolution.Models.suMat B 1 0,
          CFSG.ClassicalInvolution.Models.suMat B 1 1, 0; 0, 0, 1] * gmat := by
      rw [← hblock]
      exact hgA
    have hImem : Igl ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := by
      have hiGram : (gconj : GL (Fin 3) F) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := by
        rw [hSU]
        exact gconj.2
      exact ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_gramSU_iff_unitary
        (h := h)).mp hiGram).1
    have hgglmem : ggl ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) :=
      mul_mem (mul_mem (inv_mem hImem) A.2) hImem
    have hgu : Matrix.transpose (gmat.map h.bar) * gmat = 1 := by
      have h := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary.mp hgglmem
      simpa [gmat, CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using h
    have hAgl3 : Agl ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) cA := by
      apply Units.ext
      have h := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hA3c
      simpa [Agl, Subgroup.coe_pow] using h
    have hscalar_comm : Igl⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) cA * Igl =
        Matrix.GeneralLinearGroup.scalar (Fin 3) cA := by
      have hcomm := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar cA Igl).eq
      calc Igl⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) cA * Igl
          = Igl⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) cA * Igl) := by rw [mul_assoc]
        _ = Igl⁻¹ * (Igl * Matrix.GeneralLinearGroup.scalar (Fin 3) cA) := by rw [hcomm]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) cA := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hg3gl : ggl ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) cA := by
      calc ggl ^ 3 = (Igl⁻¹ * Agl * Igl) ^ 3 := rfl
        _ = Igl⁻¹ * Agl ^ 3 * Igl := by rw [pow_three, pow_three]; group
        _ = Igl⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) cA * Igl := by rw [hAgl3]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) cA := hscalar_comm
    have hg3 : gmat ^ 3 = Matrix.scalar (Fin 3) (cA : F) := by
      change ((ggl : Matrix (Fin 3) (Fin 3) F) ^ 3) = _
      rw [← Units.val_pow_eq_pow_val, hg3gl]
      rfl
    rcases uc22s2112r34_cube_or_conj_diag_unitary h hgu hg3 hA1mat hgA' with
      ⟨b, hb⟩ | ⟨P, μ, ν, hPdet, hPu, hPg⟩
    · left
      have hdetI : (((Igl : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = 1 := gconj.2.1
      have hdetA : (((Agl : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = b ^ 3 := by
        have hdetg : gmat.det = (((Agl : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det := by
          simp [gmat, ggl, Agl, Matrix.det_mul, hdetI]
        rw [← hdetg]
        exact hb
      let cAunit : Fˣ := Units.mk0 (((Agl : GL (Fin 3) F)) :
        Matrix (Fin 3) (Fin 3) F).det
        (Matrix.GeneralLinearGroup.det_ne_zero (A : GL (Fin 3) F))
      have hdetAunit : (((A : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).det = cAunit := rfl
      obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Malle.E27Lie.primeFormConjHom_inner_of_cube
        h3 A cAunit hdetAunit b hdetA.symm
      refine ⟨E k, ?_⟩
      have hθ'k : θ' = MulAut.conj k := by rw [← hA]; exact hk
      rw [hθE, hθ'k]
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]
    · let D : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![μ, μ, ν]
      have hdetg_ne : gmat.det ≠ 0 := by
        simpa [gmat] using Matrix.GeneralLinearGroup.det_ne_zero ggl
      have hDdet : D.det ≠ 0 := by
        have h := congrArg Matrix.det hPg
        rw [Matrix.det_mul, Matrix.det_mul, hPdet, mul_one, one_mul] at h
        rw [← h]
        exact hdetg_ne
      have hμν : μ * μ * ν ≠ 0 := by
        simpa [D, Matrix.det_diagonal, Fin.prod_univ_three] using hDdet
      have hμ : μ ≠ 0 := by
        have h1 : μ * μ ≠ 0 := (mul_ne_zero_iff.mp hμν).1
        exact (mul_ne_zero_iff.mp h1).1
      have hν : ν ≠ 0 := (mul_ne_zero_iff.mp hμν).2
      let Dgl : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero D hDdet
      have hDgl_coe : (Dgl : Matrix (Fin 3) (Fin 3) F) = D := rfl
      let Pgl : GL (Fin 3) F :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero P (by rw [hPdet]; exact one_ne_zero)
      have hPgl_coe : (Pgl : Matrix (Fin 3) (Fin 3) F) = P := rfl
      have hPmem : Pgl ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := by
        rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
        simpa [hPgl_coe, CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hPu
      have hPgram : Pgl ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := by
        rw [CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU]
        exact ⟨hPmem, by simpa [hPgl_coe] using hPdet⟩
      let Psu : CFSG.ClassicalInvolution.Phan.Su F p f 3 :=
        sc ⟨Pgl, hPgram⟩
      let j : CFSG.ClassicalInvolution.Phan.Su F p f 3 := gconj * Psu
      let Jgl : GL (Fin 3) F := Igl * Pgl
      let L' : Subgroup (CFSG.ClassicalInvolution.Phan.Su F p f 3) :=
        (CFSG.ClassicalInvolution.Models.rootSU2 F p f (by norm_num : 2 ≤ 3)).map
          (MulAut.conj j).toMonoidHom
      have hL' : L' ∈ CFSG.ClassicalInvolution.Models.longRootSetU
          (K := F) (p := p) (f := f) (by norm_num : 2 ≤ 3) := by
        rw [CFSG.ClassicalInvolution.Models.mem_longRootSetU_iff]
        exact ⟨j, rfl⟩
      let R' : Subgroup M.K := L'.map e.symm.toMonoidHom
      have hRmap : R'.map e.toMonoidHom = L' := by
        simp [R', Subgroup.map_map]
      have hR' : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU M.D :=
        (he R').mpr (by rwa [hRmap])
      let K' : Subgroup X := R'.map ψ
      have hK' : IsFundamentalOver (p ^ f) K' :=
        ⟨.PSU, 3, p, f, hp, hp2, rfl, trivial, hadm, ψ, hψ, le_of_eq hker, R', hR', rfl⟩
      have hAJmat : (Agl : Matrix (Fin 3) (Fin 3) F) * (Jgl : Matrix (Fin 3) (Fin 3) F) =
          (Jgl : Matrix (Fin 3) (Fin 3) F) * D := by
        have h1 : Agl * Jgl = Igl * (ggl * Pgl) := by
          simp only [Jgl, ggl, Agl]
          group
        calc (Agl : Matrix (Fin 3) (Fin 3) F) * (Jgl : Matrix (Fin 3) (Fin 3) F)
            = ((Agl * Jgl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
          _ = ((Igl * (ggl * Pgl) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [h1]
          _ = (Igl : Matrix (Fin 3) (Fin 3) F) * ((ggl : Matrix (Fin 3) (Fin 3) F) * P) := by
              simp [Units.val_mul, hPgl_coe]
          _ = (Igl : Matrix (Fin 3) (Fin 3) F) * (P * D) := by rw [hPg]
          _ = (Jgl : Matrix (Fin 3) (Fin 3) F) * D := by
              simp [Jgl, Units.val_mul, hPgl_coe, mul_assoc]
      have hAJgl : Agl * Jgl = Jgl * Dgl := by
        apply Units.ext
        simpa [hDgl_coe] using hAJmat
      have hJinvA : Jgl⁻¹ * Agl = Dgl * Jgl⁻¹ := by
        calc Jgl⁻¹ * Agl = Jgl⁻¹ * Agl * Jgl * Jgl⁻¹ := by group
          _ = Jgl⁻¹ * (Agl * Jgl) * Jgl⁻¹ := by group
          _ = Jgl⁻¹ * (Jgl * Dgl) * Jgl⁻¹ := by rw [hAJgl]
          _ = Dgl * Jgl⁻¹ := by group
      have hDKmat : ∀ (Bk : CFSG.ClassicalInvolution.Phan.Su F p f 2),
          D * CFSG.ClassicalInvolution.Phan.blockMat 3 0
              (CFSG.ClassicalInvolution.Models.suMat Bk) =
            CFSG.ClassicalInvolution.Phan.blockMat 3 0
              (CFSG.ClassicalInvolution.Models.suMat Bk) * D := by
        intro Bk
        exact uc22s2112r34_diag_block_comm μ ν (CFSG.ClassicalInvolution.Models.suMat Bk)
      have hDKgl : ∀ (Bk : CFSG.ClassicalInvolution.Phan.Su F p f 2),
          Dgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
              (Bk : GL (Fin 2) F) =
            CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
              (Bk : GL (Fin 2) F) * Dgl := by
        intro Bk
        apply Units.ext
        have h := hDKmat Bk
        simpa [hDgl_coe, CFSG.ClassicalInvolution.Phan.coe_blockGL,
          CFSG.ClassicalInvolution.Models.suMat] using h
      have hcomm_root : ∀ (Bk : CFSG.ClassicalInvolution.Phan.Su F p f 2),
          Agl * (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
              (Bk : GL (Fin 2) F) * Jgl⁻¹) =
            (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
              (Bk : GL (Fin 2) F) * Jgl⁻¹) * Agl := by
        intro Bk
        have hDK := hDKgl Bk
        calc Agl * (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
              (Bk : GL (Fin 2) F) * Jgl⁻¹)
            = (Agl * Jgl) * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * Jgl⁻¹ := by group
          _ = (Jgl * Dgl) * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * Jgl⁻¹ := by rw [hAJgl]
          _ = Jgl * (Dgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F)) * Jgl⁻¹ := by group
          _ = Jgl * (CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * Dgl) * Jgl⁻¹ := by rw [hDK]
          _ = Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * (Dgl * Jgl⁻¹) := by group
          _ = Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * (Jgl⁻¹ * Agl) := by rw [hJinvA]
          _ = (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * Jgl⁻¹) * Agl := by group
      have hK'fix : K' ≤ signalizerFixedSubgroup θ := by
        rintro y ⟨r, hrR', rfl⟩
        obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hrR'
        obtain ⟨k, hkroot, hk_eq⟩ := Subgroup.mem_map.mp hlL
        obtain ⟨Bk, hBk⟩ := hkroot
        let sl : CFSG.ClassicalGroups.UnitaryFlag.gramSU h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) := sc.symm l
        have hsl : sc sl = l := sc.apply_symm_apply l
        have hLgl : (sl : GL (Fin 3) F) = Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0
            (by norm_num : 2 + 0 ≤ 3) (Bk : GL (Fin 2) F) * Jgl⁻¹ := by
          have hsl_gl : (sl : GL (Fin 3) F) = (l : GL (Fin 3) F) := rfl
          rw [hsl_gl]
          have h1 : (l : GL (Fin 3) F) = Jgl * (k : GL (Fin 3) F) * Jgl⁻¹ := by
            have hk_gl := congrArg (fun z : CFSG.ClassicalInvolution.Phan.Su F p f 3 =>
              (z : GL (Fin 3) F)) hk_eq
            rw [← hk_gl]
            change (j : GL (Fin 3) F) * (k : GL (Fin 3) F) * (j : GL (Fin 3) F)⁻¹ =
              Jgl * (k : GL (Fin 3) F) * Jgl⁻¹
            rfl
          rw [h1, ← hBk, CFSG.ClassicalInvolution.Phan.coe_blockEmb]
        have hAsl : Agl * (sl : GL (Fin 3) F) * Agl⁻¹ = (sl : GL (Fin 3) F) := by
          rw [hLgl]
          calc Agl * (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                (Bk : GL (Fin 2) F) * Jgl⁻¹) * Agl⁻¹
              = (Agl * (Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                  (Bk : GL (Fin 2) F) * Jgl⁻¹)) * Agl⁻¹ := by rw [mul_assoc]
            _ = ((Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                  (Bk : GL (Fin 2) F) * Jgl⁻¹) * Agl) * Agl⁻¹ := by rw [hcomm_root Bk]
            _ = Jgl * CFSG.ClassicalInvolution.Phan.blockGL 3 0 (by norm_num : 2 + 0 ≤ 3)
                  (Bk : GL (Fin 2) F) * Jgl⁻¹ := by group
        have hfix' : θ' (QuotientGroup.mk sl) = QuotientGroup.mk sl := by
          have hconj : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
              (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 3) A
              (QuotientGroup.mk sl) = QuotientGroup.mk sl := by
            rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom_mk]
            exact congrArg QuotientGroup.mk (Subtype.ext hAsl)
          rw [← hA]
          exact hconj
        have hEy : E (QuotientGroup.mk sl) = ψ (e.symm l) := by
          rw [hEmk]
          change ψ (e.symm (sc sl)) = ψ (e.symm l)
          rw [hsl]
        change θ (ψ (e.symm l)) = ψ (e.symm l)
        rw [← hEy]
        have h1 : θ (E (QuotientGroup.mk sl)) = E (θ' (QuotientGroup.mk sl)) := by
          rw [hθE]
          simp [MulAut.congr_apply]
        rw [h1, hfix']
      exact Or.inr (Or.inl ⟨K', hK', hK'fix⟩)
  · have hθ'ne : θ' ≠ 1 := by
      intro h1
      exact hσ1 (by simp [σ, h1])
    have hθ'ord : orderOf θ' = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hθ'3 hθ'ne
    have hσ3 : σ ^ 3 = 1 := by
      change (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
        (by norm_num : 3 ≤ 3) hne θ') ^ 3 = 1
      rw [← map_pow, hθ'3, map_one]
    have hσord : orderOf σ = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hσ3 hσ1
    obtain ⟨-, -, -, -, -, Mfield, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char
        h (by norm_num : 3 ≤ 3) hne Nat.prime_three (by norm_num : 3 ≠ 2)
        θ' hθ'ord σ rfl hσord
    let δ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) Mfield
    have hδ : θ' = δ * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one σ * δ⁻¹ := by
      rw [← hM]
      change θ' = δ * (δ⁻¹ * θ' * δ) * δ⁻¹
      group
    let kfield := CFSG.LieType.Chevalley.fixSubfield σ
    let h0 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p (f / 3) kfield :=
      CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
        (by norm_num : 3 ≠ 2) hσord
    have hbar : ∀ c : kfield, (h0.bar c : F) = h.bar c :=
      CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three
        (by norm_num : 3 ≠ 2) hσord
    let ι0 := CFSG.RankThree.Classical.subfieldPSU h h0 hbar 3
    let ι := δ.toMonoidHom.comp ι0
    have hι : Function.Injective ι := δ.injective.comp
      (CFSG.RankThree.Classical.subfieldPSU_injective h h0 hbar 3 (by omega))
    have hfix : ∀ y, θ' (ι y) = ι y := by
      intro y
      change θ' (δ (ι0 y)) = δ (ι0 y)
      simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      apply congrArg δ
      exact (CFSG.RankThree.Classical.range_subfieldPSU_le h 3 h0 hbar) ⟨y, rfl⟩
    have hY : ι.range ≤ signalizerFixedSubgroup θ' := by
      rintro _ ⟨y, rfl⟩
      exact hfix y
    have hcard : Nat.card kfield = (p ^ (f / 3)) ^ 2 := by
      rw [h0.card, mul_comm 2 (f / 3), pow_mul]
    have hq03 : 3 ≤ p ^ (f / 3) :=
      hp3.trans (Nat.le_self_pow (by have := h0.one_le; omega) p)
    let e0 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h0
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram kfield 3) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ (f / 3)) kfield) :=
      (Classical.choice
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv
          h0 CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one)).trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h0 (by omega))
    have hmodel : CFSG.Blueprint.LieModel
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h0
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram kfield 3)) .PSU 3 p (f / 3) := by
      refine Or.inl ⟨by decide, ⟨h0.prime, h0.one_le, by norm_num, ?_⟩, kfield,
        inferInstance, inferInstance, hcard, ⟨e0⟩⟩
      intro he
      have := congrArg Prod.snd he
      omega
    let Y' : Subgroup X := ι.range.map E.toMonoidHom
    have hY' : Y' ≤ signalizerFixedSubgroup θ := by
      rintro _ ⟨y, hy, rfl⟩
      change θ (E y) = E y
      have h1 : θ (E y) = E (θ' y) := by
        rw [hθE]
        simp [MulAut.congr_apply]
      rw [h1, hY hy]
    have hmodel_range : CFSG.Blueprint.LieModel ι.range .PSU 3 p (f / 3) :=
      hmodel.of_mulEquiv (MonoidHom.ofInjective hι)
    have hmodel' : CFSG.Blueprint.LieModel Y' .PSU 3 p (f / 3) :=
      hmodel_range.of_mulEquiv (ι.range.equivMapOfInjective E.toMonoidHom E.injective)
    obtain ⟨S, hS, hSs, hSr⟩ :=
      fieldAutOdd_of_classical_subfield (t := .PSU) (n := 3) (p := p) (e := f / 3)
        (by decide) hp2 (by intro hh; cases hh.1) θ hY' hmodel'
    exact Or.inr (Or.inr ⟨S, hS, hSs, hSr⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
