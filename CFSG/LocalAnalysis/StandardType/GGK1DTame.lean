module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.StandardType.GGK1CBlFF
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitTameGL
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial
  supportedBlock isometryCentralizer blockGL hermForm frobPow frobPow_apply
  finite_adjoinRoot_of_fact pairedBlockEquiv)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem ggK1Dt_commutator_equiv {G B : Type} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) : Nonempty (↥⁅A, A⁆ ≃* ↥(commutator B)) := by
  have e1 : ↥⁅A, A⁆ ≃* ↥(commutator ↥A) :=
    ((Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))).symm
  exact ⟨e1.trans (MulEquiv.commutatorCongr φ)⟩

private theorem ggK1Dt_card_sq_eq_one {p nf : ℕ} (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) :
    (((2 ^ nf : ℕ) : ZMod p)) ^ 2 = 1 := by
  have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  rcases hdvd with h1 | h1
  · have h0 : (((2 ^ nf - 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_sub hpos, sub_eq_zero] at h0
    rw [h0]; simp
  · have h0 : (((2 ^ nf + 1 : ℕ) : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h2 : ((2 ^ nf : ℕ) : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h0
    rw [h2]; simp

private theorem ggK1Dt_natDegree_le_two {K : Type} [Field K] [Fintype K] {p nf : ℕ}
    (hp : p.Prime) (hpchar : p ≠ ringChar K) (hK : Fintype.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hdvdX : h ∣ X ^ p - 1) (hne : h ≠ X - 1) : h.natDegree ≤ 2 := by
  rw [ggK1CBl_ff_degree hp hpchar hirr hmon hdvdX hne]
  have hsq : ((Fintype.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hK]; exact ggK1Dt_card_sq_eq_one hdvd
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hsq)

private theorem ggK1Dt_finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem ggK1Dt_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem ggK1Dt_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (h ▸ ggK1Dt_card_primeFactors_two_three a b ha hb)

private theorem ggK1Dt_isSolvable_sesqUnitaryGroup_of_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  haveI := ggK1Dt_finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
      rcases hsmall with h | h
      · omega
      · exact h
    obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      rfl (by omega : 1 ≤ Module.finrank E W)
    have hexc : (Module.finrank E W = 2 ∧ ℓ ^ g = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ g = 3) ∨
        (Module.finrank E W = 3 ∧ ℓ ^ g = 2) := by
      by_contra hn
      push Not at hn
      obtain ⟨h1, h2, h3⟩ := hn
      refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
      · by_contra hlt
        rcases (show ℓ ^ g = 2 ∨ ℓ ^ g = 3 by omega) with hQ | hQ
        · exact h1 h2' hQ
        · exact h2 h2' hQ
      · by_contra hlt
        exact h3 h3' (by omega)
    rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
    · rw [hm2, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
      exact ggK1Dt_isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
        (by rw [h18]; norm_num)
    · rw [hm2, hQ] at hcard
      have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      exact ggK1Dt_isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
        (by rw [h96]; norm_num)
    · rw [hm3, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      exact ggK1Dt_isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by rw [h648]; norm_num)
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

private theorem ggK1Dt_sesqUnitaryGroup_tame {nf : ℕ} (hnf : 1 ≤ nf)
    {E : Type} [Field E] (hE : UnitaryFieldData 2 nf E)
    {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) :
    CFSG.IsQuasisimple ↥⁅sesqUnitaryGroup Hf, sesqUnitaryGroup Hf⁆ ∨
      Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  by_cases hsmall : Module.finrank E W ≤ 1 ∨
      ¬ ((Module.finrank E W = 2 → 4 ≤ 2 ^ nf) ∧
        (Module.finrank E W = 3 → 3 ≤ 2 ^ nf))
  · right
    exact ggK1Dt_isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl hsmall
  · left
    have hnot1 : ¬ Module.finrank E W ≤ 1 := fun h => hsmall (Or.inl h)
    have hq : (Module.finrank E W = 2 → 4 ≤ 2 ^ nf) ∧
        (Module.finrank E W = 3 → 3 ≤ 2 ^ nf) := by
      by_contra hc
      exact hsmall (Or.inr hc)
    have hm : 2 ≤ Module.finrank E W := by omega
    have hqSL : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
        hE hHf hHfl hm hq
    have hker : unitarySpecial (h := hE) Hf =
        (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
      ext δ
      rw [mem_unitarySpecial (h := hE), Subgroup.mem_subgroupOf,
        mem_sesqSpecialUnitaryGroup]
      exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
    have hle : ⁅sesqUnitaryGroup Hf, sesqUnitaryGroup Hf⁆ ≤ sesqSpecialUnitaryGroup Hf := by
      rw [← Subgroup.map_subtype_commutator (sesqUnitaryGroup Hf)]
      refine Subgroup.map_le_iff_le_comap.2 ?_
      rw [Subgroup.comap_subtype, ← hker]
      exact commutator_le_unitarySpecial (h := hE) Hf
    have hss_eq : (sesqSpecialUnitaryGroup Hf) =
        ⁅sesqUnitaryGroup Hf, sesqUnitaryGroup Hf⁆ := by
      refine le_antisymm ?_ hle
      have hperf : ⁅(sesqSpecialUnitaryGroup Hf), (sesqSpecialUnitaryGroup Hf)⁆ =
          sesqSpecialUnitaryGroup Hf := Subgroup.isPerfect_iff.mp hqSL.1
      rw [← hperf]
      exact Subgroup.commutator_mono (sesqSpecialUnitaryGroup_le Hf) (sesqSpecialUnitaryGroup_le Hf)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hss_eq) hqSL

theorem ggK1D_tame_paired {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) :
    CFSG.IsQuasisimple ↥⁅supportedBlock Q x h, supportedBlock Q x h⁆ ∨
      Group.IsSolvable ↥(supportedBlock Q x h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  have eGL : ↥(supportedBlock Q x h) ≃*
      Matrix.GeneralLinearGroup (Fin (Module.finrank (AdjoinRoot h)
        (primaryComponent x.toLinearMap h))) (AdjoinRoot h) :=
    (pairedBlockEquiv hx hh hne).trans
      (Matrix.GeneralLinearGroup.toLin'
        (Module.finBasis (AdjoinRoot h) (primaryComponent x.toLinearMap h))).symm
  exact ggNbrLSideTame_gl eGL

theorem ggK1D_tame_selfDual {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p nf : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf)
    (hK : Nat.card K = 2 ^ nf) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    CFSG.IsQuasisimple ↥⁅supportedBlock Q x h, supportedBlock Q x h⁆ ∨
      Group.IsSolvable ↥(supportedBlock Q x h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite (AdjoinRoot h)
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := (mem_primaryFactors.mp hh).2.1
  have hdvdX : h ∣ X ^ p - 1 := hx.dvd_X_pow_sub_one hh
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrc : ringChar K = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : nf ≠ 0))
  have hpchar : p ≠ ringChar K := by rw [hrc]; exact hp2
  have hcardK : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
  have hle2 : h.natDegree ≤ 2 :=
    ggK1Dt_natDegree_le_two hp hpchar hcardK hdvd hirr hmon hdvdX hne1
  obtain ⟨d, H, hndeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hpodd hh hne1 hself
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  have hd1 : d = 1 := by omega
  have hndeg2 : h.natDegree = 2 := by omega
  have hcardE : Nat.card (AdjoinRoot h) = (2 ^ nf) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K),
      CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, hndeg2, hK]
  have hU : UnitaryFieldData 2 nf (AdjoinRoot h) :=
    ⟨Nat.prime_two, hnf, by rw [hcardE, ← pow_mul]; congr 1; omega⟩
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := by
    intro z
    rw [hd1, frobPow_apply, hU.bar_apply, hK, pow_one]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e : ↥(supportedBlock Q x h) ≃* sesqUnitaryGroup B :=
    (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  rcases ggK1Dt_sesqUnitaryGroup_tame hnf hU hBsymm hBl with hq | hs
  · left
    obtain ⟨eC⟩ := ggK1Dt_commutator_equiv e
    have ecomm : ↥(commutator (sesqUnitaryGroup B)) ≃*
        ↥⁅sesqUnitaryGroup B, sesqUnitaryGroup B⁆ :=
      (Subgroup.equivMapOfInjective (commutator (sesqUnitaryGroup B))
        (sesqUnitaryGroup B).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (sesqUnitaryGroup B)))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (eC.trans ecomm).symm hq
  · right
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

end CFSG.StandardType

end
