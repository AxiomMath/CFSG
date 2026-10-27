module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSURoot
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylOuterTransport
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SylowAbstract
import CFSG.LocalAnalysis.StandardType.GGRootDetectSUDiag
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSUCent
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSULevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (SU rootDatum antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

namespace KGPSU

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev gramJm (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  AutPSU.gramJ (K := K) (m + 1)

private theorem diag_comm_one_add_single {K : Type} [Field K] {n : ℕ} (t : Fin n → K)
    {i j : Fin n} (h : t i = t j) :
    Matrix.diagonal t * (1 + Matrix.single i j (1 : K)) =
      (1 + Matrix.single i j (1 : K)) * Matrix.diagonal t := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  ext a c
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with hac
  · obtain ⟨rfl, rfl⟩ := hac
    rw [h, mul_one, one_mul]
  · simp

private theorem diagGL_comm_rootU (h : UnitaryFieldData 2 f K) (hm : 1 ≤ m)
    {t : Fin (m + 1) → K} (ht : ∀ a, t a ≠ 0) (h0 : t 0 = 1) (hl : t (Fin.last m) = 1) :
    (RootDetectSU.diagGL t ht : GL (Fin (m + 1)) K) *
        (AutPSU.rootU (f := f) (K := K) m : GL (Fin (m + 1)) K) =
      (AutPSU.rootU (f := f) (K := K) m : GL (Fin (m + 1)) K) *
        (RootDetectSU.diagGL t ht : GL (Fin (m + 1)) K) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, RootDetectSU.coe_diagGL, AutPSU.coe_rootU hm]
  exact diag_comm_one_add_single t (by rw [h0, hl])

private theorem diagGL_comm_lroot (h : UnitaryFieldData 2 f K)
    {hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev 0}
    {t : Fin (m + 1) → K} (ht : ∀ a, t a ≠ 0) (h0 : t 0 = 1) (hl : t (Fin.last m) = 1) :
    (RootDetectSU.diagGL t ht : GL (Fin (m + 1)) K) *
        (AutPSU.lroot (unitaryInvolution K 2 f) hi₀ : GL (Fin (m + 1)) K) =
      (AutPSU.lroot (unitaryInvolution K 2 f) hi₀ : GL (Fin (m + 1)) K) *
        (RootDetectSU.diagGL t ht : GL (Fin (m + 1)) K) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, RootDetectSU.coe_diagGL, AutPSU.coe_lroot]
  have hrev : (Fin.rev (0 : Fin (m + 1))) = Fin.last m := rfl
  exact diag_comm_one_add_single t (by rw [h0, hrev, hl])

theorem pCoreOf_le_range_of_rootU (h : UnitaryFieldData 2 f K) (hm : 3 ≤ m)
    {G : Type} [Group G] {ψ : AutPSU.PJ h (m + 1) →* G}
    (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (AutPSU.projU h (AutPSU.rootU (f := f) m))}) ≤ ψ.range := by
  intro a ha
  have hi₀ : (0 : Fin (m + 1)) ≠ Fin.rev 0 := zero_ne_rev_zero (by omega)
  have hlevi_eq : leviFull h m = levi h m hi₀ := by
    rw [leviFull, y0_of_le h (by omega)]
  have hCx : Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (f := f) m)} =
      radical h m ⊔ levi h m hi₀ := by
    rw [centralizer_rootU_eq_sup h hm, hlevi_eq]
  have hLQ : levi h m hi₀ ≤ Subgroup.normalizer (radical h m : Set (AutPSU.PJ h (m + 1))) :=
    hlevi_eq ▸ leviFull_le_normalizer_radical h hm
  have hdisj : Disjoint (radical h m) (levi h m hi₀) :=
    hlevi_eq ▸ disjoint_radical_leviFull h hm
  have hQ := pCoreOf_centralizer_rootU h hm
  set r₀ : AutPSU.PJ h (m + 1) := AutPSU.projU h (AutPSU.rootU (f := f) m) with hr₀
  set y₀ : AutPSU.PJ h (m + 1) :=
    AutPSU.projU h (AutPSU.lroot (unitaryInvolution K 2 f) hi₀) with hy₀
  have haM : a ∈ Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ r₀} := by
    have := GGRootNorm.pCoreOf_le (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (AutPSU.projU h (AutPSU.rootU (f := f) m))}) ha
    simpa [hr₀] using this
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  have haC : a ∈ Subgroup.centralizer ({ψ r₀} : Set G) := haM.2
  obtain ⟨α, hα⟩ := exists_mulAut_conj_of_mem_normalizer_range hψ ha_norm
  obtain ⟨i, hi, c, hc, hαeq⟩ := AutPSU.exists_mul_compl h (by omega) α
  obtain ⟨A, rfl⟩ := hi
  set σ := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ x, σ (σ x) = x := AutPSU.sigma_involutive h
  set ν : K := ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det with hνdef
  have hνn : ν * σ ν = 1 := by
    have e := norm_det_eq_one h (AutPSU.gramJ (m + 1)) A.2
    rwa [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at e
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul_eq_one hνn
  obtain ⟨ρ, hρ0, hρ⟩ := RootDetectSU.exists_div_eq h hνn
  set b : Fin (m + 1) := AutPSL.idxOne (by omega) with hbdef
  have hb : b ≠ Fin.rev b := AutPSL.idxOne_ne_rev hm
  have hdu := RootDetectSU.pairDiag_unitary hσ hb hρ0
  set d : GL (Fin (m + 1)) K := RootDetectSU.diagGL (RootDetectSU.pairDiag σ b ρ)
    (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) with hddef
  have hdU : d ∈ primeFormUnitary h (gramJm (K := K) m) := by
    rw [hddef]
    have := RootDetectSU.diagGL_mem_primeFormUnitary h hdu
    simpa [gramJm, AutPSU.coe_gramJ] using this
  have hddet : ((d : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = ν := by
    rw [hddef, RootDetectSU.coe_diagGL, det_diagonal, RootDetectSU.prod_pairDiag hb,
      ← div_eq_mul_inv, hρ]
  set s : GL (Fin (m + 1)) K := (A : GL (Fin (m + 1)) K) * d⁻¹ with hsdef
  have hs : s ∈ AutPSU.XJ h (m + 1) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem A.2 (inv_mem hdU), ?_⟩
    have e : ((s * d : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = ν := by
      rw [hsdef, inv_mul_cancel_right]
    rw [Units.val_mul, det_mul, hddet] at e
    exact mul_right_cancel₀ hν0 (e.trans (one_mul ν).symm)
  have hsU : s ∈ primeFormUnitary h (gramJm (K := K) m) := hs.1
  have hAeq : A = (⟨s, hsU⟩ : primeFormUnitary h (gramJm (K := K) m)) * ⟨d, hdU⟩ := by
    apply Subtype.ext
    change (A : GL (Fin (m + 1)) K) = s * d
    rw [hsdef]
    group
  have hconj_s : primeFormConjHom h (gramJm (K := K) m) ⟨s, hsU⟩ =
      MulAut.conj ((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)) :=
    primeFormConjHom_eq_conj h (gramJm (K := K) m) ⟨s, hs⟩
  have hsplit : primeFormConjHom h (gramJm (K := K) m) A =
      MulAut.conj ((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)) *
        primeFormConjHom h (gramJm (K := K) m) ⟨d, hdU⟩ := by
    conv_lhs => rw [hAeq]
    rw [map_mul, hconj_s]
  have h0 : RootDetectSU.pairDiag σ b ρ 0 = 1 :=
    RootDetectSU.pairDiag_of_ne (by simp [hbdef, AutPSL.idxOne, Fin.ext_iff])
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_zero]; omega) ρ
  have hl : RootDetectSU.pairDiag σ b ρ (Fin.last m) = 1 :=
    RootDetectSU.pairDiag_of_ne
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_last]; omega)
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_last]; omega) ρ
  have hd_comm_r₀ : (d : GL (Fin (m + 1)) K) *
        (AutPSU.rootU (f := f) (K := K) m : GL (Fin (m + 1)) K) =
      (AutPSU.rootU (f := f) (K := K) m : GL (Fin (m + 1)) K) * d := by
    rw [hddef]
    exact diagGL_comm_rootU h (by omega)
      (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) h0 hl
  have hd_comm_y₀ : (d : GL (Fin (m + 1)) K) *
        (AutPSU.lroot (unitaryInvolution K 2 f) hi₀ : GL (Fin (m + 1)) K) =
      (AutPSU.lroot (unitaryInvolution K 2 f) hi₀ : GL (Fin (m + 1)) K) * d := by
    rw [hddef]
    exact diagGL_comm_lroot h (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) h0 hl
  have hd_fixes_r₀ : primeFormConjHom h (gramJm (K := K) m) ⟨d, hdU⟩ r₀ = r₀ := by
    rw [hr₀, AutPSU.projU_apply, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change d * ((AutPSU.rootU (f := f) (K := K) m : SU σ (m + 1)) : GL (Fin (m + 1)) K) * d⁻¹ =
      ((AutPSU.rootU (f := f) (K := K) m : SU σ (m + 1)) : GL (Fin (m + 1)) K)
    rw [hd_comm_r₀]
    group
  have hd_fixes_y₀ : primeFormConjHom h (gramJm (K := K) m) ⟨d, hdU⟩ y₀ = y₀ := by
    rw [hy₀, AutPSU.projU_apply, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change d * ((AutPSU.lroot (unitaryInvolution K 2 f) hi₀ :
      SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) * d⁻¹ =
      ((AutPSU.lroot (unitaryInvolution K 2 f) hi₀ :
        SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K)
    rw [hd_comm_y₀]
    group
  have hc_r₀ : c r₀ = r₀ := by
    rw [hr₀]
    exact AutPSU.compl_fixes_rootU h (by omega) hc
  have hc_y₀ : c y₀ = y₀ := by
    rw [hy₀]
    exact AutPSU.compl_fixes_lroot h hc hi₀
  set c' : MulAut (AutPSU.PJ h (m + 1)) :=
    primeFormConjHom h (gramJm (K := K) m) ⟨d, hdU⟩ * c with hc'def
  have hc'_r₀ : c' r₀ = r₀ := by
    rw [hc'def, MulAut.mul_apply, hc_r₀, hd_fixes_r₀]
  have hc'_y₀ : c' y₀ = y₀ := by
    rw [hc'def, MulAut.mul_apply, hc_y₀, hd_fixes_y₀]
  have hα' : ∀ k : AutPSU.PJ h (m + 1),
      α k = ((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)) * c' k *
        (((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)))⁻¹ := by
    intro k
    rw [hαeq, hsplit, hc'def]
    rfl
  have hconj : ∀ k : AutPSU.PJ h (m + 1),
      a * ψ k * a⁻¹ = ψ (((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)) *
        c' k * (((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)))⁻¹) := by
    intro k
    rw [← hα k, hα']
  obtain ⟨g, hgL, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha
    (c := c'.toMonoidHom) (g := ((⟨s, hs⟩ : AutPSU.XJ h (m + 1)) : AutPSU.PJ h (m + 1)))
    (by simpa [hc'def] using hc'_r₀) hconj
  have hc1 : c = 1 := by
    refine eq_one_of_conj_levi h hm hc (A := ⟨d, hdU⟩) hd_comm_r₀ hd_comm_y₀ hgL ?_
    intro k hkL hckL
    have := hkey k hkL hckL
    simpa [hc'def] using this
  have hα_in : α ∈ AutPSU.inndiag h := by
    rw [hαeq, hc1, mul_one]
    exact ⟨A, rfl⟩
  have hα2 : ∃ n, α ^ 2 ^ n = 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp
      (GGRootNorm.isPGroup_pCoreOf (Subgroup.normalizer (ψ.range : Set G) ⊓
        Subgroup.centralizer {ψ r₀})))
      (⟨a, ha⟩ : ↥(pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
        Subgroup.centralizer {ψ r₀})))
    have ha_pow : a ^ 2 ^ n = 1 := by
      have h1 : (⟨a, ha⟩ : ↥(pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
          Subgroup.centralizer {ψ r₀}))) ^ 2 ^ n = 1 := by
        rw [← hn]
        exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl _)
      have h1' : ((⟨a, ha⟩ : ↥(pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
          Subgroup.centralizer {ψ r₀}))) : G) ^ 2 ^ n = 1 := congrArg Subtype.val h1
      simpa using h1'
    have hpow : ∀ j : ℕ, ∀ k : AutPSU.PJ h (m + 1),
        ψ ((α ^ j) k) = a ^ j * ψ k * (a ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro k; simp
      | succ j ih =>
          intro k
          rw [pow_succ']
          change ψ (α ((α ^ j) k)) = a ^ (j + 1) * ψ k * (a ^ (j + 1))⁻¹
          rw [hα, ih, pow_succ']
          group
    refine ⟨n, ?_⟩
    ext k
    apply hψ
    rw [hpow (2 ^ n) k, ha_pow]
    simp
  obtain ⟨n, hαn⟩ := hα2
  let Inn : Subgroup (MulAut (AutPSU.PJ h (m + 1))) :=
    (MulAut.conj : AutPSU.PJ h (m + 1) →* MulAut (AutPSU.PJ h (m + 1))).range
  have hInn_normal : Inn.Normal :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.normal_range_conj
  have hInn_le : Inn ≤ AutPSU.inndiag h := AutPSU.inn_le_inndiag h
  haveI : (Inn.subgroupOf (AutPSU.inndiag h)).Normal := hInn_normal.subgroupOf _
  let q : (AutPSU.inndiag h) ⧸ (Inn.subgroupOf (AutPSU.inndiag h)) :=
    QuotientGroup.mk ⟨α, hα_in⟩
  have hq_pow : q ^ 2 ^ n = 1 := by
    rw [show q = QuotientGroup.mk (s := Inn.subgroupOf (AutPSU.inndiag h)) ⟨α, hα_in⟩ from rfl,
      ← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    exact hαn
  have hq_order : orderOf q ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hq_pow
  have hq_card : orderOf q ∣ Nat.card ((AutPSU.inndiag h) ⧸
      (Inn.subgroupOf (AutPSU.inndiag h))) := orderOf_dvd_natCard q
  have hcard_odd : Odd (Nat.card ((AutPSU.inndiag h) ⧸
      (Inn.subgroupOf (AutPSU.inndiag h)))) := by
    rw [← Subgroup.index_eq_card (H := Inn.subgroupOf (AutPSU.inndiag h))]
    exact AutPSU.odd_relIndex_inn_inndiag h
  have hq1 : q = 1 := by
    have hqord1 : orderOf q = 1 := by
      by_contra hne
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hq_order
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hj
        exact hne hj
      have h2dvd : 2 ∣ Nat.card ((AutPSU.inndiag h) ⧸
          (Inn.subgroupOf (AutPSU.inndiag h))) := by
        refine dvd_trans ?_ hq_card
        rw [hj]
        exact dvd_pow_self 2 hj0
      exact (Nat.not_even_iff_odd.mpr hcard_odd) (even_iff_two_dvd.mpr h2dvd)
    exact orderOf_eq_one_iff.mp hqord1
  have hα_inner : α ∈ Inn := by
    have hmem : (⟨α, hα_in⟩ : AutPSU.inndiag h) ∈ Inn.subgroupOf (AutPSU.inndiag h) := by
      exact (QuotientGroup.eq_one_iff (G := AutPSU.inndiag h)
        (N := Inn.subgroupOf (AutPSU.inndiag h)) (x := ⟨α, hα_in⟩)).mp hq1
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨g', hg'⟩ := hα_inner
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := g') fun k => by
    rw [← hα k, ← hg']
    rfl

end KGPSU

section Tag

theorem ggRootCentOTwoTag_PSU : GGRootCentOTwoTag .PSU := by
  change ∀ (G : Type) [Group G] [Finite G] (n f : ℕ)
      (ψ : (ggU .PSU n f).K →* G),
      StatedLieAdmissible .PSU n 2 f → 2 ≤ (ggU .PSU n f).D.rank →
      ψ.ker ≤ Subgroup.center (ggU .PSU n f).K → commutator ↥ψ.range = ⊤ →
      LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .PSU n 2 f →
      Subgroup.centralizer (ψ.range : Set G) = ⊥ →
      (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧
        p ^ 4 ≤ Nat.card Bs ∧ Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧
        ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSU n f).D ψ b) →
      ∀ r : G, GGRootInvolution (ggU .PSU n f).D .PSU ψ r →
        ¬ Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer {r}) →
        pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
          Subgroup.centralizer {r}) ≤ ψ.range
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ hadm hrank hker _ _ hC _ r hr _
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrank
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      card_galoisField_two_mul 2 f hf
    have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
      RootDetectSU.unitaryFieldData_two hK hf
    have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := hC
    obtain ⟨w, hw⟩ := AutPSU.exists_conj_rootU_of_rootInvolution (f := f) (m := m)
      (K := GaloisField 2 (2 * f)) hK hr
    set Θ : AutPSU.PJ h (m + 1) ≃* ψ.range :=
      AutPSU.projEquivU h hn hker hC' with hΘ
    set ψP : AutPSU.PJ h (m + 1) →* G :=
      (ψ.range.subtype).comp Θ.toMonoidHom with hψPdef
    have hψP : Function.Injective ψP := by
      intro x y hxy
      exact Θ.injective (Subtype.ext hxy)
    have hrangeΘ : Θ.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr Θ.surjective
    have hrangeP : ψP.range = ψ.range := by
      rw [hψPdef, MonoidHom.range_comp, hrangeΘ, Subgroup.map_top]
      exact Subgroup.range_subtype _
    have hproj : ∀ x, ψP (AutPSU.projU h x) = ψ x := by
      intro x
      exact AutPSU.projEquivU_projU h hn hker hC' x
    set ψ' : AutPSU.PJ h (m + 1) →* G :=
      ψP.comp (MulAut.conj (AutPSU.projU h w)).toMonoidHom with hψ'def
    have hψ' : Function.Injective ψ' := by
      intro x y hxy
      exact (MulAut.conj (AutPSU.projU h w)).injective (hψP hxy)
    have hrangee : (MulAut.conj (AutPSU.projU h w)).toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (MulAut.conj (AutPSU.projU h w)).surjective
    have hrange' : ψ'.range = ψ.range := by
      rw [hψ'def, MonoidHom.range_comp, hrangee, Subgroup.map_top]
      exact hrangeP
    have hC'' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
      rw [hrange']
      exact hC'
    have hz' : ψ' (AutPSU.projU h (AutPSU.rootU (f := f) m)) = r := by
      rw [hψ'def, MonoidHom.comp_apply]
      change ψP ((MulAut.conj (AutPSU.projU h w))
        (AutPSU.projU h (AutPSU.rootU (f := f) m))) = r
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hproj]
      exact hw.symm
    have hmain := KGPSU.pCoreOf_le_range_of_rootU h hm hψ' hC''
    rw [hrange', hz'] at hmain
    exact hmain
  · intro ψ hadm
    exact absurd hadm.2.1 hf

end Tag

end CFSG.StandardType
