module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivLinear
public import CFSG.LieType.SemisimpleCentralizers.HeldTwoDimUnitaryBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.Open.StatedAPI
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.AGLEmbedding.LeviBlock Matrix
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

private def finTwoToFin (a : ℕ) (ha : 2 ≤ a) : Fin 2 → Fin a :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt ha⟩

private lemma finTwoToFin_injective (a : ℕ) (ha : 2 ≤ a) :
    Function.Injective (finTwoToFin a ha) := by
  intro i j h
  have hv : (i : ℕ) = (j : ℕ) := congrArg (fun x : Fin a => (x : ℕ)) h
  exact Fin.ext hv

private noncomputable def extendSLTwoHom (E : Type) [Field E] (a : ℕ) (ha : 2 ≤ a) :
    SpecialLinearGroup (Fin 2) E →* SpecialLinearGroup (Fin a) E where
  toFun X := ⟨extendMat (finTwoToFin_injective a ha) X.val, by
    rw [det_extendMat]
    exact X.2⟩
  map_one' := Subtype.ext (by
    show extendMat (finTwoToFin_injective a ha) (1 : Matrix (Fin 2) (Fin 2) E) = 1
    rw [extendMat_one])
  map_mul' X Y := Subtype.ext (by
    show extendMat (finTwoToFin_injective a ha) ((X : Matrix (Fin 2) (Fin 2) E) *
      (Y : Matrix (Fin 2) (Fin 2) E)) =
      extendMat (finTwoToFin_injective a ha) (X : Matrix (Fin 2) (Fin 2) E) *
        extendMat (finTwoToFin_injective a ha) (Y : Matrix (Fin 2) (Fin 2) E)
    rw [extendMat_mul])

private noncomputable def blockSLToProj (E : Type) [Field E] (a : ℕ) (ha : 2 ≤ a) :
    SpecialLinearGroup (Fin 2) E →* StatedProj (StatedSL a E) :=
  (QuotientGroup.mk' ((StatedScalars (Fin a) E).subgroupOf (StatedSL a E))).comp
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL a E).toMonoidHom.comp
      (extendSLTwoHom E a ha))

private lemma blockSLToProj_injective (E : Type) [Field E] (a : ℕ) (ha : 2 ≤ a)
    (h2 : (2 : E) = 0) : Function.Injective (blockSLToProj E a ha) := by
  refine (injective_iff_map_eq_one (blockSLToProj E a ha)).mpr ?_
  intro X hX
  simp only [blockSLToProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hX
  obtain ⟨c, hc⟩ := hX
  have hmat : Matrix.scalar (Fin a) (c : E) =
      extendMat (finTwoToFin_injective a ha) (X : Matrix (Fin 2) (Fin 2) E) := by
    calc Matrix.scalar (Fin a) (c : E)
        = ((Matrix.GeneralLinearGroup.scalar (Fin a) c : GL (Fin a) E) :
            Matrix (Fin a) (Fin a) E) := (Matrix.GeneralLinearGroup.coe_scalar c).symm
      _ = ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL a E
            ((extendSLTwoHom E a ha) X) : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) :=
          congrArg (fun g : GL (Fin a) E => (g : Matrix (Fin a) (Fin a) E)) hc
      _ = extendMat (finTwoToFin_injective a ha) (X : Matrix (Fin 2) (Fin 2) E) :=
          CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe a E _
  have hsub : (X : Matrix (Fin 2) (Fin 2) E) = Matrix.scalar (Fin 2) (c : E) := by
    calc (X : Matrix (Fin 2) (Fin 2) E)
        = (extendMat (finTwoToFin_injective a ha) (X : Matrix (Fin 2) (Fin 2) E)).submatrix
            (finTwoToFin a ha) (finTwoToFin a ha) := (submatrix_extendMat _ _).symm
      _ = (Matrix.scalar (Fin a) (c : E)).submatrix (finTwoToFin a ha) (finTwoToFin a ha) := by
            rw [hmat]
      _ = Matrix.scalar (Fin 2) (c : E) := by
            rw [Matrix.scalar_apply, Matrix.scalar_apply,
              Matrix.submatrix_diagonal (fun _ => (c : E)) (finTwoToFin a ha)
                (finTwoToFin_injective a ha)]
            rfl
  have hc2 : (c : E) * (c : E) = 1 := by
    have hx1 : (X : Matrix (Fin 2) (Fin 2) E).det = 1 := X.2
    rw [hsub, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hx1
    simpa using hx1
  have hc1 : (c : E) = 1 := by
    have h : ((c : E) - 1) * ((c : E) - 1) = 0 := by
      linear_combination hc2 - ((c : E) - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  apply Subtype.ext
  show (X : Matrix (Fin 2) (Fin 2) E) = (1 : Matrix (Fin 2) (Fin 2) E)
  rw [hsub, hc1]
  simp

theorem prime_dvd_card_statedProj_statedSL {E : Type} [Field E] [Finite E] {a p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a) (h2 : (2 : E) = 0)
    (hdvd : p ∣ Nat.card E ^ 2 - 1) : p ∣ Nat.card (StatedProj (StatedSL a E)) := by
  have hcard : Nat.card (StatedSL 2 E) = Nat.card E * (Nat.card E ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_statedSL_two E
  have hdivSL : Nat.card (SpecialLinearGroup (Fin 2) E) ∣
      Nat.card (StatedProj (StatedSL a E)) :=
    Subgroup.card_dvd_of_injective (blockSLToProj E a ha) (blockSLToProj_injective E a ha h2)
  have hdiv : Nat.card (StatedSL 2 E) ∣ Nat.card (StatedProj (StatedSL a E)) := by
    rwa [← CFSG.Open.StatedAPI.card_statedSL] at hdivSL
  exact (dvd_mul_of_dvd_right hdvd _).trans (hcard ▸ hdiv)

private noncomputable def blockSUToProj (E : Type) [Field E] [Finite E] (f a : ℕ)
    [Fact (Nat.Prime 2)] [CharP E 2] (hE : Nat.card E = (2 ^ f) ^ 2) (ha : 2 ≤ a) :
    Su E 2 f 2 →* StatedProj (StatedSU a (2 ^ f) E) :=
  (QuotientGroup.mk' ((StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ f) E))).comp
    ((MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE a)).toMonoidHom.comp
      (blockEmb E 2 f a 2 0 (by omega)))

private lemma blockSUToProj_injective (E : Type) [Field E] [Finite E] (f a : ℕ)
    [Fact (Nat.Prime 2)] [CharP E 2] (hE : Nat.card E = (2 ^ f) ^ 2) (ha : 2 ≤ a) :
    Function.Injective (blockSUToProj E f a hE ha) := by
  refine (injective_iff_map_eq_one (blockSUToProj E f a hE ha)).mpr ?_
  intro X hX
  simp only [blockSUToProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hX
  obtain ⟨c, hc⟩ := hX
  have hmat : blockMat (F := E) a 0 ((X : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      Matrix.scalar (Fin a) (c : E) := by
    calc blockMat (F := E) a 0 ((X : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)
        = ((((blockEmb E 2 f a 2 0 (by omega)) X : Su E 2 f a) : GL (Fin a) E) :
            Matrix (Fin a) (Fin a) E) := (coe_coe_blockEmb _ X).symm
      _ = ((((MulEquiv.subgroupCongr
              (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE a))
              ((blockEmb E 2 f a 2 0 (by omega)) X) : StatedSU a (2 ^ f) E) :
            GL (Fin a) E) : Matrix (Fin a) (Fin a) E) := rfl
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin a) c : GL (Fin a) E) :
            Matrix (Fin a) (Fin a) E) := by
            exact (congrArg (fun g : GL (Fin a) E => (g : Matrix (Fin a) (Fin a) E)) hc).symm
      _ = Matrix.scalar (Fin a) (c : E) := Matrix.GeneralLinearGroup.coe_scalar c
  have hXval : ((X : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      Matrix.scalar (Fin 2) (c : E) := by
    ext x y
    have h := blockMat_apply_blockIdx (F := E) (i := 0) (k := 2) (m := a)
      (by omega) ((X : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) x y
    rw [hmat] at h
    rw [← h]
    simp only [Matrix.scalar_apply, Matrix.diagonal, blockIdx_val, Fin.ext_iff]
    by_cases hxy : x = y
    · subst hxy; simp
    · have : ¬ (0 + x.val = 0 + y.val) := fun h' => hxy (Fin.ext (by omega))
      simp [hxy, this]
  have hdet : ((X : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det = 1 :=
    (mem_SUid.mp X.2).1
  have hc2 : (c : E) * (c : E) = 1 := by
    rw [hXval, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    simpa using hdet
  have hc1 : (c : E) = 1 := by
    have h : ((c : E) - 1) * ((c : E) - 1) = 0 := by
      have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
      linear_combination hc2 - ((c : E) - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  apply Subtype.ext
  apply Units.ext
  rw [hXval, hc1]
  simp

theorem prime_dvd_card_statedProj_statedSU {E : Type} [Field E] [Finite E]
    {f a p : ℕ} [Fact (Nat.Prime 2)] [CharP E 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hE : Nat.card E = (2 ^ f) ^ 2) (hdvd : p ∣ (2 ^ f) ^ 2 - 1) :
    p ∣ Nat.card (StatedProj (StatedSU a (2 ^ f) E)) := by
  have hcard : Nat.card (Su E 2 f 2) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [show Nat.card (Su E 2 f 2) = Nat.card ↥(StatedSU 2 (2 ^ f) E) from
      Nat.card_congr (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE 2)).toEquiv]
    exact CFSG.RankThree.SubgroupLists.card_statedSU_two (r := 2) (f := f) hE
  have hdvdSu : p ∣ Nat.card (Su E 2 f 2) := (dvd_mul_of_dvd_right hdvd _).trans (by rw [hcard])
  exact hdvdSu.trans (Subgroup.card_dvd_of_injective (blockSUToProj E f a hE ha)
    (blockSUToProj_injective E f a hE ha))

theorem map_ggFixSub_conj_eq_centralizer {X : Type} [Group X] {H : Subgroup X} (x : ↥H) :
    (ggFixSub (MulAut.conj x)).map H.subtype =
      Subgroup.centralizer ({(x : X)} : Set X) ⊓ H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, z.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz' : (x : X) * (z : X) * (x : X)⁻¹ = (z : X) :=
      congrArg (fun w : ↥H => (w : X)) hz
    calc (z : X) * (x : X) = ((x : X) * (z : X) * (x : X)⁻¹) * (x : X) := by rw [hz']
      _ = (x : X) * (z : X) := by group
  · rintro ⟨hy, hyH⟩
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    have h2 : y * (x : X) = (x : X) * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    show (MulAut.conj x) ⟨y, hyH⟩ = ⟨y, hyH⟩
    apply Subtype.ext
    show (x : X) * y * (x : X)⁻¹ = y
    calc (x : X) * y * (x : X)⁻¹ = (y * (x : X)) * (x : X)⁻¹ := by rw [← h2]
      _ = y := by group

private lemma orderOf_cast_ne_zero {K : Type} [Field K] [CharP K 2] {N p : ℕ}
    {x : GL (Fin N) K} (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ^ p = 1) :
    ((orderOf x : ℕ) : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K 2]
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have hodd : Odd (orderOf x) := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · rw [h1]; exact odd_one
    · rw [hp']; exact hp.odd_of_ne_two hp2
  exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private lemma coe_pow_eq_one {G : Type*} [Group G] {L : Subgroup G} {p : ℕ} {x : ↥L}
    (hx : x ^ p = 1) : ((x : G)) ^ p = 1 := by
  simpa using congrArg (fun g : ↥L => (g : G)) hx

private lemma dvd_sq_sub_one_of_dvd_sub_one_or_add_one {p q : ℕ}
    (h : p ∣ q - 1 ∨ p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  rcases h with h | h
  · exact h.trans (Nat.sub_one_dvd_pow_sub_one q 2)
  · have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      rw [sq, mul_self_tsub_one, mul_comm]
    rw [hsq]
    exact h.trans (dvd_mul_of_dvd_right (dvd_refl _) _)

private lemma dvd_card_of_dvd_card_quotient_center {G : Type*} [Group G] {p : ℕ}
    {J : Subgroup G} (h : p ∣ Nat.card (J ⧸ Subgroup.center J)) : p ∣ Nat.card J := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
  exact dvd_mul_of_dvd_left h _

private lemma exists_lift_component_to_gl {N : ℕ} {K : Type} [Field K]
    (L : Subgroup (GL (Fin N) K)) (x : ↥L) {J : Subgroup (LargeEvenProj L)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (ggFixSub (MulAut.conj (LargeEvenProjMk L x)))) :
    ∃ (J' : Subgroup ↥L) (J'' : Subgroup (GL (Fin N) K)),
      CFSG.Assembly.IsComponentOf J' (ggFixSub (MulAut.conj x)) ∧
      CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
        ({(x : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ L) ∧
      Nonempty (J' ⧸ Subgroup.center J' ≃* J ⧸ Subgroup.center J) ∧
      Nat.card (J' ⧸ Subgroup.center J') = Nat.card (J'' ⧸ Subgroup.center J'') := by
  obtain ⟨J', hJ', ⟨eJJ⟩⟩ := ggK1_lift_component
    (LargeEvenProjMk L) (QuotientGroup.mk'_surjective _)
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ker_projMk_uni_le_center L)
    (MulAut.conj x) (MulAut.conj (LargeEvenProjMk L x))
    (fun l => by simp [MulAut.conj_apply, map_mul, map_inv]) hJ
  let J'' : Subgroup (GL (Fin N) K) := J'.map L.subtype
  have hmap : (ggFixSub (MulAut.conj x)).map L.subtype =
      Subgroup.centralizer ({(x : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ L :=
    map_ggFixSub_conj_eq_centralizer x
  have hJ'' : CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
      ({(x : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ L) := by
    refine (CFSG.Assembly.isComponentOf_iff_open).mp ?_
    rw [← hmap]
    exact ⟨Subgroup.map_mono hJ'.1, hJ'.2.1.map L.subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective J' L.subtype Subtype.val_injective).symm hJ'.2.2⟩
  refine ⟨J', J'', hJ', hJ'', ⟨eJJ⟩, ?_⟩
  have ee : ↥J' ≃* ↥J'' := Subgroup.equivMapOfInjective J' L.subtype Subtype.val_injective
  exact Nat.card_congr (QuotientGroup.congr (Subgroup.center J') (Subgroup.center J'')
    ee (Subgroup.map_center_eq ee)).toEquiv

private lemma dvd_card_quotient_center_of_heldSL
    {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] [Finite E]
    {N nf a p : ℕ} {J : Subgroup (GL (Fin N) K)}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a) (h2K : (2 : K) = 0)
    (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hquot : Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E))) :
    p ∣ Nat.card (J ⧸ Subgroup.center J) := by
  have h2E : (2 : E) = 0 := by
    calc (2 : E) = algebraMap K E 2 := (map_ofNat (algebraMap K E) 2).symm
      _ = algebraMap K E 0 := by rw [h2K]
      _ = 0 := map_zero _
  have hdvdK : p ∣ Nat.card K ^ 2 - 1 := by
    rw [hK]
    exact dvd_sq_sub_one_of_dvd_sub_one_or_add_one hdvd
  have hdvdE : p ∣ Nat.card E ^ 2 - 1 := by
    have hEk : Nat.card E = Nat.card K ^ Module.finrank K E :=
      Module.natCard_eq_pow_finrank
    rw [hEk, ← pow_mul, mul_comm (Module.finrank K E) 2, pow_mul]
    exact hdvdK.trans (Nat.sub_one_dvd_pow_sub_one (Nat.card K ^ 2) (Module.finrank K E))
  have hdiv : p ∣ Nat.card (StatedProj (StatedSL a E)) :=
    prime_dvd_card_statedProj_statedSL hp hp2 ha h2E hdvdE
  obtain ⟨e⟩ := hquot
  rw [Nat.card_congr e.toEquiv]
  exact hdiv

private lemma dvd_card_quotient_center_heldSU_two
    {E : Type} [Field E] [Finite E] {nf dd p : ℕ} [Fact (Nat.Prime 2)] [CharP E 2]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hEcard2 : Nat.card E = (2 ^ (nf * dd)) ^ 2)
    (hτ'm : ∀ x, τ' x = x ^ (2 ^ (nf * dd)))
    (hdvdE' : p ∣ (2 ^ (nf * dd)) ^ 2 - 1) :
    p ∣ Nat.card (heldSU 2 E τ' hτ' ⧸
      Subgroup.center (heldSU 2 E τ' hτ')) := by
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨e2⟩ := nonempty_quotientCenter_heldSU_two_equiv_statedProj
    (p := 2) (k := nf * dd) (Q := 2 ^ (nf * dd)) rfl hEcard2 hτ'm
  have hFcard : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (nf * dd)) =
      2 ^ (nf * dd) := CFSG.LieType.Steinberg.card_fixedSubfield hEcard2
  haveI : CharP ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (nf * dd)) 2 :=
    CFSG.ComponentClassification.RankTwoClassical.charP_fixedSubfield hEcard2
  have h2F : (2 : ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (nf * dd))) = 0 :=
    CharP.cast_eq_zero _ 2
  have hdvdF : p ∣
      Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 (nf * dd)) ^ 2 - 1 := by
    rw [hFcard]
    exact hdvdE'
  have hdiv := prime_dvd_card_statedProj_statedSL hp hp2 (le_refl 2) h2F hdvdF
  rwa [Nat.card_congr e2.toEquiv]

private lemma dvd_card_quotient_center_heldSU_ge_three
    {E : Type} [Field E] [Finite E] {nf dd a p : ℕ} [Fact (Nat.Prime 2)] [CharP E 2]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha3 : 3 ≤ a)
    (hEcard2 : Nat.card E = (2 ^ (nf * dd)) ^ 2)
    (hτ'm : ∀ x, τ' x = x ^ (2 ^ (nf * dd)))
    (hdvdE' : p ∣ (2 ^ (nf * dd)) ^ 2 - 1)
    (h32 : (a, 2 ^ (nf * dd)) ≠ (3, 2)) :
    p ∣ Nat.card (heldSU a E τ' hτ' ⧸
      Subgroup.center (heldSU a E τ' hτ')) := by
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'm hEcard2 ha3 h32
  have ha : 2 ≤ a := by omega
  have hdiv := prime_dvd_card_statedProj_statedSU hp hp2 ha hEcard2 hdvdE'
  rwa [Nat.card_congr eP.toEquiv]

private lemma false_of_solvable_heldSU_three_two
    {J : Type} [Group J] (hsimple : IsSimpleGroup (J ⧸ Subgroup.center J))
    {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 2)] [CharP E 2]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hτ'2 : ∀ x, τ' x = x ^ 2) (hE4 : Nat.card E = 4)
    (hquot : Nonempty (J ⧸ Subgroup.center J ≃*
      heldSU 3 E τ' hτ' ⧸ Subgroup.center (heldSU 3 E τ' hτ'))) : False := by
  haveI := hsimple
  obtain ⟨e⟩ := hquot
  haveI : Group.IsSolvable (heldSU 3 E τ' hτ' ⧸
      Subgroup.center (heldSU 3 E τ' hτ')) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
      τ' hτ' hτ'2 hE4
  have hsol : Group.IsSolvable (J ⧸ Subgroup.center J) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
    (J := J) hsol

private lemma dvd_card_quotient_center_of_heldSU
    {E : Type} [Field E] [Finite E] {nf dd a p : ℕ} [Fact (Nat.Prime 2)]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hEcard2 : Nat.card E = (2 ^ (nf * dd)) ^ 2)
    (hτ'm : ∀ x, τ' x = x ^ (2 ^ (nf * dd)))
    (hdvdE' : p ∣ (2 ^ (nf * dd)) ^ 2 - 1)
    {R : Type} [Group R] (hsimple : IsSimpleGroup (R ⧸ Subgroup.center R))
    (hquot : Nonempty (R ⧸ Subgroup.center R ≃*
      heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) :
    p ∣ Nat.card (R ⧸ Subgroup.center R) := by
  letI : Fintype E := Fintype.ofFinite E
  have hEtwo : Nat.card E = 2 ^ (2 * (nf * dd)) := by
    rw [hEcard2, ← pow_mul, show (nf * dd) * 2 = 2 * (nf * dd) by ring]
  haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * (nf * dd))
    (by rw [← Nat.card_eq_fintype_card]; exact hEtwo)
  obtain ⟨e⟩ := hquot
  rw [Nat.card_congr e.toEquiv]
  by_cases ha2 : a = 2
  · subst ha2
    exact dvd_card_quotient_center_heldSU_two τ' hτ' hp hp2 hEcard2 hτ'm hdvdE'
  · have ha3 : 3 ≤ a := by omega
    by_cases h32 : (a, 2 ^ (nf * dd)) = (3, 2)
    · exfalso
      obtain ⟨rfl, hq2⟩ := Prod.mk.inj h32
      have hE4 : Nat.card E = 4 := by rw [hEcard2, hq2]; norm_num
      have hτ'2 : ∀ x, τ' x = x ^ 2 := fun x => by rw [hτ'm x, hq2]
      exact false_of_solvable_heldSU_three_two hsimple τ' hτ' hτ'2 hE4 ⟨e⟩
    · exact dvd_card_quotient_center_heldSU_ge_three τ' hτ' hp hp2 ha3 hEcard2 hτ'm hdvdE' h32

private lemma dvd_card_quotient_center_of_heldSU_alt
    {E : Type} [Field E] [Finite E] {nf dd a p : ℕ} [Fact (Nat.Prime 2)]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (hEcard : Nat.card E = ((2 ^ nf) ^ dd) ^ 2)
    (hτ'Q : ∀ x, τ' x = x ^ ((2 ^ nf) ^ dd))
    (hdvdQ : p ∣ (2 ^ nf) ^ 2 - 1)
    {R : Type} [Group R] (hsimple : IsSimpleGroup (R ⧸ Subgroup.center R))
    (hquot : Nonempty (R ⧸ Subgroup.center R ≃*
      heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) :
    p ∣ Nat.card (R ⧸ Subgroup.center R) := by
  have hEcard2 : Nat.card E = (2 ^ (nf * dd)) ^ 2 := by
    rw [hEcard]
    calc ((2 ^ nf) ^ dd) ^ 2 = 2 ^ (nf * (dd * 2)) := by rw [← pow_mul, ← pow_mul]
      _ = 2 ^ ((nf * dd) * 2) := by rw [show nf * (dd * 2) = (nf * dd) * 2 by ring]
      _ = (2 ^ (nf * dd)) ^ 2 := pow_mul 2 (nf * dd) 2
  have hτ'm : ∀ x, τ' x = x ^ (2 ^ (nf * dd)) := by
    intro x
    rw [hτ'Q x, ← pow_mul]
  have hdvdE' : p ∣ (2 ^ (nf * dd)) ^ 2 - 1 := by
    have hpow : (2 ^ (nf * dd)) ^ 2 = ((2 ^ nf) ^ 2) ^ dd := by
      calc (2 ^ (nf * dd)) ^ 2 = 2 ^ ((nf * dd) * 2) := (pow_mul 2 (nf * dd) 2).symm
        _ = 2 ^ (nf * (2 * dd)) := by
          rw [show (nf * dd) * 2 = nf * (2 * dd) by ring]
        _ = ((2 ^ nf) ^ 2) ^ dd := by rw [← pow_mul, ← pow_mul]
    rw [hpow]
    exact hdvdQ.trans (Nat.sub_one_dvd_pow_sub_one ((2 ^ nf) ^ 2) dd)
  exact dvd_card_quotient_center_of_heldSU τ' hτ' hp hp2 ha hEcard2 hτ'm hdvdE' hsimple hquot

private lemma dvd_card_quotient_center_of_heldSL_unitary_alt
    {E : Type} [Field E] [Finite E] {nf e₀ b p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hb : 2 ≤ b)
    (hEcard : Nat.card E = (2 ^ nf) ^ (2 * e₀))
    (hdvdQ : p ∣ (2 ^ nf) ^ 2 - 1)
    {R : Type*} [Group R]
    (hquot : Nonempty (R ⧸ Subgroup.center R ≃* StatedProj (StatedSL b E))) :
    p ∣ Nat.card (R ⧸ Subgroup.center R) := by
  letI : Fintype E := Fintype.ofFinite E
  have hEtwo : Nat.card E = 2 ^ (nf * (2 * e₀)) := by
    rw [hEcard, ← pow_mul]
  haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := nf * (2 * e₀))
    (by rw [← Nat.card_eq_fintype_card]; exact hEtwo)
  have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hdvdE : p ∣ Nat.card E ^ 2 - 1 := by
    rw [hEcard]
    have hpow : ((2 ^ nf) ^ (2 * e₀)) ^ 2 = ((2 ^ nf) ^ 2) ^ (2 * e₀) := by
      calc ((2 ^ nf) ^ (2 * e₀)) ^ 2 = (2 ^ nf) ^ ((2 * e₀) * 2) := by rw [← pow_mul]
        _ = (2 ^ nf) ^ (2 * (2 * e₀)) := by
          rw [show (2 * e₀) * 2 = 2 * (2 * e₀) by ring]
        _ = ((2 ^ nf) ^ 2) ^ (2 * e₀) := by rw [pow_mul]
    rw [hpow]
    exact hdvdQ.trans (Nat.sub_one_dvd_pow_sub_one ((2 ^ nf) ^ 2) (2 * e₀))
  have hdiv : p ∣ Nat.card (StatedProj (StatedSL b E)) :=
    prime_dvd_card_statedProj_statedSL hp hp2 hb h2E hdvdE
  obtain ⟨e⟩ := hquot
  rw [Nat.card_congr e.toEquiv]
  exact hdiv

private lemma unitary_component_setup {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ (2 ^ nf))
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1)
    {J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (ggFixSub (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat)))) :
    ∃ (J' : Subgroup ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)))
      (J'' : Subgroup (GL (Fin N) K)),
      CFSG.Assembly.IsComponentOf J' (ggFixSub (MulAut.conj xhat)) ∧
      Nonempty (J' ⧸ Subgroup.center J' ≃* J ⧸ Subgroup.center J) ∧
      Nat.card (J' ⧸ Subgroup.center J') = Nat.card (J'' ⧸ Subgroup.center J'') ∧
      CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
        ({(xhat : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ) ∧
      (xhat : GL (Fin N) K) ∈ heldGU N K τ hτ ∧
      ((orderOf (xhat : GL (Fin N) K) : ℕ) : K) ≠ 0 := by
  have hSU : heldSU N K τ hτ = StatedSU N (2 ^ nf) K := hct_heldSU_eq_statedSU hτQ
  obtain ⟨J', J'', hJ', hJ''SU, ⟨eJJ⟩, hcard''⟩ :=
    exists_lift_component_to_gl (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat hJ
  have hJ''Stated : CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
      ({(xhat : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ StatedSU N (2 ^ nf) K) := by
    rw [← largeEvenSUGroup_eq_statedSU N (2 ^ nf)]
    exact hJ''SU
  have hJ'' : CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
      ({(xhat : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ heldSU N K τ hτ) := by
    rw [hSU]
    exact hJ''Stated
  have hJ''GU : CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
      ({(xhat : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isComponentOf_centralizer_gu_of_su hτ
      (xhat : GL (Fin N) K) hJ''
  have hs : (xhat : GL (Fin N) K) ∈ heldGU N K τ hτ := by
    have hx1 : (xhat : GL (Fin N) K) ∈ StatedSU N (2 ^ nf) K := by
      rw [← largeEvenSUGroup_eq_statedSU N (2 ^ nf)]
      exact xhat.2
    rw [← hSU] at hx1
    exact (Subgroup.mem_inf.mp hx1).1
  have hxhat_pow : ((xhat : GL (Fin N) K)) ^ p = 1 := coe_pow_eq_one hxp
  have hord : ((orderOf (xhat : GL (Fin N) K) : ℕ) : K) ≠ 0 :=
    orderOf_cast_ne_zero hp hp2 hxhat_pow
  exact ⟨J', J'', hJ', ⟨eJJ⟩, hcard'', hJ''GU, hs, hord⟩

theorem ggK1A_core_dvd {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hd : d = ggMultOrd p nf)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m) :
    GGK1Dvd p (LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat)) := by
  intro J hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨J', J'', hJ', hJ''SL, ⟨eJJ⟩, hcard''⟩ :=
    exists_lift_component_to_gl (LargeEvenSLGroup (Fin N) K) xhat hJ
  have hJ'' : CFSG.Open.IsComponentOf J'' (Subgroup.centralizer
      ({(xhat : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
    rw [← largeEvenSLGroup_eq_statedSL N]
    exact hJ''SL
  have hs : (xhat : GL (Fin N) K) ∈ StatedSL N K := by
    rw [← largeEvenSLGroup_eq_statedSL N]
    exact xhat.2
  have hxhat_pow : ((xhat : GL (Fin N) K)) ^ p = 1 := coe_pow_eq_one hxp
  have hord : ((orderOf (xhat : GL (Fin N) K) : ℕ) : K) ≠ 0 :=
    orderOf_cast_ne_zero hp hp2 hxhat_pow
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eJ''⟩⟩ :=
    held_linear_components_unconditional (xhat : GL (Fin N) K) hs hord J'' hJ''
  letI : Field E := hEf
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  have hpJ'' : p ∣ Nat.card (J'' ⧸ Subgroup.center J'') :=
    dvd_card_quotient_center_of_heldSL hp hp2 ha h2K hK hdvd ⟨eJ''⟩
  have hpquot : p ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [Nat.card_congr eJJ.symm.toEquiv, hcard'']
    exact hpJ''
  exact dvd_card_of_dvd_card_quotient_center hpquot

theorem ggK1A_uni_core_dvd {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hd : d = ggMultOrd p nf)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m) :
    GGK1Dvd p (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat)) := by
  intro J hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 ^ (2 * nf) := by
    rw [hK, show (2 ^ nf) ^ 2 = 2 ^ (nf * 2) from (pow_mul 2 nf 2).symm,
      show nf * 2 = 2 * nf by ring]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * nf)
    (by rw [← Nat.card_eq_fintype_card, hK2])
  let τ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 nf
  have hτ : ∀ x, τ (τ x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hK
  have hτQ : ∀ x, τ x = x ^ (2 ^ nf) := CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 nf
  obtain ⟨J', J'', hJ', ⟨eJJ⟩, hcard'', hJ''GU, hs, hord⟩ :=
    unitary_component_setup hp hp2 τ hτ hτQ hxp hJ
  have hdvdQ : p ∣ (2 ^ nf) ^ 2 - 1 :=
    dvd_sq_sub_one_of_dvd_sub_one_or_add_one hdvd
  have hHeld := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.held_unitary_components_gu_sized
    SUComponentsTrivial_holds SLComponentsTrivial_holds hτ hτQ hK
    (xhat : GL (Fin N) K) hs hord J'' hJ''GU
  have hpJ'' : p ∣ Nat.card (J'' ⧸ Subgroup.center J'') := by
    rcases hHeld with ⟨a, dd, E, hEf, hEfin, τ', hτ', ha, hτ'Q, hEcard, ⟨e⟩⟩ |
      ⟨b, e₀, E, hEf, hEfin, hb, hEcard, ⟨eL⟩⟩
    · letI : Field E := hEf
      letI : Finite E := hEfin
      exact dvd_card_quotient_center_of_heldSU_alt τ' hτ' hp hp2 ha hEcard hτ'Q hdvdQ
        hJ''GU.2.2.2 ⟨e⟩
    · letI : Field E := hEf
      letI : Finite E := hEfin
      exact dvd_card_quotient_center_of_heldSL_unitary_alt hp hp2 hb hEcard hdvdQ ⟨eL⟩
  have hpquot : p ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [Nat.card_congr eJJ.symm.toEquiv, hcard'']
    exact hpJ''
  exact dvd_card_of_dvd_card_quotient_center hpquot


end CFSG.StandardType

end
