module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
public import CFSG.Quasithin.H13.U4ParLevi
public import CFSG.Quasithin.H13.U4ParYAmalgam
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LieType.BorelTits.LeviOrder
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open CFSG.Quasithin.H13.U4Par
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.UC22
open TauCeti.Subgroup (normalizerQuotient)

theorem normalizerQuotient_equiv_hypTorus_u4 {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {S : Subgroup (hypSU h 2 0)}
    (hS : IsSylowTwoOf S ⊤) :
    Nonempty (normalizerQuotient S ≃* hypTorus h 2 0) := by
  classical
  have D := CFSG.Quasithin.H13.Sec53F.Unit.borelAutData_u4 h
  obtain ⟨eC⟩ := normalizerQuotient_equiv_of_complement D.H_le D.U_inf_H D.B_eq
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (S := hypUnitriangular h 2 0)
    (S' := S) (MulEquiv.refl (hypSU h 2 0)) D.sylow hS
  exact ⟨eN.symm.trans eC⟩

theorem levHom_hypSU_injective {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K) :
    Function.Injective (levHom h) := by
  intro A B hAB
  have hsub : (⟨levHom h A, levHom_range_le_parH h ⟨A, rfl⟩⟩ : parH h) =
      ⟨levHom h B, levHom_range_le_parH h ⟨B, rfl⟩⟩ := Subtype.ext hAB
  have hρ := congrArg (rhoF h) hsub
  rw [rhoF_levHom h A, rhoF_levHom h B] at hρ
  exact hρ

theorem levHom_range_apply_ie1_ie1 {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    ((((levHom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) ie1 ie1 = 1 := by
  rw [coe_levHom]
  simp [levMat_apply, ie1, ie2, if1, if2]

theorem diagonal_mul_levMat_comm {K : Type} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (e : Ix → K) (hm : e ie2 = e if2) :
    diagonal e * levMat A = levMat A * diagonal e := by
  have hm' : e (Sum.inl 1) = e (Sum.inr (Sum.inr 1)) := by simpa [ie2, if2] using hm
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;>
    rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    (simp [levMat_apply, ie1, ie2, if1, if2, hm']; try ring)

theorem exists_rootLine_hypSU {n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hq : 2 < 2 ^ n)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ 2 ^ n - 1)
    (E : Subgroup (hypSU h 2 0)) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup (hypSU h 2 0), B ≤ E ∧ Nat.card B = r ∧
      (∃ Y0 : Subgroup (hypSU h 2 0),
        Y0 ≤ Subgroup.centralizer (B : Set (hypSU h 2 0)) ∧ IsL2 ↥Y0 n) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
        2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (B : Set (hypSU h 2 0))) ∧
          p ∣ Nat.card (Subgroup.centralizer (E : Set (hypSU h 2 0))) := by
  classical
  have := h.finite
  have : Fact r.Prime := ⟨hr⟩
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp at hq
    · exact hn
  set q : ℕ := 2 ^ n with hqdef
  have hn1 : 1 ≤ n := by omega
  have hcardK : Nat.card K = q ^ 2 := by
    rw [h.card, hqdef, show 2 * n = n * 2 by omega, pow_mul]
  let H := hypSU h 2 0
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 2 n := by
    refine ⟨Nat.prime_two, hn1, by norm_num, ?_⟩
    intro hcon
    simp only [Prod.mk.injEq] at hcon
    omega
  have hClass : CFSG.Open.StatedClassicalModel H .PSU 4 2 n :=
    ⟨hadm, ⟨K, inferInstance, h.finite, hcardK,
      CFSG.Quasithin.H13.U4Par.nonempty_hypSU_equiv_statedProj h⟩⟩
  have hLM : LieModel H .PSU 4 2 n := Or.inl ⟨by decide, hClass⟩
  have hS24 : IsSylowTwoOf (hypUnitriangular h 2 0) ⊤ :=
    CFSG.Quasithin.H13.U4Par.isSylowTwoOf_hypUnitriangular h
  obtain ⟨-, hOmegaCard, hfacH0⟩ :=
    k_U4CartanRank_holds H n hLM hq (hypUnitriangular h 2 0) hS24 r hr (by omega) hrd
  obtain ⟨eT⟩ := normalizerQuotient_equiv_hypTorus_u4 h hS24
  have hfacH : (Nat.card H).factorization r = (Nat.card (hypTorus h 2 0)).factorization r :=
    hfacH0.trans (congrArg (fun m : ℕ => m.factorization r) (Nat.card_congr eT.toEquiv))
  let T : Subgroup H := hypTorus h 2 0
  have hTcomm : ∀ a b : T, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h a.2 b.2)
  let RT : Subgroup T :=
    { carrier := {x | x ^ r = 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Commute.mul_pow (hTcomm a b), ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inv_pow, ha, inv_one] }
  have hRT_eq : RT = CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r (⊤ : Subgroup T) := by
    apply le_antisymm
    · intro x hx
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top x, hx⟩
    · rw [CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p, Subgroup.closure_le]
      intro x hx
      exact hx.2
  have hmapOmega : (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
      (⊤ : Subgroup (normalizerQuotient (hypUnitriangular h 2 0)))).map eT.toMonoidHom =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r (⊤ : Subgroup T) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p,
      CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.mem_top _, by rw [← map_pow eT.toMonoidHom x r, hx.2, map_one]⟩
    · intro hy
      refine ⟨eT.symm y, ⟨Subgroup.mem_top _, ?_⟩, eT.apply_symm_apply y⟩
      have h := congrArg eT.symm hy.2
      simpa using h
  have hOmegaTcard : Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.F11.Omega1p r
      (⊤ : Subgroup T)) = r ^ 2 := by
    rw [← hmapOmega, Subgroup.card_map_of_injective eT.injective, hOmegaCard]
  have hRTcard : Nat.card RT = r ^ 2 := by
    rw [hRT_eq]
    exact hOmegaTcard
  let RTH : Subgroup H := RT.map T.subtype
  have hRTHcard : Nat.card RTH = r ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := T.subtype) T.subtype_injective, hRTcard]
  have hRTH_le_T : RTH ≤ T := Subgroup.map_subtype_le RT
  let PT : Sylow r T := Classical.arbitrary _
  let PJ : Subgroup H := (PT : Subgroup T).map T.subtype
  have hPTcard : Nat.card (PT : Subgroup T) = r ^ (Nat.card T).factorization r :=
    Sylow.card_eq_multiplicity PT
  have hPJcard : Nat.card PJ = r ^ (Nat.card H).factorization r := by
    rw [Subgroup.card_map_of_injective (f := T.subtype) T.subtype_injective, hPTcard, hfacH]
  let PJs : Sylow r H := Sylow.ofCard PJ hPJcard
  have hPJs_coe : (PJs : Subgroup H) = PJ := Sylow.coe_ofCard PJ hPJcard
  obtain ⟨Q, hEQ⟩ := hEel.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q PJs
  have hQconj : (Q : Subgroup H).conjBy g = PJ := by
    have h := congrArg (fun S : Sylow r H => (S : Subgroup H)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [Subgroup.conjBy]
    convert h using 2
    · ext x
      rfl
    · exact hPJs_coe.symm
  have hEQconj : E.conjBy g ≤ PJ := by
    rw [← hQconj]
    exact Subgroup.map_mono hEQ
  let γ : H := g⁻¹
  have hPJ_le_T : PJ ≤ T := Subgroup.map_subtype_le (PT : Subgroup T)
  have hE_g_le_T : E.conjBy g ≤ T := hEQconj.trans hPJ_le_T
  have hE_le_conjT : E ≤ T.conjBy γ := by
    intro x hx
    have hxg : (MulAut.conj g) x ∈ T :=
      hE_g_le_T (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hxeq : (MulAut.conj γ) ((MulAut.conj g) x) = x := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      simp only [γ]
      group
    rw [← hxeq]
    exact Subgroup.mem_map.mpr ⟨(MulAut.conj g) x, hxg, rfl⟩
  let Tγ : Subgroup H := T.conjBy γ
  have hTγ_comm : ∀ a ∈ Tγ, ∀ b ∈ Tγ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
    show (MulAut.conj γ) a0 * (MulAut.conj γ) b0 =
      (MulAut.conj γ) b0 * (MulAut.conj γ) a0
    rw [← map_mul, ← map_mul,
      CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h ha0 hb0]
  have hE_le_Tγ : E ≤ Tγ := hE_le_conjT
  have hRconj_mem : ∀ x : H, x ∈ RTH.conjBy γ ↔ x ∈ Tγ ∧ x ^ r = 1 := by
    intro x
    change x ∈ Subgroup.map (MulAut.conj γ).toMonoidHom RTH ↔ x ∈ Tγ ∧ x ^ r = 1
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine ⟨Subgroup.mem_map.mpr ⟨(z : H), z.2, rfl⟩, ?_⟩
      have hzr : z ^ r = 1 := hz
      have hzrH : (T.subtype z : H) ^ r = 1 := by rw [← map_pow, hzr, map_one]
      rw [← map_pow, hzrH, map_one]
    · rintro ⟨hxTγ, hxr⟩
      obtain ⟨y, hyT, rfl⟩ := Subgroup.mem_map.mp hxTγ
      have hyr : y ^ r = 1 := by
        have hxr' : ((MulAut.conj γ) y) ^ r = 1 := hxr
        rw [← map_pow] at hxr'
        exact (MulAut.conj γ).injective (hxr'.trans (map_one _).symm)
      have hyRT : (⟨y, hyT⟩ : T) ∈ RT := Subtype.ext hyr
      have hyRTH : y ∈ RTH := Subgroup.mem_map.mpr ⟨⟨y, hyT⟩, hyRT, rfl⟩
      exact Subgroup.mem_map.mpr ⟨y, hyRTH, rfl⟩
  have hE_le_Rγ : E ≤ RTH.conjBy γ := by
    intro x hx
    rw [hRconj_mem]
    exact ⟨hE_le_Tγ hx, hEel.2 x hx⟩
  have hRγcard : Nat.card (RTH.conjBy γ) = r ^ 2 := by
    rw [Subgroup.conjBy, Subgroup.card_map_of_injective (MulAut.conj γ).injective, hRTHcard]
  have hE_eq : E = RTH.conjBy γ :=
    Subgroup.eq_of_le_of_card_ge hE_le_Rγ (by rw [hRγcard, hEcard])
  have hr_dvd_fixed : r ∣ Nat.card h.fixedFieldˣ := by
    rw [Nat.card_units, h.card_fixedField]
    exact hrd
  obtain ⟨ζF, hζForder⟩ := exists_prime_orderOf_dvd_card' (G := h.fixedFieldˣ) r hr_dvd_fixed
  let ζ : K := (ζF : h.fixedField)
  have hζF : IsPrimitiveRoot (ζF : h.fixedField) r := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hζForder]
  have hζ : IsPrimitiveRoot ζ r :=
    (IsPrimitiveRoot.map_iff_of_injective (f := h.fixedField.subtype)
      Subtype.val_injective).mpr hζF
  have hζbar : h.bar ζ = ζ := h.mem_fixedField.mp ζF.val.property
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := 2) h hr hζ hζbar
  let t₀ : Fin 2 → ZMod r := Pi.single 0 1
  let ιB : Multiplicative (ZMod r) →* H :=
    { toFun := fun k => ι (Multiplicative.ofAdd (k.toAdd • t₀))
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [toAdd_mul, add_smul, ofAdd_add, map_mul] }
  let B0 : Subgroup H := ιB.range
  have hιB_apply : ∀ k : Multiplicative (ZMod r),
      (((ιB k : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
        diagonal (hypEntries ζ (k.toAdd • t₀)) := fun k => hι (k.toAdd • t₀)
  have hιB_inj : Function.Injective ιB := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    have hentry : hypEntries ζ (k.toAdd • t₀) ie1 = 1 := by
      have h := congrArg (fun g : hypSU h 2 0 =>
        (((g : GL Ix K) : Matrix Ix Ix K)) ie1 ie1) hk
      rw [hιB_apply k] at h
      simpa using h
    have ht₀ : (k.toAdd • t₀) (0 : Fin 2) = k.toAdd := by
      simp [t₀, Pi.smul_apply]
    have hpow : ζ ^ (k.toAdd).val = 1 := by
      simpa [hypEntries, ie1, ht₀] using hentry
    have hdvd : r ∣ (k.toAdd).val := (hζ.pow_eq_one_iff_dvd _).mp hpow
    have hval0 : (k.toAdd).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    exact (ZMod.val_eq_zero (k.toAdd)).mp hval0
  have hB0card : Nat.card B0 = r := by
    have h1 : Nat.card B0 = Nat.card (Multiplicative (ZMod r)) :=
      (Nat.card_congr (MonoidHom.ofInjective hιB_inj).toEquiv).symm
    rw [h1, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hB0_le_T : B0 ≤ T := by
    intro x hx
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
    exact CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h (hι (k.toAdd • t₀))
  have hkpow : ∀ k : Multiplicative (ZMod r), k ^ r = 1 := by
    intro k
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    simp
  have hB0_le_RTH : B0 ≤ RTH := by
    intro x hx
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
    have hxT : ιB k ∈ T := hB0_le_T (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨⟨ιB k, hxT⟩, ?_, rfl⟩
    exact Subtype.ext (by simpa using congrArg ιB (hkpow k))
  let B : Subgroup H := B0.conjBy γ
  have hB_le_E : B ≤ E := by
    rw [hE_eq]
    exact Subgroup.map_mono hB0_le_RTH
  have hBcard : Nat.card B = r := by
    change Nat.card (Subgroup.map (MulAut.conj γ).toMonoidHom B0) = r
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, hB0card]
  let Y0 : Subgroup H := (levHom h).range
  have hY0_entry : ∀ A, (((levHom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 :=
    levHom_range_apply_ie1_ie1 h
  have hB0_le_cent_Y0 : B0 ≤ Subgroup.centralizer (Y0 : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
    apply hypSU_ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_levHom,
      hιB_apply k]
    have hm : hypEntries ζ (k.toAdd • t₀) ie2 = hypEntries ζ (k.toAdd • t₀) if2 := by
      simp [hypEntries, ie2, if2, t₀, Pi.smul_apply]
    exact (diagonal_mul_levMat_comm (slMat h A) (hypEntries ζ (k.toAdd • t₀)) hm).symm
  let Y0c : Subgroup H := Y0.conjBy γ
  have hB_le_cent_Y0c : B ≤ Subgroup.centralizer (Y0c : Set H) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    have hy0b0 : y0 * b0 = b0 * y0 :=
      (Subgroup.mem_centralizer_iff.mp (hB0_le_cent_Y0 hb0)) y0 hy0
    calc (MulAut.conj γ) y0 * (MulAut.conj γ) b0
        = (MulAut.conj γ) (y0 * b0) := (map_mul _ _ _).symm
      _ = (MulAut.conj γ) (b0 * y0) := by rw [hy0b0]
      _ = (MulAut.conj γ) b0 * (MulAut.conj γ) y0 := map_mul _ _ _
  have hY0c_le_cent_B : Y0c ≤ Subgroup.centralizer (B : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hB_le_cent_Y0c hb)) y hy).symm
  have hY0L2 : IsL2 ↥Y0 n := by
    let : Fintype h.fixedField := Fintype.ofFinite _
    let eR : Matrix.SpecialLinearGroup (Fin 2) h.fixedField →* ↥Y0 := (levHom h).rangeRestrict
    have hRsurj : Function.Surjective eR := by
      rintro ⟨y, hy⟩
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hy
      exact ⟨A, Subtype.ext rfl⟩
    have hRinj : Function.Injective eR := by
      intro A B hAB
      exact levHom_hypSU_injective h (Subtype.ext_iff.mp hAB)
    let eSL : ↥Y0 ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
      (MulEquiv.ofBijective eR ⟨hRinj, hRsurj⟩).symm
    have hKcard : Fintype.card h.fixedField = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn2 hKcard eSL
  have hY0cL2 : IsL2 ↥Y0c n := by
    let eY0 : ↥Y0 ≃* ↥Y0c :=
      Subgroup.equivMapOfInjective Y0 (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective
    exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) eY0
      (by simpa [IsL2] using hY0L2)
  refine ⟨B, hB_le_E, hBcard, ⟨Y0c, hY0c_le_cent_B, hY0cL2⟩, ?_⟩
  intro p hp hp2 hpd
  have : Fact p.Prime := ⟨hp⟩
  have hp_dvd_Kunits : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcardK]
    have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_right (by simpa [hqdef] using hpd) (q - 1)
  obtain ⟨ν, hνorder⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hp_dvd_Kunits
  have hνpow : ν ^ p = 1 := by rw [← hνorder]; exact pow_orderOf_eq_one ν
  have hνpowK : (ν : K) ^ p = 1 := by simpa using congrArg Units.val hνpow
  have hνne : ν ≠ 1 := by
    intro hν1
    rw [hν1, orderOf_one] at hνorder
    exact hp.ne_one hνorder.symm
  have hpdvd : orderOf ν ∣ q + 1 := by
    rw [hνorder]
    simpa [hqdef] using hpd
  have hν_qp1 : ν ^ (q + 1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hpdvd
  have hνbar : h.bar (ν : K) = ((ν⁻¹ : Kˣ) : K) := by
    rw [h.bar_apply]
    have hq1 : ν ^ (2 ^ n) = ν⁻¹ := by
      have h1 : ν ^ (2 ^ n + 1) = 1 := by simpa [hqdef] using hν_qp1
      rw [pow_succ] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have := congrArg Units.val hq1
    simpa [Units.val_pow_eq_pow_val] using this
  have hνinv_pow : (((ν⁻¹ : Kˣ) : K) ^ p) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hνpowK, inv_one]
  let a : Fin 2 → Kˣ := fun i => if i = 0 then ν else ν⁻¹
  let d0 : Fin 0 → Kˣ := fun k => k.elim0
  have ha0 : (a 0 : K) = (ν : K) := by simp [a]
  have ha1 : (a 1 : K) = ((ν⁻¹ : Kˣ) : K) := by simp [a]
  have hbar_a0 : h.bar ((a 0 : Kˣ) : K) = ((ν⁻¹ : Kˣ) : K) := by
    rw [ha0]; exact hνbar
  have hbar_a1 : h.bar ((a 1 : Kˣ) : K) = (ν : K) := by
    rw [ha1]
    have hνinvK : ((ν⁻¹ : Kˣ) : K) = ((ν : K)⁻¹) := Units.val_inv_eq_inv_val ν
    rw [hνinvK, map_inv₀, hνbar, hνinvK]
    exact inv_inv (ν : K)
  have hd0 : ∀ k : Fin 0, h.norm (d0 k : K) = 1 := fun k => k.elim0
  have hrat : torusRatio h a d0 = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [hbar_a0, hbar_a1, ha0, ha1]
    have hν0 : (ν : K) ≠ 0 := Units.ne_zero ν
    field_simp
  obtain ⟨d1, hd1T, hd1mat⟩ := torusMat_mem_hypSU (d := d0) h a hd0 hrat
  have hEntryPow : ∀ i : Ix, (torusEntries h a d0 i) ^ p = 1 := by
    intro i
    rcases ix_cases i with rfl | rfl | rfl | rfl
    · simpa [torusEntries, ie1, ha0] using hνpowK
    · simpa [torusEntries, ie2, ha1] using hνinv_pow
    · have h1 : torusEntries h a d0 if1 = (ν : K) := by
        rw [show torusEntries h a d0 if1 = (h.bar ((a 0 : Kˣ) : K))⁻¹ from by
          simp [torusEntries, if1]]
        rw [hbar_a0, Units.val_inv_eq_inv_val]
        exact inv_inv (ν : K)
      rw [h1]
      exact hνpowK
    · have h1 : torusEntries h a d0 if2 = ((ν : K)⁻¹) := by
        rw [show torusEntries h a d0 if2 = (h.bar ((a 1 : Kˣ) : K))⁻¹ from by
          simp [torusEntries, if2]]
        rw [hbar_a1]
      rw [h1]
      simpa [Units.val_inv_eq_inv_val] using hνinv_pow
  have hd1pow : d1 ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hd1mat, Matrix.diagonal_pow]
    rw [show (torusEntries h a d0 ^ p) = (1 : Ix → K) from funext hEntryPow]
    simpa using Matrix.diagonal_one
  have hd1_entry : ((d1 : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = (ν : K) := by
    rw [hd1mat]
    simp [Matrix.diagonal_apply, torusEntries, ha0, ie1]
  have hd1_entry_ne : ((d1 : GL Ix K) : Matrix Ix Ix K) ie1 ie1 ≠ 1 := by
    rw [hd1_entry]
    intro hK
    exact hνne (Units.ext hK)
  have hd1ne : d1 ≠ 1 := by
    intro h1
    have hentry1 : ((d1 : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := by
      rw [h1]; simp
    exact hd1_entry_ne hentry1
  have hd1order : orderOf d1 = p := orderOf_eq_prime hd1pow hd1ne
  have hp_dvd_SL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two (Q := 2 ^ n)
      h.card_fixedField]
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpd (2 ^ n - 1)) (2 ^ n)
  obtain ⟨A, hAorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) h.fixedField) p hp_dvd_SL
  let d2 : H := levHom h A
  have hd2_mem_Y0 : d2 ∈ Y0 := MonoidHom.mem_range.mpr ⟨A, rfl⟩
  have hd2order : orderOf d2 = p := by
    rw [orderOf_injective (levHom h) (levHom_hypSU_injective h) A, hAorder]
  have hd1_cent_Y0 : d1 ∈ Subgroup.centralizer (Y0 : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hy
    apply hypSU_ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_levHom, hd1mat]
    have hm : torusEntries h a d0 ie2 = torusEntries h a d0 if2 := by
      simp [torusEntries, ie2, if2, ha1, hνbar, Units.val_inv_eq_inv_val]
    exact (diagonal_mul_levMat_comm (slMat h A') (torusEntries h a d0) hm).symm
  have hcomm_d1_d2 : Commute d1 d2 :=
    ((Subgroup.mem_centralizer_iff.mp hd1_cent_Y0) d2 hd2_mem_Y0).symm
  have hd2_not_mem_d1 : d2 ∉ Subgroup.zpowers d1 := by
    intro hmem
    have hle : Subgroup.zpowers d2 ≤ Subgroup.zpowers d1 := Subgroup.zpowers_le.mpr hmem
    have hcard1 : Nat.card (Subgroup.zpowers d1) = p := by rw [Nat.card_zpowers, hd1order]
    have hcard2 : Nat.card (Subgroup.zpowers d2) = p := by rw [Nat.card_zpowers, hd2order]
    have heq : Subgroup.zpowers d2 = Subgroup.zpowers d1 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
    have hd1_mem_Y0 : d1 ∈ Y0 := by
      have h1 : d1 ∈ Subgroup.zpowers d2 := by
        rw [heq]
        exact Subgroup.mem_zpowers d1
      exact Subgroup.zpowers_le.mpr hd2_mem_Y0 h1
    obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp hd1_mem_Y0
    have hentry : ((d1 : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := by
      rw [← hA']
      exact hY0_entry A'
    exact hd1_entry_ne hentry
  let d1c : H := (MulAut.conj γ) d1
  let d2c : H := (MulAut.conj γ) d2
  have hd1c_order : orderOf d1c = p := by
    change orderOf ((MulAut.conj γ) d1) = p
    exact (orderOf_injective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective d1).trans
      hd1order
  have hd2c_order : orderOf d2c = p := by
    change orderOf ((MulAut.conj γ) d2) = p
    exact (orderOf_injective (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective d2).trans
      hd2order
  have hd1c_mem_Tγ : d1c ∈ Tγ := Subgroup.mem_map.mpr ⟨d1, hd1T, rfl⟩
  have hB_le_Tγ : B ≤ Tγ := Subgroup.map_mono hB0_le_T
  have hd1c_cent_B : d1c ∈ Subgroup.centralizer (B : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hTγ_comm d1c hd1c_mem_Tγ b (hB_le_Tγ hb)).symm
  have hd2c_mem_Y0c : d2c ∈ Y0c := Subgroup.mem_map.mpr ⟨d2, hd2_mem_Y0, rfl⟩
  have hd2c_cent_B : d2c ∈ Subgroup.centralizer (B : Set H) := hY0c_le_cent_B hd2c_mem_Y0c
  have hcomm_d1c_d2c : Commute d1c d2c := by
    change (MulAut.conj γ) d1 * (MulAut.conj γ) d2 =
      (MulAut.conj γ) d2 * (MulAut.conj γ) d1
    rw [← map_mul, ← map_mul, hcomm_d1_d2]
  have hd2c_not_mem : d2c ∉ Subgroup.zpowers d1c := by
    intro hmem
    have hmap : Subgroup.map (MulAut.conj γ).toMonoidHom (Subgroup.zpowers d1) =
        Subgroup.zpowers d1c := by
      simpa [d1c] using MonoidHom.map_zpowers (MulAut.conj γ).toMonoidHom d1
    have hmem' : d2c ∈ Subgroup.map (MulAut.conj γ).toMonoidHom (Subgroup.zpowers d1) := by
      rw [hmap]; exact hmem
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp hmem'
    have hzd : z = d2 := by
      apply (MulAut.conj γ).injective
      simpa [d2c] using hze
    exact hd2_not_mem_d1 (hzd ▸ hz)
  have hrank : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (B : Set H)) :=
    CFSG.GroupTheory.two_le_pRank_of_commute (H := Subgroup.centralizer (B : Set H))
      hd1c_cent_B hd2c_cent_B hd1c_order hd2c_order hcomm_d1c_d2c hd2c_not_mem
  have hTγ_le_cent_E : Tγ ≤ Subgroup.centralizer (E : Set H) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hTγ_comm t ht e (hE_le_Tγ he)).symm
  have hpT : p ∣ Nat.card T := by
    have h := orderOf_dvd_natCard (⟨d1, hd1T⟩ : T)
    have hord : orderOf (⟨d1, hd1T⟩ : T) = p := by
      rw [← Subgroup.orderOf_coe (⟨d1, hd1T⟩ : T)]
      exact hd1order
    rwa [hord] at h
  have hpTγ : p ∣ Nat.card Tγ := by
    change p ∣ Nat.card (Subgroup.map (MulAut.conj γ).toMonoidHom T)
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact hpT
  have hpE : p ∣ Nat.card (Subgroup.centralizer (E : Set H)) :=
    hpTγ.trans (Subgroup.card_dvd_of_le hTγ_le_cent_E)
  exact ⟨hrank, hpE⟩

theorem k_U4RootLine_holds : K_U4RootLine := by
  intro Y _ _ n hY hq r hr hr3 hrd E hEel hEcard
  classical
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  let EH : Subgroup (hypSU h 2 0) := E.map e.symm.toMonoidHom
  have hEH_el : IsElemAbelian r EH := hEel.map e.symm.toMonoidHom
  have hEH_card : Nat.card EH = r ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hEcard]
  obtain ⟨B0, hB0E, hB0card, ⟨Y00, hY00le, hY00L2⟩, hpclause⟩ :=
    exists_rootLine_hypSU h hq hr hr3 hrd EH hEH_el hEH_card
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y :=
    MonoidHom.ext fun x => e.apply_symm_apply x
  have hEHmap : EH.map e.toMonoidHom = E := by
    change (E.map e.symm.toMonoidHom).map e.toMonoidHom = E
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  let B : Subgroup Y := B0.map e.toMonoidHom
  have hBE : B ≤ E := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hB0E
    rwa [hEHmap] at h
  have hBcard : Nat.card B = r := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hB0card]
  let Y0 : Subgroup Y := Y00.map e.toMonoidHom
  have hY0le : Y0 ≤ Subgroup.centralizer (B : Set Y) := by
    have h1 : Y00.map e.toMonoidHom ≤
        (Subgroup.centralizer (B0 : Set (hypSU h 2 0))).map e.toMonoidHom :=
      Subgroup.map_mono hY00le
    rw [← CFSG.GroupTheory.CoprimeTransport.centralizer_map_mulEquiv e B0] at h1
    exact h1
  have hY0L2 : IsL2 ↥Y0 n := by
    let eY0 : ↥Y00 ≃* ↥Y0 :=
      Subgroup.equivMapOfInjective Y00 e.toMonoidHom e.injective
    exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) eY0
      (by simpa [IsL2] using hY00L2)
  refine ⟨B, hBE, hBcard, ⟨Y0, hY0le, hY0L2⟩, ?_⟩
  intro p hp hp2 hpd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpB, hpE⟩ := hpclause p hp hp2 hpd
  refine ⟨?_, ?_⟩
  · change 2 ≤ CFSG.Open.pRank p
        (Subgroup.centralizer ((B0.map e.toMonoidHom : Subgroup Y) : Set Y))
    rw [CFSG.GroupTheory.CoprimeTransport.pRank_centralizer_map_mulEquiv e B0]
    exact hpB
  · change p ∣ Nat.card (Subgroup.centralizer (E : Set Y))
    rw [← hEHmap, CFSG.GroupTheory.CoprimeTransport.card_centralizer_map_mulEquiv e EH]
    exact hpE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
