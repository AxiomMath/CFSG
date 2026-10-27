module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkTwAKnown
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem ggTwA_torusSU_card {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 1 ≤ d) :
    Nat.card (CFSG.RankThree.PartOne.KFU.torusSU p d K) = p ^ (d - 1) := by
  have hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hKd hp hpq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hunit : IsPrimitiveRoot (Units.mk0 ζ hζ0) p :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have hd' : d = (d - 1) + 1 := (Nat.sub_add_cancel hd).symm
  rw [CFSG.RankThree.PartOne.KFU.torusSU,
    Subgroup.card_map_of_injective CFSG.RankThree.PartOne.KFU.diagU_injective, hd']
  exact CFSG.RankThree.PartOne.KFU.card_torusVec_eq hp.pos ⟨_, hunit⟩ (d - 1)

private theorem ggTwA_scalar_of_mem_center {K : Type} [Field K] [Finite K] {n d p : ℕ}
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun _ => c))
    {X : ↥(unitarySU 2 n K d)}
    (hX : (X : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU p d K)
    (hcen : φ X ∈ Subgroup.center L') :
    ∃ c : K, ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun _ => c) := by
  classical
  obtain ⟨e, _he1, _he2, heX⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hX
  have heq : ∀ i j : Fin d, i ≠ j → e i = e j := by
    intro i j hij
    set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
    set s : ↥(unitarySU 2 n K d) :=
      ⟨CFSG.RankThree.PartOne.KFU.permGL σ,
        CFSG.RankThree.PartOne.KFU.permGL_mem_unitarySU hKd σ⟩ with hs
    have hker : (X * s * X⁻¹ * s⁻¹ : ↥(unitarySU 2 n K d)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : φ (X * s * X⁻¹ * s⁻¹) = φ X * φ s * (φ X)⁻¹ * (φ s)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [h1]
      have hcomm := Subgroup.mem_center_iff.mp hcen (φ s)
      rw [← hcomm]; group
    obtain ⟨c, hc⟩ := hφker _ hker
    set w : Fin d → Kˣ := e * (e⁻¹ ∘ σ.symm) with hw
    have hscoe : (s : GL (Fin d) K) = CFSG.RankThree.PartOne.KFU.permGL σ := rfl
    have hinv : (X : GL (Fin d) K)⁻¹ = CFSG.RankThree.PartOne.KFU.diagU e⁻¹ := by
      rw [← heX]
      exact inv_eq_of_mul_eq_one_right
        (by rw [CFSG.RankThree.PartOne.KFU.diagU_mul, mul_inv_cancel,
          CFSG.RankThree.PartOne.KFU.diagU_one])
    have hconj : (s : GL (Fin d) K) * (X : GL (Fin d) K)⁻¹ * (s : GL (Fin d) K)⁻¹ =
        CFSG.RankThree.PartOne.KFU.diagU (e⁻¹ ∘ σ.symm) := by
      rw [hscoe, hinv, CFSG.RankThree.PartOne.KFU.permGL_conj_diagU]
    have hdiag : ((X * s * X⁻¹ * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        CFSG.RankThree.PartOne.KFU.diagU w := by
      calc ((X * s * X⁻¹ * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)
          = (X : GL (Fin d) K) * ((s : GL (Fin d) K) * (X : GL (Fin d) K)⁻¹ *
              (s : GL (Fin d) K)⁻¹) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = (X : GL (Fin d) K) * CFSG.RankThree.PartOne.KFU.diagU (e⁻¹ ∘ σ.symm) := by
            rw [hconj]
        _ = CFSG.RankThree.PartOne.KFU.diagU e *
              CFSG.RankThree.PartOne.KFU.diagU (e⁻¹ ∘ σ.symm) := by rw [heX]
        _ = CFSG.RankThree.PartOne.KFU.diagU w := by
            rw [CFSG.RankThree.PartOne.KFU.diagU_mul, ← hw]
    have hdiagmat : (((X * s * X⁻¹ * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun k => (w k : K)) := by
      rw [hdiag, CFSG.RankThree.PartOne.KFU.diagU_val]
    have hEq : Matrix.diagonal (fun k => (w k : K)) = Matrix.diagonal (fun _ => c) := by
      rw [← hdiagmat, hc]
    obtain ⟨k, hki, hkj⟩ := LineU.exists_not_mem_two hd i j
    have hwk : w k = 1 := by
      rw [hw, Pi.mul_apply, Function.comp_apply]
      have hkk : σ.symm k = k := by
        rw [hσ, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hkk]
      exact mul_inv_cancel (e k)
    have hc1 : c = 1 := by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) K => M k k) hEq
      simpa [hwk] using h.symm
    have hwi : w i = 1 := by
      apply Units.ext
      have h1 : (w i : K) = c := by
        have h := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) hEq
        simpa using h
      rw [h1, hc1]
      rfl
    rw [hw, Pi.mul_apply, Function.comp_apply] at hwi
    have hji : σ.symm i = j := by
      rw [hσ, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hji] at hwi
    exact mul_inv_eq_one.mp hwi
  refine ⟨(e ⟨0, by omega⟩ : K), ?_⟩
  have he0 : ∀ i, e i = e ⟨0, by omega⟩ := by
    intro i
    by_cases hi : i = ⟨0, by omega⟩
    · rw [hi]
    · exact heq i _ hi
  rw [← heX, CFSG.RankThree.PartOne.KFU.diagU_val]
  congr 1
  funext i
  rw [he0 i]

theorem ggTwA_scalarSubgroup_card_le {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hp : p.Prime) (hd : 1 ≤ d) :
    Nat.card (((CFSG.RankThree.PartOne.KFU.torusSU p d K).subgroupOf (unitarySU 2 n K d) ⊓
        (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d)) :
        Subgroup ↥(unitarySU 2 n K d)) ≤ p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Z : Subgroup ↥(unitarySU 2 n K d) :=
    (CFSG.RankThree.PartOne.KFU.torusSU p d K).subgroupOf (unitarySU 2 n K d) ⊓
      (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) with hZ
  have hspec : ∀ z : Z, ∃ cc : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin d) cc = (z.1.1 : GL (Fin d) K) ∧ cc ^ p = 1 := by
    intro z
    have hzT : (z.1.1 : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU p d K :=
      Subgroup.mem_subgroupOf.mp z.2.1
    have hzS : (z.1.1 : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
      Subgroup.mem_subgroupOf.mp z.2.2
    obtain ⟨e, he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hzT
    have hzS' : (z.1.1 : GL (Fin d) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
      rwa [largeEvenScalars_def] at hzS
    obtain ⟨cc, hcc⟩ := MonoidHom.mem_range.mp hzS'
    refine ⟨cc, hcc, ?_⟩
    have hmat : (((Matrix.GeneralLinearGroup.scalar (Fin d) cc : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun _ => (cc : K)) := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
          hij]
    have hmat2 : ((z.1.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun _ => (cc : K)) := by rw [← hcc, hmat]
    have hmat3 : ((z.1.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => (e i : K)) := by
      rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_val]
    have hcc0K : (cc : K) = (e ⟨0, hd⟩ : K) := by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
        M ⟨0, hd⟩ ⟨0, hd⟩) (hmat2.symm.trans hmat3)
      simpa using h
    rw [show cc = e ⟨0, hd⟩ from Units.ext hcc0K]
    exact he1 _
  choose cc hcc_spec using hspec
  refine (Nat.card_le_card_of_injective (fun z : Z =>
      (⟨cc z, by rw [mem_rootsOfUnity]; exact (hcc_spec z).2⟩ : rootsOfUnity p K)) ?_).trans
    (card_rootsOfUnity K p)
  intro z z' h
  have hcc : cc z = cc z' := Subtype.ext_iff.mp h
  have hgl : (z.1.1 : GL (Fin d) K) = (z'.1.1 : GL (Fin d) K) := by
    rw [← (hcc_spec z).1, ← (hcc_spec z').1, hcc]
  exact Subtype.ext (Subtype.ext hgl)

private theorem ggTwA_ker_le_scalars {K : Type} [Field K] [Finite K] {n d : ℕ} {L' : Type}
    [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hd : 1 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun _ => c)) :
    φ.ker ≤ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
  intro g hg
  obtain ⟨c, hc⟩ := hφker g hg
  have hunit : IsUnit (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
    ⟨(g : GL (Fin d) K), rfl⟩
  have hdet : IsUnit (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet0 : (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det) = 0 := by
      rw [h0] at hc
      rw [hc, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd⟩) (by simp)
    exact not_isUnit_zero (hdet0 ▸ hdet)
  apply Subgroup.mem_subgroupOf.mpr
  rw [largeEvenScalars_def]
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [hc]
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hij]

theorem ggTwA_torus_pow {K : Type} [Field K] {n d p : ℕ}
    (X : ↥(unitarySU 2 n K d)) (hX : (X : GL (Fin d) K) ∈
      CFSG.RankThree.PartOne.KFU.torusSU p d K) : X ^ p = 1 := by
  obtain ⟨e, he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hX
  apply Subtype.ext
  show (X : GL (Fin d) K) ^ p = 1
  rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_pow]
  rw [show e ^ p = 1 from funext (fun i => he1 i), CFSG.RankThree.PartOne.KFU.diagU_one]

theorem ggTwA_mem_scalars {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hd : 1 ≤ d) {g : ↥(unitarySU 2 n K d)}
    (hgt : (g : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU p d K)
    {c : K} (hc : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun _ => c)) :
    g ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
  obtain ⟨e, _he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hgt
  have hmat : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal (fun i => (e i : K)) := by
    rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_val]
  have hcc : c = (e ⟨0, hd⟩ : K) := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
      M ⟨0, hd⟩ ⟨0, hd⟩) (hc.symm.trans hmat)
    simpa using h
  have hc0 : c ≠ 0 := by rw [hcc]; exact Units.ne_zero _
  apply Subgroup.mem_subgroupOf.mpr
  rw [largeEvenScalars_def]
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [hc]
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hij]

private theorem ggL48TwA_core {K : Type} [Field K] [Finite K] {n d p : ℕ}
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 7 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hE : E ≤ Subgroup.normalizer (L' : Set M))
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) θ hE)
    (hCne : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥)
    (hEcard : p ^ (d - 2) ≤ Nat.card E) :
    p ^ (d - 1) ≤ Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hEel : IsElemAbelian p E := hpos.2.1
  have hperf : commutator L' = ⊤ := hpos.1
  have hIact := hpos.2.2.2.1
  have hSC := hpos.2.2.2.2.2.1
  have hd3 : 3 ≤ d := by omega
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  set A : Subgroup (MulAut L') := (ggGamma L' hE).range with hAdef
  have hAab : IsElemAbelian p A :=
    isElemAbelian_range (fun a b => hEel.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hEel.2 a a.2)) (ggGamma L' hE)
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggLAut L' θ ⟨b, hE b.2⟩, hIact b, fun l => ggBeta_ggQuotHom L' hE θ b l⟩
  have hker3 : (ggGamma L' hE).ker ≤
      (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E := by
    intro b hb
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
    exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩
  have h3 : p ^ 3 ≤ Nat.card A :=
    tableBPosition_pow_three_le_card_range hp hpos (ggGamma L' hE) hker3
  have hkerle : Nat.card (ggGamma L' hE).ker ≤ p := by
    have hSle := tableBPosition_card_inf_centralizer_le hp hpos
    have h1 := Subgroup.card_le_of_le hker3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : E ⊓ Subgroup.centralizer (L' : Set M) ≤ E)).toEquiv] at h1
    exact h1.trans hSle
  have hcardmul : Nat.card A * Nat.card (ggGamma L' hE).ker = Nat.card E := by
    rw [hAdef, Nat.mul_comm]
    exact Subgroup.card_ker_mul_card_range (ggGamma L' hE)
  have hge : p ^ (d - 3) ≤ Nat.card A := by
    have h1 : p ^ (d - 2) ≤ Nat.card A * Nat.card (ggGamma L' hE).ker := by
      rw [hcardmul]; exact hEcard
    have h2 : p ^ (d - 2) ≤ Nat.card A * p := h1.trans (Nat.mul_le_mul_left _ hkerle)
    have h3' : p ^ (d - 2) = p ^ (d - 3) * p := by rw [← pow_succ]; congr 1; omega
    rw [h3'] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have hnd : ¬ (d = 6 ∧ p = 3) := by rintro ⟨h, -⟩; omega
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := LineU.card_ge_of_dvd hp hp2 (by omega) hpd hnd hge h3
  have hd6 : (d, n) ≠ (6, 1) := by rintro ⟨h, -⟩; omega
  obtain ⟨φ, _hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK hn (by omega) hp hpq hpd (LineU.unitaryCoverAt hK (by omega) hd6)
      (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hperf hAab hAI hcard
  have hTle : CFSG.RankThree.PartOne.KFU.torusSU p d K ≤ unitarySU 2 n K d :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hKd hpq
  set T : Subgroup ↥(unitarySU 2 n K d) :=
    (CFSG.RankThree.PartOne.KFU.torusSU p d K).subgroupOf (unitarySU 2 n K d) with hTdef
  have hTcard : Nat.card T = p ^ (d - 1) := by
    rw [hTdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact ggTwA_torusSU_card hK hn hp hpq (by omega)
  set Zs : Subgroup ↥(unitarySU 2 n K d) :=
    T ⊓ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) with hZsdef
  have hZsle : Nat.card Zs ≤ p := by
    rw [hZsdef, hTdef]
    exact ggTwA_scalarSubgroup_card_le hp (by omega)
  set φT : ↥T →* L' := φ.comp T.subtype with hφTdef
  set N' : Subgroup L' := φT.range with hN'def
  set N : Subgroup M := N'.map L'.subtype with hNdef
  set Kφ : Subgroup ↥(unitarySU 2 n K d) := T ⊓ φ.ker with hKφdef
  have hKφle : Nat.card Kφ ≤ p := by
    have hle : Kφ ≤ Zs := by
      intro x hx
      exact ⟨hx.1, ggTwA_ker_le_scalars (by omega) hφker hx.2⟩
    exact (Subgroup.card_le_of_le hle).trans hZsle
  have hKφcard : Nat.card φT.ker = Nat.card Kφ := by
    have hmap : (φT.ker).map T.subtype = Kφ := by
      ext x; constructor
      · rintro ⟨Y, hY, rfl⟩
        exact ⟨Y.2, MonoidHom.mem_ker.mp hY⟩
      · rintro ⟨hxT, hxker⟩
        exact ⟨⟨x, hxT⟩, MonoidHom.mem_ker.mpr hxker, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective T.subtype_injective]
  have hTker : Nat.card φT.ker * Nat.card N' = Nat.card T :=
    Subgroup.card_ker_mul_card_range φT
  have hN'card : Nat.card N' * Nat.card Kφ = p ^ (d - 1) := by
    rw [hKφcard, hTcard] at hTker
    rw [Nat.mul_comm]
    exact hTker
  have hNcard : p ^ (d - 2) ≤ Nat.card N := by
    have hNN' : Nat.card N = Nat.card N' := by
      rw [hNdef, Subgroup.card_map_of_injective L'.subtype_injective]
    rw [hNN']
    have h2 : p ^ (d - 1) ≤ Nat.card N' * p := by
      rw [← hN'card]; exact Nat.mul_le_mul_left _ hKφle
    have h3' : p ^ (d - 1) = p ^ (d - 2) * p := by rw [← pow_succ]; congr 1; omega
    rw [h3'] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have hNle : N ≤ E := by
    rw [hNdef]
    rintro x ⟨y, hy, rfl⟩
    rw [hN'def] at hy
    obtain ⟨X, hXy⟩ := MonoidHom.mem_range.mp hy
    rw [← hXy]
    have hXT : (X.1.1 : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU p d K :=
      Subgroup.mem_subgroupOf.mp X.2
    obtain ⟨e, _he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hXT
    have hXdiag : ((X.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => (e i : K)) := by
      rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_val]
    refine hSC ((φ X.1 : L') : M) (Subgroup.mem_sup_right (φ X.1).2) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro ee hee
      have ha : ggGamma L' hE ⟨ee, hee⟩ ∈ A := ⟨⟨ee, hee⟩, rfl⟩
      obtain ⟨t, ht⟩ := hdiag _ ha
      have hfix := ht.fix_of_diagonal X.1 hXdiag
      have hcoe : ((ggGamma L' hE ⟨ee, hee⟩ (φ X.1) : L') : M) =
          ee * (φ X.1 : M) * ee⁻¹ := ggGamma_coe L' hE ⟨ee, hee⟩ (φ X.1)
      have h1 : ee * (φ X.1 : M) * ee⁻¹ = (φ X.1 : M) := by rw [← hcoe, hfix]
      calc ee * (φ X.1 : M) = (ee * (φ X.1 : M) * ee⁻¹) * ee := by group
        _ = (φ X.1 : M) * ee := by rw [h1]
    · have hXp : X.1 ^ p = 1 := ggTwA_torus_pow X.1 hXT
      have hpowL : φ X.1 ^ p = 1 := by rw [← map_pow, hXp, map_one]
      simpa using congrArg (fun z : L' => (z : M)) hpowL
  set C : Subgroup M := E ⊓ Subgroup.centralizer (L' : Set M) with hCdef
  have hCne' : C ≠ ⊥ := by rw [hCdef]; exact hCne
  have hCcard : Nat.card C = p := by
    have hCple : Nat.card C ≤ p := by
      rw [hCdef]; exact tableBPosition_card_inf_centralizer_le hp hpos
    have hCp : IsPGroup p C := by
      rw [hCdef]; exact isPGroup_of_isElemAbelian (isElemAbelian_mono hEel inf_le_left)
    have hCge : p ≤ Nat.card C := by
      obtain ⟨k, hk⟩ := hCp.exists_card_eq
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, pow_zero] at hk
          exact absurd (Subgroup.card_eq_one.mp hk) hCne'
        · exact hkpos
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
        _ = Nat.card C := hk.symm
    exact le_antisymm hCple hCge
  have hcommNC : ∀ nn ∈ N, ∀ cc ∈ C, nn * cc = cc * nn := by
    intro nn hn cc hc
    exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨nn, hNle hn⟩ ⟨cc, hc.1⟩)
  by_cases hdisj : Disjoint N C
  · have hinf : N ⊓ C = ⊥ := disjoint_iff.mp hdisj
    have hcardsup := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N C hcommNC).1
    rw [hinf, Subgroup.card_bot, mul_one, hCcard] at hcardsup
    have hsub : N ⊔ C ≤ E := sup_le hNle inf_le_left
    have hdp : p ^ (d - 1) = p ^ (d - 2) * p := by
      rw [← pow_succ]
      congr 1
      omega
    calc p ^ (d - 1) = p ^ (d - 2) * p := hdp
      _ ≤ Nat.card N * p := Nat.mul_le_mul_right p hNcard
      _ = Nat.card (N ⊔ C : Subgroup M) := hcardsup.symm
      _ ≤ Nat.card E := Subgroup.card_le_of_le hsub
  · have hCnotdisj : N ⊓ C ≠ ⊥ := fun h => hdisj (disjoint_iff.mpr h)
    have hCleN : C ≤ N := by
      have hCinf : N ⊓ C = C := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
        have hdvd : Nat.card (N ⊓ C : Subgroup M) ∣ Nat.card C :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [hCcard] at hdvd
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hCnotdisj
        · rw [h]; exact le_of_eq hCcard
      rw [← hCinf]; exact inf_le_left
    obtain ⟨⟨x₀, hx₀C⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne'
    have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
    have hx₀N : x₀ ∈ N := hCleN hx₀C
    obtain ⟨y, hyN', hyx⟩ := Subgroup.mem_map.mp hx₀N
    rw [hN'def] at hyN'
    obtain ⟨X, hXy⟩ := MonoidHom.mem_range.mp hyN'
    have hφx0 : ((φ X.1 : L') : M) = x₀ :=
      (congrArg (fun z : L' => (z : M)) hXy).trans hyx
    have hcenφ : φ X.1 ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro l
      have hc := Subgroup.mem_centralizer_iff.mp hx₀C.2 l l.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hφx0]; exact hc)
    obtain ⟨cX, hcX⟩ := ggTwA_scalar_of_mem_center hKd hd3 hφker
      (Subgroup.mem_subgroupOf.mp X.2) hcenφ
    have hXZs : X.1 ∈ Zs :=
      ⟨X.2, ggTwA_mem_scalars (by omega) (Subgroup.mem_subgroupOf.mp X.2) hcX⟩
    have hKφbot : Kφ = ⊥ := by
      by_contra hneK
      obtain ⟨⟨Y, hYKφ⟩, hY1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneK
      have hYZs : Y ∈ Zs :=
        ⟨hYKφ.1, ggTwA_ker_le_scalars (by omega) hφker hYKφ.2⟩
      have hYp1 : Y ^ p = 1 := ggTwA_torus_pow Y (Subgroup.mem_subgroupOf.mp hYKφ.1)
      have hY1' : Y ≠ 1 := fun h => hY1 (Subtype.ext h)
      have hYorder : orderOf Y = p := orderOf_eq_prime hYp1 hY1'
      have hKφge : p ≤ Nat.card Kφ := by
        have hdvd := Subgroup.orderOf_dvd_natCard Kφ hYKφ
        rw [hYorder] at hdvd
        exact Nat.le_of_dvd Nat.card_pos hdvd
      have hKφeq : Nat.card Kφ = p := le_antisymm hKφle hKφge
      have hKφZs : Kφ ≤ Zs := by
        intro x hx
        exact ⟨hx.1, ggTwA_ker_le_scalars (by omega) hφker hx.2⟩
      have hZseq : Nat.card Zs = p :=
        le_antisymm hZsle (hKφeq ▸ Subgroup.card_le_of_le hKφZs)
      have hKφZs_eq : Kφ = Zs :=
        Subgroup.eq_of_le_of_card_ge hKφZs (by rw [hKφeq, hZseq])
      have hXKφ : X.1 ∈ Kφ := hKφZs_eq ▸ hXZs
      apply hx₀1'
      rw [← hφx0]
      simpa using congrArg (fun z : L' => (z : M)) (MonoidHom.mem_ker.mp hXKφ.2)
    have hN'card2 : Nat.card N' = p ^ (d - 1) := by
      have h := hN'card
      rw [hKφbot, Subgroup.card_bot, mul_one] at h
      simpa using h
    calc p ^ (d - 1) = Nat.card N' := hN'card2.symm
      _ = Nat.card N := by rw [hNdef, Subgroup.card_map_of_injective L'.subtype_injective]
      _ ≤ Nat.card E := Subgroup.card_le_of_le hNle

theorem ggL48TwATorusLift_holds :
    GGL48TwATorusLift := by
  intro p lab hp hlab htag h6 hpd hpq
  have h := largeEvenLabelAll_torusLift_twA hlab htag hp hpq
  have hrank : ggUnitaryTorusRank p (lab.rank + 1) = lab.rank - 2 := by
    rw [ggUnitaryTorusRank, if_pos hpd]
    omega
  simpa [hrank] using h

theorem ggL48TwAKnownGroup_holds :
    GGL48TwAKnownGroup := by
  intro p lab hp hlab htag h6 hpd hpq
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpd hpq h6 ⊢
  subst htag
  obtain ⟨hn, _hl, _hl2⟩ := hlab
  dsimp only at hn _hl _hl2
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro M _ _ L' E θ hE hpos hCne hEcard
  have hdl : (l + 1) - 2 = l - 1 := by omega
  refine ggL48TwA_core hK hn (by omega) hp hpq hpd hE hpos hCne ?_
  simpa [hdl] using hEcard

theorem ggL48TB0TwConfigInputTwA_holds :
    GGL48TB0TwConfigInputTwA :=
  ggL48TB0TwConfigInputTwA_of_known ggL48TwATorusLift_holds ggL48TwAKnownGroup_holds

end CFSG.StandardType

end
