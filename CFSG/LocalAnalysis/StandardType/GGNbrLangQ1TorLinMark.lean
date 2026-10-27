module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinBlock
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGSummandMarkingCentralSurj
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.Open (StatedSL)

private noncomputable def l02qt4b_statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem l02qt4b_statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    l02qt4b_statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [l02qt4b_statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem l02qt4b_specialLinearGroupEquivStatedSL_symm_slConjugation {m : ℕ} {E : Type}
    [Field E] {A : GL (Fin m) E} {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) = A * (l : GL (Fin m) E) * A⁻¹) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l' =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  have hl : (l : GL (Fin m) E) =
      ((e.symm l : Matrix.SpecialLinearGroup (Fin m) E) : GL (Fin m) E) := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l]
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l))
  have h' := congrArg (fun u : GL (Fin m) E => (u : Matrix (Fin m) (Fin m) E)) h
  rw [hl] at h'
  rw [show ((e (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        (e.symm l)) : StatedSL m E) : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
          (e.symm l)) from
    Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E _)]
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact h'

private theorem l02qt4b_largeEvenRawDatumLegacy_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hm : 1 ≤ m) (hcard : Nat.card E = 2 ^ f) (Q : LargeEvenRawCont)
    (hQ : Q (LargeEvenProj (LargeEvenSLGroup (Fin m) E))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)))) :
    LargeEvenRawDatumLegacy (⟨.A, m - 1, f⟩ : LargeEvenLabel) Q := by
  change LargeEvenRecipeLinear (m - 1 + 1) (2 ^ f) Q
  rw [show m - 1 + 1 = m from Nat.sub_add_cancel (by omega)]
  exact ⟨E, inferInstance, inferInstance, hcard, hQ⟩

private theorem l02qt4b_largeEvenMarking_statedSL_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL m E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)))
    (hm : 2 ≤ m) (hf : 1 ≤ f) (hmf : m = 2 → 2 ≤ f) :
    LargeEvenMarking (StatedSL m E)
      (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ (⊤ : Subgroup (GL (Fin m) E)), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  refine ⟨hperf, ⟨⟨.A, m - 1, f⟩, ?_, ?_⟩⟩
  · refine ⟨hf, by show 1 ≤ m - 1; omega, ?_⟩
    intro h
    have h' : m - 1 = 1 := by simpa using h
    exact hmf (by omega)
  · refine l02qt4b_largeEvenRawDatumLegacy_linear (by omega) hcard _ ?_
    let θ : StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      l02qt4b_statedSLCenterQuotEquivProjective.trans
        (CFSG.StandardType.TypeA.recipeEquiv m E).symm
    have hnab : ∃ a b : StatedSL m E ⧸ Subgroup.center (StatedSL m E), a * b ≠ b * a :=
      exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance
    refine ⟨?_, ?_, θ, by simp [GGChevStTag], ?_⟩
    · exact θ.symm.isSimpleGroup_congr.mpr hsimp
    · exact nonabelian_of_mulEquiv θ hnab
    · intro ε _
      let A : GL (Fin m) E := ε⁻¹
      let φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) :=
        (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv m E)).symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut m E A)
      refine ⟨φ, CFSG.StandardType.NbrGraphLinear.symm_congr_conjAut_mem A, ?_⟩
      intro l l' hll'
      apply (CFSG.StandardType.TypeA.recipeEquiv m E).injective
      simp only [φ, MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l)) =
          l02qt4b_statedSLCenterQuotEquivProjective (QuotientGroup.mk l) from rfl,
        show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l')) =
          l02qt4b_statedSLCenterQuotEquivProjective (QuotientGroup.mk l') from rfl]
      rw [l02qt4b_statedSLCenterQuotEquivProjective_mk, l02qt4b_statedSLCenterQuotEquivProjective_mk]
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
      rw [← l02qt4b_specialLinearGroupEquivStatedSL_symm_slConjugation (A := A)
        (by simpa [A] using hll')]

private theorem l02qt4b_two_le_of_card_two_statedSL {f : ℕ} {E : Type} [Field E] [Finite E]
    (hf : 1 ≤ f) (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL 2 E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E))) : 2 ≤ f := by
  by_contra hf2
  have hf1 : f = 1 := by omega
  have hcard2 : Nat.card E = 2 := by rw [hcard, hf1, pow_one]
  have hcardSL : Nat.card (StatedSL 2 E) = 6 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, hcard2]
    norm_num
  have hsolv : Group.IsSolvable (StatedSL 2 E) := by
    have hcard6 : @Fintype.card (StatedSL 2 E) (Fintype.ofFinite _) = 2 ^ 1 * 3 ^ 1 := by
      rw [← @Nat.card_eq_fintype_card (StatedSL 2 E) (Fintype.ofFinite _), hcardSL]
      norm_num
    exact @CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (StatedSL 2 E) _ (Fintype.ofFinite _) 2 3 1 1 Nat.prime_two Nat.prime_three
      (by norm_num) hcard6
  have hntq : Nontrivial (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) :=
    hsimp.toNontrivial
  have hnt : Nontrivial (StatedSL 2 E) :=
    @Function.Surjective.nontrivial (StatedSL 2 E)
      (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) hntq (QuotientGroup.mk)
      (QuotientGroup.mk_surjective (s := Subgroup.center (StatedSL 2 E)))
  have hperf' : Group.IsPerfect (StatedSL 2 E) := Group.isPerfect_def.mpr hperf
  exact @Group.IsPerfect.not_isSolvable (StatedSL 2 E) _ hnt hperf' hsolv

private theorem l02qt4b_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qt4b_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qt4b_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

theorem q1TorLin_marking {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K] [Finite K] [CharP K 2]
    (g : GL (Fin N) K) (hg : Odd (orderOf g)) (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) K))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) K)
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))) :
    CFSG.StandardType.LargeEvenMarking J₀ (fun _ _ _ IJ _ θJ =>
      ∀ h : GL (Fin N) K, h * g = g * h →
        (∀ j ∈ J₀, TableB.linConjAut (Fin N) K h j ∈ J₀) ∧
        ∃ φ ∈ IJ, LargeEvenInduces θJ
          (fun j j' : ↥J₀ => TableB.linConjAut (Fin N) K h (j : _) = (j' : _)) φ) := by
  classical
  have hord : (orderOf g : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr h)
  have hM : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
    have hM' : IsComponentOf C
        (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ LargeEvenSLGroup (Fin N) K) :=
      hC.of_le_of_le (le_inf hC.1 hCSL) inf_le_left
    have hM'' : IsComponentOf C
        (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
      rwa [CFSG.Assembly.largeEvenSLGroup_eq_statedSL N] at hM'
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hM''
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hd1, hΦinj, hθinj, hθrange, hθapply, i, hd2, hMeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsLinBlock_exists g hord C hM
  letI : ∀ j, Field (D j) := hFld
  haveI : ∀ j, Finite (D j) := hFin
  letI : ∀ j, Algebra K (D j) := hAlg
  let mulI : GL (Fin (d i)) (D i) →* (∀ j, GL (Fin (d j)) (D j)) :=
    MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i
  have hmulI_inj : Function.Injective mulI := by
    intro a b hab
    have := congrFun hab i
    simpa [mulI, MonoidHom.mulSingle_apply] using this
  let φ : StatedSL (d i) (D i) →* ↥C :=
    { toFun := fun x => ⟨θ (mulI x), by
        rw [hMeq]
        exact Subgroup.mem_map.mpr ⟨mulI x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp [mulI]
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MonoidHom.map_mul] }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have h1 : θ (mulI (x : GL (Fin (d i)) (D i))) = θ (mulI (y : GL (Fin (d i)) (D i))) :=
      congrArg Subtype.val hxy
    exact hmulI_inj (hθinj h1)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Subgroup.map θ (Subgroup.map mulI (StatedSL (d i) (D i))) := by
      rw [← hMeq]
      exact hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    show θ (mulI x) = c
    rw [hxy, hyc]
  let e : StatedSL (d i) (D i) ≃* ↥C := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hQ : CFSG.Assembly.IsQuasisimple (StatedSL (d i) (D i)) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hC.2.2
  have hperf : commutator (StatedSL (d i) (D i)) = ⊤ := hQ.1
  have hsimp : IsSimpleGroup
      (StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i))) := hQ.2
  have h2D : (2 : D i) = 0 := by
    have h : (algebraMap K (D i)) (2 : K) = 0 := by
      rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2, map_zero]
    exact (map_ofNat (algebraMap K (D i)) 2).symm.trans h
  have hcharD : ringChar (D i) = 2 := by
    have hdvd : ringChar (D i) ∣ 2 := (ringChar.spec (D i) 2).mp h2D
    rcases Nat.prime_two.eq_one_or_self_of_dvd (ringChar (D i)) hdvd with h1 | h2
    · exfalso
      haveI : CharP (D i) 1 := ringChar.of_eq h1
      have h1z : ((1 : ℕ) : D i) = 0 := (CharP.cast_eq_zero_iff (D i) 1 1).mpr (one_dvd 1)
      exact one_ne_zero (by simpa only [Nat.cast_one] using h1z)
    · exact h2
  haveI : CharP (D i) 2 := ringChar.of_eq hcharD
  obtain ⟨n, -, hfcard⟩ := @FiniteField.card (D i) _ (Fintype.ofFinite (D i)) 2 _
  let f : ℕ := n
  have hcard : Nat.card (D i) = 2 ^ f := by
    rw [@Nat.card_eq_fintype_card (D i) (Fintype.ofFinite (D i)), hfcard]
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hcard
      have := Finite.one_lt_card (α := D i)
      omega
    · exact h
  have hmf : d i = 2 → 2 ≤ f := by
    intro hdi2
    rw [hdi2] at hperf hsimp
    exact l02qt4b_two_le_of_card_two_statedSL hf hcard hperf hsimp
  have hmarkSL := l02qt4b_largeEvenMarking_statedSL_linear (m := d i) (f := f) (E := D i)
    hcard hperf hsimp hd2 hf hmf
  have hconj_mem : ∀ (A : GL (Fin (d i)) (D i)) (x : StatedSL (d i) (D i)),
      A * (x : GL (Fin (d i)) (D i)) * A⁻¹ ∈ StatedSL (d i) (D i) := by
    intro A x
    have hxL : (x : GL (Fin (d i)) (D i)) ∈ LargeEvenSLGroup (Fin (d i)) (D i) := by
      rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (d i)]
      exact x.2
    have h := (inferInstance : (LargeEvenSLGroup (Fin (d i)) (D i)).Normal).conj_mem
      (x : GL (Fin (d i)) (D i)) hxL A
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (d i)] at h
    exact h
  let πCSL : ↥C →* ↥(LargeEvenSLGroup (Fin N) K) := Subgroup.inclusion hCSL
  let πC : ↥C →* ↥J₀ :=
    { toFun := fun c => ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c), by
        rw [hJ₀]
        exact Subgroup.mem_map.mpr ⟨πCSL c, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hπC_surj : Function.Surjective πC := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
      rw [← hJ₀]
      exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)
      (πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩) = j
    have hpc : πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩ = y := Subtype.ext rfl
    rw [hpc]
    exact hyj
  have hπC_ker : πC.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hc' : πCSL c ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
      rw [MonoidHom.mem_ker]
      simpa [πC] using congrArg Subtype.val hc
    have hcen := l02qt4b_ker_projMk_le_center (LargeEvenSLGroup (Fin N) K) hc'
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro d
    apply Subtype.ext
    show (πCSL d : GL (Fin N) K) * (πCSL c : GL (Fin N) K) =
      (πCSL c : GL (Fin N) K) * (πCSL d : GL (Fin N) K)
    exact congrArg Subtype.val (hcen (πCSL d))
  let gAB : StatedSL (d i) (D i) →* ↥J₀ := πC.comp φ
  have hgAB_surj : Function.Surjective gAB := hπC_surj.comp hφsurj
  have hker : gAB.ker ≤ Subgroup.center (StatedSL (d i) (D i)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : φ x ∈ πC.ker := by rw [MonoidHom.mem_ker]; exact hx
    have hx2 : φ x ∈ Subgroup.center ↥C := hπC_ker hx1
    rw [Subgroup.mem_center_iff] at hx2 ⊢
    intro y
    apply hφinj
    rw [map_mul, map_mul]
    exact hx2 (φ y)
  have haction : ∀ h : GL (Fin N) K, h * g = g * h →
      ∃ A : GL (Fin (d i)) (D i), ∀ x : StatedSL (d i) (D i),
        (φ (⟨A * (x : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A x⟩) :
            GL (Fin N) K) = h * (φ x : GL (Fin N) K) * h⁻¹ := by
    intro h hh
    have hh_mem : h ∈ Subgroup.centralizer ({g} : Set (GL (Fin N) K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hh
    have hh_range : h ∈ θ.range := by rw [hθrange]; exact hh_mem
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hh_range
    refine ⟨w i, fun x => ?_⟩
    let y : StatedSL (d i) (D i) :=
      ⟨w i * (x : GL (Fin (d i)) (D i)) * (w i)⁻¹, hconj_mem (w i) x⟩
    have hconj_eq : w * mulI x * w⁻¹ = mulI (y : GL (Fin (d i)) (D i)) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [mulI, y, MonoidHom.mulSingle_apply]
      · simp [mulI, y, MonoidHom.mulSingle_apply, hj]
    calc (φ y : GL (Fin N) K)
        = θ (mulI (y : GL (Fin (d i)) (D i))) := rfl
      _ = θ (w * mulI x * w⁻¹) := by rw [← hconj_eq]
      _ = θ w * θ (mulI x) * (θ w)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = h * (φ x : GL (Fin N) K) * h⁻¹ := by rw [← hw]; rfl
  let PA : GL (Fin (d i)) (D i) → Prop := fun _ => True
  let PB : GL (Fin N) K → Prop := fun h => h * g = g * h
  let relA : GL (Fin (d i)) (D i) → StatedSL (d i) (D i) → StatedSL (d i) (D i) → Prop :=
    fun ε a a' => (a' : GL (Fin (d i)) (D i)) = ε⁻¹ * (a : GL (Fin (d i)) (D i)) * ε
  let relB : GL (Fin N) K → ↥J₀ → ↥J₀ → Prop :=
    fun j b b' => TableB.linConjAut (Fin N) K j
      (b : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (b' : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
  have hmarkSL' : LargeEvenMarking (StatedSL (d i) (D i))
      (fun lab _ _ I _ θ => GGChevStTag lab ∧ ∀ ε, PA ε → ∃ φ ∈ I,
        LargeEvenInduces θ (relA ε) φ) :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨hP.1, fun ε _ => hP.2 ε (Subgroup.mem_top ε)⟩) hmarkSL
  have hrel : ∀ j, PB j → ∃ ε, PA ε ∧ ∀ b b', relB j b b' →
      ∃ a a' : StatedSL (d i) (D i),
        gAB a = b ∧ gAB a' = b' ∧ relA ε a a' := by
    intro j hj
    obtain ⟨A, hA⟩ := haction j hj
    refine ⟨A⁻¹, trivial, ?_⟩
    intro b b' hb
    obtain ⟨a, ha⟩ := hgAB_surj b
    refine ⟨a, ⟨A * (a : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A a⟩, ha, ?_, ?_⟩
    · apply Subtype.ext
      dsimp only [gAB, MonoidHom.comp_apply]
      change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)
          (πCSL (φ ⟨A * (a : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A a⟩)) =
        (b' : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      have hstep : πCSL (φ ⟨A * (a : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A a⟩) =
          MulAut.conjNormal j (πCSL (φ a)) := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        exact hA a
      rw [hstep]
      change ((MulAut.conjNormal j (πCSL (φ a)) : ↥(LargeEvenSLGroup (Fin N) K)) :
          LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
        (b' : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      rw [← TableB.linConjAut_mk j (πCSL (φ a))]
      rw [show ((πCSL (φ a) : ↥(LargeEvenSLGroup (Fin N) K)) :
          LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
        (b : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) from congrArg Subtype.val ha]
      exact hb
    · simp [relA, inv_inv]
  have hmarkJ := largeEvenMarking_of_central_surj gAB hgAB_surj hker hperf PA PB
    (fun lab => GGChevStTag lab) relA relB hrel hmarkSL'
  have hnorm : ∀ h : GL (Fin N) K, h * g = g * h →
      ∀ j ∈ J₀, TableB.linConjAut (Fin N) K h j ∈ J₀ := by
    intro h hh j hj
    obtain ⟨A, hA⟩ := haction h hh
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := hJ₀ ▸ hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    let c : ↥C := ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩
    have hpc : πCSL c = y := Subtype.ext rfl
    have hjc : (πC c : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = j := by
      change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c) = j
      rw [hpc]
      exact hyj
    let x : StatedSL (d i) (D i) := e.symm c
    have hφx : φ x = c := MulEquiv.apply_symm_apply e c
    let c' : ↥C := φ ⟨A * (x : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A x⟩
    have hc'val : (c' : GL (Fin N) K) = h * (c : GL (Fin N) K) * h⁻¹ := by
      have h := hA x
      rwa [hφx] at h
    have hconj : πCSL c' = MulAut.conjNormal h (πCSL c) := by
      apply Subtype.ext
      change (c' : GL (Fin N) K) = (MulAut.conjNormal h (πCSL c) : GL (Fin N) K)
      rw [MulAut.conjNormal_apply, hc'val]
      rfl
    have hkey : TableB.linConjAut (Fin N) K h j =
        (πC c' : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) := by
      rw [← hjc]
      change TableB.linConjAut (Fin N) K h
          ((πCSL c : ↥(LargeEvenSLGroup (Fin N) K)) :
            LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
        ((πCSL c' : ↥(LargeEvenSLGroup (Fin N) K)) :
          LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      rw [TableB.linConjAut_mk, hconj]
    rw [hkey]
    exact (πC c').2
  refine largeEvenMarking_mono (fun lab R _ I F θJ hP => ?_) hmarkJ
  intro h hh
  exact ⟨hnorm h hh, hP.2 h hh⟩

end CFSG.StandardType
