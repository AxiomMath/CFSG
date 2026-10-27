module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LieType.TwoRank.PGLMap
public import CFSG.LocalAnalysis.StandardType.GGL45NtClUni
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem elu_charP_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpchar, n, hpprime, hcard⟩ := FiniteField.card' K
  have h2 : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have h1 : p ^ (n : ℕ) = 2 ^ m := by rw [← h2, hK]
  have hdvd : p ∣ 2 ^ m := h1 ▸ dvd_pow_self p n.pos.ne'
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp (hpprime.dvd_of_dvd_pow hdvd)
  rwa [hp2] at hpchar

private theorem elu_projEmbedAt_of_ker (d : ℕ) {G R S : Type} [Group G] [Group R] [Group S]
    (f : G →* MulAut S) (Z : Subgroup G) [Z.Normal] (I : Set (MulAut R))
    (F : MulAut R ≃* MulAut S) (hI : ∀ φ ∈ I, F φ ∈ Set.range f)
    (hInn : ∀ r : R, MulAut.conj r ∈ I) (hZ : f.ker = Z)
    (K' : Type) [Field K'] [IsAlgClosed K'] [CharP K' 2]
    (θ : G →* Matrix.ProjGenLinGroup (Fin d) K') (hθ : θ.ker = Z) :
    GGClassicalProjEmbedAt d R I := by
  have hle : Subgroup.closure I ≤ (f.range).comap F.toMonoidHom :=
    (Subgroup.closure_le ((f.range).comap F.toMonoidHom)).mpr (fun φ hφ => by
      show F.toMonoidHom φ ∈ f.range
      exact hI φ hφ)
  let ε₁ : ↥(Subgroup.closure I) →* ↥(f.range) :=
    { toFun := fun x => ⟨F (x : MulAut R), hle x.2⟩
      map_one' := Subtype.ext (map_one F)
      map_mul' := fun x y => Subtype.ext (map_mul F (x : MulAut R) (y : MulAut R)) }
  have hε₁ : Function.Injective ε₁ := fun x y h =>
    Subtype.ext (F.injective (Subtype.ext_iff.mp h))
  have e2 : ↥(f.range) ≃* G ⧸ Z :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ)
  have eθ : G ⧸ Z ≃* ↥θ.range :=
    (QuotientGroup.quotientMulEquivOfEq hθ).symm.trans (QuotientGroup.quotientKerEquivRange θ)
  refine ⟨hInn, K', inferInstance, inferInstance, inferInstance,
    (Subgroup.subtype θ.range).comp (eθ.toMonoidHom.comp (e2.toMonoidHom.comp ε₁)), ?_⟩
  exact (Subgroup.subtype_injective θ.range).comp (eθ.injective.comp (e2.injective.comp hε₁))

private theorem elu_linearProjEmbed (d m : ℕ) (hd : 2 ≤ d) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ m) :
    GGClassicalProjEmbedAt d (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  haveI hchar : CharP K 2 := elu_charP_two hK
  have hG : (conjAut d K).ker = Subgroup.center (GL (Fin d) K) := by
    refine le_antisymm ?_ ?_
    · intro A hA
      rw [MonoidHom.mem_ker] at hA
      exact AutPSL.mem_center_of_conjAut_eq_one (n := d) (K := K) (by omega) hA
    · intro A hA
      rw [MonoidHom.mem_ker]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
      obtain ⟨u, rfl⟩ := hA
      exact conjAut_scalar u
  have hInn : ∀ r : LargeEvenProj (LargeEvenSLGroup (Fin d) K),
      MulAut.conj r ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
    intro r
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K)) r
    refine ⟨(h : GL (Fin d) K), Set.mem_univ _, ?_⟩
    intro h₁ h₂ hh
    have hconj : MulAut.conj ((h : ↥(LargeEvenSLGroup (Fin d) K)) :
          LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =
        TableB.linConjAut (Fin d) K (h : GL (Fin d) K) :=
      (TableB.linConjAut_of_mem (h : GL (Fin d) K) h.2).symm
    change MulAut.conj ((h : ↥(LargeEvenSLGroup (Fin d) K)) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      ((h₁ : ↥(LargeEvenSLGroup (Fin d) K)) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =
      ((h₂ : ↥(LargeEvenSLGroup (Fin d) K)) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    rw [hconj, TableB.linConjAut_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hh.symm
  have hmap : Function.Injective
      (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K))) :=
    CFSG.LieType.TwoRank.projGenLinGroup_map_injective (n := Fin d)
      (algebraMap K (AlgebraicClosure K))
  let θ : GL (Fin d) K →* Matrix.ProjGenLinGroup (Fin d) (AlgebraicClosure K) :=
    (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K))).comp
      (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)))
  have hθ : θ.ker = Subgroup.center (GL (Fin d) K) := by
    ext A
    rw [MonoidHom.mem_ker]
    constructor
    · intro hA
      have hA' : (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K)))
          (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)) A) = 1 := hA
      have h1 : QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)) A =
          (1 : Matrix.ProjGenLinGroup (Fin d) K) := by
        apply hmap
        simpa using hA'
      have hmem : A ∈ (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K))).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at hmem
    · intro hA
      have h1 : QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)) A =
          (1 : Matrix.ProjGenLinGroup (Fin d) K) := by
        have hmem : A ∈ (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K))).ker := by
          rwa [QuotientGroup.ker_mk']
        exact MonoidHom.mem_ker.mp hmem
      show (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K)))
          (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)) A) = 1
      rw [h1, map_one]
  refine elu_projEmbedAt_of_ker d (conjAut d K) (Subgroup.center (GL (Fin d) K))
    (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (MulAut.congr (TypeA.recipeEquiv d K)) ?_ hInn hG
    (AlgebraicClosure K) θ hθ
  intro φ hφ
  exact TypeA.congr_recipeEquiv_mem hφ

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ClassicalGroups.UnitaryFlag

private theorem elu_unitaryProjEmbed (d n : ℕ) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGClassicalProjEmbedAt d (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [pow_zero, one_pow, Nat.card_eq_fintype_card] at hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      rw [Nat.card_eq_fintype_card] at h2
      omega
    · exact hn
  have hK2 : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, ← pow_mul, Nat.mul_comm]
  haveI hchar : CharP K 2 := elu_charP_two hK2
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  let H := LargeEvenSUGroup (Fin d) K (2 ^ n)
  let U := TableB.unitGroup (ι := Fin d) h.bar
  let R := LargeEvenProj H
  let I := LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) K (2 ^ n))
  let Z : Subgroup U := (LargeEvenScalars (Fin d) K).subgroupOf U
  have hcenter : Subgroup.center (GL (Fin d) K) = LargeEvenScalars (Fin d) K :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar.trans largeEvenScalars_def.symm
  have hUeq : U = primeFormUnitary h (idGram K d) := by
    ext A
    rw [TableB.mem_unitGroup, mem_primeFormUnitary]
    simp [idGram]
  have hInn : ∀ r : R, MulAut.conj r ∈ I := by
    intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ r
    refine ⟨(x : GL (Fin d) K), ?_, ?_⟩
    · have hxprime : (x : GL (Fin d) K) ∈ primeFormUnitary h (idGram K d) := by
        rw [mem_primeFormUnitary]
        have h1 := (mem_unitarySU_iff h).mp
          (show (x : GL (Fin d) K) ∈ unitarySU 2 n K d from x.2)
        simpa [idGram] using h1.2
      exact TableBUD.mem_guSet_of_mem_primeFormUnitary h hxprime
    · intro h₁ h₂ hh
      change MulAut.conj (LargeEvenProjMk H x) (LargeEvenProjMk H h₁) =
        LargeEvenProjMk H h₂
      rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hh.symm
  have hsub : ∀ a : U, (a : GL (Fin d) K) ∈ Subgroup.normalizer (H : Set (GL (Fin d) K)) :=
    fun a => CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer h a.2
  have hZle : (CFSG.HardMathSupport.C14Cl.uniConj h d).ker ≤ Z := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hN := hsub a
    have hmem : ∀ x : H, (a : GL (Fin d) K) * (x : GL (Fin d) K) *
        (a : GL (Fin d) K)⁻¹ ∈ H := fun x => (Subgroup.mem_normalizer_iff.mp hN x).mp x.2
    have htriv : ∀ x : H,
        (QuotientGroup.mk (⟨(a : GL (Fin d) K) * (x : GL (Fin d) K) *
          (a : GL (Fin d) K)⁻¹, hmem x⟩ : H) : LargeEvenProj H) =
        QuotientGroup.mk x := by
      intro x
      have hval : (CFSG.HardMathSupport.C14Cl.uniConj h d a) ((x : H) : R) = ((x : H) : R) := by
        simpa using DFunLike.congr_fun ha ((x : H) : R)
      have hmk : (CFSG.HardMathSupport.C14Cl.uniConj h d a) ((x : H) : R) =
          (QuotientGroup.mk (⟨(a : GL (Fin d) K) * (x : GL (Fin d) K) *
            (a : GL (Fin d) K)⁻¹, hmem x⟩ : H) : R) := by
        change (TableB.projConj H (⟨(a : GL (Fin d) K), hN⟩ :
            ↥(Subgroup.normalizer (H : Set (GL (Fin d) K))))) ((x : H) : R) =
          (QuotientGroup.mk (⟨(a : GL (Fin d) K) * (x : GL (Fin d) K) *
            (a : GL (Fin d) K)⁻¹, hmem x⟩ : H) : R)
        rw [TableB.projConj_mk]
        rfl
      exact hmk.symm.trans hval
    exact Subgroup.mem_subgroupOf.mpr
      (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.mem_scalars_of_conj_triv hd hn hK hdq hmem htriv)
  have hZge : Z ≤ (CFSG.HardMathSupport.C14Cl.uniConj h d).ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    have hscal : (a : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
      Subgroup.mem_subgroupOf.mp ha
    change (TableB.projConj H (⟨(a : GL (Fin d) K), hsub a⟩ :
      ↥(Subgroup.normalizer (H : Set (GL (Fin d) K))))) = 1
    exact TableB.projConj_of_scalar H hscal
  have hZ : (CFSG.HardMathSupport.C14Cl.uniConj h d).ker = Z := le_antisymm hZle hZge
  have hI : ∀ φ ∈ I, (MulEquiv.refl (MulAut R)) φ ∈
      Set.range (CFSG.HardMathSupport.C14Cl.uniConj h d) := by
    intro φ hφ
    obtain ⟨A, hA, hgraph⟩ := hφ
    have hA' : A ∈ Subgroup.normalizer (H : Set (GL (Fin d) K)) :=
      TableBUE.gu_subset_normalizer h hA
    let Nn : ↥(Subgroup.normalizer (H : Set (GL (Fin d) K))) := ⟨A, hA'⟩
    have hφeq : φ = TableB.projConj H Nn := by
      ext r
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ r
      have hx : φ ((x : H) : R) = ((⟨A * (x : GL (Fin d) K) * A⁻¹,
          (Subgroup.mem_normalizer_iff.mp hA' x).mp x.2⟩ : H) : R) :=
        hgraph x _ rfl
      change φ ((x : H) : R) = (TableB.projConj H Nn) ((x : H) : R)
      rw [hx, TableB.projConj_mk]
      rfl
    rw [hφeq]
    obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu h hA
    have hB : GeneralLinearGroup.scalar (Fin d) u * A ∈ U := by
      rw [hUeq]
      exact hu
    have hz : GeneralLinearGroup.scalar (Fin d) u ∈ LargeEvenScalars (Fin d) K := ⟨u, rfl⟩
    have hNs : GeneralLinearGroup.scalar (Fin d) u ∈
        Subgroup.normalizer (H : Set (GL (Fin d) K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcomm : GeneralLinearGroup.scalar (Fin d) u * x =
          x * GeneralLinearGroup.scalar (Fin d) u :=
        (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center u) x).symm
      have hconj : GeneralLinearGroup.scalar (Fin d) u * x *
          (GeneralLinearGroup.scalar (Fin d) u)⁻¹ = x := by
        rw [hcomm]; group
      constructor
      · intro hx
        rwa [hconj]
      · intro hx
        rwa [hconj] at hx
    let Bn : ↥(Subgroup.normalizer (H : Set (GL (Fin d) K))) :=
      ⟨GeneralLinearGroup.scalar (Fin d) u * A, hsub ⟨_, hB⟩⟩
    let Sn : ↥(Subgroup.normalizer (H : Set (GL (Fin d) K))) :=
      ⟨GeneralLinearGroup.scalar (Fin d) u, hNs⟩
    refine ⟨⟨GeneralLinearGroup.scalar (Fin d) u * A, hB⟩, ?_⟩
    have huni : (CFSG.HardMathSupport.C14Cl.uniConj h d
        ⟨GeneralLinearGroup.scalar (Fin d) u * A, hB⟩) = TableB.projConj H Bn := rfl
    rw [huni]
    have hmul : TableB.projConj H Bn = TableB.projConj H Sn * TableB.projConj H Nn := by
      rw [← map_mul]
      rfl
    rw [hmul, TableB.projConj_of_scalar H hz, one_mul]
    rfl
  have hmap : Function.Injective
      (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K))) :=
    CFSG.LieType.TwoRank.projGenLinGroup_map_injective (n := Fin d)
      (algebraMap K (AlgebraicClosure K))
  let ψ : U →* Matrix.ProjGenLinGroup (Fin d) K :=
    (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K))).comp (Subgroup.subtype U)
  have hmemScal : ∀ A : GL (Fin d) K, A ∈ LargeEvenScalars (Fin d) K ↔
      A ∈ Subgroup.center (GL (Fin d) K) := fun A => by rw [hcenter]
  have hψker : ψ.ker = Z := by
    ext a
    change (QuotientGroup.mk' (Subgroup.center (GL (Fin d) K)) (a : GL (Fin d) K)) = 1 ↔
      (a : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K
    rw [hmemScal]
    exact MonoidHom.mem_ker.trans
      (SetLike.ext_iff.mp (QuotientGroup.ker_mk' (Subgroup.center (GL (Fin d) K))) _)
  let θ : U →* Matrix.ProjGenLinGroup (Fin d) (AlgebraicClosure K) :=
    (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K))).comp ψ
  have hθ : θ.ker = Z := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      have ha' : (Matrix.ProjGenLinGroup.map (n := Fin d)
          (algebraMap K (AlgebraicClosure K))) (ψ a) = 1 := ha
      have h1 : ψ a = 1 := hmap (ha'.trans (map_one _).symm)
      rw [← hψker]
      exact h1
    · intro ha
      have h1 : ψ a = 1 := by
        rw [← hψker] at ha
        exact ha
      show (Matrix.ProjGenLinGroup.map (n := Fin d) (algebraMap K (AlgebraicClosure K)))
          (ψ a) = 1
      rw [h1, map_one]
  exact elu_projEmbedAt_of_ker d (CFSG.HardMathSupport.C14Cl.uniConj h d) Z I
    (MulEquiv.refl (MulAut R)) hI hInn hZ (AlgebraicClosure K) θ hθ

theorem ggClassicalProjEmbed_linUni (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (h : GGClassLinUni lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGClassicalProjEmbedAt (ggClassDeg lab) R I := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, hrank⟩ := hlab
  intro Q hQ
  dsimp only [GGClassLinUni] at h
  rcases h with ht | ht | ⟨ht, hr3⟩ | ⟨ht, hr23⟩
  · subst ht
    dsimp only [LargeEvenRawDatum, ggClassDeg] at hQ ⊢
    obtain ⟨K, hFld, hFin, hKcard, hq⟩ := hQ
    exact ⟨K, hFld, hFin, hKcard, hq,
      elu_linearProjEmbed (r + 1) n (by omega) K hKcard⟩
  · subst ht
    have hdq : (r + 1, 2 ^ n) ≠ (3, 2) := by
      rintro h
      have hr2 : r = 2 := by have := congrArg Prod.fst h; omega
      have hn2 : 2 ≤ n := hrank.2 hr2
      have hn2' : 2 ^ n = 2 := congrArg Prod.snd h
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    dsimp only [LargeEvenRawDatum, ggClassDeg] at hQ ⊢
    obtain ⟨K, hFld, hFin, hKcard, hq⟩ := hQ
    exact ⟨K, hFld, hFin, hKcard, hq,
      elu_unitaryProjEmbed (r + 1) n (by omega) hdq K hKcard⟩
  · subst ht
    subst hr3
    dsimp only [LargeEvenRawDatum, ggClassDeg] at hQ ⊢
    obtain ⟨K, hFld, hFin, hKcard, hq⟩ := hQ
    exact ⟨K, hFld, hFin, hKcard, hq, elu_linearProjEmbed 4 n (by omega) K hKcard⟩
  · subst ht
    rcases hr23 with hr2 | hr3
    · subst hr2
      dsimp only [LargeEvenRawDatum, ggClassDeg] at hQ ⊢
      obtain ⟨K, hFld, hFin, hKcard, hq⟩ := hQ
      have hK' : Nat.card K = 2 ^ (2 * n) := by
        rw [hKcard, ← pow_mul, Nat.mul_comm]
      exact ⟨K, hFld, hFin, hKcard, hq,
        elu_linearProjEmbed 2 (2 * n) (by omega) K hK'⟩
    · subst hr3
      have hdq : (4, 2 ^ n) ≠ (3, 2) := by
        rintro h
        have := congrArg Prod.fst h
        omega
      dsimp only [LargeEvenRawDatum, ggClassDeg] at hQ ⊢
      obtain ⟨K, hFld, hFin, hKcard, hq⟩ := hQ
      exact ⟨K, hFld, hFin, hKcard, hq,
        elu_unitaryProjEmbed 4 n (by omega) hdq K hKcard⟩

end CFSG.StandardType

end
