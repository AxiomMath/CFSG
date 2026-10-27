module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.LieType.Chevalley.F4FieldTwoEuclid
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.RankThree.PartOne.KF4.Lattice3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2

public noncomputable section
namespace CFSG.StandardType.F4ExplicitPos.FiveToralKernel

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rootChar_eq_zeta_zpow
    {L : Type} [Field L] {a : Fin 4 → Lˣ} {ζ : Lˣ} {n : Fin 4 → ℤ}
    (ha : ∀ i, a i = ζ ^ n i) (v : Fin Tag.F4.rank → ℤ) :
    rootChar (τ := Tag.F4) a v = ζ ^ (∑ i : Fin 4, n i * v i) := by
  calc
    rootChar (τ := Tag.F4) a v = ∏ i, (ζ ^ n i) ^ v i := by
      change (∏ i, a i ^ v i) = ∏ i, (ζ ^ n i) ^ v i
      exact Finset.prod_congr rfl (fun i _ => by rw [ha i])
    _ = ∏ i, ζ ^ (n i * v i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_mul]
    _ = ζ ^ (∑ i : Fin 4, n i * v i) := by
      exact Finset.prod_zpow_eq_zpow_sum Finset.univ ζ _

public theorem exists_toral_character
    {L : Type} [Field L]
    (a : Fin 4 → Lˣ) (ha5 : ∀ i, a i ^ 5 = 1) (ha1 : a ≠ 1)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ 5) :
    ∃ m : Fin 4 → ZMod 5,
      m ≠ 0 ∧
      (∀ i, a i = ζ ^ (m i).val) ∧
      (∀ v : Fin Tag.F4.rank → ℤ,
        rootChar (τ := Tag.F4) a v = 1 ↔
          ∑ i : Fin 4, ((v i : ZMod 5) * m i) = 0) := by
  have hζL : IsPrimitiveRoot (ζ : L) (5 : ℕ) :=
    (IsPrimitiveRoot.coe_units_iff (ζ := ζ) (k := 5)).mpr hζ
  have haL : ∀ i, (a i : L) ^ 5 = 1 := by
    intro i
    have h := congrArg (fun u : Lˣ => (u : L)) (ha5 i)
    simpa using h
  choose n hn using fun i => hζL.eq_pow_of_pow_eq_one (haL i)
  have hn_lt : ∀ i, n i < 5 := fun i => (hn i).1
  have hn_val : ∀ i, (ζ : L) ^ n i = (a i : L) := fun i => (hn i).2
  have hn_units : ∀ i, a i = ζ ^ n i := by
    intro i
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using (hn_val i).symm
  let m : Fin 4 → ZMod 5 := fun i => (n i : ZMod 5)
  have hm_ne : m ≠ 0 := by
    intro hm0
    apply ha1
    funext i
    have hmi : m i = 0 := by
      simpa using congrFun hm0 i
    have hdiv : 5 ∣ n i :=
      (ZMod.natCast_eq_zero_iff (n i) 5).mp (by simpa [m] using hmi)
    have hni : n i = 0 := by
      rcases hdiv with ⟨k, hk⟩
      have hklt : 5 * k < 5 := by simpa [hk] using hn_lt i
      have hk0 : k = 0 := by omega
      simp [hk, hk0]
    calc
      a i = ζ ^ n i := hn_units i
      _ = ζ ^ 0 := by rw [hni]
      _ = 1 := by simp
  refine ⟨m, hm_ne, ?_, ?_⟩
  · intro i
    have hmval : (m i).val = n i := by
      exact ZMod.val_natCast_of_lt (hn_lt i)
    calc
      a i = ζ ^ n i := hn_units i
      _ = ζ ^ (m i).val := by rw [hmval]
  · intro v
    let N : ℤ := ∑ i : Fin 4, (n i : ℤ) * v i
    have hroot : rootChar (τ := Tag.F4) a v = ζ ^ N := by
      have hnZ : ∀ i, a i = ζ ^ (n i : ℤ) := by
        intro i
        simpa using hn_units i
      simpa [N] using
        rootChar_eq_zeta_zpow (a := a) (ζ := ζ) (n := fun i => (n i : ℤ)) hnZ v
    have hdot : (∑ i : Fin 4, ((v i : ZMod 5) * m i)) = (N : ZMod 5) := by
      simp only [N, m, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      apply Finset.sum_congr rfl
      intro i _
      ring
    constructor
    · intro h
      have hz : ζ ^ N = 1 := by simpa [hroot] using h
      have hdvd : (5 : ℤ) ∣ N := (hζ.zpow_eq_one_iff_dvd N).mp hz
      rw [hdot]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd N 5).mpr hdvd
    · intro h
      have hz0 : (N : ZMod 5) = 0 := by
        rw [← hdot]
        exact h
      have hdvd : (5 : ℤ) ∣ N := (ZMod.intCast_zmod_eq_zero_iff_dvd N 5).mp hz0
      have hz : ζ ^ N = 1 := (hζ.zpow_eq_one_iff_dvd N).mpr hdvd
      simpa [hroot] using hz

public theorem exists_toral_character_of_nonidentity
    {L : Type} [Field L]
    (a : Fin 4 → Lˣ) (ha5 : ∀ i, a i ^ 5 = 1) (ha1 : a ≠ 1) :
    ∃ (ζ : Lˣ) (m : Fin 4 → ZMod 5),
      IsPrimitiveRoot ζ 5 ∧ m ≠ 0 ∧
      (∀ i, a i = ζ ^ (m i).val) ∧
      (∀ v : Fin Tag.F4.rank → ℤ,
        rootChar (τ := Tag.F4) a v = 1 ↔
          ∑ i : Fin 4, ((v i : ZMod 5) * m i) = 0) := by
  classical
  have hi : ∃ i, a i ≠ 1 := by
    by_contra h
    apply ha1
    funext i
    exact Classical.not_not.mp (fun hn => h ⟨i, hn⟩)
  obtain ⟨i, hi⟩ := hi
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hζ : IsPrimitiveRoot (a i) 5 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (ha5 i) hi)
  obtain ⟨m, hm, heq, hchar⟩ := exists_toral_character a ha5 ha1 (a i) hζ
  exact ⟨a i, m, hζ, hm, heq, hchar⟩

@[expose] public def f4CharValue (m : Fin 4 → ZMod 5) (v : Fin Tag.F4.rank → ℤ) : ZMod 5 :=
  ∑ i : Fin 4, (v i : ZMod 5) * m i

@[expose] public def f4CharMask (m : Fin 4 → ZMod 5) : Finset (Fin 48) :=
  Finset.univ.filter fun k => f4CharValue m (CFSG.RankThree.PartOne.KF4.f4RootVec k) = 0

@[expose] public def f4RootDot (i j : Fin 48) : ℚ :=
  (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec i)) ⬝ᵥ
    (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec j))

@[expose] public def f4Nonorth (i j : Fin 48) : Prop := f4RootDot i j ≠ 0

@[expose] public def f4PathTwo (S : Finset (Fin 48)) (i j : Fin 48) : Prop :=
  i = j ∨ f4Nonorth i j ∨ ∃ k ∈ S, f4Nonorth i k ∧ f4Nonorth k j

@[expose] public def f4MaskGood (m : Fin 4 → ZMod 5) : Prop :=
  let S := f4CharMask m
  S.card = 8 ∨ (S.card = 18 ∧ ∀ i ∈ S, ∀ j ∈ S, f4PathTwo S i j)

public instance f4MaskGood_decidable (m : Fin 4 → ZMod 5) : Decidable (f4MaskGood m) := by
  unfold f4MaskGood f4PathTwo f4Nonorth
  infer_instance

public theorem f4MaskGood_all : ∀ m : Fin 4 → ZMod 5, m ≠ 0 → f4MaskGood m := by
  decide +kernel

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section NativeKernelComponents

public theorem kernelRoots_eq_image_f4CharMask
    {L : Type} [Field L]
    (a : Fin 4 → Lˣ) (ha5 : ∀ i, a i ^ 5 = 1) (ha1 : a ≠ 1) :
    ∃ m : Fin 4 → ZMod 5,
      m ≠ 0 ∧
      (∀ v : Fin Tag.F4.rank → ℤ,
        rootChar (τ := Tag.F4) a v = 1 ↔
          f4CharValue m v = 0) ∧
      kernelRoots (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a) =
        CFSG.RankThree.PartOne.KF4.f4RootVec ''
          (↑(f4CharMask m) : Set (Fin 48)) := by
  obtain ⟨ζ, m, hζ, hm, heq, hchar⟩ :=
    exists_toral_character_of_nonidentity a ha5 ha1
  have hcharVal : ∀ v : Fin Tag.F4.rank → ℤ,
      rootChar (τ := Tag.F4) a v = 1 ↔ f4CharValue m v = 0 := by
    intro v
    simpa [f4CharValue] using hchar v
  refine ⟨m, hm, hcharVal, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hχ⟩
    have hrootChar : rootChar (τ := Tag.F4) a α = 1 := by
      simpa [CFSG.LieType.AlgebraicGroups.rootCharHom] using hχ
    obtain ⟨k, hk⟩ :=
      (CFSG.RankThree.PartOne.KF4.isRoot_iff_exists_f4RootVec).1 hα
    refine ⟨k, ?_, hk⟩
    have hz : f4CharValue m (CFSG.RankThree.PartOne.KF4.f4RootVec k) = 0 := by
      rw [hk]
      exact (hcharVal α).mp hrootChar
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hz⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨CFSG.RankThree.PartOne.KF4.isRoot_f4RootVec k, ?_⟩
    have hz : f4CharValue m (CFSG.RankThree.PartOne.KF4.f4RootVec k) = 0 :=
      (Finset.mem_filter.mp hk).2
    have hrootChar : rootChar (τ := Tag.F4) a (CFSG.RankThree.PartOne.KF4.f4RootVec k) = 1 :=
      (hcharVal _).mpr hz
    simpa [CFSG.LieType.AlgebraicGroups.rootCharHom] using hrootChar

public theorem component_ncard_dichotomy
    {L : Type} [Field L]
    (a : Fin 4 → Lˣ) (ha5 : ∀ i, a i ^ 5 = 1) (ha1 : a ≠ 1) :
    ∀ i : KernelComponent (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a),
      (componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a) i).ncard ≤ 8 ∨
        ((componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a) i =
            kernelRoots (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a)) ∧
          (componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a) i).ncard = 18) := by
  classical
  let χ := CFSG.LieType.AlgebraicGroups.rootCharHom (τ := Tag.F4) a
  obtain ⟨m, hm, hcharVal, hker⟩ := kernelRoots_eq_image_f4CharMask a ha5 ha1
  have hkerFin : (kernelRoots χ).Finite := by
    rw [hker]
    exact (Finset.finite_toSet (f4CharMask m)).image _
  have hkerCard : (kernelRoots χ).ncard = (f4CharMask m).card := by
    rw [hker, Set.ncard_image_of_injective _ CFSG.RankThree.PartOne.KF4.f4RootVec_injective,
      Set.ncard_coe_finset]
  have hmask' : (f4CharMask m).card = 8 ∨
      ((f4CharMask m).card = 18 ∧
        ∀ i ∈ f4CharMask m,
          ∀ j ∈ f4CharMask m,
            f4PathTwo (f4CharMask m) i j) := by
    simpa [f4MaskGood] using f4MaskGood_all m hm
  have hmemKer : ∀ k ∈ f4CharMask m,
      CFSG.RankThree.PartOne.KF4.f4RootVec k ∈ kernelRoots χ := by
    intro k hk
    rw [hker]
    exact ⟨k, by simpa using hk, rfl⟩
  have hnonorth_iform : ∀ {i j : Fin 48}, f4Nonorth i j →
      iform (CFSG.RankThree.PartOne.KF4.f4RootVec i)
        (CFSG.RankThree.PartOne.KF4.f4RootVec j) ≠ 0 := by
    intro i j h hzero
    have hdotne :
        (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec i)) ⬝ᵥ
          (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec j)) ≠ 0 := by
      simpa [f4Nonorth, f4RootDot] using h
    apply hdotne
    rw [CFSG.LieType.Chevalley.f4Euclid_dotProduct, hzero]
    norm_num
  rcases hmask' with h8 | ⟨h18, hpath⟩
  · intro i
    have hsubset : componentRoots χ i ⊆ kernelRoots χ := by
      intro α hα
      exact hα.1
    have hle : (componentRoots χ i).ncard ≤ (kernelRoots χ).ncard :=
      Set.ncard_le_ncard hsubset hkerFin
    have hcard8 : (kernelRoots χ).ncard = 8 := hkerCard.trans h8
    left
    dsimp [χ] at hle hcard8 ⊢
    omega
  · have hconnFin : ∀ i j (hi : i ∈ f4CharMask m)
        (hj : j ∈ f4CharMask m),
        (⟦⟨CFSG.RankThree.PartOne.KF4.f4RootVec i, hmemKer i hi⟩⟧ : KernelComponent χ) =
          ⟦⟨CFSG.RankThree.PartOne.KF4.f4RootVec j, hmemKer j hj⟩⟧ := by
      intro i j hi hj
      rcases hpath i hi j hj with rfl | hadj | ⟨k, hk, hik, hkj⟩
      · rfl
      · exact mk_eq_of_iform_ne_zero
          (α := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec i, hmemKer i hi⟩)
          (β := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec j, hmemKer j hj⟩)
          (hnonorth_iform hadj)
      · exact (mk_eq_of_iform_ne_zero
          (α := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec i, hmemKer i hi⟩)
          (β := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec k, hmemKer k hk⟩)
          (hnonorth_iform hik)).trans
          (mk_eq_of_iform_ne_zero
            (α := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec k, hmemKer k hk⟩)
            (β := ⟨CFSG.RankThree.PartOne.KF4.f4RootVec j, hmemKer j hj⟩)
            (hnonorth_iform hkj))
    have hconn : ∀ α β : kernelRoots χ,
        (⟦α⟧ : KernelComponent χ) = ⟦β⟧ := by
      intro α β
      have hαimg : (α : Fin Tag.F4.rank → ℤ) ∈
          CFSG.RankThree.PartOne.KF4.f4RootVec ''
            (↑(f4CharMask m) : Set (Fin 48)) := by
        rw [← hker]
        exact α.2
      have hβimg : (β : Fin Tag.F4.rank → ℤ) ∈
          CFSG.RankThree.PartOne.KF4.f4RootVec ''
            (↑(f4CharMask m) : Set (Fin 48)) := by
        rw [← hker]
        exact β.2
      rcases hαimg with ⟨i, hi, hαeq⟩
      rcases hβimg with ⟨j, hj, hβeq⟩
      have hi' : i ∈ f4CharMask m := by simpa using hi
      have hj' : j ∈ f4CharMask m := by simpa using hj
      have hαsub : (⟨CFSG.RankThree.PartOne.KF4.f4RootVec i, hmemKer i hi'⟩ : kernelRoots χ) = α := by
        apply Subtype.ext
        exact hαeq
      have hβsub : (⟨CFSG.RankThree.PartOne.KF4.f4RootVec j, hmemKer j hj'⟩ : kernelRoots χ) = β := by
        apply Subtype.ext
        exact hβeq
      rw [← hαsub, ← hβsub]
      exact hconnFin i j hi' hj'
    have hcompEq : ∀ i : KernelComponent χ, componentRoots χ i = kernelRoots χ := by
      intro i
      obtain ⟨x, rfl⟩ := Quot.exists_rep i
      ext α
      constructor
      · rintro ⟨hα, -⟩
        exact hα
      · intro hα
        exact ⟨hα, hconn ⟨α, hα⟩ x⟩
    intro i
    right
    refine ⟨hcompEq i, ?_⟩
    rw [hcompEq i, hkerCard, h18]

end NativeKernelComponents

section NativeEighteenRootShape
open CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.F4ExplicitPos
  CFSG.RankThree.PartOne.KF4

private theorem ncard_pair (j : Fin Tag.F4.rank) :
    ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
  rw [Set.ncard_pair]
  intro h
  have := congrFun h j
  simp at this

private theorem ncard_long :
    (parabolicRoots Tag.F4 f4LongSupport).ncard = 6 := by
  have h : (parabolicRoots Tag.F4
      (↑({f4Index 0, f4Index 1} : Finset (Fin Tag.F4.rank)) : Set _)).ncard = 6 := by
    rw [CFSG.RankThree.PartOne.KF4.f4_parabolic_card]
    decide +kernel
  simpa [CFSG.RankThree.PartOne.KF4.f4LongSupport] using h

private theorem ncard_short :
    (parabolicRoots Tag.F4 f4ShortSupport).ncard = 6 := by
  have h : (parabolicRoots Tag.F4
      (↑({f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) : Set _)).ncard = 6 := by
    rw [CFSG.RankThree.PartOne.KF4.f4_parabolic_card]
    decide +kernel
  simpa [CFSG.RankThree.PartOne.KF4.f4ShortSupport] using h

private theorem ncard_b2 :
    (CFSG.SeitzReduction.F4Pilot.b2LeviRoots).ncard = 8 := by
  rw [CFSG.SeitzReduction.F4Pilot.b2LeviRoots]
  have hset : (↑({f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) : Set _) =
      CFSG.SeitzReduction.F4Pilot.nodesTU := by
    ext j
    fin_cases j <;> simp [CFSG.SeitzReduction.F4Pilot.nodesTU, f4Index] <;> decide +kernel
  rw [← hset, CFSG.RankThree.PartOne.KF4.f4_parabolic_card]
  decide +kernel

private theorem five_ne_zero_of_charP_two
    {Ω : Type} [Field Ω] [CharP Ω 2] : (5 : Ω) ≠ 0 := by
  intro h
  have hdvd : 2 ∣ 5 := (CharP.cast_eq_zero_iff Ω 2 5).mp h
  norm_num at hdvd

private theorem compRank_ge_three_of_ncard_eighteen
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {a : Fin Tag.F4.rank → Ωˣ} (ha5 : ∀ i, a i ^ 5 = 1)
    (i : KernelComponent (rootCharHom a))
    (h18 : (componentRoots (rootCharHom a) i).ncard = 18) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  by_contra hnot
  have h2 : compRank (componentRoots (rootCharHom a) i) ≤ 2 := by omega
  have hNΩ : (5 : Ω) ≠ 0 := five_ne_zero_of_charP_two
  have hap : rootDiagUnit Tag.F4 a ^ 5 = 1 :=
    rootDiagUnit_pow_eq_one_of_coord ha5
  obtain ⟨v, hcases⟩ := f4_rank_le_two_component_shape
    (p := 5) (by norm_num) hNΩ (a := a) hap i h2
  rcases hcases with ⟨j, hj⟩ | hlong | hshort | hb2
  · rw [hj, ncard_image_smul, ncard_pair j] at h18
    omega
  · rw [hlong, ncard_image_smul, ncard_long] at h18
    omega
  · rw [hshort, ncard_image_smul, ncard_short] at h18
    omega
  · rw [hb2, ncard_image_smul, ncard_b2] at h18
    omega

public theorem compRank_eq_three_and_shape_of_ncard_eighteen
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (a : Fin Tag.F4.rank → Ωˣ) (ha5 : ∀ i, a i ^ 5 = 1) (ha1 : a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h18 : (componentRoots (rootCharHom a) i).ncard = 18) :
    compRank (componentRoots (rootCharHom a) i) = 3 ∧
      ((∃ v : WeylGroup Tag.F4,
          componentRoots (rootCharHom a) i =
            (fun α => v • α) '' C3Range.c3RootSet) ∨
        (∃ v : WeylGroup Tag.F4,
          componentRoots (rootCharHom a) i =
            (fun α => v • α) '' CFSG.SeitzReduction.F4Pilot.b3LeviRoots)) := by
  have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) :=
    compRank_ge_three_of_ncard_eighteen ha5 i h18
  have ha1Diag : rootDiagUnit Tag.F4 a ≠ 1 := by
    intro h
    apply ha1
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.F4) (K := Ω)
    simpa [rootDiagUnit_one] using h
  have hNΩ : (5 : Ω) ≠ 0 := five_ne_zero_of_charP_two
  have hap : rootDiagUnit Tag.F4 a ^ 5 = 1 :=
    rootDiagUnit_pow_eq_one_of_coord ha5
  obtain ⟨v, J, hJ, hshape, hrank, _hncard⟩ :=
    f4_rank_ge_three_component_is_levi_odd
      (N := 5) (by norm_num) (by norm_num) hNΩ hap ha1Diag i h3
  refine ⟨hrank, ?_⟩
  rcases hJ with rfl | rfl
  · right
    exact ⟨v, by
      rw [hshape, CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviB3_eq_b3LeviRoots]⟩
  · left
    exact ⟨v, by
      rw [hshape, CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviC3_eq_c3RootSet]⟩

public theorem compRank_le_two_of_ncard_le_eight
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (a : Fin Tag.F4.rank → Ωˣ) (ha5 : ∀ j, a j ^ 5 = 1) (ha1 : a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h8 : (componentRoots (rootCharHom a) i).ncard ≤ 8) :
    compRank (componentRoots (rootCharHom a) i) ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hap : rootDiagUnit .F4 a ^ 5 = 1 := rootDiagUnit_pow_eq_one_of_coord ha5
  have hdiag : rootDiagUnit .F4 a ≠ 1 := by
    intro h0
    apply ha1
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := .F4) (K := Ω)
    simpa [rootDiagUnit_one] using h0
  obtain ⟨_v, _J, _hJ, _hshape, _hrank, hncard⟩ :=
    f4_rank_ge_three_component_is_levi_odd (N := 5)
      (by norm_num) (by norm_num) five_ne_zero_of_charP_two hap hdiag i h3
  omega

end NativeEighteenRootShape

end CFSG.StandardType.F4ExplicitPos.FiveToralKernel
