module
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXDefs
public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularSL3
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixSylow
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.Walter.Defs
public section
namespace CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
open scoped Matrix MatrixGroups
private lemma triD4LineV_smul_eq (x : Fin Tag.D4.rank → ℤ) :
    triD4LineV • x = reflect Tag.D4 0 (reflect Tag.D4 2 (reflect Tag.D4 1
      (reflect Tag.D4 3 x))) := by
  rw [show triD4LineV = simple Tag.D4 0 * simple Tag.D4 2 * simple Tag.D4 1 *
      simple Tag.D4 3 from by
    simp [triD4LineV, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, simple, mul_assoc]]
  simp only [mul_smul, simple_smul]
private def d4LongVec (a c : ℤ) : Fin Tag.D4.rank → ℤ :=
  a • Pi.single 0 1 + a • Pi.single 1 1 + c • Pi.single 2 1 + a • Pi.single 3 1
private lemma triD4LineV_smul_values :
    triD4LineV • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = d4LongVec 0 1 ∧
    triD4LineV • (-Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = d4LongVec 0 (-1) ∧
    triD4LineV • (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = d4LongVec 1 1 ∧
    triD4LineV • (-Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = d4LongVec (-1) (-1) ∧
    triD4LineV • (Pi.single 0 1 + Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = d4LongVec 1 2 ∧
    triD4LineV • (-(Pi.single 0 1 + Pi.single 2 1) : Fin Tag.D4.rank → ℤ) =
      d4LongVec (-1) (-2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [triD4LineV_smul_eq] <;> decide +kernel
private lemma rootChar_d4LongVec (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) (a c : ℤ) :
    rootChar b (d4LongVec a c) = b 0 ^ a * b 1 ^ a * b 2 ^ c * b 3 ^ a := by
  rw [d4LongVec, rootChar_add, rootChar_add, rootChar_add, rootChar_zsmul, rootChar_zsmul,
    rootChar_zsmul, rootChar_zsmul, rootChar_single_D4, rootChar_single_D4,
    rootChar_single_D4, rootChar_single_D4]
private lemma rootChar_neg (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ)
    (v : Fin Tag.D4.rank → ℤ) : rootChar b (-v) = (rootChar b v)⁻¹ := by
  simpa using rootChar_zsmul b (-1) v
private lemma permLattice_triD4LineV_chainRoot (i j : Fin 3) :
    permLattice (τ := Tag.D4) TwistTag.D4.perm
        (triD4LineV • (chainRoot d4ChainA2 i j : Fin Tag.D4.rank → ℤ)) =
      triD4LineV • (chainRoot d4ChainA2 i j : Fin Tag.D4.rank → ℤ) := by
  fin_cases i <;> fin_cases j <;> decide +kernel
private def Dtuple (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) : Fin 3 → Lˣ :=
  ![rootChar b (d4LongVec 1 2), rootChar b (d4LongVec 1 1), 1]
private lemma rootChar_chainRoot_ratio (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ)
    (i j : Fin 3) (hij : i ≠ j) :
    rootChar b (triD4LineV • (chainRoot d4ChainA2 i j : Fin Tag.D4.rank → ℤ)) =
      Dtuple L b i / Dtuple L b j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [chainRootA2_values, chainRootA2_values', triD4LineV_smul_values, Dtuple,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_two] <;>
    simp_all [rootChar_add, rootChar_d4LongVec, rootChar_neg, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm, pow_two]
private lemma diagonal_Dtuple_literal (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) :
    Matrix.diagonal (fun k => (Dtuple L b k : L)) =
      Matrix.diagonal ![(rootChar b ![1, 1, 2, 1] : L), (rootChar b ![1, 1, 1, 1] : L), 1] := by
  change Matrix.diagonal (fun k => (Dtuple L b k : L)) =
    Matrix.diagonal ![(rootChar b (d4LongVec 1 2) : L), (rootChar b (d4LongVec 1 1) : L), 1]
  congr 1 <;> funext k
  fin_cases k <;> rfl
private lemma diagonal_Dtuple_inv_literal (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) :
    Matrix.diagonal (fun k => ((Dtuple L b k)⁻¹ : L)) =
      Matrix.diagonal ![(((rootChar b ![1, 1, 2, 1])⁻¹ : Lˣ) : L),
        (((rootChar b ![1, 1, 1, 1])⁻¹ : Lˣ) : L), 1] := by
  change Matrix.diagonal (fun k => ((Dtuple L b k)⁻¹ : L)) =
    Matrix.diagonal ![(((rootChar b (d4LongVec 1 2))⁻¹ : Lˣ) : L),
      (((rootChar b (d4LongVec 1 1))⁻¹ : Lˣ) : L), 1]
  congr 1 <;> funext k
  fin_cases k <;> simp [Dtuple]
private lemma diagonal_mul_inv (L : Type) [Field L] (d : Fin 3 → Lˣ) :
    Matrix.diagonal (fun k => (d k : L)) * Matrix.diagonal (fun k => ((d k)⁻¹ : L)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  ext k
  simp
private lemma conj_mul (L : Type) [Field L] (d : Fin 3 → Lˣ) (X Y : Matrix (Fin 3) (Fin 3) L) :
    (Matrix.diagonal (fun k => (d k : L)) * X * Matrix.diagonal (fun k => ((d k)⁻¹ : L))) *
      (Matrix.diagonal (fun k => (d k : L)) * Y *
        Matrix.diagonal (fun k => ((d k)⁻¹ : L))) =
    Matrix.diagonal (fun k => (d k : L)) * (X * Y) *
      Matrix.diagonal (fun k => ((d k)⁻¹ : L)) := by
  have h : Matrix.diagonal (fun k => ((d k)⁻¹ : L)) * Matrix.diagonal (fun k => (d k : L)) = 1 := by
    simpa using diagonal_mul_inv L (fun k => (d k)⁻¹)
  calc
    _ = Matrix.diagonal (fun k => (d k : L)) * X *
        (Matrix.diagonal (fun k => ((d k)⁻¹ : L)) * Matrix.diagonal (fun k => (d k : L))) * Y *
        Matrix.diagonal (fun k => ((d k)⁻¹ : L)) := by noncomm_ring
    _ = Matrix.diagonal (fun k => (d k : L)) * (X * Y) *
        Matrix.diagonal (fun k => ((d k)⁻¹ : L)) := by rw [h]; noncomm_ring
private lemma diagonal_conj_single (L : Type) [Field L] (d : Fin 3 → Lˣ)
    (i j : Fin 3) (a : L) :
    Matrix.diagonal (fun k => (d k : L)) * (1 + Matrix.single i j a) *
      Matrix.diagonal (fun k => ((d k)⁻¹ : L)) =
    1 + Matrix.single i j (((d i / d j : Lˣ) : L) * a) := by
  ext i' j'
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> by_cases h3 : i' = j'
  all_goals simp_all [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Units.val_div_eq_div_val, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
private lemma map_eq_self_of_sq_one (L : Type) [Field L] (Fr : L →+* L) {κ : L}
    (hκ : κ * κ = 1) : Fr κ = κ := by
  have h : (κ - 1) * (κ + 1) = 0 := by linear_combination hκ
  rcases mul_eq_zero.1 h with h1 | h1
  · have h2 : κ = 1 := by linear_combination h1
    rw [h2, map_one]
  · have h2 : κ = -1 := by linear_combination h1
    rw [h2, map_neg, map_one]
private lemma map_sl_eq_single (L : Type) [Field L] (Fr : L →+* L)
    (i j : Fin 3) (a : L) (X : Matrix.SpecialLinearGroup (Fin 3) L)
    (hX : (X : Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single i j a) :
    ((Matrix.SpecialLinearGroup.map Fr X : Matrix.SpecialLinearGroup (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single i j (Fr a) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, hX]
  ext i' j'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, map_one, map_zero]
  split_ifs with h <;> simp_all
theorem triD4Line_entrywise_d4A2Qv
    (L : Type) [Field L] (Fr : L →+* L) (q : ModGL Tag.D4 L) (hq : q ∈ d4A2Qv L triD4LineV) :
    ∃ hq' : Units.map (entrywiseHom Fr) q ∈ d4A2Qv L triD4LineV,
      d4A2QvEquiv (K := L) triD4LineV ⟨Units.map (entrywiseHom Fr) q, hq'⟩ =
        Matrix.SpecialLinearGroup.map Fr (d4A2QvEquiv (K := L) triD4LineV ⟨q, hq⟩) := by
  classical
  let S : Set (ModGL Tag.D4 L) :=
    {g | ∃ α ∈ (fun β => triD4LineV • β) '' d4A2Sigma, ∃ c : L,
      pinnedX Tag.D4 L α c = g}
  have hQeq : d4A2Qv L triD4LineV = Subgroup.closure S := by
    rw [d4A2Qv_eq_rootSpan, rootSpan_eq_closure]
  have hmem : ∀ g ∈ d4A2Qv L triD4LineV,
      Units.map (entrywiseHom Fr) g ∈ d4A2Qv L triD4LineV := by
    have hgen : ∀ x ∈ S, Units.map (entrywiseHom Fr) x ∈ d4A2Qv L triD4LineV := by
      intro x hx
      obtain ⟨α, hα, c, rfl⟩ := hx
      obtain ⟨β, hβ, rfl⟩ := hα
      rw [show Units.map (entrywiseHom Fr) (pinnedX Tag.D4 L (triD4LineV • β) c) =
          pinnedX Tag.D4 L (triD4LineV • β) (Fr c) from
        Units.ext (entrywise_pinnedX Fr (triD4LineV • β) c)]
      exact pinnedX_mem_d4A2Qv triD4LineV hβ (Fr c)
    intro g hg
    have hg' : g ∈ Subgroup.closure S := by rwa [← hQeq]
    exact (Subgroup.closure_le (K := (d4A2Qv L triD4LineV).comap
      (Units.map (entrywiseHom Fr)))).2 hgen hg'
  let FrStar : d4A2Qv L triD4LineV →* d4A2Qv L triD4LineV :=
    { toFun := fun g => ⟨Units.map (entrywiseHom Fr) g, hmem g g.2⟩
      map_one' := Subtype.ext (map_one (f := Units.map (entrywiseHom Fr)))
      map_mul' := fun a b => Subtype.ext (map_mul (Units.map (entrywiseHom Fr))
        (a : ModGL Tag.D4 L) (b : ModGL Tag.D4 L)) }
  let G : d4A2Qv L triD4LineV →* Matrix.SpecialLinearGroup (Fin 3) L :=
    (d4A2QvEquiv (K := L) triD4LineV).toMonoidHom.comp FrStar
  let F : d4A2Qv L triD4LineV →* Matrix.SpecialLinearGroup (Fin 3) L :=
    (Matrix.SpecialLinearGroup.map Fr).comp
      (d4A2QvEquiv (K := L) triD4LineV).toMonoidHom
  have hmain : ∀ (g : ModGL Tag.D4 L), g ∈ Subgroup.closure S →
      ∀ hgQ : g ∈ d4A2Qv L triD4LineV, G ⟨g, hgQ⟩ = F ⟨g, hgQ⟩ := by
    intro g hgcl
    induction hgcl using Subgroup.closure_induction with
    | mem x hx =>
        intro hxQ
        obtain ⟨α, hα, c, rfl⟩ := hx
        obtain ⟨β, hβ, rfl⟩ := hα
        obtain ⟨i, j, hij, hβeq⟩ :=
          exists_chainRootA2_of_mem (by rw [parabolicRoots_d4SuppA2]; exact hβ)
        subst β
        obtain ⟨κ, hκ, hΨ⟩ := exists_d4A2QvEquiv_pinnedX (Ω := L) triD4LineV hij
        have hgen : Units.map (entrywiseHom Fr)
            (pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c) =
            pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) (Fr c) :=
          Units.ext (entrywise_pinnedX Fr _ c)
        change d4A2QvEquiv (K := L) triD4LineV
            ⟨Units.map (entrywiseHom Fr)
              (pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c), hmem _ hxQ⟩ =
          Matrix.SpecialLinearGroup.map Fr (d4A2QvEquiv (K := L) triD4LineV
            ⟨pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c, hxQ⟩)
        rw [show (⟨Units.map (entrywiseHom Fr)
              (pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c),
              hmem _ hxQ⟩ : d4A2Qv L triD4LineV) =
            ⟨pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) (Fr c),
              pinnedX_mem_d4A2Qv triD4LineV (chainRootA2_mem_d4A2Sigma hij) (Fr c)⟩
          from Subtype.ext hgen]
        apply Subtype.ext
        rw [hΨ (Fr c), map_sl_eq_single L Fr i j (κ * c) _ (hΨ c), map_mul,
          map_eq_self_of_sq_one L Fr hκ]
    | one =>
        intro h1Q
        have hone : (⟨1, h1Q⟩ : d4A2Qv L triD4LineV) = 1 := Subtype.ext rfl
        rw [hone, map_one, map_one]
    | mul x y hx hy ihx ihy =>
        intro hxyQ
        have hxQ : x ∈ d4A2Qv L triD4LineV := by rwa [hQeq]
        have hyQ : y ∈ d4A2Qv L triD4LineV := by rwa [hQeq]
        rw [show (⟨x * y, hxyQ⟩ : d4A2Qv L triD4LineV) =
            (⟨x, hxQ⟩ : d4A2Qv L triD4LineV) * ⟨y, hyQ⟩ from Subtype.ext rfl,
          map_mul, map_mul, ihx hxQ, ihy hyQ]
    | inv x hx ih =>
        intro hxQ
        have hxQ' : x ∈ d4A2Qv L triD4LineV := by rwa [hQeq]
        rw [show (⟨x⁻¹, hxQ⟩ : d4A2Qv L triD4LineV) =
            ((⟨x, hxQ'⟩ : d4A2Qv L triD4LineV))⁻¹ from Subtype.ext rfl,
          map_inv, map_inv, ih hxQ']
  have hqcl : q ∈ Subgroup.closure S := by rwa [hQeq] at hq
  exact ⟨hmem q hq, hmain q hqcl hq⟩
theorem triD4Line_twistHom_eq_entrywise
    (L : Type) [Field L] [CharP L 2] (Fr : L →+* L) (q : ModGL Tag.D4 L)
    (hq : q ∈ d4A2Qv L triD4LineV) :
    twistHom TwistTag.D4 L Fr q = Units.map (entrywiseHom Fr) q := by
  classical
  let S : Set (ModGL Tag.D4 L) :=
    {g | ∃ α ∈ (fun β => triD4LineV • β) '' d4A2Sigma, ∃ c : L,
      pinnedX Tag.D4 L α c = g}
  have hQeq : d4A2Qv L triD4LineV = Subgroup.closure S := by
    rw [d4A2Qv_eq_rootSpan, rootSpan_eq_closure]
  have hmain : ∀ (g : ModGL Tag.D4 L), g ∈ Subgroup.closure S →
      twistHom TwistTag.D4 L Fr g = Units.map (entrywiseHom Fr) g := by
    intro g hgcl
    induction hgcl using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨α, hα, c, rfl⟩ := hx
        obtain ⟨β, hβ, rfl⟩ := hα
        obtain ⟨i, j, hij, hβeq⟩ :=
          exists_chainRootA2_of_mem (by rw [parabolicRoots_d4SuppA2]; exact hβ)
        subst β
        have hroot : IsRoot TwistTag.D4.tag
            (triD4LineV • chainRoot d4ChainA2 i j) :=
          isRoot_of_mem_image_d4A2Sigma ⟨chainRoot d4ChainA2 i j,
            chainRootA2_mem_d4A2Sigma hij, rfl⟩
        rw [show pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c =
            pinnedX TwistTag.D4.tag L (triD4LineV • chainRoot d4ChainA2 i j) c from rfl,
          twistHom_D4_pinnedX_of_fixed Fr hroot (permLattice_triD4LineV_chainRoot i j) c]
        exact (Units.ext (entrywise_pinnedX Fr (triD4LineV • chainRoot d4ChainA2 i j) c)).symm
    | one =>
        have h1 : twistHom TwistTag.D4 L Fr (1 : ModGL Tag.D4 L) = 1 :=
          map_one (twistHom TwistTag.D4 L Fr)
        have h2 : Units.map (entrywiseHom Fr) (1 : ModGL Tag.D4 L) = 1 :=
          map_one (Units.map (entrywiseHom Fr))
        rw [h1, h2]
        rfl
    | mul x y hx hy ihx ihy =>
        have h1 : twistHom TwistTag.D4 L Fr (x * y : ModGL Tag.D4 L) =
            twistHom TwistTag.D4 L Fr (x : ModGL Tag.D4 L) *
              twistHom TwistTag.D4 L Fr (y : ModGL Tag.D4 L) :=
          map_mul (twistHom TwistTag.D4 L Fr) (x : ModGL Tag.D4 L) (y : ModGL Tag.D4 L)
        have h2 : Units.map (entrywiseHom Fr) (x * y) =
            Units.map (entrywiseHom Fr) x * Units.map (entrywiseHom Fr) y :=
          map_mul (Units.map (entrywiseHom Fr)) x y
        rw [h1, h2, ihx, ihy]
        rfl
    | inv x hx ih =>
        have h1 : twistHom TwistTag.D4 L Fr (x⁻¹ : ModGL Tag.D4 L) =
            (twistHom TwistTag.D4 L Fr (x : ModGL Tag.D4 L))⁻¹ :=
          map_inv (twistHom TwistTag.D4 L Fr) (x : ModGL Tag.D4 L)
        have h2 : Units.map (entrywiseHom Fr) (x⁻¹) =
            (Units.map (entrywiseHom Fr) x)⁻¹ := map_inv (Units.map (entrywiseHom Fr)) x
        rw [h1, h2, ih]
        rfl
  have hqcl : q ∈ Subgroup.closure S := by rwa [hQeq] at hq
  exact hmain q hqcl
theorem triD4Line_d4A2QvEquiv_conj
    (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) (q : ModGL Tag.D4 L)
    (hq : q ∈ d4A2Qv L triD4LineV) :
    ∃ hq' : rootDiagUnit Tag.D4 b * q * (rootDiagUnit Tag.D4 b)⁻¹ ∈ d4A2Qv L triD4LineV,
      ((d4A2QvEquiv (K := L) triD4LineV ⟨_, hq'⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
          Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal ![(rootChar b ![1, 1, 2, 1] : L), (rootChar b ![1, 1, 1, 1] : L), 1] *
          (d4A2QvEquiv (K := L) triD4LineV ⟨q, hq⟩ : Matrix (Fin 3) (Fin 3) L) *
          Matrix.diagonal ![(((rootChar b ![1, 1, 2, 1])⁻¹ : Lˣ) : L),
            (((rootChar b ![1, 1, 1, 1])⁻¹ : Lˣ) : L), 1] := by
  classical
  let S : Set (ModGL Tag.D4 L) :=
    {g | ∃ α ∈ (fun β => triD4LineV • β) '' d4A2Sigma, ∃ c : L,
      pinnedX Tag.D4 L α c = g}
  have hQeq : d4A2Qv L triD4LineV = Subgroup.closure S := by
    rw [d4A2Qv_eq_rootSpan, rootSpan_eq_closure]
  have base : ∀ (i j : Fin 3) (hij : i ≠ j) (c : L)
      (hQ : pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c ∈
        d4A2Qv L triD4LineV),
      ∃ hq' : rootDiagUnit Tag.D4 b *
          pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c *
          (rootDiagUnit Tag.D4 b)⁻¹ ∈ d4A2Qv L triD4LineV,
        ((d4A2QvEquiv (K := L) triD4LineV ⟨_, hq'⟩ :
            Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
          Matrix.diagonal (fun k => (Dtuple L b k : L)) *
            (d4A2QvEquiv (K := L) triD4LineV
              ⟨pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) c, hQ⟩ :
                Matrix (Fin 3) (Fin 3) L) *
            Matrix.diagonal (fun k => ((Dtuple L b k)⁻¹ : L)) := by
    intro i j hij c hQ
    obtain ⟨κ, hκ, hΨ⟩ := exists_d4A2QvEquiv_pinnedX (Ω := L) triD4LineV hij
    have hroot : IsRoot Tag.D4 (triD4LineV • chainRoot d4ChainA2 i j) :=
      isRoot_of_mem_image_d4A2Sigma ⟨chainRoot d4ChainA2 i j,
        chainRootA2_mem_d4A2Sigma hij, rfl⟩
    have hconj := rootDiagUnit_conj_pinnedX b hroot c
    have hmem' : rootDiagUnit Tag.D4 b * pinnedX Tag.D4 L
        (triD4LineV • chainRoot d4ChainA2 i j) c * (rootDiagUnit Tag.D4 b)⁻¹ ∈
        d4A2Qv L triD4LineV := by
      rw [hconj]
      exact pinnedX_mem_d4A2Qv triD4LineV (chainRootA2_mem_d4A2Sigma hij) _
    refine ⟨hmem', ?_⟩
    rw [show (⟨rootDiagUnit Tag.D4 b * pinnedX Tag.D4 L
          (triD4LineV • chainRoot d4ChainA2 i j) c * (rootDiagUnit Tag.D4 b)⁻¹,
          hmem'⟩ : d4A2Qv L triD4LineV) =
        ⟨pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j)
          ((rootChar b (triD4LineV • chainRoot d4ChainA2 i j) : L) * c),
          pinnedX_mem_d4A2Qv triD4LineV (chainRootA2_mem_d4A2Sigma hij) _⟩ from
      Subtype.ext hconj,
      hΨ ((rootChar b (triD4LineV • chainRoot d4ChainA2 i j) : L) * c),
      hΨ c, diagonal_conj_single L (Dtuple L b) i j (κ * c)]
    congr 1
    rw [rootChar_chainRoot_ratio L b i j hij]
    ring
  have hmain : ∀ (g : ModGL Tag.D4 L), g ∈ Subgroup.closure S →
      ∀ hgQ : g ∈ d4A2Qv L triD4LineV,
        ∃ hg' : rootDiagUnit Tag.D4 b * g * (rootDiagUnit Tag.D4 b)⁻¹ ∈
          d4A2Qv L triD4LineV,
          ((d4A2QvEquiv (K := L) triD4LineV ⟨_, hg'⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
              Matrix (Fin 3) (Fin 3) L) =
            Matrix.diagonal (fun k => (Dtuple L b k : L)) *
              (d4A2QvEquiv (K := L) triD4LineV ⟨g, hgQ⟩ : Matrix (Fin 3) (Fin 3) L) *
              Matrix.diagonal (fun k => ((Dtuple L b k)⁻¹ : L)) := by
    intro g hgcl
    induction hgcl using Subgroup.closure_induction'' with
    | mem x hx =>
        intro hxQ
        obtain ⟨α, hα, c, rfl⟩ := hx
        obtain ⟨β, hβ, rfl⟩ := hα
        obtain ⟨i, j, hij, hβeq⟩ :=
          exists_chainRootA2_of_mem (by rw [parabolicRoots_d4SuppA2]; exact hβ)
        subst β
        exact base i j hij c hxQ
    | inv_mem x hx =>
        intro hxQ
        obtain ⟨α, hα, c, rfl⟩ := hx
        obtain ⟨β, hβ, rfl⟩ := hα
        obtain ⟨i, j, hij, hβeq⟩ :=
          exists_chainRootA2_of_mem (by rw [parabolicRoots_d4SuppA2]; exact hβ)
        subst β
        have hxQ' : pinnedX Tag.D4 L (triD4LineV • chainRoot d4ChainA2 i j) (-c) ∈
            d4A2Qv L triD4LineV := by
          rw [← pinnedX_neg]
          exact hxQ
        simpa only [pinnedX_neg] using base i j hij (-c) hxQ'
    | one =>
        intro h1Q
        have hgrp : rootDiagUnit Tag.D4 b * (1 : ModGL Tag.D4 L) *
            (rootDiagUnit Tag.D4 b)⁻¹ = 1 := by group
        have hmem0 : rootDiagUnit Tag.D4 b * (1 : ModGL Tag.D4 L) *
            (rootDiagUnit Tag.D4 b)⁻¹ ∈ d4A2Qv L triD4LineV := by
          rw [hgrp]
          exact one_mem _
        refine ⟨hmem0, ?_⟩
        have h1' : (⟨rootDiagUnit Tag.D4 b * (1 : ModGL Tag.D4 L) *
            (rootDiagUnit Tag.D4 b)⁻¹, hmem0⟩ : d4A2Qv L triD4LineV) = 1 :=
          Subtype.ext hgrp
        have hone : (⟨1, h1Q⟩ : d4A2Qv L triD4LineV) = 1 := Subtype.ext rfl
        rw [h1', hone, map_one]
        change ((1 : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
          Matrix.diagonal (fun k => (Dtuple L b k : L)) *
            ((1 : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
            Matrix.diagonal (fun k => ((Dtuple L b k)⁻¹ : L))
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, diagonal_mul_inv]
    | mul x y hx hy ihx ihy =>
        intro hxyQ
        have hxQ : x ∈ d4A2Qv L triD4LineV := by rwa [hQeq]
        have hyQ : y ∈ d4A2Qv L triD4LineV := by rwa [hQeq]
        obtain ⟨hx', hx'eq⟩ := ihx hxQ
        obtain ⟨hy', hy'eq⟩ := ihy hyQ
        have hconj : rootDiagUnit Tag.D4 b * (x * y) * (rootDiagUnit Tag.D4 b)⁻¹ =
            (rootDiagUnit Tag.D4 b * x * (rootDiagUnit Tag.D4 b)⁻¹) *
              (rootDiagUnit Tag.D4 b * y * (rootDiagUnit Tag.D4 b)⁻¹) := by group
        have hmem' : rootDiagUnit Tag.D4 b * (x * y) * (rootDiagUnit Tag.D4 b)⁻¹ ∈
            d4A2Qv L triD4LineV := by
          rw [hconj]
          exact mul_mem hx' hy'
        refine ⟨hmem', ?_⟩
        have hsub : (⟨rootDiagUnit Tag.D4 b * (x * y) * (rootDiagUnit Tag.D4 b)⁻¹,
            hmem'⟩ : d4A2Qv L triD4LineV) =
            (⟨rootDiagUnit Tag.D4 b * x * (rootDiagUnit Tag.D4 b)⁻¹, hx'⟩ :
              d4A2Qv L triD4LineV) *
            ⟨rootDiagUnit Tag.D4 b * y * (rootDiagUnit Tag.D4 b)⁻¹, hy'⟩ :=
          Subtype.ext hconj
        have hprod : ((d4A2QvEquiv (K := L) triD4LineV ⟨x * y, hxyQ⟩ :
              Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
            ((d4A2QvEquiv (K := L) triD4LineV ⟨x, hxQ⟩ :
              Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
            ((d4A2QvEquiv (K := L) triD4LineV ⟨y, hyQ⟩ :
              Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
          rw [show (⟨x * y, hxyQ⟩ : d4A2Qv L triD4LineV) =
              (⟨x, hxQ⟩ : d4A2Qv L triD4LineV) * ⟨y, hyQ⟩ from Subtype.ext rfl]
          rw [map_mul]
          rfl
        rw [hsub, map_mul]
        simp only [Matrix.SpecialLinearGroup.coe_mul]
        rw [hx'eq, hy'eq, hprod]
        exact conj_mul L (Dtuple L b) _ _
  have hqcl : q ∈ Subgroup.closure S := by rwa [hQeq] at hq
  obtain ⟨hq', heq⟩ := hmain q hqcl hq
  refine ⟨hq', ?_⟩
  rw [heq, diagonal_Dtuple_literal, diagonal_Dtuple_inv_literal]

end CFSG.StandardType
