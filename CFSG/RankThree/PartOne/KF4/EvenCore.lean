module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4DescendedRootCore
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartOne.KF4.CoreStep
public import CFSG.RankThree.PartOne.KF4.B2Twist
public import CFSG.RankThree.PartOne.KE.CommutatorFactor

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KE
open scoped Pointwise commutatorElement


theorem exists_even_descended_root (K : Type) [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (i : Fin Tag.F4.rank) (h'' : ModGL .F4 L)
    (hh''C : h'' ∈ adjointGroup .F4 L) (E : Subgroup (adjointGroup .F4 K))
    (hKey : ∀ Y : SL2 K, ∃ y ∈ E, adjEmb .F4 K L y = h'' * simpleRootSL2 .F4 L i
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹) :
    ∃ (M : Type) (_ : Field M) (_ : Finite M) (ι : K →+* M) (g : ModGL .F4 M),
      g ∈ adjointGroup .F4 M ∧ ∃ R₀ : Subgroup (adjointGroup .F4 K), R₀ ≤ E ∧
        (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
            (MulAut.conj g).toMonoidHom =
          ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL 1)).map
            (rootSL2 .F4 M (Pi.single i 1)) := by
  classical
  set X : Subgroup (ModGL .F4 L) :=
    (((simpleRootSL2 .F4 L i).comp (Matrix.SpecialLinearGroup.map (algebraMap K L))).range).map
      (MulAut.conj h'').toMonoidHom with hX
  have hXmem : ∀ z, z ∈ X ↔ ∃ Y : SL2 K,
      z = h'' * simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
        h''⁻¹ := by
    intro z
    constructor
    · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
      exact ⟨Y, by simp [MulAut.conj_apply]⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨_, ⟨Y, rfl⟩, by simp [MulAut.conj_apply]⟩
  set R₀ : Subgroup (adjointGroup .F4 K) := X.comap (adjEmb .F4 K L) with hR₀def
  have hR₀E : R₀ ≤ E := by
    intro u hu
    obtain ⟨Y, hY⟩ := (hXmem _).1 hu
    obtain ⟨y, hyE, hy⟩ := hKey Y
    rw [adjEmb_injective (hy.trans hY.symm)] at hyE
    exact hyE
  obtain ⟨M, hMfin, ι, hι, g', hg'C, hg'⟩ := exists_finite_subfield_descent K L (inv_mem hh''C)
  have hbc : ∀ u : adjointGroup .F4 K,
      baseChangeGL M.subtype (baseChangeGL ι (u : ModGL .F4 K)) = adjEmb .F4 K L u := by
    intro u
    rw [baseChangeGL_baseChangeGL, hι]
    rfl
  have hSLmap : ∀ Y : SL2 K, Matrix.SpecialLinearGroup.map M.subtype
      (Matrix.SpecialLinearGroup.map ι Y) = Matrix.SpecialLinearGroup.map (algebraMap K L) Y := by
    intro Y
    apply Subtype.ext
    ext a b
    have := congrArg (fun f : K →+* L => f ((Y : Matrix (Fin 2) (Fin 2) K) a b)) hι
    simpa using this
  have hrho : ∀ A : SL2 M, baseChangeGL M.subtype (rootSL2 .F4 M (Pi.single i 1) A) =
      simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map M.subtype A) := fun A => by
    rw [rootSL2_single_eq_simple, baseChangeGL_simpleRootSL2]
  refine ⟨M, inferInstance, hMfin, ι, g', hg'C, R₀, hR₀E, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨Y, hY⟩ := (hXmem _).1 hu
    refine ⟨_, ⟨_, ⟨Y, rfl⟩, rfl⟩, ?_⟩
    apply baseChangeGL_injective M.subtype
    rw [hrho, CFSG.RankThree.Classical.conjSL_one, hSLmap]
    change _ = baseChangeGL M.subtype (g' * baseChangeGL ι (u : ModGL .F4 K) * g'⁻¹)
    rw [map_mul, map_mul, map_inv, hg', hbc, hY]
    group
  · rintro ⟨_, ⟨_, ⟨Y, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨y, hyE, hy⟩ := hKey Y
    have hyR₀ : y ∈ R₀ := (hXmem _).2 ⟨Y, hy⟩
    refine ⟨_, ⟨y, hyR₀, rfl⟩, ?_⟩
    apply baseChangeGL_injective M.subtype
    rw [hrho, CFSG.RankThree.Classical.conjSL_one, hSLmap]
    change baseChangeGL M.subtype (g' * baseChangeGL ι (y : ModGL .F4 K) * g'⁻¹) = _
    rw [map_mul, map_mul, map_inv, hg', hbc, hy]
    group

theorem f4_even_core_odd_of_embedding (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .F4 K))}
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    {x : adjointGroup .F4 K} (c : adjointGroup .F4 K) (g0 : ModGL .F4 L)
    (hg0C : g0 ∈ adjointGroup .F4 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L)
    (hψinj : Function.Injective ψ)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .F4 L)} (hPq : CFSG.IsQuasisimple Pt)
    (hcomm : ⁅ψ.range, ψ.range⁆ = Pt) (i : Fin Tag.F4.rank) (h₀ : ModGL .F4 L)
    (hh₀C : h₀ ∈ adjointGroup .F4 L)
    (hroot : (∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) ∨
      ((∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ ψ.range) ∧
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
            Subgroup.centralizer ((⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
              Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
                Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
          (Subgroup.center (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))).map
            (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))).subtype))
    (hsolv : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V)) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .F4 K))} :
        Set (MulAut (adjointGroup .F4 K)))))) := by
  classical
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  have hRL : CFSG.layer (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) =
        ⊤ := layer_eq_top_of_isQuasisimple hq
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
      Subgroup.centralizer ((⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
          Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)))) :=
    odd_card_inf_centralizer_derived hsolv
  obtain ⟨h'', hh''⟩ : ∃ h'' : ModGL .F4 L, h'' = (adjEmb .F4 K L c)⁻¹ * g0 * h₀ := ⟨_, rfl⟩
  have hh''C : h'' ∈ adjointGroup .F4 L := by
    rw [hh'']
    exact mul_mem (mul_mem (inv_mem (adjEmb_mem c)) hg0C) hh₀C
  have hpull : ∀ (T : Subgroup (ModGL .F4 L)), T ≤ ψ.range → (∀ Y : SL2 K, h₀ *
      simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ T) →
      ∀ Y : SL2 K, ∃ y' : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        ψ y' = h₀ * simpleRootSL2 .F4 L i
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∧
        adjEmb .F4 K L (y' : adjointGroup .F4 K) = h'' * simpleRootSL2 .F4 L i
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro T hT hh Y
    obtain ⟨y', hy'ψ⟩ := hT (hh Y)
    refine ⟨y', hy'ψ, ?_⟩
    have h3 := hψ y'
    rw [hy'ψ] at h3
    have h4 : adjEmb .F4 K L (c * (y' : adjointGroup .F4 K) * c⁻¹) =
        g0 * (h₀ * simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
          h₀⁻¹) * g0⁻¹ := by
      rw [h3]
      group
    rw [map_mul, map_mul, map_inv] at h4
    rw [hh'']
    calc adjEmb .F4 K L (y' : adjointGroup .F4 K)
        = (adjEmb .F4 K L c)⁻¹ * (adjEmb .F4 K L c * adjEmb .F4 K L (y' : adjointGroup .F4 K) *
            (adjEmb .F4 K L c)⁻¹) * adjEmb .F4 K L c := by group
      _ = _ := by rw [h4]; group
  have hmapB := map_subtype_theta_centralizer hp B (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)
  rcases hroot with hPt | ⟨hψr, hZ⟩
  ·
    have hle : Pt ≤ ψ.range := by
      rw [← hcomm, Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)),
        adjEmb .F4 K L y = h'' * simpleRootSL2 .F4 L i
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
      intro Y
      obtain ⟨y', hy'ψ, hy'⟩ := hpull Pt hle hPt Y
      have hmem := hPt Y
      rw [← h2] at hmem
      obtain ⟨y'', hy'', hy''ψ⟩ := hmem
      have hyy : y'' = y' := hψinj (hy''ψ.trans hy'ψ.symm)
      refine ⟨(y' : adjointGroup .F4 K), ?_, hy'⟩
      rw [← h1]
      exact ⟨y', hyy ▸ hy'', rfl⟩
    obtain ⟨M, _, _, ι, g', hg'C, R₀, hR₀R, hRg⟩ :=
      exists_even_descended_root K L i h'' hh''C
        (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K))
        hKey
    have hS := even_F4_descended_root_layer_centralizer_local_core_odd hf K hK hp B hB x hRL hodd
      R₀ hR₀R M ι hg'C (IsRoot.basis i) 1 hRg
    rw [← hmapB, Subgroup.card_map_of_injective B.subtype_injective]
    exact hS
  ·
    have hKeyD : ∀ Y : SL2 K, ∃ y ∈ Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        adjEmb .F4 K L y = h'' * simpleRootSL2 .F4 L i
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
      intro Y
      obtain ⟨y', -, hy'⟩ := hpull ψ.range le_rfl hψr Y
      exact ⟨y', y'.2, hy'⟩
    obtain ⟨M, _, _, ι, g', hg'C, R₀, hR₀D, hRg⟩ :=
      exists_even_descended_root K L i h'' hh''C
        (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))) hKeyD
    have hS := even_F4_central_derived_layer_and_descended_root_local_core_odd hf K hK hp B hB x
      hRL hZ hodd R₀ hR₀D M ι hg'C (IsRoot.basis i) 1 hRg
    rw [← hmapB, Subgroup.card_map_of_injective B.subtype_injective]
    exact hS

theorem f4_even_core_step (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (L : Type) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] : F4CoreStep K p L := by
  intro B hB x c g0 hg0C ψ hψinj hψ Pt hPq hcomm i _ h₀ hh₀C hh₀ hsolv
  exact f4_even_core_odd_of_embedding K hf hK L hp hB c g0 hg0C ψ hψinj hψ hPq hcomm i h₀ hh₀C
    (Or.inl hh₀) hsolv

end CFSG.RankThree.PartOne.KF4
