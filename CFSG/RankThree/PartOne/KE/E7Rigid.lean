module

public import CFSG.RankThree.PartOne.KE.E8Rigid

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

theorem e7_core_normalForm (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]
    {x : adjointGroup .E7 K} (c : adjointGroup .E7 K) (g0 : ModGL .E7 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .E7 L)} (hPψ : Pt ≤ ψ.range)
    (m : Fin Tag.E7.rank) (h₀ : ModGL .E7 L)
    (hh₀ : ∀ Y : SL(2, K), h₀ * simpleRootSL2 .E7 L m
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt)
    (η : MulAut (adjointGroup .E7 K))
    (hη : ∀ k ∈ (Pt.comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype,
      η k = k) :
    ∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      ∀ y : adjointGroup .E7 K, (η y : ModGL .E7 K) =
        ((g : ModGL .E7 K) * rootDiagUnit .E7 a) * (y : ModGL .E7 K) *
          ((g : ModGL .E7 K) * rootDiagUnit .E7 a)⁻¹ := by
  classical
  set K₀ : Subgroup (adjointGroup .E7 K) :=
    (Pt.comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype with hK₀
  set h'' : ModGL .E7 L := (adjEmb .E7 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL(2, K), ∃ y ∈ K₀,
      adjEmb .E7 K L y = h'' * simpleRootSL2 .E7 L m
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    obtain ⟨y', hy'⟩ := hPψ hmem
    refine ⟨(y' : adjointGroup .E7 K), ⟨y', ?_, rfl⟩, ?_⟩
    · change ψ y' ∈ Pt
      rw [hy']
      exact hmem
    · have h3 := hψ y'
      rw [hy'] at h3
      have h4 : adjEmb .E7 K L (c * (y' : adjointGroup .E7 K) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 .E7 L m (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc adjEmb .E7 K L (y' : adjointGroup .E7 K)
          = (adjEmb .E7 K L c)⁻¹ * (adjEmb .E7 K L c * adjEmb .E7 K L (y' : adjointGroup .E7 K) *
              (adjEmb .E7 K L c)⁻¹) * adjEmb .E7 K L c := by group
        _ = _ := by rw [h4]; group
  have hU : ∀ Y : SL(2, K), h'' * simpleRootSL2 .E7 L m (conjGL (1 : GL (Fin 2) L)
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ ∈
        (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := by
    intro Y
    obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one, ← hy]
    exact ⟨(y : ModGL .E7 K), y.2, rfl⟩
  have hmem : ∀ (u : adjointGroup .E7 K) (Y : SL(2, K)),
      baseChangeGL (algebraMap K L) (u : ModGL .E7 K) =
        h'' * simpleRootSL2 .E7 L m (conjGL (1 : GL (Fin 2) L)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ → u ∈ K₀ := by
    intro u Y hu
    obtain ⟨y, hyD, hy⟩ := hKey Y
    rw [conjGL_one, ← hy] at hu
    have hu' : adjEmb .E7 K L u = adjEmb .E7 K L y := by rw [adjEmb_apply, hu]
    rw [adjEmb_injective hu']
    exact hyD
  let Z : Subgroup (MulAut (adjointGroup .E7 K)) :=
    { carrier := {η | ∀ d ∈ K₀, η d = d}
      mul_mem' := fun {a b} ha hb d hd => by
        rw [MulAut.mul_apply, hb d hd, ha d hd]
      one_mem' := fun d _ => rfl
      inv_mem' := fun {a} ha d hd => by
        have := ha d hd
        calc a⁻¹ d = a⁻¹ (a d) := by rw [this]
          _ = d := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
  have hηZ : η ∈ Z := hη
  have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup .E7 K) (Y : SL(2, K)),
      baseChangeGL (algebraMap K L) (u : ModGL .E7 K) =
        h'' * simpleRootSL2 .E7 L m (conjGL (1 : GL (Fin 2) L)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ → η' u = u :=
    fun η' hη'Z u Y hu => hη'Z u (hmem u Y hu)
  have hrig := (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E7
    (Or.inr (Or.inl rfl)) K L m 1 h'' hU Z hZ).1
  obtain ⟨g, a, σ, ε, hexpr⟩ := (ordinary_E_exact_automorphism_normal_form .E7
    (Or.inr (Or.inl rfl)) K).2.2 η
  have hσ : σ = 1 := hrig η hηZ g a σ ε hexpr
  subst hσ
  refine ⟨g, a, fun y => ?_⟩
  rw [hexpr y]
  have hQ : exactQ Tag.E7 K (ε : ℕ) = 1 := rfl
  have hY : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (y : ModGL .E7 K) =
      (y : ModGL .E7 K) := Units.ext (entrywise_id _)
  rw [hQ, hY]
  simp only [mul_assoc, mul_inv_rev, inv_one, mul_one]

end CFSG.RankThree.PartOne.KE
