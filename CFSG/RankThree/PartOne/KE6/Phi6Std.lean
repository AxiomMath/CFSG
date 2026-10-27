module

public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.PartOne.KE6.Phi6Frob

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (adjEmb adjEmb_apply)

variable {K : Type} [Field K] {Ω : Type} [Field Ω]

theorem entrywise_canonicalRep' (ς : Ω →+* Ω) (hς : Function.Bijective ς)
    (w : WeylGroup Tag.E6) :
    Units.map (entrywiseHom ς) (canonicalRep (coxeterSystem Tag.E6) Ω w) =
      canonicalRep (coxeterSystem Tag.E6) Ω w :=
  entrywise_canonicalRep (RingEquiv.ofBijective ς hς) w

theorem entrywise_mem_adjointGroup' (ς : Ω →+* Ω) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ adjointGroup Tag.E6 Ω) : Units.map (entrywiseHom ς) x ∈ adjointGroup Tag.E6 Ω := by
  rw [units_map_entrywiseHom_eq_baseChangeGL]
  exact baseChangeGL_mem_adjointGroup ς hx

theorem diagL_mem_adjointGroup [Algebra K Ω] [IsAlgClosed Ω] (a : Fin Tag.E6.rank → Kˣ) :
    diagL Ω a ∈ adjointGroup Tag.E6 Ω :=
  (exceptional_Lang_adjoint_diagonal_lift Tag.E6 Ω _).1

theorem phi6_frame_transport [Algebra K Ω] [IsAlgClosed Ω] (ς : Ω →+* Ω) {ε : ℕ}
    (hε : ε < 2) {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ)
    (η : MulAut (adjointGroup Tag.E6 K))
    (hη : ∀ h : adjointGroup Tag.E6 K, adjEmb Tag.E6 K Ω (η h) =
      (adjEmb Tag.E6 K Ω g * diagL Ω a * (diagQ Ω) ^ ε) *
        Units.map (entrywiseHom ς) (adjEmb Tag.E6 K Ω h) *
      (adjEmb Tag.E6 K Ω g * diagL Ω a * (diagQ Ω) ^ ε)⁻¹) :
    ∃ G₃ : ModGL Tag.E6 Ω, G₃ ∈ adjointGroup Tag.E6 Ω ∧
      G₃ * (diagQ Ω) ^ ε = g0⁻¹ * (adjEmb Tag.E6 K Ω g * diagL Ω a * (diagQ Ω) ^ ε) *
        Units.map (entrywiseHom ς) g0 ∧
      ∀ d : adjointGroup Tag.E6 K, g0⁻¹ * adjEmb Tag.E6 K Ω (η d) * g0 =
        (G₃ * (diagQ Ω) ^ ε) *
          Units.map (entrywiseHom ς) (g0⁻¹ * adjEmb Tag.E6 K Ω d * g0) *
        (G₃ * (diagQ Ω) ^ ε)⁻¹ := by
  classical
  set Qε : ModGL Tag.E6 Ω := (diagQ Ω) ^ ε with hQε
  set Nι : ModGL Tag.E6 Ω := adjEmb Tag.E6 K Ω g * diagL Ω a * Qε with hNι
  have hQG : ∀ x ∈ adjointGroup Tag.E6 Ω, Qε * x * Qε⁻¹ ∈ adjointGroup Tag.E6 Ω := by
    intro x hx
    have : ε = 0 ∨ ε = 1 := by omega
    rcases this with rfl | rfl
    · rw [hQε, pow_zero]
      simpa using hx
    · rw [hQε, pow_one]
      exact CFSG.LieType.Chevalley.E6GraphLevi.diagramMap_conj_mem_adjointGroup' hx
  refine ⟨g0⁻¹ * adjEmb Tag.E6 K Ω g * diagL Ω a *
    (Qε * Units.map (entrywiseHom ς) g0 * Qε⁻¹), ?_, ?_, fun d => ?_⟩
  · exact mul_mem (mul_mem (mul_mem (inv_mem hg0) (CFSG.RankThree.PartOne.KE.adjEmb_mem g))
      (diagL_mem_adjointGroup a)) (hQG _ (entrywise_mem_adjointGroup' ς hg0))
  · rw [hNι]
    group
  · have hΦ : Units.map (entrywiseHom ς) (adjEmb Tag.E6 K Ω d) =
        Units.map (entrywiseHom ς) g0 * Units.map (entrywiseHom ς) (g0⁻¹ * adjEmb Tag.E6 K Ω d * g0) *
          (Units.map (entrywiseHom ς) g0)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have e1 : g0⁻¹ * adjEmb Tag.E6 K Ω g * diagL Ω a *
        (Qε * Units.map (entrywiseHom ς) g0 * Qε⁻¹) * Qε =
        g0⁻¹ * Nι * Units.map (entrywiseHom ς) g0 := by
      rw [hNι]
      group
    rw [e1, hη d, hΦ]
    group

theorem phi6_std_position (ς : Ω →+* Ω) (hς : Function.Bijective ς)
    (w : WeylGroup Tag.E6) {Qε G₃ : ModGL Tag.E6 Ω}
    (hQε : ∀ g ∈ adjointGroup Tag.E6 Ω, Qε * g * Qε⁻¹ ∈ adjointGroup Tag.E6 Ω)
    (hG₃ : G₃ ∈ adjointGroup Tag.E6 Ω) :
    ∃ G₃' : ModGL Tag.E6 Ω, G₃' ∈ adjointGroup Tag.E6 Ω ∧
      G₃' * Qε = canonicalRep (coxeterSystem Tag.E6) Ω w * (G₃ * Qε) *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∧
      ∀ u : ModGL Tag.E6 Ω, (G₃ * Qε) * Units.map (entrywiseHom ς) u * (G₃ * Qε)⁻¹ = u →
        (G₃' * Qε) * Units.map (entrywiseHom ς) (canonicalRep (coxeterSystem Tag.E6) Ω w * u *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) * (G₃' * Qε)⁻¹ =
          canonicalRep (coxeterSystem Tag.E6) Ω w * u *
            (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ := by
  classical
  set n : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hnA : n ∈ adjointGroup Tag.E6 Ω := canonicalRep_mem_adjointGroup _ Ω w
  have hΦn : Units.map (entrywiseHom ς) n = n := entrywise_canonicalRep' ς hς w
  refine ⟨n * G₃ * (Qε * n⁻¹ * Qε⁻¹), mul_mem (mul_mem hnA hG₃) (hQε _ (inv_mem hnA)), ?_,
    fun u hu => ?_⟩
  · group
  · have e1 : n * G₃ * (Qε * n⁻¹ * Qε⁻¹) * Qε = n * (G₃ * Qε) * n⁻¹ := by group
    rw [e1, map_mul, map_mul, map_inv, hΦn]
    calc n * (G₃ * Qε) * n⁻¹ * (n * Units.map (entrywiseHom ς) u * n⁻¹) *
        (n * (G₃ * Qε) * n⁻¹)⁻¹ =
        n * ((G₃ * Qε) * Units.map (entrywiseHom ς) u * (G₃ * Qε)⁻¹) * n⁻¹ := by group
      _ = n * u * n⁻¹ := by rw [hu]

theorem torusRootKernel_conj_canonicalRep {y : ModGL Tag.E6 Ω}
    (hy : y ∈ torusGroup Tag.E6 Ω) (w : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) Ω w * y * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈
        torusGroup Tag.E6 Ω ∧
      torusRootKernel (canonicalRep (coxeterSystem Tag.E6) Ω w * y *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) = (w • ·) '' torusRootKernel y := by
  classical
  have hnN := canonicalRep_mem_normalizer (R := Ω) (τ := Tag.E6) w
  have hy' := (Subgroup.mem_normalizer_iff.1 hnN y).1 hy
  refine ⟨hy', ?_⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy'
  have hconj : rootDiagUnit Tag.E6 b' = canonicalRep (coxeterSystem Tag.E6) Ω w *
      rootDiagUnit Tag.E6 b * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ := by
    rw [← hb', hb]
  have hrc := (rootDiagUnit_eq_conj_canonicalRep_iff b' b w).1 hconj
  rw [hb', torusRootKernel_rootDiagUnit]
  rw [hb, torusRootKernel_rootDiagUnit]
  ext α
  constructor
  · rintro ⟨hα, hα1⟩
    refine ⟨w⁻¹ • α, ⟨IsRoot.smul hα w⁻¹, ?_⟩, by simp⟩
    have := hrc (w⁻¹ • α)
    rw [smul_inv_smul] at this
    rw [← this]
    exact hα1
  · rintro ⟨β, ⟨hβ, hβ1⟩, rfl⟩
    refine ⟨IsRoot.smul hβ w, ?_⟩
    rw [hrc β]
    exact hβ1

end CFSG.RankThree.PartOne.KE6
