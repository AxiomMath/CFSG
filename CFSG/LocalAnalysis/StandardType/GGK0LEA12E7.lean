module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LEGamma
public import CFSG.LocalAnalysis.StandardType.GGK0LQAlgSetup
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lea12e_tau_eq_E7
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {phi : MulAut R} (A : K0LangMark Omega lab p R I phi) (hT : A.row.T = .E7) :
    A.tau = .E7 := by
  rw [← A.tau_eq, hT]
  rfl

private lemma lea12e_tw_eq_false
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {phi : MulAut R} (A : K0LangMark Omega lab p R I phi) (hT : A.row.T = .E7) :
    A.row.tw = false := by
  cases h : A.row.tw with
  | false => rfl
  | true =>
    obtain ⟨ht, -⟩ := A.phi_twisted h
    exact absurd (ht.trans (lea12e_tau_eq_E7 A hT)) (by decide)

private lemma lea12e_isInner_of_card_two
    {K : Type} [Field K] [Finite K] {τ : Tag} (hτ : τ = .E7) (hK : Nat.card K = 2)
    (α : MulAut (adjointGroup τ K)) :
    ∃ g : adjointGroup τ K, MulAut.conj g = α := by
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form (f := 1) (by norm_num) K
      (by simpa using hK) τ (Or.inl hτ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Subsingleton (K ≃+* K) :=
    CFSG.RankThree.PartOne.CTP.subsingleton_ringEquiv_of_card_eq_prime (p := 2) hK
  have h1 : Θ α = 1 := Subsingleton.elim _ _
  have h2 : α ∈ Θ.ker := MonoidHom.mem_ker.mpr h1
  rw [hΘker] at h2
  exact MonoidHom.mem_range.mp h2

private lemma lea12e_exists_conj_of_isInner
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {phi : MulAut R} (A : K0LangMark Omega lab p R I phi)
    {K : Type} [Field K] [Algebra K Omega]
    (hmap : A.setup.Γ.map (MulAut.conj A.setup.D.g0).toMonoidHom =
      (adjointGroup A.tau K).map
        (CFSG.LieType.Chevalley.baseChangeGL (τ := A.tau) (algebraMap K Omega)))
    (u : MulAut R)
    (hInner : ∀ α : MulAut (adjointGroup A.tau K),
      ∃ g : adjointGroup A.tau K, MulAut.conj g = α) :
    ∃ r : R, u = MulAut.conj r := by
  classical
  let bc : ModGL A.tau K →* ModGL A.tau Omega :=
    CFSG.LieType.Chevalley.baseChangeGL (τ := A.tau) (algebraMap K Omega)
  have hbc : Function.Injective bc :=
    CFSG.LieType.Chevalley.baseChangeGL_injective (τ := A.tau) (algebraMap K Omega)
  let cj : ModGL A.tau Omega →* ModGL A.tau Omega :=
    (MulAut.conj A.setup.D.g0).toMonoidHom
  have hcj : Function.Injective cj := (MulAut.conj A.setup.D.g0).injective
  let eΓ : R ≃* A.setup.Γ :=
    (MonoidHom.ofInjective (f := A.iota) A.iota_inj).trans (MulEquiv.subgroupCongr A.iota_range)
  let eC : A.setup.Γ ≃* A.setup.Γ.map cj :=
    Subgroup.equivMapOfInjective A.setup.Γ cj hcj
  let eS : A.setup.Γ.map cj ≃* (adjointGroup A.tau K).map bc :=
    MulEquiv.subgroupCongr hmap
  let eK : (adjointGroup A.tau K).map bc ≃* adjointGroup A.tau K :=
    (Subgroup.equivMapOfInjective (adjointGroup A.tau K) bc hbc).symm
  let ψ : R ≃* adjointGroup A.tau K := eΓ.trans (eC.trans (eS.trans eK))
  have hψ : ∀ r : R, bc (ψ r) = cj (A.iota r) := by
    intro r
    have hΓr : (eΓ r : ModGL A.tau Omega) = A.iota r :=
      MonoidHom.ofInjective_apply A.iota_inj
    have hCr : (eC (eΓ r) : ModGL A.tau Omega) = cj (A.iota r) := by
      rw [Subgroup.coe_equivMapOfInjective_apply, hΓr]
    have hSr : (eS (eC (eΓ r)) : ModGL A.tau Omega) =
        (eC (eΓ r) : ModGL A.tau Omega) :=
      MulEquiv.subgroupCongr_apply hmap (eC (eΓ r))
    have hKr : bc (eK (eS (eC (eΓ r)))) =
        (eS (eC (eΓ r)) : ModGL A.tau Omega) := by
      have h := Subgroup.coe_equivMapOfInjective_apply (adjointGroup A.tau K) bc hbc
        (eK (eS (eC (eΓ r))))
      dsimp only [eK] at h
      simpa using h.symm
    calc bc (ψ r) = bc (eK (eS (eC (eΓ r)))) := rfl
      _ = (eS (eC (eΓ r)) : ModGL A.tau Omega) := hKr
      _ = (eC (eΓ r) : ModGL A.tau Omega) := hSr
      _ = cj (A.iota r) := hCr
  obtain ⟨g', hg'⟩ := hInner (ψ.symm.trans (u.trans ψ))
  refine ⟨ψ.symm g', ?_⟩
  ext x
  apply ψ.injective
  have hαψ : (ψ.symm.trans (u.trans ψ)) (ψ x) = ψ (u x) := by
    simp [MulEquiv.trans_apply]
  rw [← hαψ, ← hg']
  simp [MulAut.conj_apply]

theorem k0_exists_modelAction_eq_E7
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (hT : A.row.T = .E7) (hn : lab.n = 1)
    (u : MulAut R) : ∃ g : A.setup.D.model, A.modelAction g = u := by
  classical
  have hτ7 : A.tau = .E7 := lea12e_tau_eq_E7 A hT
  have hτ : A.tau = .F4 ∨ A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 :=
    Or.inr (Or.inr (Or.inl hτ7))
  have htw : A.row.tw = false := lea12e_tw_eq_false A hT
  have hq : A.setup.D.q = 2 ^ 1 := by
    rw [A.q_eq, hn]
  have hΦ : A.setup.D.Φ = Units.map (entrywiseHom A.fr) :=
    MonoidHom.ext (A.phi_split htw)
  obtain ⟨K, hKfield, hKfinite, hKalgebra, hKcard, hmap⟩ :=
    CFSG.StandardType.LangRat.langGamma_conj_eq_map_adjointGroup
      (S := A.setup) hτ (f := 1) hq
      (CFSG.StandardType.GGK0LQ.lq_setup_isAlgebraic hAlg A)
      (Fr := A.fr) (by intro c; rw [A.fr_eq, A.q_eq]) hΦ
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Algebra K Omega := hKalgebra
  have hK2 : Nat.card K = 2 := by
    rw [hKcard, hq]
    norm_num
  have hinner : ∀ α : MulAut (adjointGroup A.tau K),
      ∃ g : adjointGroup A.tau K, MulAut.conj g = α :=
    lea12e_isInner_of_card_two (K := K) (τ := A.tau) hτ7 hK2
  obtain ⟨r, hu⟩ := lea12e_exists_conj_of_isInner A hmap u hinner
  have hΓ : A.iota r ∈ A.setup.Γ := by
    rw [← A.iota_range]
    exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
  refine ⟨⟨A.iota r, LangSetup.Γ_le_model A.setup hΓ⟩, ?_⟩
  ext x
  rw [hu, MulAut.conj_apply]
  apply A.iota_inj
  rw [A.modelAction_compat]
  simp [map_mul, map_inv]

end CFSG.StandardType.GGK0MarkedKacIface1587
