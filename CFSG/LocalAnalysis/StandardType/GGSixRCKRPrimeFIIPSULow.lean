module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoMatrixCentralizer

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.LieType.BorelTits

section

variable {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)] {f : ℕ}

private theorem rckRPu2_le_one {n : ℕ} (hn : n ≤ 1) {X : Type*} [Group X]
    {K J : Subgroup X} {d : X} (φ : Unitary.SU (unitaryInvolution F 2 f) n →* X)
    (hφr : φ.range = K)
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({d} : Set X))) : J = K := by
  have hsub : Subsingleton (Unitary.SU (unitaryInvolution F 2 f) n) := by
    interval_cases n
    · infer_instance
    · refine ⟨fun a b => ?_⟩
      have hdet : ∀ a : Unitary.SU (unitaryInvolution F 2 f) 1,
          ((a : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
        intro a
        have h := a.2.1
        rwa [Matrix.det_fin_one] at h
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i
      fin_cases j
      simp [hdet a, hdet b]
  letI : Subsingleton (Unitary.SU (unitaryInvolution F 2 f) n) := hsub
  letI : Subsingleton ↥φ.range := (MonoidHom.rangeRestrict_surjective φ).subsingleton
  have hKbot : K = ⊥ := by
    rw [← hφr]
    exact Subgroup.eq_bot_of_subsingleton φ.range
  have hJbot : J = ⊥ :=
    le_bot_iff.mp ((hcomp.1.trans inf_le_left).trans (le_of_eq hKbot))
  rw [hJbot, hKbot]

private theorem rckRPu2_injective (hF : Nat.card F = (2 ^ f) ^ 2)
    {X : Type*} [Group X] (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X)
    (hφk : φ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2)) :
    Function.Injective φ := by
  letI : CharP ↥(CFSG.LieType.Steinberg.fixedSubfield F 2 f) 2 :=
    Subfield.charP (CFSG.LieType.Steinberg.fixedSubfield F 2 f) 2
  have hcenter : Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2) = ⊥ := by
    obtain ⟨⟨e⟩, -⟩ := CFSG.StandardType.RCSTSU.exists_equiv_sl2 (F := F) (f := f) hF
    rw [← Subgroup.map_center_eq e, CFSG.Timmesfeld.RankOne.center_SL2_eq_bot,
      Subgroup.map_bot]
  exact (MonoidHom.ker_eq_bot_iff φ).mp (le_bot_iff.mp (hφk.trans (le_of_eq hcenter)))

private theorem rckRPu2_scalar_centralizes {X : Type*} [Group X] {K : Subgroup X} {d : X}
    (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X) (hφr : φ.range = K)
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A)
    (hsc : ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c)
    (hconj : ∀ u, d⁻¹ * φ u * d = φ (InnerDiagSU.conjSU A hA u)) :
    K ≤ Subgroup.centralizer ({d} : Set X) := by
  obtain ⟨c, hc⟩ := hsc
  have hAcomm : ∀ u : GL (Fin 2) F, A * u = u * A := by
    intro u
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc]
    exact Matrix.scalar_comm c (fun r => Commute.all c r) (u : Matrix (Fin 2) (Fin 2) F)
  have hAconj : ∀ u : GL (Fin 2) F, A * u * A⁻¹ = u := by
    intro u
    rw [hAcomm u, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : ∀ u, InnerDiagSU.conjSU A hA u = u := by
    intro u
    apply Subtype.ext
    rw [InnerDiagSU.coe_conjSU]
    exact hAconj (u : GL (Fin 2) F)
  have hdu : ∀ u, φ u * d = d * φ u := by
    intro u
    have h1 : d⁻¹ * φ u * d = φ u := by rw [hconj u, hfix u]
    calc φ u * d = d * (d⁻¹ * φ u * d) := by group
      _ = d * φ u := by rw [h1]
  rw [← hφr]
  rintro _ ⟨u, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hdu u)

private theorem rckRPu2_scalar (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {X : Type*} [Group X] [Finite X] {K J : Subgroup X} {d : X}
    (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2))
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({d} : Set X)))
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A)
    (hsc : ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c)
    (hconj : ∀ u, d⁻¹ * φ u * d = φ (InnerDiagSU.conjSU A hA u)) : J = K := by
  have hKle : K ≤ Subgroup.centralizer ({d} : Set X) :=
    rckRPu2_scalar_centralizes φ hφr hA hsc hconj
  have hKinf : K ⊓ Subgroup.centralizer ({d} : Set X) = K := inf_eq_left.mpr hKle
  rw [hKinf] at hcomp
  have hφinj := rckRPu2_injective hF φ hφk
  let e : Unitary.SU (unitaryInvolution F 2 f) 2 ≃* K :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφr)
  rcases lt_or_ge f 2 with hf1 | hf2
  · have hcard : 2 ^ f = 2 := by
      rw [show f = 1 by omega]
      norm_num
    obtain ⟨eS3⟩ := CFSG.StandardType.RCSTSU.nonempty_su2_equiv_perm (F := F) (f := f) hF hcard
    letI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    have hKsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective
        (f := (e.symm.trans eS3).toMonoidHom) (e.symm.trans eS3).injective
    exact (CFSG.StandardType.Line63.H5.false_of_isComponentOf_of_isSolvable hKsolv hcomp).elim
  · have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hSUq : CFSG.IsQuasisimple (Unitary.SU (unitaryInvolution F 2 f) 2) :=
      CFSG.StandardType.RCSTSU.isQuasisimple_su (k := 2) hF (Or.inr ⟨rfl, h4⟩)
    have hAssem : Assembly.IsQuasisimple (Unitary.SU (unitaryInvolution F 2 f) 2) :=
      ⟨hSUq.1.commutator_eq_top, hSUq.2.1⟩
    have hKq : Assembly.IsQuasisimple ↥K := Assembly.IsQuasisimple.of_mulEquiv e.symm hAssem
    exact CFSG.StandardType.Line63.H5.eq_of_isComponentOf_of_isQuasisimple hcomp hKq

private theorem rckRPu2_nonscalar_matrix_comm (hF : Nat.card F = (2 ^ f) ^ 2)
    {X : Type*} [Group X] [Finite X] {d : X}
    (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X)
    (hφk : φ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2))
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A)
    (hconj : ∀ u, d⁻¹ * φ u * d = φ (InnerDiagSU.conjSU A hA u)) :
    ∀ (u : Unitary.SU (unitaryInvolution F 2 f) 2) {x : X}, φ u = x →
      x ∈ Subgroup.centralizer ({d} : Set X) →
      (A : Matrix (Fin 2) (Fin 2) F) * ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) := by
  have hφinj := rckRPu2_injective hF φ hφk
  intro u x hx hxd
  have hxd' : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxd
  have h1 : d⁻¹ * φ u * d = φ u := by
    rw [hx]
    calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
      _ = d⁻¹ * (d * x) := by rw [hxd']
      _ = x := by group
  have hsu : InnerDiagSU.conjSU A hA u = u := hφinj (by rw [← hconj u, h1])
  have hgl : A * (u : GL (Fin 2) F) * A⁻¹ = (u : GL (Fin 2) F) := by
    have := congrArg (fun z : Unitary.SU (unitaryInvolution F 2 f) 2 =>
      (z : GL (Fin 2) F)) hsu
    simpa only [InnerDiagSU.coe_conjSU] using this
  have hcommGL : A * (u : GL (Fin 2) F) = (u : GL (Fin 2) F) * A := by
    have h := congrArg (fun z : GL (Fin 2) F => z * A) hgl
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  simpa only [Units.val_mul] using congrArg Units.val hcommGL

private theorem rckRPu2_nonscalar_commute (hF : Nat.card F = (2 ^ f) ^ 2)
    {X : Type*} [Group X] [Finite X] {K : Subgroup X} {d : X}
    (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2))
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A)
    (hnsc : ¬ ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c)
    (hconj : ∀ u, d⁻¹ * φ u * d = φ (InnerDiagSU.conjSU A hA u)) :
    ∀ a b : ↥(K ⊓ Subgroup.centralizer ({d} : Set X)), a * b = b * a := by
  have hmat_comm := rckRPu2_nonscalar_matrix_comm hF φ hφk hA hconj
  intro a b
  have ha : a.1 ∈ φ.range := by rw [hφr]; exact a.2.1
  have hb : b.1 ∈ φ.range := by rw [hφr]; exact b.2.1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hb
  have hu' := hmat_comm u hu a.2.2
  have hv' := hmat_comm v hv b.2.2
  have huv : ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBLinearTwo.nonscalar_matrix_centralizer_commutative
      (A : Matrix (Fin 2) (Fin 2) F) ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      ((v : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) hnsc hu' hv'
  have huvSU : u * v = v * u := by
    apply Subtype.ext
    apply Units.ext
    exact huv
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  rw [← hu, ← hv, ← map_mul, ← map_mul, huvSU]

private theorem rckRPu2_nonscalar (hF : Nat.card F = (2 ^ f) ^ 2)
    {X : Type*} [Group X] [Finite X] {K J : Subgroup X} {d : X}
    (φ : Unitary.SU (unitaryInvolution F 2 f) 2 →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution F 2 f) 2))
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({d} : Set X)))
    {A : GL (Fin 2) F} (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A)
    (hnsc : ¬ ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c)
    (hconj : ∀ u, d⁻¹ * φ u * d = φ (InnerDiagSU.conjSU A hA u)) : J = K := by
  have hcentral := rckRPu2_nonscalar_commute hF φ hφr hφk hA hnsc hconj
  exfalso
  refine CFSG.StandardType.Line63.H5.isQuasisimple_not_comm hcomp.2.2 ?_
  intro a b
  have h := congrArg Subtype.val (hcentral ⟨a.1, hcomp.1 a.2⟩ ⟨b.1, hcomp.1 b.2⟩)
  exact Subtype.ext (show (a.1 * b.1 : X) = b.1 * a.1 from h)

end

theorem rckRP_eq_of_PSU_le_two
    {X : Type} [Group X] [Finite X] {n g : ℕ} (hn : n ≤ 2) {K J : Subgroup X} {d : X}
    (φ : (ggU .PSU n (g + 1)).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (_hdK : d ∈ Subgroup.normalizer (K : Set X))
    (hdiag : GGPsiInnerDiag (ggU .PSU n (g + 1)).D φ d)
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) : J = K := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases lt_or_ge n 2 with hn1 | hn2
  · exact rckRPu2_le_one (f := g + 1) (by omega) φ hφr hcomp
  · have hn_eq : n = 2 := by omega
    subst hn_eq
    let F₀ := GaloisField 2 (2 * (g + 1))
    have hc : Nat.card F₀ = (2 ^ (g + 1)) ^ 2 := by
      dsimp only [F₀]
      exact card_galoisField_two_mul 2 (g + 1) (by omega)
    obtain ⟨A, hA, hconj⟩ :=
      InnerDiagSU.suInnerDiagConj_two hc X φ hφk d hdiag
    by_cases hsc : ∃ c : F₀, (A : Matrix (Fin 2) (Fin 2) F₀) = Matrix.scalar (Fin 2) c
    · exact rckRPu2_scalar (F := F₀) (f := g + 1) hc (by omega) φ hφr hφk hcomp hA hsc hconj
    · exact rckRPu2_nonscalar (F := F₀) (f := g + 1) hc φ hφr hφk hcomp hA hsc hconj

end CFSG.StandardType.RCKRP
