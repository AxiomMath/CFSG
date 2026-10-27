module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Gamma
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
import CFSG.LieType.Chevalley.GraphFixedF4Canonical
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem famTrivialF4_Γ_data
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) :
    ∃ f : ℕ, 2 ^ f = S.D.q ∧ LieModel (S.Γ ⧸ Subgroup.center S.Γ) .F4 0 2 f ∧
      CFSG.Open.IsQuasisimple ↥S.Γ := by
  obtain ⟨Fr, hFr, hΦ⟩ := S.exists_frobenius_of_steinberg (by decide) (by decide)
  obtain ⟨K', hK'f, hK'fin, hK'a, e, hK'q, he⟩ := S.descends_of_exact (Or.inr rfl)
    ⟨Fr, hFr, hΦ⟩ (fun K' _ _ =>
      CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_F4_eq_top K')
  let : Field K' := hK'f
  let : Finite K' := hK'fin
  let : Algebra K' L := hK'a
  obtain ⟨f, hf1, hqf⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_exists_f S (ℓ := 2)
  have hk : Nat.card K' = 2 ^ f := hK'q.trans hqf
  have hadm : StatedLieAdmissible .F4 0 2 f := ⟨Nat.prime_two, hf1, rfl⟩
  have hLie : LieModel (S.Γ ⧸ Subgroup.center S.Γ) .F4 0 2 f :=
    CFSG.ComponentClassification.CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) hadm hk e.symm
  have hperf : Group.IsPerfect ↥S.Γ := by
    have hperfK : commutator ↥(adjointGroup .F4 K') = ⊤ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_F4_eq_top K'
    have hperfE : Group.IsPerfect ↥(adjointGroup .F4 K') := ⟨hperfK⟩
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hCE : ChevalleyExceptionalModel (S.Γ ⧸ Subgroup.center S.Γ) .F4 2 f :=
    ((LieModel.chevalleyExceptional_iff (t := .F4) (by decide)).1 hLie).2
  have hsimple : IsSimpleGroup (S.Γ ⧸ Subgroup.center S.Γ) :=
    (CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 f hCE).2
  exact ⟨f, hqf.symm, hLie, hperf.commutator_eq_top, hsimple⟩

theorem langFamilyCompFieldF4_trivial
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) {ι : Type}
    (a : ι → Fin Tag.F4.rank → Lˣ) (h1 : ∀ u, rootDiagUnit Tag.F4 (a u) = 1)
    (K : Subgroup (ModGL Tag.F4 L))
    (hK : IsComponentOf K
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit Tag.F4 (a u)))) :
    ∃ i : KernelComponent (famCharHom a),
      K ≤ rootSpan Tag.F4 L (rationalRootsM S.ρ (famCharHom a) i) ∧
        (CFSG.StandardType.GGCompFieldAt
            (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) K ∨
          (S.D.q = 2 ∧ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 ∧
            Nat.card K = 360 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360)) := by
  classical
  have ha1 : ∀ u, a u = 1 := fun u => rootDiagUnit_injective (by rw [h1 u, rootDiagUnit_one])
  have hχ : ∀ γ : Fin Tag.F4.rank → ℤ, famCharHom a (Multiplicative.ofAdd γ) = 1 := by
    intro γ
    funext u
    change rootChar (a u) γ = 1
    rw [ha1 u, rootChar_one_tuple']
  have hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus := fun u => by
    rw [h1 u]
    exact Subgroup.one_mem _
  have hap : ∀ u j, a u j ^ 3 = 1 := fun u j => by rw [ha1 u]; simp
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h
    norm_num at h2
  obtain ⟨i, hi⟩ := CFSG.StandardType.LangRat.langFamilyComponentsInRootSpan
    Tag.F4 L p₀ 3 S (Or.inl rfl) Nat.prime_three (by norm_num) h3L ι a hT hap K hK
  refine ⟨i, hi, ?_⟩
  have hcent : Subgroup.centralizer (Set.range fun u => rootDiagUnit Tag.F4 (a u)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨u, rfl⟩
    simp [h1 u]
  have hK' : IsComponentOf K S.Γ := by simpa [hcent] using hK
  obtain ⟨f, hqf, hLie, hqΓ⟩ := famTrivialF4_Γ_data S
  have hKΓ : K = S.Γ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isComponentOf_eq_of_isQuasisimple hK' hqΓ
  have horbit := (famF4_orbit S Nat.prime_three (by norm_num) hT hap i).2
  rw [horbit, pow_one, hKΓ]
  have hgg : GGCompFieldAt S.D.q S.Γ := by
    have hgg' : GGCompFieldAt (2 ^ f) S.Γ :=
      CFSG.StandardType.ggCompFieldAt_of_lieModel hqΓ hLie ⟨by decide, by decide, by decide⟩
    rwa [hqf] at hgg'
  exact Or.inl hgg

end CFSG.StandardType.TableCRes
