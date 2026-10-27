module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeAction
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_exists_f)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (rootDiagUnit_pow_eq_one_of_forall)
open CFSG.StandardType.TableCRes (langFamilyCompFieldSL_holds)

theorem langModel_le_familyGroup_E6_centerPrime
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (S : LangSetup .E6 L p₀)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : (S.D.Φ = Units.map (entrywiseHom Fr) ∧ ¬ (p = 3 ∧ 3 ∣ S.D.q - 1)) ∨
      (S.D.Φ = twistHom TwistTag.E6 L Fr ∧ ¬ (p = 3 ∧ 3 ∣ S.D.q + 1)))
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit .E6 b ∈ S.D.torus)
    (hbp : ∀ j, b j ^ p = 1) {E : Subgroup (ModGL .E6 L)}
    (hE : E ≤ S.D.model) (hEC : E ≤ Subgroup.centralizer {rootDiagUnit .E6 b}) :
    E ≤ familyGroup (fun _ : Unit => b) := by
  have hker : familyKernel (fun _ : Unit => b) = rootCharKernel b := by
    ext α
    simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  intro y hy
  have hyC : y ∈ toralCentralizer .E6 L b := ⟨(hE hy).1, hEC hy⟩
  have hyF : S.D.step y = y := (S.D.mem_model.mp (hE hy)).2
  have hyM : y ∈ toralRootGroup .E6 L b := by
    by_cases hp3 : p = 3
    · subst p
      rcases hΦ with ⟨hΦ, hq⟩ | ⟨hΦ, hq⟩
      · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.e6CentralizerConnOdd_untw_holds
          L p₀ S ⟨Fr, hFr, hΦ⟩ (fun h => hq ⟨rfl, h⟩) b hb hbp y hyC hyF
      · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6CentralizerConnOdd_holds
          L p₀ S ⟨Fr, hFr, hΦ⟩ (fun h => hq ⟨rfl, h⟩) b hb hbp y hyC hyF
    · have hW := CFSG.LocalAnalysis.GLTheoremA.T171Sh.rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun _ => hp3) hbp
      rwa [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le .E6 L b hW] at hyC
  simpa only [familyGroup, hker, toralRootGroup] using hyM

theorem langTorus_innerDiagOn_subgroup_E6_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {d : Fin Tag.E6.rank → Lˣ} (hd : rootDiagUnit .E6 d ∈ S.D.torus)
    (hd3 : ∀ j, d j ^ 3 = 1) (hd1 : rootDiagUnit .E6 d ≠ 1)
    {E K : Subgroup (ModGL .E6 L)} (hE : E ≤ S.D.torus) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hK : CFSG.Open.IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 d})) :
    GGInnerDiagOn E K := by
  classical
  obtain ⟨f, hf1, hqf⟩ := ssTw_exists_f S (ℓ := 2)
  obtain ⟨S5, hD5, -⟩ :=
    CFSG.StandardType.LieCore.exists_langSetup_of_datum S.D S.ρ S.frob S.finite hf1 hqf
  have hΓ5 : S5.Γ = S.Γ := by
    show S5.D.Γ = S.D.Γ
    rw [hD5]
  have htor5 : S5.D.torus = S.D.torus := by rw [hD5]
  have hmod5 : S5.D.model = S.D.model := by rw [hD5]
  have hEmod : E ≤ S5.D.model := by
    rw [hmod5]
    exact hE.trans S.D.torus_le_model
  have hconn : E ≤ familyGroup (fun _ : Unit => d) := by
    intro e he
    exact Subgroup.mem_sup_left (by
      have htor : e ∈ S.D.torus := hE he
      exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp htor).1)
  have hX : CFSG.Assembly.IsComponentOf K (S5.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 d}) := by
    rw [hΓ5]
    exact CFSG.Assembly.isComponentOf_iff_open.2 hK
  have hGE := connected_model_action S5 d (by rw [htor5]; exact hd) hd3 hd1 E K hEmod hE3 hconn hX
  have hrange : (Set.range fun u : PUnit.{1} =>
      rootDiagUnit .E6 ((fun _ : PUnit.{1} => d) u)) = {rootDiagUnit .E6 d} := Set.range_const
  obtain ⟨_, -, hfield⟩ := langFamilyCompFieldSL_holds .E6 L p₀ 3 S (Or.inl rfl) Nat.prime_three
    (by norm_num) PUnit.{1} (fun _ => d) (fun _ => hd) (fun _ j => hd3 j) K
    (by rw [hrange]; exact hK)
  have hq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).1 hK.2.2
  obtain ⟨lab, -, hc, -, -, -, -, -, R, instR, hR, ⟨θ⟩⟩ := hfield.toAt
  let : Group R := instR
  have hR2 : LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hR
    rwa [hc] at hR
  have hR3 : LieModel (↥K ⧸ Subgroup.center ↥K) (markTag lab) (markRank lab) 2 (markDeg lab) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv θ.symm hR2
  have hmark : CFSG.Assembly.LargeEvenMarking ↥K (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hq.1) hR3)
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨hGE.1, h.2⟩) (hGE.2 hmark)


theorem langTorus_innerDiagOn_E6_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {d t : Fin Tag.E6.rank → Lˣ} (hd : rootDiagUnit .E6 d ∈ S.D.torus)
    (ht : rootDiagUnit .E6 t ∈ S.D.torus) (hd3 : ∀ j, d j ^ 3 = 1) (ht3 : ∀ j, t j ^ 3 = 1)
    (hd1 : rootDiagUnit .E6 d ≠ 1) {K : Subgroup (ModGL .E6 L)}
    (hK : CFSG.Open.IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 d})) :
    GGInnerDiagOn (Subgroup.zpowers (rootDiagUnit .E6 t)) K := by
  refine langTorus_innerDiagOn_subgroup_E6_three S hd hd3 hd1
    (Subgroup.zpowers_le.mpr ht) ?_ hK
  intro e he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    rootDiagUnit_pow_eq_one_of_forall ht3, one_zpow]

end CFSG.StandardType

end
