module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFramePairCore
import CFSG.LocalAnalysis.StandardType.ExcPos.StableOppositePairLang
import CFSG.RankThree.PartOne.D4RC.Descent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart1
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCompPairIncidence

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)
open CFSG.SeitzReduction
open scoped commutatorElement

theorem exists_mem_adjointGroup_conj_stdPair_D4
    {k : Type} [Field k] {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α)
    {w : ModGL Tag.D4 k} (hw : w ∈ adjointGroup Tag.D4 k) :
    ∃ u ∈ adjointGroup Tag.D4 k, conjSub u (Uθ Tag.D4 k) = conjSub w (rootSubgroup Tag.D4 k α) ∧
      conjSub u (Uneg Tag.D4 k) = conjSub w (rootSubgroup Tag.D4 k (-α)) := by
  obtain ⟨x, hx⟩ : ∃ x : WeylGroup Tag.D4, x • highRoot Tag.D4 = α :=
    CFSG.RankThree.PartOne.D4RC.rcd_exists_smul_highRoot hα
  have h1 := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := k) x
    (isRoot_highRoot Tag.D4)
  have h2 := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := k) x
    (IsRoot.neg (isRoot_highRoot Tag.D4))
  rw [hx] at h1
  rw [smul_neg, hx] at h2
  refine ⟨w * canonicalRep (coxeterSystem Tag.D4) k x,
    mul_mem hw (canonicalRep_mem_adjointGroup _ k x), ?_, ?_⟩
  · rw [conjSub_mul]
    exact congrArg (conjSub w) h1
  · rw [conjSub_mul]
    exact congrArg (conjSub w) h2

theorem exists_frobTwist_fixed_conj_opposite_pair_D4
    {k : Type} [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {e : ℕ} (he : 1 ≤ e) (Q : ModGL Tag.D4 k)
    (hFA : ∀ g ∈ adjointGroup Tag.D4 k, frobTwistGL Tag.D4 k p e Q g ∈ adjointGroup Tag.D4 k)
    {α α' : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) (hα' : IsRoot Tag.D4 α')
    {w w' : ModGL Tag.D4 k} (hw : w ∈ adjointGroup Tag.D4 k) (hw' : w' ∈ adjointGroup Tag.D4 k)
    (h₁ : (conjSub w (rootSubgroup Tag.D4 k α)).map (frobTwistGL Tag.D4 k p e Q) =
      conjSub w (rootSubgroup Tag.D4 k α))
    (h₂ : (conjSub w (rootSubgroup Tag.D4 k (-α))).map (frobTwistGL Tag.D4 k p e Q) =
      conjSub w (rootSubgroup Tag.D4 k (-α)))
    (h₁' : (conjSub w' (rootSubgroup Tag.D4 k α')).map (frobTwistGL Tag.D4 k p e Q) =
      conjSub w' (rootSubgroup Tag.D4 k α'))
    (h₂' : (conjSub w' (rootSubgroup Tag.D4 k (-α'))).map (frobTwistGL Tag.D4 k p e Q) =
      conjSub w' (rootSubgroup Tag.D4 k (-α'))) :
    ∃ h ∈ adjointGroup Tag.D4 k, frobTwistGL Tag.D4 k p e Q h = h ∧
      conjSub h (conjSub w (rootSubgroup Tag.D4 k α)) = conjSub w' (rootSubgroup Tag.D4 k α') ∧
      conjSub h (conjSub w (rootSubgroup Tag.D4 k (-α))) = conjSub w' (rootSubgroup Tag.D4 k (-α')) := by
  obtain ⟨u₀, hu₀, hV, hV'⟩ := exists_mem_adjointGroup_conj_stdPair_D4 (k := k) hα hw
  obtain ⟨u₁, hu₁, hW, hW'⟩ := exists_mem_adjointGroup_conj_stdPair_D4 (k := k) hα' hw'
  have hF₁ : ∀ x, frobTwistGL Tag.D4 k p e (u₀⁻¹ * Q * entrywiseFrobGL Tag.D4 k p e u₀) x =
      u₀⁻¹ * frobTwistGL Tag.D4 k p e Q (u₀ * x * u₀⁻¹) * u₀ := by
    intro x
    simp only [frobTwistGL_apply, map_mul, map_inv]
    group
  refine CFSG.StandardType.LieKnownR2.ExcPos.exists_fixed_conj_pair_of_lang
    (frobTwistGL Tag.D4 k p e Q)
    (frobTwistGL Tag.D4 k p e (u₀⁻¹ * Q * entrywiseFrobGL Tag.D4 k p e u₀)) hFA hu₀ hu₁ hV hV'
    hW hW' h₁ h₂ h₁' h₂' hF₁ ?_
  intro hstab c hc
  have hZ := CFSG.StandardType.F4ExplicitPos.PairStabilizer.isConnectedAlgebraicSubgroup_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
    Tag.D4 k
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he
    (u₀⁻¹ * Q * entrywiseFrobGL Tag.D4 k p e u₀) hstab
  exact hlang c hc

theorem rckPairFixedConj
    {τ : Tag} (hτ : τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7) (S : LangSetup τ GGL 5)
    {γ γ' : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ' : IsRoot τ γ')
    {z z' : ModGL τ GGL} (hz : z ∈ adjointGroup τ GGL) (hz' : z' ∈ adjointGroup τ GGL)
    (h1 : ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom)
    (h2 : ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom)
    (h1' : ((rootSubgroup τ GGL γ').map (MulAut.conj z').toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ').map (MulAut.conj z').toMonoidHom)
    (h2' : ((rootSubgroup τ GGL (-γ')).map (MulAut.conj z').toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ')).map (MulAut.conj z').toMonoidHom) :
    ∃ h ∈ S.D.model,
      conjSub h (conjSub z (rootSubgroup τ GGL γ)) = conjSub z' (rootSubgroup τ GGL γ') ∧
      conjSub h (conjSub z (rootSubgroup τ GGL (-γ))) = conjSub z' (rootSubgroup τ GGL (-γ')) := by
  obtain ⟨e, Q, he, hstep, hA⟩ := rckStep_eq_frobTwist S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hstep] at h1 h2 h1' h2'
  have hFA : ∀ g ∈ adjointGroup τ GGL, frobTwistGL τ GGL 2 e Q g ∈ adjointGroup τ GGL := by
    intro g hg; rw [← hstep]; exact hA g hg
  have hfix : ∀ h : ModGL τ GGL, h ∈ adjointGroup τ GGL → frobTwistGL τ GGL 2 e Q h = h →
      h ∈ S.D.model := fun h hh hF =>
    Subgroup.mem_inf.mpr ⟨hh, show S.D.step h = h by rw [hstep]; exact hF⟩
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨h, hh, hF, c1, c2⟩ := exists_frobTwist_fixed_conj_opposite_pair_D4 2 he Q hFA hγ hγ'
      hz hz' h1 h2 h1' h2'
    exact ⟨h, hfix h hh hF, c1, c2⟩
  · obtain ⟨h, hh, hF, c1, c2⟩ :=
      CFSG.StandardType.LieKnownR2.ExcPos.exists_frobTwist_fixed_conj_opposite_pair (Or.inl rfl) 2 he
        Q hFA hγ hγ' hz hz' h1 h2 h1' h2'
    exact ⟨h, hfix h hh hF, c1, c2⟩
  · obtain ⟨h, hh, hF, c1, c2⟩ :=
      CFSG.StandardType.LieKnownR2.ExcPos.exists_frobTwist_fixed_conj_opposite_pair
        (Or.inr (Or.inl rfl)) 2 he Q hFA hγ hγ' hz hz' h1 h2 h1' h2'
    exact ⟨h, hfix h hh hF, c1, c2⟩

theorem rckFrameIncidence_of_pairCore
    (hPC : RCKFramePairCore) : RCKFrameIncidence := by
  intro τ hτ S γ γ' hγ hγ' z hz z' hz' h1 h2 h1' h2'
  obtain ⟨h, hhM, hp, hm⟩ := rckPairFixedConj hτ S hγ hγ' hz hz' h1 h2 h1' h2'
  obtain ⟨u, huΓ, htp, htm⟩ := hPC τ hτ S γ' hγ' z' hz' h1' h2' h⁻¹ (inv_mem hhM)
  have huM0 : u ∈ S.D.model := Subgroup.commutator_le_self S.D.model huΓ
  have huM : S.D.step u = u := (Subgroup.mem_inf.mp huM0).2
  have key : ∀ (P Q : Subgroup (ModGL τ GGL)), P.map (MulAut.conj h).toMonoidHom = Q →
      u⁻¹ * h⁻¹ ∈ Subgroup.normalizer (Q : Set (ModGL τ GGL)) →
      P ⊓ S.D.step.eqLocus (MonoidHom.id _) =
        (Q ⊓ S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj u).toMonoidHom := by
    intro P Q hPQ hn
    have hP : P = Q.map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [← hPQ, Subgroup.map_map]
      ext x
      simp only [Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
        Function.comp_apply, MulAut.conj_apply]
      constructor
      · intro hx
        exact ⟨x, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        have hyy : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
        rw [hyy]
        exact hy
    have hQ : Q.map (MulAut.conj h⁻¹).toMonoidHom = Q.map (MulAut.conj u).toMonoidHom := by
      have := CFSG.map_conj_mul_right_eq_of_mem_normalizer (H := Q) u ⟨u⁻¹ * h⁻¹, hn⟩
      simpa using this
    rw [hP, hQ]
    exact CFSG.StandardType.F4ExplicitPos.AmbientPairDescent.map_conj_fixed_eq S.D.step huM Q
  exact ⟨u, huΓ, key _ _ hp htp, key _ _ hm htm⟩

end CFSG.StandardType.RCKRP
