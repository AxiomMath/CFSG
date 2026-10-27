module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4Contracts
public import CFSG.LocalAnalysis.StandardType.GGF4OrigWeyl
import CFSG.LocalAnalysis.StandardType.GGF4CoxeterSystem
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGF4RankLow
import CFSG.LocalAnalysis.StandardType.GGF4LinFour
import CFSG.LocalAnalysis.StandardType.GGF4RankFour
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import TauCeti.GroupTheory.Coxeter.Geometric
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.F4Model

private theorem ggF4Orig_sup_le_join {G : Type} [Group G] {Bs L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {K : Subgroup G} (hK : K ∈ 𝒦) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  rw [ggAutomizerJoin]
  exact sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl))

private theorem ggF4Orig_mem_zpowers_of_fix {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTBF : GGTBFixInput) (hR : GGSecFiveRestHyp p B Bs x L D J)
    (hW : GGSecFiveWeylCase' p B Bs x D J) (hN : GGNbr p B x D J y K) (b : ↥Bs)
    (hb : ∀ φ ∈ ggAutomizer L Bs, φ b = b) : (b : G) ∈ Subgroup.zpowers x := by
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hW y K hN
  have hSW : GGScalarsOrWeyl' p B Bs x D J := Or.inr hW
  exact hTBF G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hN hrefl hSW b hb

theorem ggSecFiveF4OriginalTypesInput_holds
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGSecFiveF4OriginalTypesInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 hCard ι M e hP hF
  classical
  obtain ⟨e', rfl⟩ := hF
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hx'1 : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := ggAutomizerJoin_le_ggInduced_top L 𝒦
  have : Finite (MulAut ↥Bs) := MulEquiv.finite_left
  have : Fintype ι := Fintype.ofEquiv (Fin 4) e'
  have hcardι : Fintype.card ι = 4 := by rw [← Fintype.card_congr e', Fintype.card_fin]
  let cs := ggF4CoxeterSystem e' e
  have hconv : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizerJoin L Bs 𝒦), GGIsReflection p φ →
      cs.IsReflection ⟨φ, hφ⟩ := by
    intro φ hφ hr
    exact (ggF4CoxeterSystem_isReflection_iff hp hp2 hBs hNT hAind e' hP ⟨φ, hφ⟩).2 hr
  have hW : GGWeylOfType p (CoxeterMatrix.F₄.reindex e') (ggAutomizerJoin L Bs 𝒦) := ⟨e, hP.2⟩
  obtain ⟨K, hK⟩ := hCard
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hle2 : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggF4Orig_sup_le_join hK
  have hfixA : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 := fun b hb =>
    GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b (fun φ hφ => hb φ (hle2 hφ))
  have hcard4 : Nat.card ↥Bs ≤ p ^ 4 := by
    have h := SpJoinRefl.card_le_pow_of_weylOfType hW hfixA
    rwa [hcardι] at h
  have hAL_weyl : GGWeylReflectionGroup p (ggAutomizer L Bs) :=
    ggF4Orig_weyl_of_route hX hTCJ hRig hR
  have hALA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have hcardA : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 1152 :=
    ggF4Orig_card_weylOfType_F4 (GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) hW)
  have hdvd : Nat.card ↥(ggAutomizer L Bs) ∣ 1152 := by
    have h1 := Subgroup.card_dvd_of_le hALA
    rwa [hcardA] at h1
  have hfixAL : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers x :=
    fun b hb => ggF4Orig_mem_zpowers_of_fix hTBF hR.1 hR.2.1 hN b hb
  have hxfix : ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := fun φ hφ =>
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) hLx hφ
  have contra_quad : (∃ t : Fin 4 → ↥(ggAutomizerJoin L Bs 𝒦),
      (∀ k, ((t k : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs) ∧
      (∀ k, GGIsReflection p ((t k : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∧
      (∀ j k, t j * t k = t k * t j) ∧ Function.Injective t) → False := by
    rintro ⟨t, htAL, htrefl, hcomm, hinj⟩
    refine hx'1 (ggF4Orig_fix_four hp2 hBs hcard4 (fun k => ((t k : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs)) htrefl (fun j k => ?_) (fun j k h => hinj (Subtype.ext h)) ⟨x, hxBs⟩
      (fun k => hxfix _ (htAL k)))
    exact congrArg Subtype.val (hcomm j k)
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  let H : Subgroup ↥(ggAutomizerJoin L Bs 𝒦) :=
    (ggAutomizer L Bs).comap (ggAutomizerJoin L Bs 𝒦).subtype
  have hdata : ∀ (T : CoxeterMatrix (Fin 4)), GGWeylOfType p T (ggAutomizer L Bs) →
      ∃ a : Fin 4 → ↥(ggAutomizerJoin L Bs 𝒦), (∀ i, R.IsRefl (a i)) ∧ (∀ i, a i ∈ H) ∧
        (∀ i, GGIsReflection p ((a i : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) ∧
        ∀ i j, orderOf (a i * a j) = T.M i j := by
    intro T hT
    obtain ⟨eT, heT⟩ := hT
    obtain ⟨a, ha_def⟩ : ∃ a : Fin 4 → ↥(ggAutomizerJoin L Bs 𝒦), ∀ i,
        a i = Subgroup.inclusion hALA (eT (T.simple i)) :=
      ⟨fun i => Subgroup.inclusion hALA (eT (T.simple i)), fun i => rfl⟩
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · intro i
      refine (F4Rep.isRefl_iff hRs).2 ?_
      rw [ha_def i]
      exact hconv (eT (T.simple i) : MulAut ↥Bs) (hALA (eT (T.simple i)).2) (heT i)
    · intro i
      rw [ha_def i]
      exact (eT (T.simple i)).2
    · intro i
      rw [ha_def i]
      exact heT i
    · intro i j
      have h1 : a i * a j = Subgroup.inclusion hALA (eT (T.simple i * T.simple j)) := by
        rw [ha_def i, ha_def j, map_mul, map_mul]
      rw [h1, orderOf_injective (Subgroup.inclusion hALA) (Subgroup.inclusion_injective hALA),
        MulEquiv.orderOf_eq eT]
      simpa using T.toCoxeterSystem.orderOf_simple_mul_simple i j
  have htrefl_of : ∀ (a : Fin 4 → ↥(ggAutomizerJoin L Bs 𝒦)),
      (∀ i, GGIsReflection p ((a i : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) →
      ∀ (t : Fin 4 → ↥(ggAutomizerJoin L Bs 𝒦)),
        (∀ k, ∃ (g : ↥(ggAutomizerJoin L Bs 𝒦)) (j : Fin 4), t k = g * a j * g⁻¹) →
        ∀ k, GGIsReflection p ((t k : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    intro a harefl t htconj k
    obtain ⟨g, j, hg⟩ := htconj k
    rw [hg]
    exact (harefl j).conj ((g : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  rcases ggF4Orig_type_cases hAL_weyl hdvd with ⟨n, hn1, hn3, hT⟩ | ⟨n, hn2, hn4, hT⟩ | hT | hT |
    hT
  · have hr := ggF4Orig_three_le_card hp hBs hxBs h4 hT hfixAL
    rw [Fintype.card_fin] at hr
    obtain rfl : n = 3 := by omega
    exact Or.inl hT
  · have hr := ggF4Orig_three_le_card hp hBs hxBs h4 hT hfixAL
    rw [Fintype.card_fin] at hr
    by_cases hn : n = 3
    · subst hn
      exact Or.inr hT
    · exfalso
      obtain rfl : n = 4 := by omega
      obtain ⟨a, haR, haH, harefl, hord⟩ := hdata (CoxeterMatrix.B 4) hT
      obtain ⟨t, htH, htconj, htcomm, htinj⟩ := R.rank_four_B H haR haH
        (by rw [hord 0 1]; decide)
        (by rw [hord 1 2]; decide)
        (by rw [hord 2 3]; decide)
        (by rw [hord 0 2]; decide)
        (by rw [hord 0 3]; decide)
        (by rw [hord 1 3]; decide)
      exact contra_quad ⟨t, htH, htrefl_of a harefl t htconj, htcomm, htinj⟩
  · exfalso
    obtain ⟨a, haR, haH, harefl, hord⟩ := hdata (ggCoxeterMatrixD 4) hT
    obtain ⟨t, htH, htconj, htcomm, htinj⟩ := R.rank_four_D H haR haH
      (by rw [hord 0 1]; decide)
      (by rw [hord 1 2]; decide)
      (by rw [hord 1 3]; decide)
      (by rw [hord 0 2]; decide)
      (by rw [hord 0 3]; decide)
      (by rw [hord 2 3]; decide)
    exact contra_quad ⟨t, htH, htrefl_of a harefl t htconj, htcomm, htinj⟩
  · exfalso
    have hcardAL := ggF4Orig_card_weylOfType_F4 hT
    have hEq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
      Subgroup.eq_of_le_of_card_ge hALA (le_of_eq (by rw [hcardA, hcardAL]))
    refine hx'1 (hfixA ⟨x, hxBs⟩ fun ψ hψ => hxfix ψ ?_)
    rw [hEq]
    exact hψ
  · exfalso
    have hr := ggF4Orig_three_le_card hp hBs hxBs h4 hT hfixAL
    rw [Fintype.card_fin] at hr
    omega

end CFSG.StandardType

end
