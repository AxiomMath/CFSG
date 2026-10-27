module

public import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofPush
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsBasic
import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2Tools
import CFSG.RankThree.PartTwo.Sec19.Step1918ProofTools
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1917XGen :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G) (c : G),
    Group.IsPerfect X → IsQuasisimple (X ⧸ CFSG.pCore 2 X) →
    E ≤ Subgroup.normalizer (X : Set G) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    c ∈ E →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ 2 < p ^ e ∧
        Sec4.IsoLThreePi (X ⧸ CFSG.pCore 2 X) p (3 * e) ∧ KFacts.InducesStdKind X c .field) ∨
      ∃ n : ℕ, 2 ≤ n ∧ CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ CFSG.pCore 2 X)
        .trialityD4 2 n ∧ Sec4.InducesOuterTheta c X) →
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X

namespace Item19Res3Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_of_eq_sup {X L : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (X : Set G)) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLX : L ≤ X) (hXL : X = L ⊔ CFSG.Open.pCoreOf 2 X) :
    ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
  set O := CFSG.Open.pCoreOf 2 X with hO
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hc
  let S : Subgroup G :=
    { carrier := {x | x ∈ X ∧ c * x * c⁻¹ * x⁻¹ ∈ O}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨X.mul_mem hx hy, ?_⟩
        have h1 : x * (c * y * c⁻¹ * y⁻¹) * x⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hXO hx) _).mp hy'
        have e : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
            (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact O.mul_mem hx' h1
      one_mem' := ⟨X.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨X.inv_mem hx, ?_⟩
        have h1 : x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hx)) _).mp (O.inv_mem hx')
        have e : c * x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hLS : L ≤ S := fun l hl => ⟨hLX hl, by
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)).symm
    rw [hcl, mul_inv_cancel_right, mul_inv_cancel]
    exact O.one_mem⟩
  have hOS : O ≤ S := fun o ho => ⟨hOX ho, by
    have h1 : c * o * c⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hcO o).mp ho
    exact O.mul_mem h1 (O.inv_mem ho)⟩
  intro x hx
  rw [hXL] at hx
  exact (sup_le hLS hOS hx).2

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

end Item19Res3Proof

open Item19Res3Proof

theorem step1917EqCentral_of
    (h1913 : Step1913) (hC : Census1915) (hG : KS1917XGen) : Step1917EqCentral := by
  intro G _ _ A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK hKL hKH X hX hLX hKX hcX
  by_contra hnc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  obtain ⟨-, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Step1917Proof.map_conj_eq_of_mem_of_isMaximalTwoLocal hst hH.1 hZ hX hLX hFL hF hF9 hh)
  have hEH : E ≤ H := Step1917Steps.E_le_H hctx hdD.2 hH.2
  have hE := Step1916Proof2.isE27_E hctx
  have hcE := Step1916Proof2.mem_E hctx
  have hcensus := Step1917EqProof.xStar_of_census h1913 hC hctx hdD hH hX hLX hnc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hctx.mem_lA.1
  have hLqp : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 L))
      (QuotientGroup.mk'_surjective _)
  have htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ 2 < p ^ e ∧
        Sec4.IsoLThreePi (X ⧸ CFSG.pCore 2 X) p (3 * e) ∧ KFacts.InducesStdKind X c .field) ∨
      ∃ n : ℕ, 2 ≤ n ∧ CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ CFSG.pCore 2 X)
        .trialityD4 2 n ∧ Sec4.InducesOuterTheta c X := by
    rcases hcensus with ⟨p, e, hp, he, hLiso, hXiso, hind⟩ |
      ⟨n, hn, F', _, _, -, σ, -, -, hLiso, hD4, hout⟩
    · have hq2 := (Step1914TriProof.isSimpleGroup_of_isoLThreePi he hLiso).2
      have hp2 : 2 ≤ p := hp.out.two_le
      have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
      exact Or.inl ⟨p, e, hp, he, by omega, hXiso, hind⟩
    · have hq2 := (Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hLiso).2
      refine Or.inr ⟨n, ?_, hD4, hout⟩
      by_contra hn2
      exact hq2 (by rw [show n = 1 by omega, pow_one])
  have hgen := hG G X E c (isPerfect_of_mem_oTwoComponentsIn hX)
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hX) (hEH.trans hHX) hE.1 hE.2 hcE htype
  have hOH : CFSG.Open.pCoreOf 2 H ≤ M := by
    rw [← hctx.hyp191 E M H hE hctx.mem_scriptM hEH (pCoreOf_ne_bot_of_isMaximalTwoLocal hH.1)]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hXM : X ≤ M := by
    refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact inf_le_right.trans ((Item19Res3Proof.centralizer_le_normalizer_zpowers c).trans
        (step1916_of h1913 G A c L E M hctx hLM))
    · refine iSup_le fun F => inf_le_right.trans ?_
      have hFab : CFSG.Assembly.IsElemAbelian 3 (F : Subgroup G) :=
        ⟨⟨⟨fun x y => Subtype.ext (by
          have h := congrArg Subtype.val
            (hE.1.1.is_comm.comm ⟨(x : G), F.2.1 x.2⟩ ⟨(y : G), F.2.1 y.2⟩)
          simpa using h)⟩⟩, fun x hx => hE.1.2 x (F.2.1 hx)⟩
      have h2 : 2 ≤ CFSG.Open.pRank 3 (F : Subgroup G) :=
        CFSG.SectionRank.le_pRank (by norm_num) le_rfl hFab (by rw [F.2.2]; norm_num)
      exact (Subgroup.centralizer_le_normalizer _).trans
        ((normalizer_le_gamma F.2.1 h2).trans hctx.mem_scriptM.2)
    · exact (Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hX).trans hOH
  have hKX' : K = X := Step1917EqProof.eq_of_le_M h1913 hctx hK hLK hKH hX hLX hXM
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hctx.mem_lA.1
  rw [hKX'] at hKL
  exact hnc (commutator_mem_of_eq_sup hcX hLc hLX hKL)

end CFSG.RankThree.PartTwo.Sec19
