module

public import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2Tools
public import CFSG.RankThree.PartTwo.Sec19.Step196KFact
import CFSG.RankThree.PartTwo.Sec19.Step196Proof
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

namespace Step1916Proof2

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem outThreeClosed_thetaQuot
    (h1913 : Step1913) (hctx : Ctx1912 G A c L E M) :
    OutThreeClosed (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨hθ, -, -⟩ := lBar_facts h1913 hctx
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  set ι : L ⧸ aschbacherSolvableCore 3 L ≃* L ⧸ CFSG.pCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq hθ with hι
  rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | hM12
  · obtain ⟨-, hq2⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact OutThreeClosed.of_mulEquiv
        ((ι.trans φ).trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField p e)))
        Step196Proof.outThreeClosed_projectiveSL
    · have hU := Sec4.unitaryFieldData_galoisField p e he
      have hq2' : 2 < p ^ e := by
        have : 2 ≤ p ^ e := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      exact OutThreeClosed.of_mulEquiv ((ι.trans φ).trans (Sec4.projSUEquivUnitaryPSU p e hU))
        (Step196Proof.outThreeClosed_unitaryPSU hU hq2')
  · obtain ⟨-, -, hinn, -⟩ := KFacts.ks18M12 _ hM12
    refine OutThreeClosed.of_mulEquiv ι (OutThreeClosed.of_forall_mem_range fun σ hσ => ?_)
    obtain ⟨x, hx⟩ := hinn σ hσ
    exact ⟨x, hx.symm⟩

theorem centralizer_inf_le (hctx : Ctx1912 G A c L E M) (hL3 : 3 ∣ Nat.card L) (hLM : L ≤ M) :
    Sec4.thetaQuotCentralizer L ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzAE, hzL, hz1, hz3⟩ := exists_mem_inf_of_three_dvd hctx hL3
  have hE := isE27_E hctx
  have hcE := mem_E hctx
  have hzE : z ∈ E := hzAE.2
  have hc3 := orderOf_eq hctx
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set F : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers z with hF
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr hcE) (Subgroup.zpowers_le.mpr hzE)
  have hzc : z ∉ Subgroup.zpowers c := by
    intro h
    have hbot := Step1914TriProof.zpowers_inf_eq_bot_of_not_mem hc3 (not_mem_L hctx)
    have : z ∈ Subgroup.zpowers c ⊓ L := ⟨h, hzL⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 this
  have hF9 : 9 ≤ Nat.card F :=
    Step1914TriProof.nine_le_card_of_mem_of_not_mem hE hFE hc3
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hzc
  have hFN : Subgroup.normalizer (F : Set G) ≤ M :=
    (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hFE)
      hF9)).trans hctx.mem_scriptM.2
  have hF3 : IsPGroup 3 F := hE.isPGroup.to_le hFE
  have hθ3 : ¬ 3 ∣ Nat.card θL := (Sec6.theta_solvable_and_not_dvd L).2
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1 (mem_A hctx)
  have hFθ : F ≤ Subgroup.normalizer (θL : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_theta L hcN))
      (Subgroup.zpowers_le.mpr (Sec6.le_normalizer_theta L hzL))
  set Y := F ⊔ θL with hY
  have hFY : F ≤ Y := le_sup_left
  have hcardY := Sec6.card_sup_mul_card_inf hFθ
  rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hθ3 hF3, Subgroup.card_bot,
    mul_one] at hcardY
  have hrel := Subgroup.relIndex_mul_card F Y
  rw [inf_eq_left.mpr hFY, hcardY] at hrel
  have hrel' : F.relIndex Y = Nat.card θL := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hrel, mul_comm])
  have hSyl : IsSylowOf 3 F Y := isSylowOf_iff.mpr ⟨hFY, hF3, by rw [hrel']; exact hθ3⟩
  set X := Sec4.thetaQuotCentralizer L ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) with hX
  have hXL : X ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans (Sec6.thetaQuotCentralizer_le_normalizer L)
  have hXθ : ∀ a ∈ X, ∀ x ∈ θL, a * x * a⁻¹ ∈ θL := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta L (hXL ha)) x).mp hx
  have hXz : X ≤ Subgroup.normalizer ((Subgroup.zpowers z ⊔ θL : Subgroup G) : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h1 : z⁻¹ * (a * z * a⁻¹) ∈ θL :=
        (Sec6.mem_thetaQuotCentralizer_iff.mp ha.1).2 z hzL
      have h2 : a * z * a⁻¹ ∈ Subgroup.zpowers z ⊔ θL := by
        rw [show a * z * a⁻¹ = z * (z⁻¹ * (a * z * a⁻¹)) by group]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) h1
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ h2 n
    · intro a ha x hx
      exact Subgroup.mem_sup_right (hXθ a ha x hx)
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := by
    have hYeq : Y = Subgroup.zpowers c ⊔ (Subgroup.zpowers z ⊔ θL) := by
      rw [hY, hF, sup_assoc]
    rw [hYeq]
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp ha.2 x).mp hx)
    · intro a ha x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hXz ha) x).mp hx)
  refine (Sec18.le_sup_normalizer_of_isSylowOf hSyl hXY).trans (sup_le (sup_le ?_ ?_) hFN)
  · exact hFE.trans (le_of_mem_scriptM_gamma hE hctx.mem_scriptM)
  · exact (Sec6.theta_le L).trans hLM

end Step1916Proof2

open Step1916Proof2

theorem step1916D_of
    (h1913 : Step1913) : Step1916D := by
  intro G _ _ A c L E M hctx
  exact card_inf_eq_nine hctx (lBar_facts h1913 hctx).2.2

theorem step1916_of
    (h1913 : Step1913) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
      Ctx1912 G A c L E M → L ≤ M →
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ M := by
  intro G _ _ A c L E M hctx hLM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hL3⟩ := lBar_facts h1913 hctx
  have hE := isE27_E hctx
  have hOut := outThreeClosed_thetaQuot h1913 hctx
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    Step1914TriProof.normalizer_zpowers_le_of_three_dvd hctx hL3
  set S : Set G := {y | y ∈ H ∧ ∃ k : ℕ, y ^ 3 ^ k = 1} with hSdef
  set K := Subgroup.closure S with hKdef
  have hKH : K ≤ H := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hSN : S ⊆ Subgroup.normalizer (L : Set G) := fun y hy => hHL hy.1
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun a ha x hx => ?_
    have hle : K ≤ K.comap (MulAut.conj a).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun y hy => Subgroup.subset_closure ?_
      obtain ⟨hyH, k, hk⟩ := hy
      refine ⟨H.mul_mem (H.mul_mem ha hyH) (H.inv_mem ha), k, ?_⟩
      change (a * y * a⁻¹) ^ 3 ^ k = 1
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    exact hle hx
  have hEH : E ≤ H := hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c)
  obtain ⟨Q, hEQ⟩ := (hE.isPGroup.comap_subtype (K := H)).exists_le_sylow
  set P₀ : Subgroup G := (Q : Subgroup H).map H.subtype with hP₀
  have hP₀H : IsSylowOf 3 P₀ H := ⟨Q, rfl⟩
  have hEP₀ : E ≤ P₀ := fun e he => ⟨⟨e, hEH he⟩, hEQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  have hP₀3 : IsPGroup 3 P₀ := hP₀H.isPGroup
  have hP₀K : P₀ ≤ K := by
    intro x hx
    refine Subgroup.subset_closure ⟨hP₀H.le hx, ?_⟩
    obtain ⟨k, hk⟩ := hP₀3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨Q₀, hQ₀⟩ := hP₀H.of_le hP₀K hKH
  have hNP₀ : Subgroup.normalizer (P₀ : Set G) ≤ M :=
    rank3II_19_3 hctx.hyp191 hE hctx.mem_scriptM hEP₀
      (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hP₀3 _)
  set W := L ⊔ Sec4.thetaQuotCentralizer L with hW
  have hNW : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro a ha x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp ha x).mp hx)
    · intro a ha x hx
      exact Subgroup.mem_sup_right (Sec6.conj_mem_thetaQuotCentralizer hx ha)
  have hLH : L ≤ H := by
    have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := by
      obtain ⟨L', -, hL'⟩ := hctx.mem_lA.1
      rw [← hL']
      exact Subgroup.map_subtype_le _
    exact hLC.trans (centralizer_le_normalizer_zpowers c)
  have hKWM : K ⊓ W ≤ M := by
    intro x ⟨hxK, hxW⟩
    have hxW' : x ∈ ((L ⊔ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := hxW
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _
      (Sec6.thetaQuotCentralizer_le_normalizer L)] at hxW'
    obtain ⟨l, hl, y, hy, rfl⟩ := hxW'
    have hyH : y ∈ H := by
      have := H.mul_mem (H.inv_mem (hLH hl)) (hKH hxK)
      simpa using this
    exact M.mul_mem (hLM hl) (centralizer_inf_le hctx hL3 hLM ⟨hy, hyH⟩)
  have hKW : K ≤ (Q₀ : Subgroup K).map K.subtype ⊔ (K ⊓ W) :=
    Sec6.le_sylow_sup_of_forall_pow_mem inf_le_left
      ((le_inf Subgroup.le_normalizer ((Subgroup.closure_le _).mpr hSN |>.trans hNW)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      (fun y hy => by
        obtain ⟨k, hk⟩ := Step196Proof.exists_pow_mem_sup hOut hSN (fun y hy => hy.2) hy
        exact ⟨k, K.pow_mem hy _, hk⟩) Q₀
  rw [hQ₀] at hKW
  have hKM : K ≤ M := hKW.trans (sup_le (Subgroup.le_normalizer.trans hNP₀) hKWM)
  exact (Sec18.le_sup_normalizer_of_isSylowOf ⟨Q₀, hQ₀⟩ hHK).trans (sup_le hKM hNP₀)

end CFSG.RankThree.PartTwo.Sec19
