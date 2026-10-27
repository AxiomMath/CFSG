module

public import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
public import CFSG.OddTranspositions.PartThree.Twelve.Ten
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open QuadraticMap

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isMarkedComponentSp_commSet_inter (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    IsMarkedComponentSp hC f (commSet D hC.d ∩ commSet D w) := by
  classical
  obtain ⟨k, F, _, _, _, hnk, hF, ⟨c⟩⟩ := exists_spChart hC hMZ hα hs hSp
  obtain ⟨Q, hpol, hQw, hgen⟩ :=
    exists_quadraticForm_commSet_inter hIH hC hMZ hα hs hn hf hSp c hnk hF hv hw hwd hwv
  have hZ := center_Hbar_eq_bot hC
  set R := CFSG.solvableRadical (Halpha D hC.alpha) with hRdef
  let ψ : (Halpha D hC.alpha ⧸ R) ≃* StatedSp k F :=
    (QuotientGroup.quotientMulEquivOfEq c.ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.ρ c.surjective)
  let e₀ : ((Halpha D hC.alpha ⧸ R) ⧸ Subgroup.center (Halpha D hC.alpha ⧸ R)) ≃*
      (Halpha D hC.alpha ⧸ R) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e := e₀.trans ψ
  have he : ∀ x : Halpha D hC.alpha, e (QuotientGroup.mk (QuotientGroup.mk x)) = c.ρ x :=
    fun x => rfl
  have hQsp : IsSpQuadForm (Q : (Fin k ⊕ Fin k → F) → F) :=
    ⟨fun a x => by rw [QuadraticMap.map_smul, smul_eq_mul, _root_.sq],
      fun x y => by rw [QuadraticMap.map_add Q x y, hpol]⟩
  set Γ := commSet D hC.d ∩ commSet D w with hΓdef
  have hle : Subgroup.closure Γ ≤ Halpha D hC.alpha :=
    (Subgroup.closure_le _).mpr fun z hz => mem_Halpha_of_mem_commSet hC hα hz.1
  have hsub : ∀ y ∈ Subgroup.closure Γ, ∀ hy : y ∈ Halpha D hC.alpha,
      c.ρ ⟨y, hy⟩ ∈ spOrthSubgroup (Q : (Fin k ⊕ Fin k → F) → F) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hyΓ =>
      intro hy
      have h1 : c.ρ ⟨y, hy⟩ = spTransvection (c.vec y) 1 := c.map_eq y hyΓ.1
      rw [h1, hQsp.spTransvection_mem_iff (c.vec_ne_zero y hyΓ.1), (hQw y hyΓ.1).mp hyΓ.2,
        one_pow, one_mul, CharTwo.add_self_eq_zero]
    | one =>
      intro hy
      exact (show c.ρ ⟨1, hy⟩ = 1 from c.ρ.map_one) ▸ Subgroup.one_mem _
    | mul y z hy hz ihy ihz =>
      intro hyz
      have h1 : (⟨y * z, hyz⟩ : Halpha D hC.alpha) = ⟨y, hle hy⟩ * ⟨z, hle hz⟩ := rfl
      rw [h1, map_mul]
      exact Subgroup.mul_mem _ (ihy (hle hy)) (ihz (hle hz))
    | inv y hy ihy =>
      intro hy'
      have h1 : (⟨y⁻¹, hy'⟩ : Halpha D hC.alpha) = (⟨y, hle hy⟩ : Halpha D hC.alpha)⁻¹ := rfl
      rw [h1, map_inv]
      exact Subgroup.inv_mem _ (ihy (hle hy))
  set L' : Subgroup (Halpha D hC.alpha) :=
    (Subgroup.closure Γ).comap (Halpha D hC.alpha).subtype with hL'def
  have hgenle : Subgroup.closure ((fun a => spTransvection a 1) '' {a | Q a = 1}) ≤
      L'.map c.ρ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Set.mem_setOf_eq, QuadraticMap.map_zero] at ha
      exact zero_ne_one ha
    obtain ⟨z, hz, rfl⟩ := c.exists_vec a ha0
    have hzΓ : z ∈ Γ := ⟨hz, (hQw z hz).mpr ha⟩
    exact ⟨⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩, Subgroup.subset_closure hzΓ, c.map_eq z hz⟩
  refine ⟨k, F, inferInstance, inferInstance, inferInstance, hF, e, Q, hQsp, ?_⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hsub _ hx x.2
  · intro hg
    obtain ⟨x, hx, rfl⟩ := hgenle (hgen g (mem_spOrthSubgroup.mp (SetLike.mem_coe.mp hg)))
    exact ⟨x, hx, he x⟩

theorem twelveTen_sp_stabilizers_of_commSet_inter (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    (∀ g ∈ Halpha D hC.alpha, g ∈ Subgroup.normalizer (hypLineGroup D hC.d w : Set G) →
      g ∈ hypLineGroup D hC.d w ∨ hC.d * g ∈ hypLineGroup D hC.d w) ∧
    Halpha D hC.alpha ⊓ Subgroup.centralizer {w} = hypLineGroup D hC.d w :=
  twelveTen_sp_stabilizers hC hMZ hs hn hf hSp hwd
    (isMarkedComponentSp_commSet_inter hIH hC hMZ hα hs hn hf hSp hv hw hwd hwv)

end CFSG.OddTranspositions.PartThree
