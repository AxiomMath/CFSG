module

public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStdInputs
public import CFSG.RankThree.PartTwo.Sec12.Coordinates
import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStd
import CFSG.RankThree.PartTwo.KFacts.K74Normal
import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTrans
public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Foundations
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Certificates.Certificate3029
import Certificates.Certificate3086
import Certificates.Certificate3139

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T52

open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def planeU1 (n1 : ZMod 3) : V3 := vsub (unitV 1) (vsmulR n1 (unitV 0))

@[expose] def planeU2 (n2 : ZMod 3) : V3 := vsub (unitV 2) (vsmulR n2 (unitV 0))

@[expose] def planeR (n1 n2 : ZMod 3) : R9 := ⟨0, 0, n2, n1, 0, 0, 0, n1 * n2, 0⟩

@[expose] def inSpanTwo (x u w : V3) : Bool :=
  vals.any fun α => vals.any fun β => x == vadd (vsmulR α u) (vsmulR β w)

@[expose] def inSpanThree (x u v w : V3) : Bool :=
  vals.any fun α => vals.any fun β => vals.any fun γ =>
    x == vadd (vsmulR α u) (vadd (vsmulR β v) (vsmulR γ w))

theorem plane_check : ∀ n1 ∈ vals, ∀ n2 ∈ vals, n1 ≠ 0 → n2 ≠ 0 →
    planeR n1 n2 ∈ n0Raw ∧ inSpanR (planeU2 n2) (planeU1 n1) = false ∧
    inSpanTwo (rmv (planeR n1 n2) (planeU1 n1)) (planeU1 n1) (planeU2 n2) = true ∧
    inSpanTwo (rmv (planeR n1 n2) (planeU2 n2)) (planeU1 n1) (planeU2 n2) = true ∧
    ∀ v ∈ allV3, inSpanTwo v (planeU1 n1) (planeU2 n2) = true ∨
      (inSpanThree (planeU1 n1) v (rmv (planeR n1 n2) v)
          (rmv (planeR n1 n2) (rmv (planeR n1 n2) v)) = true ∧
        inSpanThree (planeU2 n2) v (rmv (planeR n1 n2) v)
          (rmv (planeR n1 n2) (rmv (planeR n1 n2) v)) = true) := by
  decide

theorem exists_of_inSpanTwo {x u w : V3} (h : inSpanTwo x u w = true) :
    ∃ α β : ZMod 3, x = vadd (vsmulR α u) (vsmulR β w) := by
  simp only [inSpanTwo, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨α, -, β, -, h⟩ := h
  exact ⟨α, β, h⟩

theorem exists_of_inSpanThree {x u v w : V3} (h : inSpanThree x u v w = true) :
    ∃ α β γ : ZMod 3, x = vadd (vsmulR α u) (vadd (vsmulR β v) (vsmulR γ w)) := by
  simp only [inSpanThree, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨α, -, β, -, γ, -, h⟩ := h
  exact ⟨α, β, γ, h⟩

variable {G : Type} [Group G] {A : Subgroup G}

private theorem coordVec_mul (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (x y : A) :
    Sec12.coordVec f (x * y) = Sec12.coordVec f x + Sec12.coordVec f y := by
  simp [Sec12.coordVec]

private theorem coordVec_pow_val (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (x : A)
    (α : ZMod 3) : Sec12.coordVec f (x ^ α.val) = α • Sec12.coordVec f x := by
  rw [KFacts.coordVec_pow, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem mem_of_coordVec_eq_two (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {S : Subgroup G}
    {x y t : A} (hx : (x : G) ∈ S) (hy : (y : G) ∈ S) {α β : ZMod 3}
    (h : ofVec (Sec12.coordVec f t) =
      vadd (vsmulR α (ofVec (Sec12.coordVec f x))) (vsmulR β (ofVec (Sec12.coordVec f y)))) :
    (t : G) ∈ S := by
  have ht : t = x ^ α.val * y ^ β.val := by
    apply KFacts.coordVec_injective f
    apply ofVec_injective
    rw [h, coordVec_mul, coordVec_pow_val, coordVec_pow_val, ofVec_add, ofVec_smul, ofVec_smul]
  rw [ht, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  exact S.mul_mem (S.pow_mem hx _) (S.pow_mem hy _)

theorem mem_of_coordVec_eq_three (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {S : Subgroup G}
    {x y z t : A} (hx : (x : G) ∈ S) (hy : (y : G) ∈ S) (hz : (z : G) ∈ S) {α β γ : ZMod 3}
    (h : ofVec (Sec12.coordVec f t) =
      vadd (vsmulR α (ofVec (Sec12.coordVec f x)))
        (vadd (vsmulR β (ofVec (Sec12.coordVec f y))) (vsmulR γ (ofVec (Sec12.coordVec f z))))) :
    (t : G) ∈ S := by
  have ht : t = x ^ α.val * (y ^ β.val * z ^ γ.val) := by
    apply KFacts.coordVec_injective f
    apply ofVec_injective
    rw [h, coordVec_mul, coordVec_mul, coordVec_pow_val, coordVec_pow_val, coordVec_pow_val,
      ofVec_add, ofVec_add, ofVec_smul, ofVec_smul, ofVec_smul]
  rw [ht, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
    Subgroup.coe_pow]
  exact S.mul_mem (S.pow_mem hx _) (S.mul_mem (S.pow_mem hy _) (S.pow_mem hz _))

private theorem ofVec_coordVec_of_eq (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {b : A}
    {j : Fin 3} {n : ℕ}
    (h : f (Multiplicative.ofAdd (Pi.single 0 1)) ^ n * b =
      f (Multiplicative.ofAdd (Pi.single j 1))) :
    ofVec (Sec12.coordVec f b) = vsub (unitV j) (vsmulR (n : ZMod 3) (unitV 0)) := by
  have hc := congrArg (Sec12.coordVec f) h
  rw [coordVec_mul, KFacts.coordVec_pow] at hc
  have hv : Sec12.coordVec f b = Pi.single j 1 - (n : ZMod 3) • Pi.single 0 1 := by
    rw [Nat.cast_smul_eq_nsmul]
    have e0 : Sec12.coordVec f (f (Multiplicative.ofAdd (Pi.single 0 1))) = Pi.single 0 1 := by
      simp [Sec12.coordVec]
    have ej : Sec12.coordVec f (f (Multiplicative.ofAdd (Pi.single j 1))) = Pi.single j 1 := by
      simp [Sec12.coordVec]
    rw [e0, ej] at hc
    rw [← hc]
    abel
  rw [hv, ofVec_sub, ofVec_smul, ofVec_single, ofVec_single]
  rfl

theorem exists_raw_plane [Finite G] (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {B : Subgroup G}
    (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hpt : ∀ j : Fin 3, (f (Multiplicative.ofAdd (Pi.single j 1)) : G) ∉ B) :
    ∃ b₁ b₂ : A, (b₁ : G) ∈ B ∧ (b₂ : G) ∈ B ∧ b₁ ≠ 1 ∧ b₂ ∉ Subgroup.zpowers b₁ ∧
      ∃ R ∈ n0Raw,
        inSpanTwo (rmv R (ofVec (Sec12.coordVec f b₁))) (ofVec (Sec12.coordVec f b₁))
          (ofVec (Sec12.coordVec f b₂)) = true ∧
        inSpanTwo (rmv R (ofVec (Sec12.coordVec f b₂))) (ofVec (Sec12.coordVec f b₁))
          (ofVec (Sec12.coordVec f b₂)) = true ∧
        ∀ v ∈ allV3, inSpanTwo v (ofVec (Sec12.coordVec f b₁))
            (ofVec (Sec12.coordVec f b₂)) = true ∨
          (inSpanThree (ofVec (Sec12.coordVec f b₁)) v (rmv R v) (rmv R (rmv R v)) = true ∧
            inSpanThree (ofVec (Sec12.coordVec f b₂)) v (rmv R v) (rmv R (rmv R v)) = true) := by
  classical
  set p : Fin 3 → A := fun j => f (Multiplicative.ofAdd (Pi.single j 1))
  have hp0A : (p 0 : G) ∈ A := (p 0).2
  have hAB : A ⊓ B = B := inf_eq_right.mpr hBA
  have hsup : Subgroup.zpowers (p 0 : G) ⊔ B = A := by
    have h := Sec13.TransProof.sup_eq_of_card (L := B) h27 (by rw [hAB]; exact hB9) hp0A (hpt 0)
    rwa [hAB] at h
  have hp03 : (p 0 : G) ^ 3 = 1 := hAe.2 _ hp0A
  have hcomm : ∀ k ∈ B, (p 0 : G) * k = k * (p 0 : G) := fun k hk =>
    congrArg Subtype.val (hAe.1.is_comm.comm (p 0) ⟨k, hBA hk⟩)
  have hdec : ∀ j : Fin 3, ∃ n < 3, n ≠ 0 ∧ ∃ b : A, (b : G) ∈ B ∧ p 0 ^ n * b = p j := by
    intro j
    have hj : (p j : G) ∈ Subgroup.zpowers (p 0 : G) ⊔ B := by
      rw [hsup]
      exact (p j).2
    obtain ⟨n, hn, k, hk, hkj⟩ := Sec13.TransProof.exists_pow_mul_of_mem_sup' hp03 hcomm hj
    refine ⟨n, hn, ?_, ⟨k, hBA hk⟩, hk, Subtype.ext ?_⟩
    · rintro rfl
      apply hpt j
      rw [show (f (Multiplicative.ofAdd (Pi.single j 1)) : G) = (p j : G) from rfl, hkj, pow_zero,
        one_mul]
      exact hk
    · rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact hkj.symm
  obtain ⟨n₁, hn₁3, hn₁0, b₁, hb₁B, hb₁⟩ := hdec 1
  obtain ⟨n₂, hn₂3, hn₂0, b₂, hb₂B, hb₂⟩ := hdec 2
  have hv₁ := ofVec_coordVec_of_eq f hb₁
  have hv₂ := ofVec_coordVec_of_eq f hb₂
  have hz : ∀ n : ℕ, n < 3 → n ≠ 0 → (n : ZMod 3) ≠ 0 := by
    intro n hn hn0
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    interval_cases n <;> decide
  have hval : ∀ z : ZMod 3, z ∈ vals := by decide
  obtain ⟨hR, hind, hR₁, hR₂, hall⟩ :=
    plane_check _ (hval (n₁ : ZMod 3)) _ (hval (n₂ : ZMod 3)) (hz n₁ hn₁3 hn₁0) (hz n₂ hn₂3 hn₂0)
  have hu₁ : ofVec (Sec12.coordVec f b₁) = planeU1 (n₁ : ZMod 3) := hv₁
  have hu₂ : ofVec (Sec12.coordVec f b₂) = planeU2 (n₂ : ZMod 3) := hv₂
  refine ⟨b₁, b₂, hb₁B, hb₂B, ?_, ?_, planeR (n₁ : ZMod 3) (n₂ : ZMod 3), hR, ?_, ?_, ?_⟩
  · rintro rfl
    have h0 : ofVec (Sec12.coordVec f 1) = vzero := by
      rw [show Sec12.coordVec f 1 = 0 by simp [Sec12.coordVec], ofVec_zero]
    rw [h0] at hu₁
    revert hu₁
    have h1 : 1 ≤ n₁ := Nat.one_le_iff_ne_zero.mpr hn₁0
    interval_cases n₁ <;> decide
  · intro hmem
    rw [← KFacts.coordVec_mem_span_iff f, mem_span_iff_inSpanR, hu₁, hu₂, hind] at hmem
    exact Bool.false_ne_true hmem
  · rw [hu₁, hu₂]
    exact hR₁
  · rw [hu₁, hu₂]
    exact hR₂
  · rw [hu₁, hu₂]
    exact hall

end CFSG.RankThree.PartTwo.Sec15.Sylow155T52
