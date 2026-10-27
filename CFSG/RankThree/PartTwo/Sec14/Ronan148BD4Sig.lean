module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1420
import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Sec14.Item148StepFieldTypes
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofD4
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec11.Item112
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCentTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Res148BD4

theorem exists_signalizer148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {e : G} (he : e ∈ A)
    {K : Subgroup G} (hKY : K ≤ Y) (hKe : K ≤ Subgroup.centralizer ({e} : Set G))
    (hKΔ : K = deltaZero A (lB A) K) (hKO : ¬ K ≤ pPrimeCoreOf 3 Y) :
    ∃ D : Subgroup G, IsHyperplane A D ∧ e ∈ D ∧ ∃ W ∈ scriptQZero A (lB A), W ≤ K ∧
      W ≤ Subgroup.centralizer (D : Set G) ∧
      W ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (D : Set G)) ∧ ¬ W ≤ pPrimeCoreOf 3 Y := by
  have hA : Late.IsE27 A := h.isE27
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set O := pPrimeCoreOf 3 Y with hOdef
  obtain ⟨Q, hQK, hQO⟩ : ∃ Q ∈ collectionIn (scriptQZero A (lB A)) K, ¬ Q ≤ O := by
    by_contra hall
    push Not at hall
    apply hKO
    calc K = deltaZero A (lB A) K := hKΔ
      _ ≤ O := sSup_le hall
  obtain ⟨⟨hQ, hQA⟩, hQKle⟩ := hQK
  have hQinv : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) := hQ.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQinv.2.2
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQinv.2.1
  have hQcop : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    rw [hA.2, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
  obtain ⟨D, hD, hDO⟩ : ∃ D, IsHyperplane A D ∧
      ¬ ⁅Q ⊓ Subgroup.centralizer (D : Set G), A⁆ ≤ O := by
    by_contra hall
    push Not at hall
    apply hQO
    set N := Q ⊓ O with hNdef
    let U : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ N}
        mul_mem' := by
          rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
          refine ⟨Q.mul_mem hxQ hyQ, fun a ha => ?_⟩
          have hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
            intro n hn
            refine ⟨Q.mul_mem (Q.mul_mem hxQ hn.1) (Q.inv_mem hxQ), ?_⟩
            exact (Subgroup.mem_normalizer_iff.mp
              (le_normalizer_pPrimeCoreOf 3 Y (hQKle.trans hKY hxQ)) n).mp hn.2
          have h1 : x * y * a * (x * y)⁻¹ * a⁻¹ =
              x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹) := by group
          rw [h1]
          exact N.mul_mem (hxN _ (hy a ha)) (hx a ha)
        one_mem' := ⟨Q.one_mem, fun a ha => by simp⟩
        inv_mem' := by
          rintro x ⟨hxQ, hx⟩
          refine ⟨Q.inv_mem hxQ, fun a ha => ?_⟩
          have hxN : ∀ n ∈ N, x⁻¹ * n * x⁻¹⁻¹ ∈ N := by
            intro n hn
            refine ⟨Q.mul_mem (Q.mul_mem (Q.inv_mem hxQ) hn.1) (by simpa using hxQ), ?_⟩
            exact (Subgroup.mem_normalizer_iff.mp
              (le_normalizer_pPrimeCoreOf 3 Y (hQKle.trans hKY (Q.inv_mem hxQ))) n).mp hn.2
          have h1 : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ := by group
          rw [h1]
          exact hxN _ (N.inv_mem (hx a ha)) }
    have hQU : Q ≤ U := Proof1413Res3.le_of_forall_hyperplane hA hAQ hQ3 fun D' hD' _ => by
      intro x hx
      refine ⟨hx.1, fun a ha => ⟨?_, ?_⟩⟩
      · have h1 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
        rw [h1]
        exact Q.mul_mem hx.1 ((Subgroup.mem_normalizer_iff.mp (hAQ ha) _).mp (Q.inv_mem hx.1))
      · exact hall D' hD' (Subgroup.commutator_mem_commutator hx ha)
    rw [hQA]
    refine (Subgroup.commutator_le.mpr fun x hx a ha => ?_).trans (inf_le_right : N ≤ O)
    exact (hQU hx).2 a ha
  have heD : e ∈ D := by
    by_contra heD
    apply hDO
    have hC : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      exact Res7Sig.mem_centralizer_of_hyperplane148 hA hD he heD hx.2 (hKe (hQKle hx.1))
    have hbot : ⁅Q ⊓ Subgroup.centralizer (D : Set G), A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hC
    rw [hbot]
    exact bot_le
  set X := Q ⊓ Subgroup.centralizer (D : Set G) with hXdef
  set W := ⁅X, A⁆ with hWdef
  have hAD : A ≤ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
    intro a ha
    refine Ronan148N.mem_normalizer_centralizer148 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      have : a * d * a⁻¹ = d := by
        rw [hAc a ha d (hD.1 hd), mul_inv_cancel_right]
      rw [this]
      exact hd
    · intro hd
      have hdA : a * d * a⁻¹ ∈ A := hD.1 hd
      have h1 : d = a⁻¹ * (a * d * a⁻¹) * a := by group
      rw [h1]
      have h2 : a⁻¹ * (a * d * a⁻¹) * a = a * d * a⁻¹ := by
        rw [hAc (a⁻¹) (A.inv_mem ha) _ hdA]
        group
      rw [h2]
      exact hd
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAQ ha, hAD ha⟩
  have hWX : W ≤ X := by
    rw [hWdef, Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have h1 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [h1]
    exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hAX ha) _).mp (X.inv_mem hx))
  have hXQ : X ≤ Q := inf_le_left
  have hWQ : W ≤ Q := hWX.trans hXQ
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator hAX Subgroup.le_normalizer
  have hWqs : W ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ hWQ hAW
  have hXcop : Nat.Coprime (Nat.card A) (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXQ) hQcop
  have hWWA : W = ⁅W, A⁆ :=
    (CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime X A hXcop hAX).symm
  have hW0 : W ∈ scriptQZero A (lB A) := ⟨hWqs, hWWA⟩
  have hWK : W ≤ K := hWQ.trans hQKle
  have hWD : W ≤ Subgroup.centralizer (D : Set G) := hWX.trans inf_le_right
  refine ⟨D, hD, heD, W, hW0, hWK, hWD, ?_, hDO⟩
  exact (le_deltaZero hW0 (le_inf (hWK.trans hKY) hWD)).trans (hYB D hD)

theorem types148D4
    {A Y : Subgroup G} [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G}
    (hkt : KType148 A Y e K Le) {n : ℕ} (hn : 1 ≤ n)
    (hK2 : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n) :
    Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
      ¬ Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  rcases hkt.2 with ⟨heΩ, hLe, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · refine ⟨heΩ, hLe, fun ⟨ψ⟩ => ?_⟩
    have hc := Nat.card_congr (φ.trans ψ).toEquiv
    rw [KFacts.KS14.card_nativeJ2] at hc
    exact Main148.card_ne_of_isoLThreePi_two148 hn hK2 (Or.inl rfl) hc
  · exact ((isEmpty_mulEquiv_a7_of_isoLThreePi_two hn hK2).false φ).elim
  · refine ⟨heΩ, hLe, fun ⟨ψ⟩ => ?_⟩
    exact KFacts.KS14.ks17J2NotList.1 p (f * e') (isoLThreePi_of_mulEquiv148 ψ.symm hiso)
  · exact ((isEmpty_mulEquiv_a7_of_isoLThreePi_two hn hK2).false φ).elim
  · exact ((isEmpty_mulEquiv_l37_of_isoLThreePi_two hn hK2 h7).false φ).elim

theorem not_allPointsHJ148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {e : G}
    (heΩ : Subgroup.zpowers e ∈ omegaA A) {Le : Subgroup G} (hLe : Le ∈ lA A e)
    (hJ2 : ¬ Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ AllPointsHJ A := by
  intro hall
  obtain ⟨Le', hLe', ⟨ψ⟩⟩ := hall e heΩ
  have h3 : 3 ∣ Nat.card Le' := three_dvd_card_of_types148 (Or.inl ⟨ψ⟩)
  have heq : Le' = Le := (h.chosen136.2 e heΩ Le hLe).2 Le' hLe'.1 h3
  subst heq
  exact hJ2 ⟨ψ⟩

theorem not_innerOn148_of_inducesOuterTheta {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    {x : Γ} (hout : Sec4.InducesOuterTheta x S) : ¬ InnerOn148 S x := by
  rintro ⟨s, hs, hsx⟩
  obtain ⟨hx, hnot⟩ := hout
  apply hnot
  have heq : Sec4.compAction S ⟨x, hx⟩ = Sec4.compAction S ⟨s, Subgroup.le_normalizer hs⟩ := by
    ext y
    simp only [Sec4.compAction, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hsx y y.2
  rw [heq, Sec11.thetaQuotMulAut_compAction_of_mem S hs]
  exact ⟨_, rfl⟩

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
