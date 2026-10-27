module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
public import Certificates.Certificate9950
public import Certificates.Certificate3086
public import Certificates.Certificate8174
public import Certificates.Certificate3139
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofBar
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.Asc83Table.GL23
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate2202
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Sporadic.Th.F2Spec
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

section PGroup

variable {X : Type*} [Group X]

theorem le_normalizer_of_card_nine {B P : Subgroup X} (hBP : B ≤ P) (hB : Nat.card B = 9)
    (hP : Nat.card P = 27) : P ≤ Subgroup.normalizer (B : Set X) := by
  have hidx : (B.subgroupOf P).index = 3 := by
    have := Subgroup.relIndex_mul_card B P
    rw [inf_eq_left.mpr hBP, hB, hP] at this
    change B.relIndex P = 3
    omega
  have hmin : (Nat.card P).minFac = 3 := by rw [hP]; norm_num
  have := Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  exact Subgroup.le_normalizer_of_normal_subgroupOf hBP

theorem mul_comm_of_conj_mem_zpowers {s x : X} (hs3 : s ^ 3 = 1) (hx3 : x ^ 3 = 1)
    (hmem : s * x * s⁻¹ ∈ Subgroup.zpowers x) : s * x = x * s := by
  have hcomm : s * x * s⁻¹ = x → s * x = x * s := fun h1 => by
    calc s * x = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [h1]
  rcases Sec13.eq_of_mem_zpowers_of_pow_three hx3 hmem with h0 | h1 | h2
  · have hx : x = 1 := by
      calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
        _ = 1 := by rw [h0]; group
    rw [hx]
    group
  · exact hcomm h1
  · apply hcomm
    have hconj : ∀ k : ℕ, s * x ^ k * s⁻¹ = x ^ (2 * k) := fun k => by
      rw [← conj_pow, h2, ← pow_mul]
    have hs3' : s * s * s = 1 := by rw [← pow_three']; exact hs3
    have e1 : x = x ^ 8 := by
      calc x = (s * s * s) * x * (s * s * s)⁻¹ := by rw [hs3']; group
        _ = s * (s * (s * x * s⁻¹) * s⁻¹) * s⁻¹ := by group
        _ = s * (s * x ^ 2 * s⁻¹) * s⁻¹ := by rw [h2]
        _ = s * x ^ (2 * 2) * s⁻¹ := by rw [hconj 2]
        _ = x ^ (2 * (2 * 2)) := by rw [hconj (2 * 2)]
    have e2 : x ^ 8 = x ^ 2 := by
      rw [show 8 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hx3, one_pow, one_mul]
    rw [e2] at e1
    have hx1 : x = 1 := by
      have : x * 1 = x * x := by rw [mul_one, ← sq]; exact e1
      exact (mul_left_cancel this).symm
    rw [h2, hx1]
    group

end PGroup

section M12

variable {G : Type} [Group G] [Finite G]

theorem false_of_m12
    (h45 : Sec4.Item4_5) (h125 : Item125BarTC) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {K : Subgroup G} (hK : K ∈ lA422 A a)
    (hcK : c ∈ K)
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hAH := Proof128.le_normalizer_zpowers_of_isElemAbelian hAe haA
  obtain ⟨-, ⟨hMp, hMZ⟩, -⟩ := Sec13.sporadicModels131
  obtain ⟨ψ⟩ := Proof128.nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hMp φ
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv ψ hMZ
  have haK : a ∉ K := Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1
  have h9 : Nat.card (A ⊓ K : Subgroup G) = 9 :=
    Proof128.card_inf_eq_nine hAe h27 hK.1 hK.2.1 hAH hMp φ
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set B : Subgroup K := (A ⊓ K).subgroupOf K with hBdef
  have hB9 : Nat.card B = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hBab : CFSG.Assembly.IsElemAbelian 3 B :=
    Sec13.isElemAbelian_of_injOn K.subtype K.subtype_injective.injOn
      (by rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
          exact Sec13.isElemAbelian_inf_right hAe K)
  obtain ⟨S, hBS⟩ := hBp.exists_le_sylow
  set Sb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    S.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = (S : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hHeis, -, E, F', A', t, -, -, hΔ, ⟨eE⟩, -, -, -⟩ :=
    Sec4.Sporadic.rank3II_4_14_local _ ⟨ψ⟩ Sb
  have hinjS := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three S.isPGroup'
  have hSb3 : ∀ x ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)), x ^ 3 = 1 := fun x hx =>
    congrArg Subtype.val (Sec13.pow_three_eq_one_of_mulEquiv (MulEquiv.refl _) hHeis.2.2 ⟨x, hx⟩)
  have hSb27 : Nat.card (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = 27 := hHeis.2.1
  set c' : K := ⟨c, hcK⟩ with hc'def
  have hc'B : c' ∈ B := Subgroup.mem_subgroupOf.mpr ⟨h.mem_A, hcK⟩
  have hc'S : c' ∈ (S : Subgroup K) := hBS hc'B
  have hcbS : π c' ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
    hSb ▸ Subgroup.mem_map_of_mem π hc'S
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 c h.mem_A)
  have hcb3 : π c' ^ 3 = 1 := by rw [← map_pow, hc'3, map_one]
  have hcb1 : π c' ≠ 1 := by
    intro h1
    apply h.ne_one
    have : c' = 1 := hinjS hc'S (Subgroup.one_mem _) (by rw [h1, map_one])
    exact congrArg Subtype.val this
  by_cases hZc : ∀ x ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)), x * π c' = π c' * x
  ·
    have hEmem : E ∈ {Y : Subgroup (K ⧸ aschbacherSolvableCore 3 K) |
        Y ≤ (Sb : Subgroup _) ∧ Nat.card Y = 9} := by
      rw [hΔ]
      exact Set.mem_insert _ _
    obtain ⟨hESb, hE9⟩ := hEmem
    have hE9' : Nat.card E = 3 ^ 2 := by rw [hE9]; norm_num
    have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
      ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hE9', fun x hx => hSb3 x (hESb hx)⟩
    have hcomm : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers (π c'), x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (hZc x (hESb hx)) k).eq
    have hcE : π c' ∈ E := by
      by_contra hcE
      have hinf : E ⊓ Subgroup.zpowers (π c') = ⊥ := by
        have hdvd : Nat.card (E ⊓ Subgroup.zpowers (π c') : Subgroup _) ∣ 3 := by
          have h1 := Subgroup.card_dvd_of_le
            (inf_le_right : E ⊓ Subgroup.zpowers (π c') ≤ Subgroup.zpowers (π c'))
          rwa [Sec13.card_zpowers_of_pow_three hcb3 hcb1] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          apply hcE
          have heq : E ⊓ Subgroup.zpowers (π c') = Subgroup.zpowers (π c') :=
            Subgroup.eq_of_le_of_card_ge inf_le_right
              (by rw [h3, Sec13.card_zpowers_of_pow_three hcb3 hcb1])
          have hmem : π c' ∈ E ⊓ Subgroup.zpowers (π c') := by
            rw [heq]
            exact Subgroup.mem_zpowers _
          exact hmem.1
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
      rw [hinf, Subgroup.card_bot, mul_one, hE9,
        Sec13.card_zpowers_of_pow_three hcb3 hcb1] at hcard
      have hsup : E ⊔ Subgroup.zpowers (π c') = (Sb : Subgroup _) :=
        Subgroup.eq_of_le_of_card_ge (sup_le hESb (Subgroup.zpowers_le.mpr hcbS))
          (by rw [hSb27, hcard])
      have hab := Sec13.isElemAbelian_sup hEab (Sec13.isElemAbelian_zpowers hcb3) hcomm
      rw [hsup] at hab
      have htop : Subgroup.center (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = ⊤ := by
        have := hab.1
        refine eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => ?_
        exact mul_comm' y x
      have h3 := hHeis.1.2.2.2
      rw [htop, Subgroup.card_top, hSb27] at h3
      norm_num at h3
    let f : QuaternionGroup 2 →* MulAut E :=
      (Sec4.autIn ⊤ E).subtype.comp (eE.symm.toMonoidHom.comp CFSG.RankThree.Asc83Table.quatHom)
    have hf : Function.Injective f :=
      Subtype.val_injective.comp (eE.symm.injective.comp
        CFSG.RankThree.Asc83Table.quatHom_injective)
    have hirr : Sec21.IsIrreducibleOn (Sec4.autIn ⊤ E) := by
      refine Sec13.isIrreducibleOn_of_order_four hEab hE9 (τ := f (QuaternionGroup.a 1))
        (eE.symm (CFSG.RankThree.Asc83Table.quatHom (QuaternionGroup.a 1))).2 ?_ ?_
      · rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
      · rw [← map_pow]
        intro h1
        have := hf (h1.trans (map_one f).symm)
        exact absurd this (by decide)
    set cE : E := ⟨π c', hcE⟩ with hcEdef
    have hcE3 : orderOf cE = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hcb3))
        (fun h1 => hcb1 (congrArg Subtype.val h1))
    have hD1 : Subgroup.zpowers cE ≠ ⊥ := by
      intro hbot
      have hmem : cE ∈ Subgroup.zpowers cE := Subgroup.mem_zpowers cE
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hcb1 (congrArg Subtype.val hmem)
    have hDtop : Subgroup.zpowers cE ≠ ⊤ := by
      intro htop
      have h1 := congrArg (fun H : Subgroup E => Nat.card H) htop
      simp only [Subgroup.card_top, Nat.card_zpowers, hcE3, hE9] at h1
      norm_num at h1
    obtain ⟨σ, hσT, hσD⟩ : ∃ σ ∈ Sec4.autIn ⊤ E,
        (Subgroup.zpowers cE).map σ.toMonoidHom ≠ Subgroup.zpowers cE := by
      by_contra hcon
      push Not at hcon
      rcases hirr _ hcon with h1 | h1
      · exact hD1 h1
      · exact hDtop h1
    obtain ⟨nb, hnbN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσT
    refine false_of_bar h45 h125 h hty ha3 hK.1 haK hcK hEab hE9 hcE hnbN ?_
    intro hmem
    apply hσD
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hσc : E.normalizerMonoidHom ⟨nb, hnbN⟩ cE ∈ Subgroup.zpowers cE :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by
        rw [Subgroup.coe_zpow, Sec4.normalizerMonoidHom_apply_coe]
        exact hk)⟩
    rw [MonoidHom.map_zpowers]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hσc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, MulEquiv.coe_toMonoidHom,
        MulEquiv.orderOf_eq])
  ·
    push Not at hZc
    obtain ⟨s, hsS, hsc⟩ := hZc
    have hinjB : Set.InjOn π (B : Set K) := hinjS.mono hBS
    have hBb9 : Nat.card (B.map π) = 9 := by rw [Sec13.card_map_eq_of_injOn π hinjB, hB9]
    have hBbS : B.map π ≤ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
      hSb ▸ Subgroup.map_mono hBS
    refine false_of_bar h45 h125 h hty ha3 hK.1 haK hcK (Sec13.isElemAbelian_map hBab π) hBb9
      (Subgroup.mem_map_of_mem π hc'B) (le_normalizer_of_card_nine hBbS hBb9 hSb27 hsS) ?_
    intro hmem
    exact hsc (mul_comm_of_conj_mem_zpowers (hSb3 s hsS) hcb3 hmem)

end M12

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC
