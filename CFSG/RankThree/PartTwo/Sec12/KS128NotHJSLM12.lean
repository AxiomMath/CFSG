module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLPGL
public import Certificates.Certificate9950
public import Certificates.Certificate3086
public import Certificates.Certificate8174
public import Certificates.Certificate3139
public import Certificates.Certificate3029
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJM12
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofBar
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
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
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagBasic
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

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open KS128NotHJTC (le_normalizer_of_card_nine mul_comm_of_conj_mem_zpowers)

theorem exists_conj_of_card_autIn {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hA : Nat.card (Sec4.autIn ⊤ E) = 48) {u v : X} (huE : u ∈ E) (hu1 : u ≠ 1)
    (hvE : v ∈ E) (hv1 : v ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E : Set X), n * u * n⁻¹ = v := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Aut := Sec4.autIn ⊤ E with hAut
  set u' : E := ⟨u, huE⟩ with hu'
  set v' : E := ⟨v, hvE⟩ with hv'
  have hu'1 : u' ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  have hv'1 : v' ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
  have hE3 : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hEc : ∀ x y : E, x * y = y * x := fun x y => hE.1.is_comm.comm x y
  have hord : orderOf u' = 3 := orderOf_eq_prime (hE3 u') hu'1
  obtain ⟨w, hw⟩ : ∃ w : E, w ∉ Subgroup.zpowers u' := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show (⊤ : Subgroup E) ≤ Subgroup.zpowers u' from
      fun x _ => hcon x)
    rw [Subgroup.card_top, Nat.card_zpowers, hord, hE9] at h1
    omega
  have hgen : Subgroup.zpowers u' ⊔ Subgroup.zpowers w = ⊤ := by
    have h9 := Sec4.card_zpowers_sup_zpowers (hE3 w) hord hw (hEc w u')
    exact Subgroup.eq_top_of_card_eq _ (by rw [h9, hE9])
  have hstab : Nat.card (MulAction.stabilizer Aut u') ≤ 6 := by
    have hmaps : ∀ σ : MulAction.stabilizer Aut u',
        ((σ : Aut) : MulAut E) w ∈ (Subgroup.zpowers u' : Set E)ᶜ := by
      intro σ hmem
      apply hw
      have hσu : ((σ : Aut) : MulAut E) u' = u' := σ.2
      have hσz : ∀ k : ℤ, ((σ : Aut) : MulAut E) (u' ^ k) = u' ^ k := fun k => by
        rw [map_zpow, hσu]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have : w = u' ^ k := ((σ : Aut) : MulAut E).injective (by rw [hσz, hk])
      rw [this]
      exact Subgroup.zpow_mem_zpowers u' k
    let f : MulAction.stabilizer Aut u' → ((Subgroup.zpowers u' : Set E)ᶜ : Set E) :=
      fun σ => ⟨((σ : Aut) : MulAut E) w, hmaps σ⟩
    have hf : Function.Injective f := by
      intro σ τ hστ
      have hw' : ((σ : Aut) : MulAut E) w = ((τ : Aut) : MulAut E) w := congrArg Subtype.val hστ
      have hσu : ((σ : Aut) : MulAut E) u' = u' := σ.2
      have hτu : ((τ : Aut) : MulAut E) u' = u' := τ.2
      have hle : Subgroup.zpowers u' ⊔ Subgroup.zpowers w ≤
          MonoidHom.eqLocus ((σ : Aut) : MulAut E).toMonoidHom
            ((τ : Aut) : MulAut E).toMonoidHom := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr hw')
        change ((σ : Aut) : MulAut E) u' = ((τ : Aut) : MulAut E) u'
        rw [hσu, hτu]
      apply Subtype.ext
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      exact hle (hgen ▸ Subgroup.mem_top x)
    calc Nat.card (MulAction.stabilizer Aut u')
        ≤ Nat.card ((Subgroup.zpowers u' : Set E)ᶜ : Set E) := Nat.card_le_card_of_injective f hf
      _ = 6 := by
        rw [Nat.card_coe_set_eq]
        have h1 := Set.ncard_add_ncard_compl (Subgroup.zpowers u' : Set E)
        rw [← Nat.card_coe_set_eq (Subgroup.zpowers u' : Set E), SetLike.coe_sort_coe,
          Nat.card_zpowers, hord, hE9] at h1
        omega
  have horb := Subgroup.card_mul_index (MulAction.stabilizer Aut u')
  rw [MulAction.index_stabilizer, hA] at horb
  have hO8 : 8 ≤ (MulAction.orbit Aut u').ncard := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (MulAction.stabilizer Aut u') * (MulAction.orbit Aut u').ncard ≤ 6 * 7 :=
      Nat.mul_le_mul hstab (by omega)
    omega
  have hsub : MulAction.orbit Aut u' ⊆ (Set.univ \ {1} : Set E) := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨Set.mem_univ _, fun h1 => hu'1 ?_⟩
    have h2 : ((σ : Aut) : MulAut E) u' = 1 := h1
    exact ((σ : Aut) : MulAut E).injective (by rw [h2, map_one])
  have hT8 : (Set.univ \ {1} : Set E).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hE9]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hT8]; exact hO8) (Set.toFinite _)
  have hv'O : v' ∈ MulAction.orbit Aut u' := by
    rw [heq]
    exact ⟨Set.mem_univ _, hv'1⟩
  obtain ⟨σ, hσ⟩ := hv'O
  obtain ⟨n, hnN, -, hnσ⟩ := Sec4.mem_autIn_iff.mp σ.2
  refine ⟨n, hnN, ?_⟩
  have h1 : ((σ : Aut) : MulAut E) u' = v' := hσ
  rw [← hnσ] at h1
  have h2 := congrArg Subtype.val h1
  rwa [Sec4.normalizerMonoidHom_apply_coe] at h2

variable {G : Type} [Group G] [Finite G]

theorem false_of_m12
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hM : KS128TypeCMove) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    (haL : a ∈ L) {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K)
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) :
    False := by
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
    have hA48 : Nat.card (Sec4.autIn ⊤ E) = 48 := by
      rw [Nat.card_congr eE.toEquiv]
      exact CFSG.RankThree.Asc83Table.card_GL23
    obtain ⟨F, hFK, hFe, hF9, hcF, hT⟩ := exists_lift_trans hcK (hAe.2 c h.mem_A) hEab hE9 hcE
      (fun u hu hu1 v hv hv1 => exists_conj_of_card_autIn hEab hE9 hA48 hu hu1 hv hv1)
    exact false_of_transitive h45 hK2 hG1 hM h hSL ha3 haB haL hK.1 haK hFK hFe hF9 hcF hT
  ·
    push Not at hZc
    obtain ⟨s, hsS, hsc⟩ := hZc
    have hinjB : Set.InjOn π (B : Set K) := hinjS.mono hBS
    have hBb9 : Nat.card (B.map π) = 9 := by rw [Sec13.card_map_eq_of_injOn π hinjB, hB9]
    have hBbS : B.map π ≤ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
      hSb ▸ Subgroup.map_mono hBS
    have hsN := le_normalizer_of_card_nine hBbS hBb9 hSb27 hsS
    have hscm : s * π c' * s⁻¹ ∉ Subgroup.zpowers (π c') := fun hmem =>
      hsc (mul_comm_of_conj_mem_zpowers (hSb3 s hsS) hcb3 hmem)
    rw [Sec13.normalizer_map_mk_eq hBp] at hsN
    obtain ⟨n, hn, rfl⟩ := hsN
    have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
    have hna : (n : G) * a = a * n := Subgroup.mem_centralizer_singleton_iff.mp (hKa n.2)
    have hnAK : (n : G) ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
      have h1 := Sec13.mem_normalizer_map_subtype hn
      rwa [hBdef, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    have hAsup : Subgroup.zpowers a ⊔ (A ⊓ K) = A :=
      eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left) le_sup_right h9
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haK h1.2)
    have hnA : (n : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnAK ⊢
      rw [← hAsup, Subgroup.map_sup, hnAK, MonoidHom.map_zpowers]
      congr 2
      change (n : G) * a * (n : G)⁻¹ = a
      rw [hna, mul_inv_cancel_right]
    have hnc : (n : G) * c * (n : G)⁻¹ ∉ Subgroup.zpowers c := by
      intro hmem
      apply hscm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have e1 : c' ^ k = n * c' * n⁻¹ := Subtype.ext (by simpa using hk)
      rw [← map_zpow, e1, map_mul, map_mul, map_inv]
    exact hnc ((Subgroup.mem_normalizer_iff.mp
      (normalizer_le_of_sec12StdBar_of_list h45 hK2 h (Or.inl hSL) hnA) c).mp
        (Subgroup.mem_zpowers c))

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL
