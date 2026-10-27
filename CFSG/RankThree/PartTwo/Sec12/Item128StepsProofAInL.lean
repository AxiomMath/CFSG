module

public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofAInLEnd
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLM12
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLFree
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSU
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128
public import Certificates.Certificate9950
public import Certificates.Certificate3086
public import Certificates.Certificate8174
public import Certificates.Certificate3139
public import Certificates.Certificate3029
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJM12
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
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
import CFSG.RankThree.PartTwo.KFacts.KS12OrderNineProof
import CFSG.RankThree.PartTwo.KFacts.KS12MovesM22
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.KFacts.K412Alternating
public import CFSG.RankThree.PartTwo.KFacts.KP4Aut
public import CFSG.RankThree.PartTwo.KFacts.KP4Gen
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import Certificates.Certificate13951
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

@[expose] def KS128SLAInLOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L → A ∈ partTwoE G →
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → a ∉ Sec4.thetaQuotCentralizer L →
    ∀ K ∈ lA422 A a, c ∈ K →
      ((Sec8.IsZ3PGLThreePi (lBarA a K A) ∧
          Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∨
        (Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)))) →
    ∀ F : Subgroup G, F ≤ K → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → c ∈ F →
      (∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v) →
    ∀ f ∈ F, ∀ hfN : f ∈ Subgroup.normalizer (L : Set G),
      (¬ ∃ y : L ⧸ aschbacherSolvableCore 3 L, thetaBarAct L ⟨f, hfN⟩ = MulAut.conj y) →
    ∀ d : G, d ∈ A → ∀ hdL : d ∈ L, a * d⁻¹ ∈ Sec4.thetaQuotCentralizer L →
      thetaBarAct L ⟨f, hfN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) ≠
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ →
      a ∈ L

namespace Item128StepsProof

open KS128NotHJSL
open KS128NotHJTC (le_normalizer_of_card_nine mul_comm_of_conj_mem_zpowers)

variable {G : Type} [Group G] [Finite G]

theorem false_of_pgl_of_not_mem (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hK9 : KFacts.KS12OrderNine) (hKT : KS125TypeCInvol)
    (hD : Item125Diag) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    (haL : a ∉ L) {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K) {x : G} (hxA : x ∈ A)
    (hx : Sec4.InducesTypeOn K x 3)
    (hR : ∀ F : Subgroup G, F ≤ K → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → c ∈ F →
      (∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v) →
      ∀ f ∈ F, ∀ hfN : f ∈ Subgroup.normalizer (L : Set G),
        (¬ ∃ y : L ⧸ aschbacherSolvableCore 3 L, thetaBarAct L ⟨f, hfN⟩ = MulAut.conj y) →
        ∀ d : G, d ∈ A → ∀ hdL : d ∈ L, a * d⁻¹ ∈ Sec4.thetaQuotCentralizer L →
          thetaBarAct L ⟨f, hfN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) ≠
            QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ → a ∈ L) :
    False := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hxc : x * c = c * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hxA⟩ ⟨c, h.mem_A⟩)
  obtain ⟨hZ, Fb, hFab, hF9, hcF, hT⟩ :=
    exists_heis_trans hK.1 hcK (hAe.2 c h.mem_A) h.ne_one hxc hx.1 hx
  obtain ⟨F, hFK, hFe, hF9', hcF', hT'⟩ := exists_lift_trans hcK (hAe.2 c h.mem_A) hFab hF9 hcF hT
  exact false_of_transitive_of_not_mem h45 hK2 hG1 hK9 hKT hD h hSL haA haB haL hK.1
    (Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1) hFK hFe hF9' hcF' hT'
    (hR F hFK hFe hF9' hcF' hT')

theorem false_of_m12_of_not_mem
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hK9 : KFacts.KS12OrderNine) (hKT : KS125TypeCInvol)
    (hD : Item125Diag) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    (haL : a ∉ L) {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K)
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12)
    (hR : ∀ F : Subgroup G, F ≤ K → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → c ∈ F →
      (∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v) →
      ∀ f ∈ F, ∀ hfN : f ∈ Subgroup.normalizer (L : Set G),
        (¬ ∃ y : L ⧸ aschbacherSolvableCore 3 L, thetaBarAct L ⟨f, hfN⟩ = MulAut.conj y) →
        ∀ d : G, d ∈ A → ∀ hdL : d ∈ L, a * d⁻¹ ∈ Sec4.thetaQuotCentralizer L →
          thetaBarAct L ⟨f, hfN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) ≠
            QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ → a ∈ L) :
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
    exact false_of_transitive_of_not_mem h45 hK2 hG1 hK9 hKT hD h hSL haA haB haL hK.1 haK hFK
      hFe hF9 hcF hT (hR F hFK hFe hF9 hcF hT)
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

end Item128StepsProof

open Item128StepsProof in
theorem ks128SLAInL_of_items
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves) (hG1 : Gap125NonCentralBar)
    (hK9 : KFacts.KS12OrderNine) (hKT : KS125TypeCInvol) (hD : Item125Diag)
    (hR : KS128SLAInLOuter) : KS128SLAInL := by
  intro G _ _ A c L h hAE hSL a ha haB K hK hcK hconf
  by_contra haL
  rcases hconf with hpgl | hm12
  · obtain ⟨x, hxA, -, hx⟩ := hpgl.2.2
    exact false_of_pgl_of_not_mem h45 hK2 hG1 hK9 hKT hD h hAE hSL ha haB haL hK hcK hxA hx
      (fun F hFK hF hF9 hcF hT f hfF hfN hout d hdA hdL had hmv =>
        hR G A c L h hAE hSL a ha haB K hK hcK (Or.inl hpgl) F hFK hF hF9 hcF hT f hfF hfN hout
          d hdA hdL had hmv)
  · obtain ⟨φ⟩ := hm12.1
    exact false_of_m12_of_not_mem h45 hK2 hG1 hK9 hKT hD h hAE hSL ha haB haL hK hcK φ
      (fun F hFK hF hF9 hcF hT f hfF hfN hout d hdA hdL had hmv =>
        hR G A c L h hAE hSL a ha haB K hK hcK (Or.inr hm12) F hFK hF hF9 hcF hT f hfF hfN hout
          d hdA hdL had hmv)

section Unconditional

theorem ks128SLAInL_of
    (hR : KS128SLAInLOuter) : KS128SLAInL :=
  ks128SLAInL_of_items Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves gap125NonCentralBar
    KFacts.ks12OrderNine Item125DiagSU.ks125TypeCInvol_closed
    (Item125DiagSU.item125Diag_of_item45 Sec4.rank3II_4_5) hR

theorem ks128NotHJFree_of_outer
    (hR : KS128SLAInLOuter) : KS128NotHJFree :=
  ks128NotHJFree_of_named (ks128SLAInL_of hR) ks128TypeCMove

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
