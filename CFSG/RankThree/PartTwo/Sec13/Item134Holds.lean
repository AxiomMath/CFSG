module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Holds134.isQuasisimple_of_isSimpleGroup_of_nonabelian {Q : Type*} [Group Q]
    (hQ : IsSimpleGroup Q) (hnab : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  have hc : Subgroup.center Q = ⊥ := by
    rcases hQ.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, @MulEquiv.isSimpleGroup _ _ _ _ hQ e, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases hQ.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hmem : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem nonempty_thetaQuot_equiv_j2 (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hspor : SporadicModels131) {K : Subgroup G}
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨-, -, -, hJ2z⟩ := hspor
  obtain ⟨e⟩ := hK
  have hc0 : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := center_eq_bot_of_mulEquiv e hJ2z
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.J2, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hall y x
    rw [hJ2z] at htop
    obtain ⟨x, hx⟩ := @exists_ne _ hJs.toNontrivial (1 : CFSG.Blueprint.NativeSporadic.J2)
    exact hx ((Subgroup.mem_bot).mp (htop ▸ Subgroup.mem_top x))
  have hQs : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := @MulEquiv.isSimpleGroup _ _ _ _ hJs e
  have hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K) := by
    refine Holds134.isQuasisimple_of_isSimpleGroup_of_nonabelian hQs ?_
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (Sec14.aschbacherSolvableCore_eq_pCore_two hq hc0)).trans e⟩

theorem card_inf_eq_nine_of_j2 (h131 : Item131) (hspor : SporadicModels131) {A L : Subgroup G}
    {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hspor' := hspor
  obtain ⟨-, -, -, hJ2z⟩ := hspor'
  obtain ⟨φ⟩ := hJ
  have hcL : c ∉ L := not_mem_of_center_eq_bot h (center_eq_bot_of_mulEquiv φ hJ2z)
  refine ⟨hcL, ?_⟩
  obtain ⟨-, -, h9 | hPGL⟩ := facts_of_not_mem h131 hspor slTwoCenter h hcL
  · exact h9
  · exfalso
    obtain ⟨p, e, hp, -, hiso⟩ := (facts_of_isZ3PGLThreePi h hPGL).1
    apply KFacts.KS14.ks17J2NotList.1 p e
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩

theorem lA_eq_singleton_of_j2 (h131 : Item131) (hspor : SporadicModels131) {A L : Subgroup G}
    {c : G} (h : Sec13Data G A c L) {a : G} (ha : Subgroup.zpowers a ∈ omegaA A)
    {La : Subgroup G} (hLa : La ∈ lA A a)
    (hJa : Nonempty (La ⧸ aschbacherSolvableCore 3 La ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    lA A a = {La} := by
  have hDa : Sec13Data G A a La := { h with zpowers_mem_omegaA := ha, mem_lA := hLa }
  obtain ⟨-, h9⟩ := card_inf_eq_nine_of_j2 h131 hspor hDa hJa
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hLa, fun L' hL' => ?_⟩
  by_contra hne
  have hle : A ⊓ La ≤ Subgroup.zpowers a := by
    intro x hx
    have hx' : x ∈ ((A ⊓ Sec4.thetaQuotCentralizer L' : Subgroup G) : Set G) :=
      ⟨hx.1, Sec12.mem_thetaQuotCentralizer_of_ne hLa.1 hL'.1 (Ne.symm hne) hx.2 (hL'.2.1 hx.1)⟩
    rw [← sectionCentralizer_eq_inf hL'.2.1, hL'.2.2.1] at hx'
    exact hx'
  have h3 := Subgroup.card_le_of_le hle
  rw [h9, hDa.card_zpowers] at h3
  omega

end Helpers

theorem item134Arg128_of_sec12StdBar (h128 : Sec12.Item128BarAt) (h131 : Item131)
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) (h45 : Sec4.Item4_5)
    (h422 : Sec4.Item4_22) (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hstd : Sec12.Sec12StdBar G A d K) :
    omegaA A = {Subgroup.zpowers c} ∨
    CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
      IsSylowOf 3 (oThreeWStar A) (wStar A) ∧
      ((omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧ (omegaA A).ncard = 3) ∨
        ∃ I ∈ thetaComponentsAt 3 d, d ∈ I ∧
          Sec4.IsTripleCover (I ⧸ aschbacherSolvableCore 3 I) (alternatingGroup (Fin 6)) ∧
          ∃ a ∈ A ⊓ K, a ∉ Subgroup.zpowers d ∧
            omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
              orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 ∧
            ∃ La : Subgroup G, lA A a = {La} ∧
              Nonempty (La ⧸ aschbacherSolvableCore 3 La ≃*
                CFSG.Blueprint.NativeSporadic.J2)) := by
  right
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.isElemAbelian
  have h27 := h.card_eq
  have hAE := h.mem_partTwoE
  have hAF := h.mem_partTwoF
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcA := h.mem_A
  have hAa : ∀ {x : G}, x ∈ A → A ≤ Subgroup.centralizer ({x} : Set G) := fun hx y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hy hx)
  obtain ⟨hdK, hB, hB9, hsup⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have hZK : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3 := hA6.1
  have hAK9 : Nat.card (A ⊓ K : Subgroup G) = 9 :=
    Sec12.card_inf_eq_nine_bar hstd.isE27 hdA hd1 hdK hKd hZK hB9 hsup
  have hdcard : Nat.card (Subgroup.zpowers d) = 3 := card_zpowers_of_pow_three hd3 hd1
  have hBK : A ⊓ Sec4.thetaQuotCentralizer K ⊓ K ≤ Subgroup.zpowers d := by
    have hB3 : IsPGroup 3 (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) := fun x =>
      ⟨1, Subtype.ext (by simpa using hAe.2 x x.2.1)⟩
    have h1 := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := K)
    rw [hZK] at h1
    have hdmem : d ∈ A ⊓ Sec4.thetaQuotCentralizer K ⊓ K :=
      ⟨⟨hdA, Sec12.mem_thetaQuotCentralizer_of_central hdK hKd⟩, hdK⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdmem)
      (by rw [hdcard]; exact h1)).symm.le
  have hcd : c ∉ Subgroup.zpowers d := by
    intro hc
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Subgroup.zpowers d :=
      sup_le (Subgroup.zpowers_le.mpr hc) le_rfl
    have := Subgroup.card_le_of_le hle
    rw [← hB, hB9, hdcard] at this
    omega
  obtain ⟨P, hP, hPB⟩ := hstd.exists_sylow
  obtain ⟨hPaut, hP9⟩ := Sec12.autIn_eq_transvectionGroup_bar h45 hstd hZK
    (fun T _ hT9 _ => KFacts.exists_normalizer_moves_of_isTripleCover_alt
      (Sec12.isQuasisimple_thetaQuot_of_mem hK) (Or.inl hA6) T hT9) hP hPB
  set T := Sec12.transvectionGroup A ⟨d, hdA⟩ with hTdef
  have hT9 : Nat.card T = 9 := hPaut ▸ hP9
  have hT3 : 3 < Nat.card T := by rw [hT9]; norm_num
  have hPW : IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) := by
    rw [← inf_eq_left.mpr hW]
    exact hP
  have hTsyl : IsSylowOf 3 T (wStar A) := hPaut ▸ Holds134.isSylowOf_autIn_wStar hPW
  have hTn : ∀ g ∈ wStar A, ∀ σ ∈ T, g * σ * g⁻¹ ∈ T := by
    intro g hg σ hσ
    obtain ⟨w, hwN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hg
    refine Holds134.conj_mem (fun y => ?_) hσ
    rw [Sec12.mem_zpowers_subtype_iff, Sec12.mem_zpowers_subtype_iff,
      Sec4.normalizerMonoidHom_apply_coe]
    exact Subgroup.mem_normalizer_iff.mp (hW hwN) y
  have hO3 : oThreeWStar A = T := Holds134.oThreeWStar_eq_of_normal hTsyl hTn
  have horb : ∀ {x : G}, x ∈ A → x ∉ Subgroup.zpowers d →
      orbitIn (oThreeWPre A) (Subgroup.zpowers x) =
        pointsOff (Subgroup.zpowers x ⊔ Subgroup.zpowers d) (Subgroup.zpowers d) :=
    fun hxA hxd => Holds134.orbitIn_eq_pointsOff hAe h27 hdA hd1 hO3 hPaut hT3 hxA hxd
  have hncard : ∀ {x : G}, x ∈ A → x ∉ Subgroup.zpowers d →
      (orbitIn (oThreeWPre A) (Subgroup.zpowers x)).ncard = 3 := fun hxA hxd => by
    rw [horb hxA hxd]
    exact Holds134.ncard_pointsOff_zpowers hAe hdA hd1 hxA hxd
  have horbΩ : ∀ F ∈ omegaA A, orbitIn (oThreeWPre A) F ⊆ omegaA A := by
    rintro F hF _ ⟨w, hw, rfl⟩
    exact (map_conj_mem_omegaA_iff (Subgroup.map_subtype_le _ hw)).mpr hF
  have hdΩ : Subgroup.zpowers d ∉ omegaA A := by
    intro hdΩ
    obtain ⟨I, hIc, hAN', hsc', -⟩ := item13SetupAt_of h422 h45 G h.toPartTwoStanding
      h.partTwoS_eq A hAF h.not_mem_partTwoT d hdΩ
    have hIeq : A ⊓ Sec4.thetaQuotCentralizer I = Subgroup.zpowers d := by
      have h1 := sectionCentralizer_eq_inf hAN'
      rw [hsc'] at h1
      exact (SetLike.coe_injective h1).symm
    by_cases hKI : K = I
    · subst hKI
      rw [hIeq, hdcard] at hB9
      omega
    · have hle : A ⊓ K ≤ Subgroup.zpowers d := by
        intro x hx
        rw [← hIeq]
        exact ⟨hx.1, Sec12.mem_thetaQuotCentralizer_of_ne hK hIc hKI hx.2 (hAN' hx.1)⟩
      have := Subgroup.card_le_of_le hle
      rw [hAK9, hdcard] at this
      omega
  have hpt : ∀ {e : G}, Subgroup.zpowers e ∈ omegaA A → e ∈ A ∧ e ∉ Subgroup.zpowers d := by
    intro e he
    obtain ⟨heA, he3, -⟩ := zpowers_mem_omegaA_iff.mp he
    refine ⟨heA, fun hed => hdΩ ?_⟩
    have heq : Subgroup.zpowers e = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hed) (by rw [he3, hdcard])
    exact heq ▸ he
  have hty : Sec4.IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K) ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) CFSG.Blueprint.NativeSporadic.M22 :=
    Or.inr (Or.inl hA6)
  have hmemOff : ∀ {X : Subgroup G} {e : G}, e ∈ X → e ∉ Subgroup.zpowers d →
      Nat.card (Subgroup.zpowers e) = 3 →
      Subgroup.zpowers e ∈ pointsOff X (Subgroup.zpowers d) := fun heX hed he3 =>
    ⟨Subgroup.zpowers_le.mpr heX, he3, fun hle => hed (hle (Subgroup.mem_zpowers _))⟩
  have h128' := (h128 G A d K hstd hAE hty).resolve_left h.not_mem_partTwoT
  have hcase : ∀ F ∈ omegaA A, F ∈ orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∨
      ∃ e ∈ K, F = Subgroup.zpowers e := by
    intro F hF
    obtain ⟨-, hF3, e, rfl, -⟩ := id hF
    obtain ⟨heA, hed⟩ := hpt hF
    rcases (h128' e hF).1 with ⟨heK, -⟩ | ⟨heK, -⟩
    · left
      rw [horb hcA hcd, ← hB]
      exact hmemOff ⟨heA, heK⟩ hed hF3
    · exact Or.inr ⟨e, heK, rfl⟩
  have hTab : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) := by
    rw [hO3]
    exact Holds134.isElemAbelian (Subtype.ext hd3)
  refine ⟨hTab, by rw [hO3, hT9], hO3 ▸ hTsyl, ?_⟩
  by_cases hex : ∃ a : G, Subgroup.zpowers a ∈ omegaA A ∧ a ∈ K
  ·
    right
    obtain ⟨a, ha, haK⟩ := hex
    obtain ⟨haA, had⟩ := hpt ha
    obtain ⟨hcase', hHJ⟩ := h128' a ha
    rcases hcase' with ⟨haC, -⟩ | ⟨-, hAKa, I, hI, -, hIA6, hdI, -⟩
    · exact absurd (hBK ⟨⟨haA, haC⟩, haK⟩) had
    have horba : orbitIn (oThreeWPre A) (Subgroup.zpowers a) =
        pointsOff (A ⊓ K) (Subgroup.zpowers d) := by
      rw [horb haA had, hAKa]
    have hΩ : omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
        orbitIn (oThreeWPre A) (Subgroup.zpowers a) := by
      apply le_antisymm
      · intro F hF
        rcases hcase F hF with hFc | ⟨e, heK, rfl⟩
        · exact Or.inl hFc
        · right
          obtain ⟨heA, hed⟩ := hpt hF
          rw [horba]
          exact hmemOff ⟨heA, heK⟩ hed hF.2.1
      · exact Set.union_subset (horbΩ _ h.zpowers_mem_omegaA) (horbΩ _ ha)
    have hdisj : Disjoint (orbitIn (oThreeWPre A) (Subgroup.zpowers c))
        (orbitIn (oThreeWPre A) (Subgroup.zpowers a)) := by
      rw [horb hcA hcd, horba, ← hB]
      refine Set.disjoint_left.mpr fun F hF hF' => hF.2.2 ?_
      exact (le_inf hF.1 hF'.1).trans
        ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans hBK)
    obtain ⟨La, hLa⟩ := Sec12.exists_mem_lA422 h422 h45 h.toPartTwoStanding hAF h27 ha
    have hLaA : La ∈ lA A a := Sec12.mem_lA_of_mem_lA422 (hAa haA) hLa
    have hJa := nonempty_thetaQuot_equiv_j2 hJs hspor (hHJ La hLa)
    refine ⟨I, hI, hdI, hIA6, a, ⟨haA, haK⟩, had, hΩ, ?_, La,
      lA_eq_singleton_of_j2 h131 hspor h ha hLaA hJa, hJa⟩
    rw [hΩ, Set.ncard_union_eq hdisj, hncard hcA hcd, hncard haA had]
  ·
    left
    push Not at hex
    have hΩ : omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) := by
      apply le_antisymm
      · intro F hF
        rcases hcase F hF with hFc | ⟨e, heK, rfl⟩
        · exact hFc
        · exact absurd heK (hex e hF)
      · exact horbΩ _ h.zpowers_mem_omegaA
    exact ⟨hΩ, by rw [hΩ, hncard hcA hcd]⟩

theorem sec12StdBar_of_exists_sylow (h131 : Item131) (hspor : SporadicModels131)
    (h415 : Sec4.Item4_15) {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}
    (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hP : ∃ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) ∧
      ¬ Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype) :
    Sec12.Sec12StdBar G A d K := by
  obtain ⟨hdK, heq, h9, hsup⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
  obtain ⟨P, hP, hPB⟩ := hP
  exact
    { h.toPartTwoStanding with
      partTwoF_eq := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
      isE27 := ⟨h.isElemAbelian, h.card_eq⟩
      mem_A := hdA
      ne_one := hd1
      mem_thetaComponentsAt := hK
      mem_L := hdK
      card_B := h9
      sup_eq := hsup
      exists_sylow := ⟨P, hP, by rwa [heq]⟩ }

theorem item134Arg128_of_exists_sylow (h128 : Sec12.Item128BarAt) (h131 : Item131)
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) (h45 : Sec4.Item4_5)
    (h422 : Sec4.Item4_22) (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hP : ∃ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) ∧
      ¬ Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype) :
    omegaA A = {Subgroup.zpowers c} ∨
    CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
      IsSylowOf 3 (oThreeWStar A) (wStar A) ∧
      ((omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∧ (omegaA A).ncard = 3) ∨
        ∃ I ∈ thetaComponentsAt 3 d, d ∈ I ∧
          Sec4.IsTripleCover (I ⧸ aschbacherSolvableCore 3 I) (alternatingGroup (Fin 6)) ∧
          ∃ a ∈ A ⊓ K, a ∉ Subgroup.zpowers d ∧
            omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c) ∪
              orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6 ∧
            ∃ La : Subgroup G, lA A a = {La} ∧
              Nonempty (La ⧸ aschbacherSolvableCore 3 La ≃*
                CFSG.Blueprint.NativeSporadic.J2)) :=
  item134Arg128_of_sec12StdBar h128 h131 hspor h415 h45 h422 hJs h hJ hdA hd1 hS hK hLK hKeq
    hA6 hW (sec12StdBar_of_exists_sylow h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6 hP)

end CFSG.RankThree.PartTwo.Sec13
