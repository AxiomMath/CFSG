module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec13.Item131bProofF
import CFSG.RankThree.PartTwo.Sec13.Item131bProofA6
import CFSG.RankThree.PartTwo.Sec13.Item131bProofK
import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (aschCore)

section Members

variable {G : Type} [Group G] [Finite G]

theorem mem_partTwoE_of_le_centralizer {X : Subgroup G} (hXe : CFSG.Assembly.IsElemAbelian 3 X)
    (hX27 : Nat.card X = 27) {a : G} (hXa : X ≤ Subgroup.centralizer ({a} : Set G))
    (h2 : 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)))) :
    X ∈ partTwoE G := by
  have hX3 : IsPGroup 3 X := fun g => ⟨1, Subtype.ext (by simpa using hXe.2 g g.2)⟩
  have hXN : X ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) :=
    Sec21.le_normalizer_theta (hXa.trans Subgroup.le_normalizer)
  have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Sec11.not_three_dvd_card_inSubgroup_theta _)
  obtain ⟨S, hSN, hS1⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    3 2 Nat.prime_three Nat.prime_two X _ hX3 hXN hcop h2
  exact ⟨hXe, hX27, _, hS1, S.isPGroup'.map _, hSN⟩

theorem exists_even_theta {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    ∃ a ∈ A, a ≠ 1 ∧ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))) := by
  by_contra hcon
  push Not at hcon
  have hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)))) := fun a ha ha1 =>
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (hcon a ha ha1))
  have hAS : A ∈ partTwoS G := by
    refine ⟨hD.mem_partTwoF, fun a ha ha1 => ?_, fun B hBA hB9 => ?_⟩
    · have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx ha)
      have hnorm := Sec21.le_normalizer_theta (hAa.trans Subgroup.le_normalizer)
      exact (hodd a ha ha1).of_dvd_nat (Subgroup.card_dvd_of_le
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm))
    · have hBne : B ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hB9
        omega
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hle : thetaT 3 B ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) :=
        iInf_le_of_le b (iInf_le_of_le hb (iInf_le_of_le hb1' le_rfl))
      exact (hodd b (hBA hb) hb1').of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rw [hD.partTwoS_eq] at hAS
  exact hAS

theorem normalizer_le_aschCore_self {F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) : Subgroup.normalizer (F : Set G) ≤ aschCore 2 3 F := by
  have h3 : 3 ≤ CFSG.Assembly.pRank 3 F :=
    Source.le_assembly_pRank Nat.prime_three le_rfl hF (by rw [hF27]; norm_num)
  refine le_sSup ⟨F, le_rfl, by omega, ?_, rfl⟩
  have hFC : F ⊓ Subgroup.centralizer (F : Set G) = F := by
    refine inf_of_le_left fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hF.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  rwa [hFC, sup_idem]

end Members

theorem exists_two_subgroup_of_mk {H : Type} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsPGroup 3 P) {R : Subgroup (H ⧸ aschbacherSolvableCore 3 H)} (hR1 : R ≠ ⊥)
    (hR2 : IsPGroup 2 R)
    (hPR : ∀ x ∈ P, QuotientGroup.mk' (aschbacherSolvableCore 3 H) x ∈
      Subgroup.normalizer (R : Set (H ⧸ aschbacherSolvableCore 3 H))) :
    ∃ U : Subgroup H, U ≠ ⊥ ∧ IsPGroup 2 U ∧ P ≤ Subgroup.normalizer (U : Set H) := by
  set N := aschbacherSolvableCore 3 H with hN
  set π := QuotientGroup.mk' N with hπ
  set T := R.comap π with hT
  have hTcard : Nat.card T = Nat.card N * Nat.card R :=
    QuotientGroup.card_preimage_mk N (R : Set (H ⧸ N))
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hR1 (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    rw [hTcard, hk]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      three_not_dvd_card_aschbacherSolvableCore) (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card T := by
    rw [hTcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hPT : P ≤ Subgroup.normalizer (T : Set H) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : π y ∈ R := hy
    show π (x * y * x⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hPR x hx) _).mp hy'
  obtain ⟨S, hSN, hS1⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    3 2 Nat.prime_three Nat.prime_two P T hP hPT hcop h2
  exact ⟨_, hS1, S.isPGroup'.map _, hSN⟩

section AltSix

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_conj_of_pow_three
    {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (htc : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) {σ : MulAut X} (hσ3 : σ ^ 3 = 1) :
    ∃ κ : X, σ = MulAut.conj κ ∧ κ ^ 3 = 1 := by
  obtain ⟨κ, hκ⟩ := KFacts.ks12OutInner X hq (Or.inl htc) σ ⟨1, by rw [pow_one]; exact hσ3⟩
  refine ⟨κ, hκ, ?_⟩
  have hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
    intro z hz
    have hdvd := Subgroup.orderOf_dvd_natCard _ hz
    rw [htc.1] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have h1 : MulAut.conj (κ ^ 3) = 1 := by rw [map_pow, ← hκ, hσ3]
  have hZ : κ ^ 3 ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
    have h2 := congrArg (fun f : MulAut X => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc y * κ ^ 3 = κ ^ 3 * y * (κ ^ 3)⁻¹ * κ ^ 3 := by rw [h2]
      _ = κ ^ 3 * y := by group
  have h9 := hZ3 _ hZ
  have h9' : κ ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul]; exact h9
  exact KFacts.pow_three_eq_one_of_isTripleCover (Or.inl htc) κ ⟨2, by norm_num; exact h9'⟩

theorem exists_two_subgroup_of_A6
    (h45 : Sec4.Item4_5) (hD : Sec13Data G A c L)
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) {E : Subgroup G} (hEle : E ≤ L ⊔ A)
    (hE : Sec12.Sec12StdBar G E c L) {L₀ : Subgroup G} (hL₀ : L₀ ∈ thetaComponentsAt 3 c)
    (hL₀6 : Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6))) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hD.mem_thetaComponentsAt
  have hne : L₀ ≠ L := by
    rintro rfl
    exact not_isTripleCover_six hty hL₀6
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hE.isE27.1
  have hE27 : Nat.card E = 27 := hE.isE27.2
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hEle.trans (sup_le (le_normalizer_zpowers_of_mem hL) hD.A_le_normalizer_zpowers)
  have hEN₀ : E ≤ Subgroup.normalizer (L₀ : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hD.toTheoremFourHyp hD.orderOf_eq hL₀ hE3
      hEH
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 :=
    Sec12.card_inf_eq_nine_bar hE.isE27 hE.mem_A hE.ne_one hE.mem_L hD.le_centralizer
      (card_center_eq_three hty) hE.card_B hE.sup_eq
  obtain ⟨e₀, he₀E, he₀L⟩ : ∃ e₀ ∈ E, e₀ ∉ L := by
    by_contra h
    push Not at h
    rw [inf_eq_left.mpr h, hE27] at hEL9
    norm_num at hEL9
  have hEJ : E ≤ Subgroup.zpowers e₀ ⊔ (E ⊓ L) := by
    have hJE : Subgroup.zpowers e₀ ⊔ (E ⊓ L) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr he₀E) inf_le_left
    have hdvd : Nat.card (Subgroup.zpowers e₀ ⊔ (E ⊓ L) : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le hJE
    have h9 : 9 ∣ Nat.card (Subgroup.zpowers e₀ ⊔ (E ⊓ L) : Subgroup G) :=
      hEL9 ▸ Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk] at h9
      norm_num at h9
    · rw [hk] at h9
      norm_num at h9
    · exfalso
      have heq : E ⊓ L = Subgroup.zpowers e₀ ⊔ (E ⊓ L) :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hk, hEL9]; norm_num)
      have hmem : e₀ ∈ Subgroup.zpowers e₀ ⊔ (E ⊓ L) :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers e₀)
      rw [← heq] at hmem
      exact he₀L hmem.2
    · exact (Subgroup.eq_of_le_of_card_ge hJE (by rw [hE27, hk]; norm_num)).ge
  have he₀N : e₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hEH he₀E
  set x₀ : HBar c := QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ⟨e₀, he₀N⟩ with hx₀
  have hx₀M : x₀ ∈ Subgroup.normalizer ((Sec12.lBar c L₀ : Subgroup (HBar c)) : Set (HBar c)) :=
    mk_mem_normalizer_lBar (hEN₀ he₀E)
  set σ := (Sec12.lBar c L₀).normalizerMonoidHom ⟨x₀, hx₀M⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨x₀, hx₀M⟩ : Subgroup.normalizer ((Sec12.lBar c L₀ : Subgroup (HBar c)) :
        Set (HBar c))) ^ 3 = 1 := by
      apply Subtype.ext
      have he₀3 : (⟨e₀, he₀N⟩ : Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hEe.2 e₀ he₀E)
      have : x₀ ^ 3 = 1 := by rw [hx₀, ← map_pow, he₀3, map_one]
      simpa using this
    rw [h1, map_one]
  obtain ⟨η, -⟩ := exists_lBarEquiv hL₀
  have hq : IsQuasisimple (Sec12.lBar c L₀) :=
    LocalCores.isQuasisimple_of_mulEquiv η (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL₀)
  have htc : Sec4.IsTripleCover (Sec12.lBar c L₀) (alternatingGroup (Fin 6)) :=
    isTripleCover_of_mulEquiv η hL₀6
  obtain ⟨κ, hκ, hκ3⟩ := exists_conj_of_pow_three hq htc hσ3
  have hconj : ∀ y : Sec12.lBar c L₀,
      x₀ * (y : HBar c) * x₀⁻¹ = (κ : HBar c) * y * (κ : HBar c)⁻¹ := by
    intro y
    have h := congrArg (fun f : MulAut (Sec12.lBar c L₀) => ((f y : Sec12.lBar c L₀) : HBar c)) hκ
    simp only [hσ, Sec4.normalizerMonoidHom_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  obtain ⟨R, hR1, hR2, hκR⟩ :=
    exists_two_subgroup_of_isTripleCover htc κ ⟨1, by rw [pow_one]; exact hκ3⟩
  set R' := R.map (Sec12.lBar c L₀).subtype with hR'
  have hx₀R : x₀ ∈ Subgroup.normalizer (R' : Set (HBar c)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨κ * r * κ⁻¹, (Subgroup.mem_normalizer_iff.mp hκR r).mp hr, ?_⟩
    rw [Subgroup.coe_subtype, hconj r]
    simp
  have hLR : ∀ g : Subgroup.normalizer (Subgroup.zpowers c : Set G), (g : G) ∈ L →
      QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) g ∈
        Subgroup.normalizer (R' : Set (HBar c)) := by
    intro g hg
    have hgL : QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) g ∈ Sec12.lBar c L :=
      ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    have h1 := lBar_commute_of_ne hL₀ hL hne r.2 hgL
    rw [Subgroup.coe_subtype, ← h1, mul_inv_cancel_right]
    exact ⟨r, hr, rfl⟩
  have hEN : E ≤ ((Subgroup.normalizer (R' : Set (HBar c))).comap
      (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))))).map
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype := by
    refine hEJ.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨e₀, he₀N⟩, hx₀R, rfl⟩
    · intro g hg
      exact ⟨⟨g, hEH hg.1⟩, hLR _ hg.2, rfl⟩
  have hE3' : IsPGroup 3 (E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    fun g => ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hEe.2 _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  have hR'1 : R' ≠ ⊥ := fun h =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective _ (Sec12.lBar c L₀).subtype_injective).mp h)
  obtain ⟨U, hU1, hU2, hEU⟩ := exists_two_subgroup_of_mk hE3' hR'1 (hR2.map _) fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hEN (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  refine ⟨U.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype, fun h => hU1
    ((Subgroup.map_eq_bot_iff_of_injective _ Subtype.coe_injective).mp h), hU2.map _,
    fun e he => ?_⟩
  exact Subgroup.le_normalizer_map _ ⟨⟨e, hEH he⟩, hEU (Subgroup.mem_subgroupOf.mpr he), rfl⟩

end AltSix

end CFSG.RankThree.PartTwo.Sec13.Item131bProof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Item131bProof

theorem step131bHeisE
    (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) : Step131bHeisE := by
  intro G _ _ A c L hD hH hty E hEle hE _
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hE.isE27.1
  have hE27 : Nat.card E = 27 := hE.isE27.2
  have hcL : c ∈ L := mem_of_isHeisCentral hD hH
  have hZ3 := card_center_eq_three hty
  have hEc : E ≤ Subgroup.centralizer ({c} : Set G) :=
    (hEle.trans inf_le_left).trans (sup_le hD.le_centralizer hD.A_le_centralizer)
  obtain ⟨a, haA, -, ha2⟩ := exists_even_theta hD
  by_cases hac : a ∈ Subgroup.zpowers c
  ·
    refine mem_partTwoE_of_le_centralizer hEe hE27 (fun e he => ?_) ha2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hac
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hec : Commute e c := Subgroup.mem_centralizer_singleton_iff.mp (hEc he)
    exact (hec.zpow_right k).eq
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 :=
    Sec12.card_inf_eq_nine_bar hE.isE27 hE.mem_A hE.ne_one hE.mem_L hD.le_centralizer hZ3
      hE.card_B hE.sup_eq
  have hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    not_isCyclic_of_nine_le (fun x hx => hEe.2 x hx.1) hE.card_B.ge
  have hEL : ¬ IsCyclic (E ⊓ L : Subgroup G) :=
    not_isCyclic_of_nine_le (fun x hx => hEe.2 x hx.1) hEL9.ge
  obtain ⟨F, hFle, hFe, hF27, hFC, hFL, hFa, hEF⟩ :=
    exists_F_of_heis hD hH hty hEle hEe hE27 hEC hEL haA hac
  have hFE : F ∈ partTwoE G := mem_partTwoE_of_le_centralizer hFe hF27 hFa ha2
  obtain ⟨hcF, hFC9, -, hFsup⟩ :=
    e_facts hD hty hcL (hFle.trans inf_le_left) hFe hF27 hFC hFL
  have hAF : A ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_heis hD (inf_le_zpowers hD hH hcL hZ3) (hFle.trans inf_le_right) hcF hFsup
  have hFS := sec12StdBar_of_heis hD hcL hFe hF27 hcF hFC9 hFsup hAF
  refine ⟨hEe, hE27, ?_⟩
  rcases Sec12.item1210BarS_of h128 h422 h45 G F c L hFS hFE hD.partTwoS_eq (type122_of hty)
    with hFT | ⟨-, L₀, hL₀, hL₀6, -⟩
  · obtain ⟨-, H₂, ⟨P, hP1, hP2, rfl⟩, hΓ⟩ := hFT
    exact ⟨P, hP1, hP2, hEF.trans ((normalizer_le_aschCore_self hFe hF27).trans hΓ)⟩
  · exact exists_two_subgroup_of_A6 h45 hD hty (hEle.trans inf_le_left) hE hL₀ hL₀6

end CFSG.RankThree.PartTwo.Sec13
