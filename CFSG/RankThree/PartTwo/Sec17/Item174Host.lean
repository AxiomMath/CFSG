module

public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofTwo
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProof
import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec16.Proof165
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isPGroup_two_of_coprime {H : Type*} [Group H] [Finite H] {P Q : Subgroup H}
    (hP : IsPGroup 2 P) (hQ : Nat.Coprime 2 (Nat.card Q)) {x : H} (hxP : x ∈ P) (hxQ : x ∈ Q) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf x ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hxQ
  have hcop : Nat.Coprime (orderOf x) (Nat.card Q) := by
    rw [hm]
    exact Nat.Coprime.pow_left m hQ
  have h3 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  exact orderOf_eq_one_iff.mp h3

theorem exists_mem_normalizer_inv_mul_mem (hSz : KFacts.KPSz) (hR : TheoremFourHyp G)
    {T U O : Subgroup G} (hT2 : IsPGroup 2 T) (hU3 : ¬ 3 ∣ Nat.card U)
    (hsyl : CFSG.Open.fusionIsSylowIn 2 T U) (hOU : O ≤ U) (hOn : (O.subgroupOf U).Normal)
    (hOodd : Nat.Coprime 2 (Nat.card O))
    (hchar : Subgroup.centralizer (S4Free.oTwo (↥U ⧸ O.subgroupOf U) : Set (↥U ⧸ O.subgroupOf U))
      ≤ S4Free.oTwo (↥U ⧸ O.subgroupOf U)) :
    ∀ u ∈ U, ∃ n ∈ Subgroup.normalizer (stellmacherSub T : Set G), n⁻¹ * u ∈ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTU : T ≤ U := hsyl.1
  set N' : Subgroup ↥U := O.subgroupOf U with hN'
  set f : ↥U →* ↥U ⧸ N' := QuotientGroup.mk' N' with hf
  set incl : ↥T →* ↥U := Subgroup.inclusion hTU with hincl
  set ι : ↥T →* ↥U ⧸ N' := f.comp incl with hι
  have hN'card : Nat.Coprime 2 (Nat.card N') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOU).toEquiv]
    exact hOodd
  have hker : ∀ {Q : Subgroup ↥U}, IsPGroup 2 Q → ∀ x ∈ Q, x ∈ N' → x = 1 :=
    fun hQ x hxQ hxN => eq_one_of_isPGroup_two_of_coprime hQ hN'card hxQ hxN
  obtain ⟨P, hP⟩ := sylow_of_fusionIsSylowIn hsyl
  have hrange : incl.range = T.subgroupOf U := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr s.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hTU2 : IsPGroup 2 (T.subgroupOf U) := hP ▸ P.isPGroup'
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : incl t ∈ N' := (QuotientGroup.eq_one_iff (incl t)).mp ht
    have h2 : incl t ∈ T.subgroupOf U := hrange ▸ ⟨t, rfl⟩
    have h3 : incl t = 1 := hker hTU2 _ h2 h1
    exact Subgroup.inclusion_injective hTU (h3.trans (map_one incl).symm)
  have hsylQ : ∃ Q : Sylow 2 (↥U ⧸ N'), (Q : Subgroup _) = ι.range :=
    ⟨P.mapSurjective (QuotientGroup.mk'_surjective N'), by
      rw [Sylow.coe_mapSurjective, hι, MonoidHom.range_comp, hrange, hP]⟩
  have h3 : ¬ 3 ∣ Nat.card (↥U ⧸ N') :=
    fun h => hU3 (h.trans (Subgroup.card_quotient_dvd_card N'))
  have hadm : S4Free.IsAdmissibleHost ι :=
    S4Free.isAdmissibleHost_of_not_three_dvd h3 hinj hsylQ hchar
  set W := S4Free.stellmacherWSz.{0, 0} ↥T with hW
  have hWn : (W.map ι).Normal :=
    S4Free.stellmacherWSz_normal hadm ((hR.szSections hSz hU3).quotient N')
  set C' : Subgroup ↥U := W.map incl with hC'
  set N₀ : Subgroup ↥U := (W.map ι).comap f with hN₀
  haveI : N₀.Normal := Subgroup.Normal.comap hWn f
  have hC'N₀ : C' ≤ N₀ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have hC'2 : IsPGroup 2 C' := (hT2.to_subgroup W).map incl
  have hdec : ∀ y ∈ N₀, ∃ c ∈ C', c⁻¹ * y ∈ N' := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hy
    refine ⟨incl w, ⟨w, hw, rfl⟩, ?_⟩
    have : f (incl w) = f y := hwy
    exact (QuotientGroup.eq).mp this
  let PN : Sylow 2 ↥N₀ :=
    { toSubgroup := C'.subgroupOf N₀
      isPGroup' := hC'2.comap_subtype
      is_maximal' := by
        intro Q hQ hCQ
        refine le_antisymm (fun x hx => ?_) hCQ
        obtain ⟨c, hc, hcy⟩ := hdec (x : ↥U) x.2
        have hcN : (⟨c, hC'N₀ hc⟩ : ↥N₀) ∈ Q := hCQ (Subgroup.mem_subgroupOf.mpr hc)
        have hmem : (⟨c, hC'N₀ hc⟩ : ↥N₀)⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hcN) hx
        have hQ' : IsPGroup 2 (Q.map N₀.subtype) := hQ.map N₀.subtype
        have h1 : c⁻¹ * (x : ↥U) = 1 :=
          hker hQ' _ ⟨_, hmem, rfl⟩ hcy
        have h2 : (x : ↥U) = c := (inv_mul_eq_one.mp h1).symm
        exact Subgroup.mem_subgroupOf.mpr (h2 ▸ hc) }
  have hfrat := Sylow.normalizer_sup_eq_top PN
  have hPN : ((PN : Subgroup ↥N₀).map N₀.subtype) = C' := by
    change (C'.subgroupOf N₀).map N₀.subtype = C'
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC'N₀]
  rw [hPN] at hfrat
  have hsplit : ∀ u : ↥U, ∃ n ∈ Subgroup.normalizer (C' : Set ↥U), n⁻¹ * u ∈ N' := by
    intro u
    have hu : u ∈ Subgroup.normalizer (C' : Set ↥U) ⊔ N₀ := hfrat ▸ Subgroup.mem_top u
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hu
    obtain ⟨n, hn, y, hy, rfl⟩ := hu
    obtain ⟨c, hc, hcy⟩ := hdec y hy
    refine ⟨n * c, Subgroup.mul_mem _ hn (Subgroup.le_normalizer hc), ?_⟩
    rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCeq : C'.map U.subtype = stellmacherSub T := by
    rw [hC', Subgroup.map_map, Subgroup.subtype_comp_inclusion]
    rfl
  have hnorm : ∀ n ∈ Subgroup.normalizer (C' : Set ↥U),
      (n : G) ∈ Subgroup.normalizer (stellmacherSub T : Set G) := by
    intro n hn
    rw [← hCeq]
    exact Subgroup.le_normalizer_map U.subtype ⟨n, hn, rfl⟩
  intro u hu
  obtain ⟨n, hn, hno⟩ := hsplit ⟨u, hu⟩
  refine ⟨n, hnorm n hn, ?_⟩
  have := Subgroup.mem_subgroupOf.mp hno
  simpa using this

@[expose] def Core168At (A Y₀ : Subgroup G) : Prop :=
  ∀ Ŷ ∈ scriptY1Star A (lB A), Ŷ ≤ Subgroup.normalizer (Y₀ : Set G) →
  ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Ŷ →
    ∃ R : Subgroup G, R ≤ Ŷ ∧ ∃ _ : (R.subgroupOf Ŷ).Normal,
      Nat.Coprime 2 (Nat.card R) ∧
      Subgroup.centralizer (S4Free.oTwo (↥Ŷ ⧸ R.subgroupOf Ŷ) : Set (↥Ŷ ⧸ R.subgroupOf Ŷ)) ≤
        S4Free.oTwo (↥Ŷ ⧸ R.subgroupOf Ŷ) ∧
      R ≤ Subgroup.centralizer (stellmacherSub S : Set G)

theorem two168Out_of_core168At {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (h146 : Item146 A (lB A)) (h167 : Item167 A (lB A) c L) (hCore : Core168At A Y₀) :
    Two168Out A Y₀ := by
  intro V hV Y hY hVY N hN hYN S hS Y₁ hY₁ hSY₁ _ _ _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  by_contra hall
  push Not at hall
  obtain ⟨hSG, hDN, -⟩ := Proof168Steps.facts_at_N h hst h146 h167 hV hY hVY hN hYN hS
  obtain ⟨Ŷ, hY₁Ŷ, hŶ⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY1 A (lB A))) hY₁
  have hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G) := hall Ŷ hŶ.prop.1 hY₁Ŷ
  have hSŶ : S ≤ Ŷ := hSY₁.trans hY₁Ŷ
  obtain ⟨R, hRŶ, hRn, hRodd, hchar, hRC⟩ := hCore Ŷ hŶ hŶM S hSG hSŶ
  have hŶ3 : ¬ 3 ∣ Nat.card Ŷ := not_three_dvd_of_mem_scriptY1 hŶ.prop
  have hŶQ : Ŷ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_three hA h146 hŶ.prop.1.2 hŶ.prop.1.1.1.2 hŶ3
  have hSŶ' : S ∈ scriptQPiStar A (lB A) Ŷ (piOf 2) :=
    ⟨⟨⟨hSG.prop.1.1, hSŶ⟩, hSG.prop.2⟩,
      fun S' hS' hSS' => hSG.2 ⟨⟨hS'.1.1, le_top⟩, hS'.2⟩ hSS'⟩
  have hŶsyl := fusionIsSylowIn_of_mem_scriptQPiStar hA hŶQ hŶ3 hSŶ'
  have hsplit := exists_mem_normalizer_inv_mul_mem hst.2 h.toTheoremFourHyp hŶsyl.2.1 hŶ3 hŶsyl
    hRŶ hRn hRodd hchar
  have hŶC : Ŷ ≤ Subgroup.normalizer (stellmacherSub S : Set G) := by
    intro y hy
    obtain ⟨n, hn, hno⟩ := hsplit y hy
    have hoN : n⁻¹ * y ∈ Subgroup.normalizer (stellmacherSub S : Set G) :=
      Subgroup.centralizer_le_normalizer _ (hRC hno)
    have e : y = n * (n⁻¹ * y) := by group
    rw [e]
    exact mul_mem hn hoN
  have hŶN : Ŷ ≤ N :=
    calc Ŷ = delta A (lB A) Ŷ := hŶ.prop.1.2
      _ ≤ delta A (lB A) (Subgroup.normalizer (stellmacherSub S : Set G)) := delta_mono hŶC
      _ = N := hDN
  have hNŶ : N ≤ Ŷ := hŶ.2 hN.prop hŶN
  exact Proof168Steps.not_le_M_of_mem_omega168 h hV
    ((hVY.trans (hYN Y hY le_rfl)).trans (hNŶ.trans hŶM))

theorem commute_pPrimeCore_of_commute_pCore {H : Type*} [Group H] [Finite H]
    {γ : H} {m : ℕ} (hγ : γ ^ m = 1)
    (hm : Nat.Coprime m (Nat.card (CFSG.pPrimeCore 2 H)))
    (hfix : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ CFSG.pCore p H, γ * x = x * γ) :
    ∀ r ∈ CFSG.pPrimeCore 2 H, γ * r = r * γ := by
  classical
  set R := CFSG.pPrimeCore 2 H with hRdef
  haveI : R.Normal := CFSG.pPrimeCore_normal
  have hRodd : Nat.Coprime 2 (Nat.card R) := CFSG.pPrimeCore_coprime_card
  have hRs : Group.IsSolvable R :=
    CFSG.Milestones.odd_order_solvable (Nat.coprime_two_left.mp hRodd)
  set φ : MulAut R := MulAut.conjNormal γ with hφ
  have hφm : φ ^ m = 1 := by rw [hφ, ← map_pow, hγ, map_one]
  have hcop : Nat.Coprime m (Nat.card (CFSG.fittingSubgroup R)) :=
    hm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
  have hfixed : ∀ x ∈ CFSG.fittingSubgroup R, φ x = x := by
    have hle : CFSG.fittingSubgroup R ≤ MonoidHom.eqLocus (φ : R →* R) (MonoidHom.id R) := by
      rw [CFSG.fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hq2 : q.1.1 ≠ 2 := by
        intro h2
        have hdvd : q.1.1 ∣ Nat.card R := Nat.dvd_of_mem_primeFactors q.1.2
        rw [h2] at hdvd
        exact Nat.prime_two.coprime_iff_not_dvd.mp hRodd hdvd
      haveI : Fact q.1.1.Prime := ⟨hq⟩
      intro y hy
      have hK : (CFSG.pCore q.1.1 R).map R.subtype ≤ CFSG.pCore q.1.1 H := by
        refine le_sSup ⟨⟨fun x hx h => ?_⟩, (CFSG.pCore_isPGroup).map _⟩
        obtain ⟨z, hz, rfl⟩ := hx
        refine ⟨MulAut.conjNormal h z, ?_, by simp⟩
        exact (Subgroup.characteristic_iff_le_comap.mp inferInstance
          (MulAut.conjNormal h)) hz
      have h1 := hfix q.1.1 hq hq2 (y : H) (hK ⟨y, hy, rfl⟩)
      change φ y = y
      apply Subtype.ext
      rw [hφ, MulAut.conjNormal_apply, h1, mul_inv_cancel_right]
    exact fun x hx => hle hx
  have h1 : φ = 1 := CFSG.mulAut_eq_one_of_fixes_fittingSubgroup R hRs φ m hφm hcop hfixed
  intro r hr
  have h2 : (φ ⟨r, hr⟩ : H) = r := by rw [h1]; rfl
  rw [hφ, MulAut.conjNormal_apply] at h2
  calc γ * r = γ * r * γ⁻¹ * γ := by group
    _ = r * γ := by rw [h2]

theorem pCore_two_eq_oTwo (X : Type*) [Group X] [Finite X] :
    CFSG.pCore 2 X = S4Free.oTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.pCore_eq_piCore X 2]
  congr 1
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; rw [h]

theorem le_centralizer_pPrimeCoreOf {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) :
    A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨⟨hY2, hYΔ⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3', hAY⟩
  have hYQ : Y ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  set X := deltaZero A (lB A) Y with hXdef
  have hYAX : ⁅Y, A⁆ ≤ X := by
    have hcomm : ⁅Y, A⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hAY
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Y, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Y
    exact le_deltaZero ⟨mem_scriptQ_of_le hYQ hcomm hAcomm,
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
        A Y hA3 hY3' hAY).symm⟩ hcomm
  set Z := pPrimeCoreOf 2 Y with hZdef
  have hZY : Z ≤ Y := pPrimeCoreOf_le 2 Y
  have hFX : generalizedFitting ↥X = CFSG.pCore 2 ↥X :=
    rank3II_16_7_1 h.isSimpleGroup h.nonabelian h.charTwoType h149 hY
  have hZX : Z ⊓ X = ⊥ := pPrimeCoreOf_inf_deltaZero_eq_bot hFX
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have haZ : a ∈ Subgroup.normalizer (Z : Set G) :=
    (hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 2 Y)) ha
  have hk1 : z * a * z⁻¹ * a⁻¹ ∈ Z := by
    have : a * z⁻¹ * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp haZ _).mp (inv_mem hz)
    have h2 := mul_mem hz this
    rwa [show z * (a * z⁻¹ * a⁻¹) = z * a * z⁻¹ * a⁻¹ by group] at h2
  have hk2 : z * a * z⁻¹ * a⁻¹ ∈ X := by
    apply hYAX
    have := Subgroup.commutator_mem_commutator (hZY hz) ha
    rwa [commutatorElement_def] at this
  have hk : z * a * z⁻¹ * a⁻¹ = 1 := by
    have : z * a * z⁻¹ * a⁻¹ ∈ Z ⊓ X := ⟨hk1, hk2⟩
    rwa [hZX, Subgroup.mem_bot] at this
  calc z * a = (z * a * z⁻¹ * a⁻¹) * (a * z) := by group
    _ = a * z := by rw [hk, one_mul]

theorem pCoreOf_le_pPrimeCoreOf_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Y : Subgroup G) :
    CFSG.Open.pCoreOf p Y ≤ pPrimeCoreOf 2 Y := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_pPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le p Y)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Y) ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := p) Y)
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem stellmacherSub_le_centralizer_pCoreOf {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    {Ŷ : Subgroup G} (hŶ : Ŷ ∈ scriptY1Star A (lB A))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hSŶ : S ≤ Ŷ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCA : stellmacherSub S ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf p Ŷ : Set G)) :
    stellmacherSub S ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p Ŷ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  by_cases hS1 : S = ⊥
  · have hC1 : stellmacherSub S = ⊥ := by
      rw [eq_bot_iff, ← hS1]
      exact Subgroup.map_subtype_le _
    rw [hC1]
    exact bot_le
  set C := stellmacherSub S with hCdef
  set Z := CFSG.Open.pCoreOf p Ŷ with hZdef
  obtain ⟨hCS, -, hNS, -⟩ := stellmacherSub_spec hst h.toTheoremFourHyp hS2 hS1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hS.prop.1.1).2.1
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAS.trans hNS
  have hC2 : IsPGroup 2 C := hS2.to_le hCS
  have hCsol : Group.IsSolvable ↥C := by
    haveI := hC2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card C) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC2
    obtain ⟨l, hl⟩ := IsPGroup.iff_card.mp hA.isPGroup
    rw [hk, hl]
    exact Nat.Coprime.pow l k (by norm_num)
  have hfac := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.le_commutator_sup_inf_centralizer
    hAC hCsol hcop
  have hAZ : A ≤ Subgroup.centralizer (Z : Set G) :=
    (le_centralizer_pPrimeCoreOf h.toSec15R h149 h146 hŶ).trans
      (Subgroup.centralizer_le (pCoreOf_le_pPrimeCoreOf_two hp hp2 Ŷ))
  have hCZ : C ≤ Subgroup.normalizer (Z : Set G) :=
    (hCS.trans hSŶ).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Ŷ)
  have hNZ : C ≤ Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) :=
    Sec16.le_normalizer_centralizer_of_le_normalizer hCZ
  have hcomm : ⁅C, A⁆ ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.commutator_le]
    intro g hg a ha
    rw [commutatorElement_def]
    have h1 : g * a * g⁻¹ ∈ Subgroup.centralizer (Z : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hNZ hg) a).mp (hAZ ha)
    exact mul_mem h1 (inv_mem (hAZ ha))
  exact hfac.trans (sup_le hcomm hCA)

theorem le_normalizer_inf {X H K : Subgroup G} (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => ⟨(Subgroup.mem_normalizer_iff.mp (hH hg) x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp (hK hg) x).mp hx.2⟩,
      fun hx => ⟨(Subgroup.mem_normalizer_iff.mp (hH hg) x).mpr hx.1,
        (Subgroup.mem_normalizer_iff.mp (hK hg) x).mpr hx.2⟩⟩

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
