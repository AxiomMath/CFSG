module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofTwoThree
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.J4
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec8.Item83ProofDistinct
import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRankTools
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwelve

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_inner_A6_of_pow {τ : MulAut (alternatingGroup (Fin 6))} {k : ℕ}
    (hτ : τ ^ (3 ^ k) = 1) : τ ∈ inner (alternatingGroup (Fin 6)) := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  set o : Outer (alternatingGroup (Fin 6)) := QuotientGroup.mk τ with ho
  have hok : o ^ (3 ^ k) = 1 := by rw [ho, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have hdvdk : orderOf o ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hok
  have hdvdO : orderOf o ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := orderOf_dvd_natCard o
  have hle := CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have h2 := Sec14.Item148PtRes.two_dvd_card_outer_six
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hord : orderOf o = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvdk
    rcases j with _ | j
    · simpa using hj
    · exfalso
      have h3 : 3 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) :=
        (dvd_pow_self 3 (Nat.succ_ne_zero j)).trans (hj ▸ hdvdO)
      obtain ⟨a, ha⟩ := h3
      obtain ⟨b, hb⟩ := h2
      generalize Nat.card (Outer (alternatingGroup (Fin 6))) = n at ha hb hle hpos
      omega
  have ho1 : o = 1 := orderOf_eq_one_iff.mp hord
  rw [ho, QuotientGroup.eq_one_iff] at ho1
  exact ho1

theorem exists_eq_conj_of_tripleCover {T : Type*} [Group T] [Group.IsPerfect T]
    (e : T ⧸ center T ≃* alternatingGroup (Fin 6)) {σ : MulAut T} {k : ℕ}
    (hσ : σ ^ (3 ^ k) = 1) : ∃ t : T, σ = MulAut.conj t := by
  set σbar := PerfectAutomorphisms.centerQuotientHom T σ with hσbar
  set τ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr e σbar with hτ
  have hτk : τ ^ (3 ^ k) = 1 := by
    rw [hτ, hσbar, ← map_pow, ← map_pow, hσ, map_one, map_one]
  obtain ⟨a, ha⟩ := mem_inner_A6_of_pow hτk
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (center T) (e.symm a)
  refine ⟨t, PerfectAutomorphisms.centerQuotientHom_injective T ?_⟩
  apply (MulAut.congr e).injective
  rw [← hσbar, ← hτ, ← ha]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (center T) (e.symm x)
  change (MulAut.conj a) x = e (PerfectAutomorphisms.onCenterQuotient (MulAut.conj t) (e.symm x))
  rw [← hs, PerfectAutomorphisms.onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv, ht, hs, MulEquiv.apply_symm_apply]

theorem nonempty_lBar_equiv_of_eq_sup {I J : Subgroup G} (hIJ : I ≤ J)
    (hJI : J = I ⊔ inSubgroup (aschbacherSolvableCore 3) J) : Nonempty (lBar I ≃* lBar J) := by
  set θ := aschbacherSolvableCore 3 ↥J with hθ
  set I' : Subgroup ↥J := I.subgroupOf J with hI'
  have hsup : I' ⊔ θ = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hIJ, ← Subgroup.subgroupOf_self,
      Subgroup.map_subgroupOf_eq_of_le le_rfl]
    exact hJI.symm
  have htop : I'.map (QuotientGroup.mk' θ) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' θ)) hsup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective θ)] at h1
    have h2 : θ.map (QuotientGroup.mk' θ) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [h2, sup_bot_eq] at h1
    exact h1
  have hN : (I'.map (QuotientGroup.mk' θ)).Normal := by
    rw [htop]
    infer_instance
  obtain ⟨η, -⟩ := Item2113Res3Proof.exists_mulEquiv_map_of_normal I' hN
  set e₀ : ↥I ≃* ↥I' := (subgroupOfEquivOfLe hIJ).symm
  let e₁ : lBar I ≃* ↥I' ⧸ aschbacherSolvableCore 3 ↥I' :=
    QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)
  exact ⟨e₁.trans (η.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv))⟩

omit [Finite G] in
theorem isTripleCover_of_item219_J2
    {L : Subgroup G} {d : G}
    (hJ2 : Nonempty (lBar L ≃* NativeSporadic.J2))
    (h : (Nonempty (L ≃* NativeSporadic.He) ∧
            Sec4.IsTripleCover (iOf218 L d) (alternatingGroup (Fin 7))) ∨
          ((Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.J2) ∨
              Nonempty (lBar L ≃* NativeSporadic.Ru)) ∧
            Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6))) ∨
          (Nonempty (L ≃* NativeSporadic.J4) ∧
            Nat.card (Subgroup.center (iOf218 L d)) = 6 ∧
            Nonempty (iOf218 L d ⧸ Subgroup.center (iOf218 L d) ≃* NativeSporadic.M22)) ∨
          (∃ n : ℕ, 0 < n ∧ Even n ∧
            (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
              ChevalleyExceptionalModel (lBar L) .trialityD4 2 n) ∧
            Nonempty (lBar (iOf218 L d) ≃* SL3 n))) :
    Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6)) := by
  obtain ⟨eJ⟩ := hJ2
  have hJc : Nat.card (lBar L) = 604800 := by
    rw [Nat.card_congr eJ.toEquiv, KFacts.KS14.card_nativeJ2]
  have hsimple : IsSimpleGroup ↥L → Nat.card (lBar L) = Nat.card ↥L := by
    intro hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with h1 | h1
    · exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h1).trans
        QuotientGroup.quotientBot).toEquiv
    · exfalso
      have : Subsingleton (lBar L) := by
        change Subsingleton (↥L ⧸ aschbacherSolvableCore 3 ↥L)
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      have h1' : Nat.card (lBar L) = 1 := Nat.card_unique
      rw [hJc] at h1'
      norm_num at h1'
  have hv : padicValNat 2 604800 = 7 := by
    rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num]
    exact Sec8.Item83Proof.padicValNat_two_pow_mul_odd (by decide)
  rcases h with ⟨⟨eHe⟩, -⟩ | ⟨-, hA6⟩ | ⟨⟨eJ4⟩, -⟩ | ⟨n, hn, -, hG | hD, -⟩
  · exfalso
    have : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
    have h1 := hsimple (@MulEquiv.isSimpleGroup _ _ _ _ this eHe)
    rw [hJc, Nat.card_congr eHe.toEquiv, CFSG.Sporadic.He.card_He] at h1
    norm_num at h1
  · exact hA6
  · exfalso
    have : IsSimpleGroup NativeSporadic.J4 := CFSG.Sporadic.J4.isSimpleGroup_J4
    have h1 := hsimple (@MulEquiv.isSimpleGroup _ _ _ _ this eJ4)
    rw [hJc, Nat.card_congr eJ4.toEquiv, CFSG.Sporadic.J4.card_J4] at h1
    norm_num at h1
  · exfalso
    have hc : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG
    rw [hJc] at hc
    have hv' := Item218Proof.padicValNat_ordG2 (m := n) (by omega)
    rw [← hc, hv] at hv'
    omega
  · exfalso
    have hc : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD
    rw [hJc] at hc
    have hv' := Item218Proof.padicValNat_ordTrialityD4 (m := n) (by omega)
    rw [← hc, hv] at hv'
    omega

omit [Finite G] in
theorem conj_pow_eq {x c d : G} (hxd : x * d * x⁻¹ = d) (hxc : x * c * x⁻¹ = c * d) (m : ℕ) :
    x ^ m * c * (x ^ m)⁻¹ = c * d ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hxdm : x * d ^ m * x⁻¹ = d ^ m := by rw [← conj_pow, hxd]
    calc x ^ (m + 1) * c * (x ^ (m + 1))⁻¹ = x * (x ^ m * c * (x ^ m)⁻¹) * x⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
      _ = (x * c * x⁻¹) * (x * d ^ m * x⁻¹) := by rw [ih]; group
      _ = c * d ^ (m + 1) := by rw [hxc, hxdm, pow_succ', mul_assoc]

theorem exists_three_part {x c d : G} (hd3 : d ^ 3 = 1) (hxd : x * d * x⁻¹ = d)
    (hxc : x * c * x⁻¹ = c * d) :
    ∃ y : G, y * d * y⁻¹ = d ∧ y * c * y⁻¹ = c * d ∧ ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hxdC : Commute x d := by
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [hxd]
  refine ⟨x ^ (b * b), by rw [(hxdC.pow_left (b * b)).eq, mul_inv_cancel_right], ?_, a, ?_⟩
  · rw [conj_pow_eq hxd hxc, pow_eq_pow_mod (b * b) hd3]
    have hb : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have : b * b % 3 = 1 := by
      rcases hb with hb | hb <;> simp [Nat.mul_mod, hb]
    rw [this, pow_one]
  · rw [← pow_mul, show b * b * 3 ^ a = (3 ^ a * b) * b by ring, ← hab, pow_mul,
      pow_orderOf_eq_one, one_pow]

section HJ


theorem item2112TwoGroupHJ_of (h2 : Item2110Two) (h45 : Sec4.Item4_5) (hJ : Item2110JThetaI)
    (hU : Item2110ThreeUnique) (hC : Item2110CentAJ) (h219 : Item219) : Item2112TwoGroupHJ := by
  intro G _ _ A E U c L hpair hL hJ2 d hdA hd1 hdcen x _ hxd hxc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, -, -, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAe.2
  have hAp : IsPGroup 3 A := fun z => ⟨1, Subtype.ext (by simpa using hA3 z z.2)⟩
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hcd : c ∉ zpowers d := fun h => hcL ((zpowers_le.mpr hdL) h)
  have hdc : d ∉ zpowers c := by
    intro h
    apply hcd
    exact (Item2110Res2Proof.zpowers_eq_of_mem_cube hc3 h hd1) ▸ mem_zpowers c
  obtain ⟨hdI, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨-, J₀, hJ₀, hJ₀I⟩ := hJ G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hB9, hsup⟩ := hC G A E U c L hpair hL d hdA hd1 hdcen J₀ hJ₀ hJ₀I
  have hBcd := centA_eq h45 hpair hL hdA hd1 hdcen hJ₀ hJ₀I hB9
  have hcJ : c ∈ Sec4.thetaQuotCentralizer J₀ :=
    (hBcd ▸ mem_sup_left (mem_zpowers c) : c ∈ A ⊓ Sec4.thetaQuotCentralizer J₀).2
  have hdJ : d ∈ Sec4.thetaQuotCentralizer J₀ :=
    (hBcd ▸ mem_sup_right (mem_zpowers d) : d ∈ A ⊓ Sec4.thetaQuotCentralizer J₀).2
  set T := inSubgroup (aschbacherSolvableCore 3) J₀ with hT
  have hJd : J₀ ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ₀
  have hTJ : T ≤ J₀ := map_subtype_le _
  have hJT : J₀ ≤ normalizer (T : Set G) := Sec6.le_normalizer_theta J₀
  have hAJ : A ≤ normalizer (J₀ : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hdA hd1
      J₀ hJ₀
  have hNT : ∀ g ∈ normalizer (J₀ : Set G), g ∈ normalizer (T : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro t
    refine ⟨fun ht => Sec12.conj_mem_inSubgroup_theta hg ht, fun ht => ?_⟩
    have := Sec12.conj_mem_inSubgroup_theta (inv_mem hg) ht
    simpa [mul_assoc] using this
  have hcomm : ∀ u ∈ Sec4.thetaQuotCentralizer J₀, ∀ l ∈ J₀, l * u * l⁻¹ * u⁻¹ ∈ T := by
    intro u hu l hl
    have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hu).2 l⁻¹ (inv_mem hl)
    simpa [mul_assoc] using h1
  obtain ⟨y, hyd, hyc, k, hyk⟩ := exists_three_part hd3 hxd hxc
  have hyC : y ∈ centralizer ({d} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc y * d = y * d * y⁻¹ * y := by group
      _ = d * y := by rw [hyd]
  have hdJ₀ : d ∈ J₀ := by
    rw [hJ₀I]
    exact mem_sup_left hdI
  have hyN : y ∈ normalizer (J₀ : Set G) := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj y) hJ₀
    have hyd' : (MulAut.conj y) d = d := by rw [MulAut.conj_apply, hyd]
    rw [hyd'] at h1
    have hdmem : d ∈ J₀.map (MulAut.conj y).toMonoidHom := ⟨d, hdJ₀, hyd'⟩
    have heq := hU G A E U c L hpair hL d hdA hd1 hdcen _ h1 J₀ hJ₀ hdmem hdJ₀
    exact mem_normalizer_iff_map_conj_eq.mpr heq
  have hIJ : iOf218 L d ≤ J₀ := by
    rw [hJ₀I]
    exact le_sup_left
  obtain ⟨eIJ⟩ := nonempty_lBar_equiv_of_eq_sup hIJ hJ₀I
  have hA6 : Sec4.IsTripleCover (lBar J₀) (alternatingGroup (Fin 6)) :=
    Sec13.isTripleCover_of_mulEquiv eIJ (isTripleCover_of_item219_J2 hJ2 hcases)
  obtain ⟨-, ⟨eA6⟩⟩ := hA6
  have hJp : Group.IsPerfect ↥J₀ := Sec6.isPerfect_of_mem_thetaComponentsAt hJ₀
  have hJbp : Group.IsPerfect (lBar J₀) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J₀))
      (QuotientGroup.mk'_surjective _)
  set σ := Sec4.thetaQuotMulAut ↥J₀ (J₀.normalizerMonoidHom ⟨y, hyN⟩) with hσ
  have hσk : σ ^ (3 ^ k) = 1 := by
    rw [hσ, ← map_pow, ← map_pow]
    have : (⟨y, hyN⟩ : normalizer (J₀ : Set G)) ^ (3 ^ k) = 1 := Subtype.ext hyk
    rw [this, map_one, map_one]
  obtain ⟨jb, hjb⟩ := exists_eq_conj_of_tripleCover eA6 hσk
  obtain ⟨j₀, hj₀⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥J₀) jb
  set j : G := (j₀ : G) with hj
  have hjJ : j ∈ J₀ := j₀.2
  have hyl : ∀ l ∈ J₀, (y * l * y⁻¹)⁻¹ * (j * l * j⁻¹) ∈ T := by
    intro l hl
    have h1 := congrArg (fun φ : MulAut (lBar J₀) => φ ((⟨l, hl⟩ : J₀) : lBar J₀)) hjb
    simp only [hσ, Sec4.thetaQuotMulAut_mk, MulAut.conj_apply] at h1
    rw [← hj₀] at h1
    have h2 : ((J₀.normalizerMonoidHom ⟨y, hyN⟩ ⟨l, hl⟩ : J₀) : lBar J₀) =
        ((j₀ * ⟨l, hl⟩ * j₀⁻¹ : J₀) : lBar J₀) := by
      rw [h1]
      rfl
    rw [QuotientGroup.eq] at h2
    refine ⟨_, h2, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, hj]
  set g := j⁻¹ * y with hg
  have hgN : g ∈ normalizer (J₀ : Set G) := mul_mem (inv_mem (le_normalizer hjJ)) hyN
  have hjC : j ∈ centralizer ({d} : Set G) := hJd hjJ
  have hgC' : g ∈ centralizer ({d} : Set G) := mul_mem (inv_mem hjC) hyC
  have hgd : g * d * g⁻¹ = d := by
    rw [mem_centralizer_singleton_iff.mp hgC', mul_inv_cancel_right]
  have hgC : g ∈ Sec4.thetaQuotCentralizer J₀ := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hgN, fun l hl => ?_⟩
    have h1 : (j * l * j⁻¹)⁻¹ * (y * l * y⁻¹) ∈ T := by
      have := T.inv_mem (hyl l hl)
      simpa [mul_assoc] using this
    have h2 := (mem_normalizer_iff.mp (hJT (inv_mem hjJ)) _).mp h1
    convert h2 using 1
    simp only [hg]
    group
  have hAT : A ≤ normalizer (T : Set G) := fun a ha => hNT a (hAJ ha)
  have hATb : A ⊓ T = ⊥ := Sec12.inf_inSubgroup_theta_eq_bot hAp
  have hA_eq : A = (zpowers c ⊔ zpowers d) ⊔ (A ⊓ J₀) := by rw [hBcd, hsup]
  have hgA : A.map (MulAut.conj g).toMonoidHom ≤ A ⊔ T := by
    rw [Subgroup.map_le_iff_le_comap]
    have key : (zpowers c ⊔ zpowers d) ⊔ (A ⊓ J₀) ≤
        (A ⊔ T).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) fun a ha => ?_
      · rw [mem_comap]
        change g * c * g⁻¹ ∈ A ⊔ T
        have hw : c * d ∈ Sec4.thetaQuotCentralizer J₀ := mul_mem hcJ hdJ
        have h1 := hcomm _ hw j⁻¹ (inv_mem hjJ)
        have h2 : g * c * g⁻¹ = j⁻¹ * (c * d) * j⁻¹⁻¹ * (c * d)⁻¹ * (c * d) := by
          rw [hg, show j⁻¹ * y * c * (j⁻¹ * y)⁻¹ = j⁻¹ * (y * c * y⁻¹) * j by group, hyc]
          group
        rw [h2]
        exact mul_mem (mem_sup_right h1) (mem_sup_left (A.mul_mem hcA hdA))
      · rw [mem_comap]
        change g * d * g⁻¹ ∈ A ⊔ T
        rw [hgd]
        exact mem_sup_left hdA
      · rw [mem_comap]
        change g * a * g⁻¹ ∈ A ⊔ T
        have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hgC).2 a ha.2
        have h2 : g * a * g⁻¹ = a * (a⁻¹ * (g * a * g⁻¹)) := by group
        rw [h2]
        exact mul_mem (mem_sup_left ha.1) (mem_sup_right h1)
    exact hA_eq.le.trans key
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, inSubgroup, card_map_of_injective J₀.subtype_injective]
    exact three_not_dvd_card_aschbacherSolvableCore
  have hKcard : Nat.card (A ⊔ T : Subgroup G) = Nat.card A * Nat.card T := by
    have h1 := Sec6.card_sup_mul_card_inf hAT
    rw [hATb, card_bot, mul_one] at h1
    exact h1
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hsylA : CFSG.ABGLocalTools.IsSylowOf 3 A (A ⊔ T) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_left, hAp, ?_⟩
    have h1 := relIndex_mul_card A (A ⊔ T)
    rw [inf_eq_left.mpr le_sup_left, hKcard] at h1
    have h2 : A.relIndex (A ⊔ T) = Nat.card T := by
      rw [mul_comm (Nat.card A)] at h1
      exact Nat.eq_of_mul_eq_mul_right hApos h1
    rw [h2]
    exact hT3
  have hA'card : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    card_map_of_injective (MulAut.conj g).injective
  have hsylA' : CFSG.ABGLocalTools.IsSylowOf 3 (A.map (MulAut.conj g).toMonoidHom) (A ⊔ T) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hgA, hAp.map _, ?_⟩
    have h1 := relIndex_mul_card (A.map (MulAut.conj g).toMonoidHom) (A ⊔ T)
    rw [inf_eq_left.mpr hgA, hKcard, hA'card] at h1
    have h2 : (A.map (MulAut.conj g).toMonoidHom).relIndex (A ⊔ T) = Nat.card T := by
      rw [mul_comm (Nat.card A)] at h1
      exact Nat.eq_of_mul_eq_mul_right hApos h1
    rw [h2]
    exact hT3
  obtain ⟨m, hmK, hm⟩ := Sec13.Item134SylowBarProof.exists_conj_of_isSylowOf hsylA' hsylA
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A T hAT] at hmK
  obtain ⟨a', ha', t', ht', rfl⟩ := hmK
  set n := t' * g with hn
  have hnA : n ∈ normalizer (A : Set G) := by
    refine mem_normalizer_fintype fun b hb => ?_
    have h1 : (a' * t') * (g * b * g⁻¹) * (a' * t')⁻¹ ∈ A := by
      rw [hm]
      exact ⟨g * b * g⁻¹, ⟨b, hb, rfl⟩, rfl⟩
    have h2 := A.mul_mem (A.mul_mem (A.inv_mem ha') h1) ha'
    have h3 : n * b * n⁻¹ = a'⁻¹ * (a' * t' * (g * b * g⁻¹) * (a' * t')⁻¹) * a' := by
      simp only [hn]
      group
    change n * b * n⁻¹ ∈ A
    rw [h3]
    exact h2
  have ht'C : t' ∈ centralizer ({d} : Set G) := hJd (hTJ ht')
  have hnd : n * d * n⁻¹ = d := by
    rw [mem_centralizer_singleton_iff.mp (mul_mem ht'C hgC'), mul_inv_cancel_right]
  have hnc : n * c * n⁻¹ = c * d := by
    set s := t' * j⁻¹ with hs
    have hsJ : s ∈ J₀ := mul_mem (hTJ ht') (inv_mem hjJ)
    have hw : c * d ∈ Sec4.thetaQuotCentralizer J₀ := mul_mem hcJ hdJ
    have h1 : s * (c * d) * s⁻¹ * (c * d)⁻¹ ∈ T := hcomm _ hw s hsJ
    have h2 : n * c * n⁻¹ = s * (c * d) * s⁻¹ := by
      rw [← hyc, hn, hg, hs]
      group
    have h3 : n * c * n⁻¹ * (c * d)⁻¹ ∈ A :=
      A.mul_mem ((mem_normalizer_iff.mp hnA c).mp hcA) (A.inv_mem (A.mul_mem hcA hdA))
    have h4 : n * c * n⁻¹ * (c * d)⁻¹ ∈ A ⊓ T := ⟨h3, h2 ▸ h1⟩
    rw [hATb, mem_bot] at h4
    calc n * c * n⁻¹ = n * c * n⁻¹ * (c * d)⁻¹ * (c * d) := by group
      _ = c * d := by rw [h4, one_mul]
  exact Item2113Res2Proof.item2112TwoGroup_of_mem_W h2 hpair hL hdA hd1 hdcen hdc hnA hnd hnc

end HJ

end CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof
