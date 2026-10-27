module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJA7
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM22
public import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

theorem checkSL_a7 : ∀ q < 14, 2 ≤ q → q ^ 3 ∣ 2520 →
    2520 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide

theorem checkSU_a7 : ∀ q < 14, 2 ≤ q → q ^ 3 ∣ 2520 →
    2520 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide

theorem not_isoLThreePi_of_card_eq_2520 {X : Type} [Group X] (hX : Nat.card X = 2520)
    (p e : ℕ) [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e :=
  KFacts.KS14.not_isoLThreePi_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_a7)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a7) p e

section Groups

open CFSG.RankThree.PartTwo.KFacts.KP2 Equiv

theorem eNine_le_centOne : eNine ≤ centOne := by
  rintro _ ⟨i, j, rfl⟩
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, eNineF_sign i j⟩
  rw [show cOne = eNineF 1 0 by decide +kernel]
  exact eNineF_comm i j 1 0

theorem exists_two_of_card_nine_alt7 (E : Subgroup (alternatingGroup (Fin 7)))
    (hE9 : Nat.card E = 9) :
    ∃ S : Subgroup (alternatingGroup (Fin 7)), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      E ≤ Subgroup.normalizer (S : Set (alternatingGroup (Fin 7))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hE'9 : Nat.card (eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
      card_eNine]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hE'p : IsPGroup 3 (eNine.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  have hEi : ¬ 3 ∣ E.index := by
    have h := E.index_mul_card
    rw [hE9, hcard] at h
    omega
  have hE'i : ¬ 3 ∣ (eNine.subgroupOf (alternatingGroup (Fin 7))).index := by
    have h := (eNine.subgroupOf (alternatingGroup (Fin 7))).index_mul_card
    rw [hE'9, hcard] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hEp.toSylow hEi)
    (hE'p.toSylow hE'i)
  have hmem' : ∀ x : alternatingGroup (Fin 7), x ∈ E →
      g * x * g⁻¹ ∈ eNine.subgroupOf (alternatingGroup (Fin 7)) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ ((g • hEp.toSylow hEi : Sylow 3 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [this, IsPGroup.toSylow_coe]
      exact hx
    rw [hg, IsPGroup.toSylow_coe] at hx'
    exact hx'
  let ψ : alternatingGroup (Fin 7) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (MulAut.conj g).toMonoidHom
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp (MulAut.conj g).injective
  have hV2 : IsPGroup 2 vOne := IsPGroup.of_card (n := 2) (by rw [card_vOne]; norm_num)
  have hvA : vOne ≤ alternatingGroup (Fin 7) := fun v hv => (vOne_le_centOne hv).2
  have hrange : ψ.range = alternatingGroup (Fin 7) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcardS : Nat.card (vOne.comap ψ) = 4 := by
    rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq, hrange,
      inf_eq_right.mpr hvA, card_vOne]
  refine ⟨vOne.comap ψ, fun h0 => ?_, hV2.comap_of_injective ψ hψinj, fun x hx => ?_⟩
  · rw [h0, Subgroup.card_bot] at hcardS
    omega
  ·
    have hxE : ψ x ∈ eNine := Subgroup.mem_subgroupOf.mp (hmem' x hx)
    exact Subgroup.le_normalizer_comap ψ
      (mem_normalizer_of_le_of_normal_perm_seven vOne_le_centOne vOne_normal
        (eNine_le_centOne hxE))

open CFSG.RankThree.PartTwo.KFacts.KP4 (G22 V lineE exists_centralizer_eq conj_mem_V card_V)

theorem exists_two_of_elemAbelian_m22
    (E : Subgroup G22)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ S : Subgroup G22, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set G22) := by
  obtain ⟨b, hbE, hb1⟩ : ∃ b ∈ E, b ≠ 1 := by
    by_contra hne
    push Not at hne
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hne
    rw [hE1, Subgroup.card_bot] at hE9
    omega
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  obtain ⟨g, hg⟩ := exists_conj_mem_P0 hb3 hb1
  have hg1 : g * b * g⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨i, hi⟩ := exists_centralizer_eq hg hg1
  set φ : G22 ≃* G22 := MulAut.conj g with hφ
  have hφb : φ b = g * b * g⁻¹ := rfl
  have hcen : (Subgroup.centralizer ({b} : Set G22)).map φ.toMonoidHom =
      Subgroup.centralizer ({lineE i} : Set G22) := by
    rw [CFSG.RankThree.PartTwo.map_centralizer_singleton φ b, hφb, hi]
  have hφφ : ∀ x : G22, φ.symm (φ x) = x := fun x => φ.symm_apply_apply x
  have hV4 : Nat.card ((V i).map φ.symm.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, card_V]
  refine ⟨(V i).map φ.symm.toMonoidHom, ?_, IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num),
    fun x hx => ?_⟩
  · intro h0
    rw [h0, Subgroup.card_bot] at hV4
    omega
  ·
    have hxb : x ∈ Subgroup.centralizer ({b} : Set G22) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨b, hbE⟩ ⟨x, hx⟩)).symm
    have hφx : φ x ∈ Subgroup.centralizer ({lineE i} : Set G22) :=
      hcen ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hxb
    have hN : φ x ∈ Subgroup.normalizer ((V i : Subgroup G22) : Set G22) :=
      Subgroup.mem_normalizer_fintype fun v hv => conj_mem_V hφx hv
    have hN' : φ.symm (φ x) ∈ (Subgroup.normalizer ((V i : Subgroup G22) : Set G22)).map
        φ.symm.toMonoidHom := Subgroup.mem_map_of_mem φ.symm.toMonoidHom hN
    rw [Subgroup.map_equiv_normalizer_eq, hφφ] at hN'
    exact hN'

theorem exists_two_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∃ S : Subgroup Y, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set Y))
    (E : Subgroup X) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X) := by
  obtain ⟨S, hS1, hS2, hES⟩ := hY (E.map e.toMonoidHom)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 e.toMonoidHom E hE)
    (by rw [Subgroup.card_map_of_injective e.injective, hE9])
  refine ⟨S.map e.symm.toMonoidHom, fun h0 => hS1 ?_, hS2.map _, fun x hx => ?_⟩
  · have := congrArg (Subgroup.map e.toMonoidHom) h0
    rwa [CFSG.RankThree.PartTwo.map_map_symm, Subgroup.map_bot] at this
  · have hx' : e x ∈ Subgroup.normalizer (S : Set Y) := hES (Subgroup.mem_map_of_mem _ hx)
    have hN := Subgroup.mem_map_of_mem e.symm.toMonoidHom hx'
    rw [Subgroup.map_equiv_normalizer_eq] at hN
    simpa using hN

end Groups

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A L : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) : CFSG.Assembly.IsElemAbelian p (A.subgroupOf L) :=
  CFSG.Open.IsElemAbelian.subgroupOf hA L

theorem hasInvEven_of_inner {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hX : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E = 9 → ∃ S : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), S ≠ ⊥ ∧
        IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    HasInvEven A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  set Ab := (A.subgroupOf L).map π with hAb
  have hE9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEab : CFSG.Assembly.IsElemAbelian 3 Ab :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
      (isElemAbelian_subgroupOf hD.isElemAbelian)
  obtain ⟨Sb, hSb1, hSb2, hSbN⟩ := hX Ab hEab hE9
  have h2Sb : 2 ∣ Nat.card Sb := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSb2
    have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hSb1
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  set K := Sb.comap π with hK
  have h2K : 2 ∣ Nat.card K := by
    refine h2Sb.trans ?_
    have hmap : K.map π = Sb := Subgroup.map_comap_eq_self_of_surjective hπs Sb
    rw [← hmap]
    exact Subgroup.card_map_dvd K π
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hπk : π k ∈ Sb := k.2
    have hk3 : (k : ↥L) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
    have hπ1 : π (k : ↥L) = 1 := by
      obtain ⟨n, hn⟩ := hSb2 ⟨π k, hπk⟩
      have hn' : (π (k : ↥L)) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have ho1 : orderOf (π (k : ↥L)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      have ho2 : orderOf (π (k : ↥L)) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk3, map_one])
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n (by norm_num)) ho1 ho2)
    have hkθ : (k : ↥L) ∈ θ := by
      rw [← QuotientGroup.eq_one_iff]
      exact hπ1
    have hk1 : (k : ↥L) = 1 := eq_one_of_mem_aschbacherSolvableCore hkθ hk3
    have : orderOf k = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hk1
    omega
  set KG := K.map L.subtype with hKG
  have hKGL : KG ≤ L := Subgroup.map_subtype_le K
  have hcKG : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective L.subtype_injective
  have hAKG : A ≤ Subgroup.normalizer (KG : Set G) := by
    rw [hAc]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hKGL hx))
    · intro b hb
      obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
      have hbAb : π ⟨b, hbL⟩ ∈ Ab :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbA)
      have hbN : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.normalizer (K : Set ↥L) :=
        Subgroup.le_normalizer_comap π (show π ⟨b, hbL⟩ ∈ _ from hSbN hbAb)
      exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hbN)
  exact ⟨KG, hKGL, hAKG, by rwa [hcKG], by rwa [hcKG]⟩

theorem ks163QLInv_of
    (h131 : Item131) (hL3 : KS163QLInvL3) : KS163QLInv := by
  intro G _ _ A c L h h32 hJ h12 hθ
  have hD := h.toSec13Data
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have htypes := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have hZ := Sec15.center_eq_bot_of_types hLc htypes
  rcases htypes with hJ' | hL3' | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | h12'
  · exact absurd hJ' (not_nonempty_iff.mpr hJ)
  · exact hL3 G A c L h h32 hL3' hθ
  · have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rintro ⟨p, e, hp, -, hiso⟩
      exact KFacts.KS14.not_isoLThreePi_of_card hcard
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_a7)
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a7) p e hiso
    obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 sporadicModels131 hD hZ hnL3
    exact hasInvEven_of_inner h h9 hAc
      (exists_two_of_mulEquiv φ fun E _ hE9 => exists_two_of_card_nine_alt7 E hE9)
  · have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rintro ⟨p, e, hp, -, hiso⟩
      exact KFacts.KS14.not_isoLThreePi_of_card hcard
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22)
        p e hiso
    obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 sporadicModels131 hD hZ hnL3
    exact hasInvEven_of_inner h h9 hAc (exists_two_of_mulEquiv φ exists_two_of_elemAbelian_m22)
  · exact absurd h12' (not_nonempty_iff.mpr h12)

end Lift

end CFSG.RankThree.PartTwo.Sec16
