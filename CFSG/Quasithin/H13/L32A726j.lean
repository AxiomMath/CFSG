module

public import CFSG.Quasithin.H13.L32A726i
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoOfNoComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.EmptyFaithful.T1515Der

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_no_component_726 {X : Subgroup G}
    (hE : ∀ K : Subgroup G, ¬ IsComponentIn K X) (hodd : oddCoreIn X = ⊥) : CharTwo X :=
  CFSG.QuasithinUnique.charTwo_of_forall_not_isComponentIn hE hodd

omit [Finite G] in
theorem eq_bot_of_oddCoreIn_eq_bot_726 {X : Subgroup G} (h : oddCoreIn X = ⊥) {N : Subgroup G}
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hn : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hodd' : Odd (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ fusionOddCore ↥X := le_sSup ⟨hn, hodd'⟩
  rw [eq_bot_iff]
  intro n hn'
  have hmem : n ∈ oddCoreIn X := ⟨⟨n, hNX hn'⟩, hle hn', rfl⟩
  rw [h] at hmem
  exact hmem

section Ctx

variable {T L V H D : Subgroup G}

theorem exists_z_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) :
    ∃ z ∈ fsuV1 T V, z ≠ 1 ∧ z * z = 1 ∧ z ∈ T ∧ z ∈ Subgroup.centralizer (T : Set G) ∧
      Subgroup.centralizer ({z} : Set G) = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hzV⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (v1_ne_bot_726 hc)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨hzT, hzc, hz2⟩ := mem_omegaOneCenter_726 (Subgroup.mem_inf.mp hzV).2
  have hzpow : Subgroup.zpowers z = fsuV1 T V :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzV)
      (by rw [card_v1_726 hc hdD hdV, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1'])
  refine ⟨z, hzV, hz1', hz2, hzT, hzc, ?_⟩
  rw [hc.eq_hz]
  show Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (fsuV1 T V : Set G)
  rw [← hzpow, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem lemma115Hyp_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {z : G}
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzT : z ∈ T) (hzc : z ∈ Subgroup.centralizer (T : Set G))
    (hzH : Subgroup.centralizer ({z} : Set G) = H) :
    Lemma115Hyp (Subgroup.centralizer ({d} : Set G)) (T ⊓ Subgroup.centralizer ({d} : Set G)) H
      z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd1 : d ≠ 1 := ne_one_of_not_mem_v1_726 hdV
  have hdo : orderOf d = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1
  have hT := hc.setting.hyp.hyp.h13.sylow
  refine lemma116 hc.setting.hyp.fsu.qtke.2.1 (B := Subgroup.zpowers d) ?_ ?_ ?_
    (centralizer_le_normalizer_zpowers_726 d) (isSylowTwoOf_td_726 hc hdD hdV htT htd)
    ⟨le_top, hT.1, ?_⟩ inf_le_left hzT hzc hz1 (by rw [pow_two]; exact hz2) hc.max_two_local
    hzH.le
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdo, pow_one])
  · exact fun h => hd1 (Subgroup.zpowers_eq_bot.mp h)
  · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers d))
  · show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2

theorem isElemAbelian_u_726 (hc : Ctx726 G T L V H D) : IsElemAbelian 2 (fsuU T V) := by
  have hab := hc.setting.hyp.abelian
  have hcomm : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm (⟨a, ha⟩ : ↥(fsuU T V)) ⟨b, hb⟩)
  rw [F7.isElemAbelian_iff]
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, -, v, hv, rfl⟩ := hx
    rw [conj_pow, (U3.mem_reducedAggregate' (hc.setting.hyp.fsu.irrPlus.1 hv)).2.2]
    group
  | one => simp
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hcomm _ ha _ hb) 2, iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

theorem u_le_h_726 (hc : Ctx726 G T L V H D) : fsuU T V ≤ H := by
  have hcomm := (F7.isElemAbelian_iff.mp (isElemAbelian_u_726 hc)).1
  have hV1U : fsuV1 T V ≤ fsuU T V := (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  rw [hc.eq_hz]
  intro u hu
  rw [L32A.hz, Subgroup.mem_centralizer_iff]
  intro v hv
  exact hcomm _ (hV1U hv) _ hu

theorem u_le_l1_726 (hc : Ctx726 G T L V H D) : fsuU T V ≤ L32A.l1 T L V := by
  rw [← hc.u_eq]
  refine (Subgroup.commutator_le).mpr fun u hu l hl => ?_
  have hn := (Subgroup.mem_normalizer_iff.mp (hc.l1_normal (u_le_h_726 hc hu)) l).mp hl
  rw [commutatorElement_def]
  exact (L32A.l1 T L V).mul_mem hn ((L32A.l1 T L V).inv_mem hl)

theorem pRank_pCoreOf_le_two_726 (hc : Ctx726 G T L V H D) {X : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p X) ≤ 2 := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have h := (isSQTKCat_of_pCoreOf_ne_bot_726 hc hX).1
  have h' := CFSG.SectionRank.isStronglyQuasithin_iff.mp h p hp hp2
  rw [pRank_top_subtype] at h'
  exact (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p X)).trans h'

theorem oddCoreIn_eq_bot_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    oddCoreIn (Subgroup.centralizer ({d} : Set G)) = ⊥ := by
  obtain ⟨z, hzV, hz1, hz2, hzT, hzc, hzH⟩ := exists_z_726 hc hdD hdV
  have hinv := (lemma115Hyp_726 hc hdD hdV hd2 htT htd hz1 hz2 hzT hzc hzH).inverts_oddCoreIn
  have hL1Gd : L32A.l1 T L V ≤ Subgroup.centralizer ({d} : Set G) :=
    (l1_le_k_726 hc).trans ((k_le_hd_726 hc hdD).trans inf_le_right)
  have hUe := isElemAbelian_u_726 hc
  have hUc : fsuU T V ≤
      Subgroup.centralizer (oddCoreIn (Subgroup.centralizer ({d} : Set G)) : Set G) :=
    a126_one hL1Gd (by rw [hc.l1_eq]; exact opResidual_two_oTwoUpper1516 _)
      ((u_le_l1_726 hc).trans hL1Gd) (B2F.isPGroup_of_isElemAbelian hUe) hc.u_eq
      (pRank_pCoreOf_le_two_726 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 inf_le_right le_rfl))
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hUe)
  have hzU : z ∈ fsuU T V := le_conjClosure V _ (Subgroup.mem_inf.mp hzV).1
  rw [eq_bot_iff]
  intro y hy
  have hyz := Subgroup.mem_centralizer_iff.mp (hUc hzU) y hy
  have h1 : z⁻¹ * y * z = y := by
    calc z⁻¹ * y * z = z⁻¹ * (y * z) := by group
      _ = z⁻¹ * (z * y) := by rw [hyz]
      _ = y := by group
  have h2 : y = y⁻¹ := by rw [← hinv y hy, h1]
  have hy2 : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel y
  have hodd := odd_card_oddCoreIn (Subgroup.centralizer ({d} : Set G))
  have hord : orderOf (⟨y, hy⟩ : ↥(oddCoreIn (Subgroup.centralizer ({d} : Set G)))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hy2))
  have hord' := orderOf_dvd_natCard
    (⟨y, hy⟩ : ↥(oddCoreIn (Subgroup.centralizer ({d} : Set G))))
  have hone : orderOf (⟨y, hy⟩ : ↥(oddCoreIn (Subgroup.centralizer ({d} : Set G)))) = 1 := by
    have := Nat.dvd_gcd hord hord'
    rw [(Nat.coprime_two_left.mpr hodd).gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (orderOf_eq_one_iff.mp hone))

theorem oddCoreModTwoTrivial_gd_726 (hC129 : ASC129Statement G)
    (h3x : NQCore.Prop134ThreeExtraspecial) (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t)
    (hGdH : ¬ Subgroup.centralizer ({d} : Set G) ≤ H) :
    OddCoreModTwoTrivial (Subgroup.centralizer ({d} : Set G)) :=
  oddCoreModTwoTrivial_726 hC129 hc hdD hdV hd2 htT htd inf_le_right le_rfl hGdH
    (pCoreOf_h_le_td_of_g0_726 h3x hc hdD hdV hd2 htT htd inf_le_right le_rfl hGdH)
    fun _ hNX hXN hodd => eq_bot_of_oddCoreIn_eq_bot_726
      (oddCoreIn_eq_bot_726 hc hdD hdV hd2 htT htd) hNX hXN hodd

theorem exists_component_726 (hC129 : ASC129Statement G) (h121 : Id2519.Prop121Three)
    (hC27 : KG14726C27C) (h3x : NQCore.Prop134ThreeExtraspecial) (hc : Ctx726 G T L V H D)
    {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T)
    (htd : t * d ≠ d * t) (hGdH : ¬ Subgroup.centralizer ({d} : Set G) ≤ H) :
    ∃ Ld : Subgroup G, IsComponentIn Ld (Subgroup.centralizer ({d} : Set G)) := by
  by_contra hne
  push Not at hne
  exact false_of_charTwo_726 hC129 h121 hC27 hc hdD hdV hd2 htT htd inf_le_right le_rfl hGdH
    (pCoreOf_h_le_td_of_g0_726 h3x hc hdD hdV hd2 htT htd inf_le_right le_rfl hGdH)
    (charTwo_of_no_component_726 hne (oddCoreIn_eq_bot_726 hc hdD hdV hd2 htT htd))

end Ctx

end CFSG.Quasithin.H13.L32A
