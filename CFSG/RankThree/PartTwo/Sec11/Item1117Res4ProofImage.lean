module

import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1116KFact
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.RFacts
public import CFSG.RankThree.PartTwo.Sec11.Skeleton

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def AutThree1129 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c : G),
    (∃ (X : Type) (_ : Group X), IsList119 X ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X)) →
    c ∈ Subgroup.normalizer (Y : Set G) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) → (Nat.card K).factorization 3 = 1 →
    ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.normalizer (Y : Set G) →
      Nat.card Q ≤ 27 * Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y : Subgroup G)

namespace Item1117Res4Proof

section Generic

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isPGroup (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G) {e : G}
    (he1 : e ≠ 1) (he3 : e ^ 3 = 1) {Q : Subgroup G} (hQ3 : IsPGroup 3 Q)
    (hQC : Q ≤ Subgroup.centralizer ({e} : Set G)) :
    ∀ L ∈ thetaComponentsAt 3 e, Q ≤ Subgroup.normalizer (L : Set G) := by
  have := hG.isSimpleGroup
  set C := Subgroup.centralizer ({e} : Set G)
  have hCtop : C ≠ ⊤ := by
    intro hC
    have hcz : e ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hC ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hZ : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with
        hb | ht
      · exact hb
      · exfalso
        obtain ⟨u, v, huv⟩ := hG.nonabelian
        have hu : u ∈ Subgroup.center G := ht ▸ Subgroup.mem_top u
        exact huv (Subgroup.mem_center_iff.mp hu v).symm
    rw [hZ, Subgroup.mem_bot] at hcz
    exact he1 hcz
  have hC4 : SectionFourHyp C := hG.sectionFourHyp hCtop
  have hQ' : IsPGroup 3 (Q.subgroupOf C) := hQ3.comap_subtype
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcore : CFSG.pCore 3 C ≠ ⊥ := by
    set e' : C := ⟨e, heC⟩
    have he'3 : orderOf e' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime he3 he1
    have hZn : (Subgroup.zpowers e').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hge : g * e' = e' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * e' ^ k * g⁻¹ = e' ^ k := by
        rw [(Commute.zpow_right hge k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers e' k
    have hZ3 : IsPGroup 3 (Subgroup.zpowers e') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he'3, pow_one])
    have hZle : Subgroup.zpowers e' ≤ CFSG.pCore 3 C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have he'1 : e' = 1 := by
      have := hZle (Subgroup.mem_zpowers e')
      rwa [hbot, Subgroup.mem_bot] at this
    exact he1 (congrArg Subtype.val he'1)
  intro L hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hN := h45 C hC4 (Q.subgroupOf C) hQ' (Or.inl hcore) L' hL'
  intro q hq
  have hqN : (⟨q, hQC hq⟩ : C) ∈ Subgroup.normalizer (L' : Set C) :=
    hN (Subgroup.mem_subgroupOf.mpr hq)
  rw [Subgroup.mem_normalizer_iff] at hqN ⊢
  intro z
  constructor
  · rintro ⟨z', hz', rfl⟩
    exact ⟨_, (hqN z').mp hz', rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have hyz' : (y : G) = q * z * q⁻¹ := hyz
    have hzC : z ∈ C := by
      have hz' : z = q⁻¹ * (y : G) * q := by
        rw [hyz']
        group
      rw [hz']
      exact C.mul_mem (C.mul_mem (C.inv_mem (hQC hq)) y.2) (hQC hq)
    refine ⟨⟨z, hzC⟩, (hqN ⟨z, hzC⟩).mpr ?_, rfl⟩
    have : (⟨q, hQC hq⟩ : C) * ⟨z, hzC⟩ * (⟨q, hQC hq⟩ : C)⁻¹ = y := Subtype.ext hyz'.symm
    rw [this]
    exact hy

end Generic

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem card_sec11K_factorization_eq_one (h45 : Sec4.Item4_5)
    (h : Sec11Data G A c L a R Y d x s r g) (hx : orderOf x = 9) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y') :
    (Nat.card (sec11K L e)).factorization 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hKL : sec11K L e ≤ L := sec11K_le L e
  have hKe : sec11K L e ≤ Subgroup.centralizer ({e} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (sec11K L e)
  have hxL : orderOf x = 3 ^ (Nat.card L).factorization 3 := by
    rw [← Nat.card_zpowers, ← h.inf_L_eq]
    exact hstd.isSylowOf_inf_L.card_eq
  have hdvd : 3 ^ (Nat.card (sec11K L e)).factorization 3 ∣ 3 ^ (Nat.card L).factorization 3 :=
    Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le hKL) 3
  have hne : 3 ^ (Nat.card (sec11K L e)).factorization 3 ≠ 3 ^ (Nat.card L).factorization 3 := by
    intro heq
    have hTL : IsSylowOf 3 T L :=
      CFSG.ABGLocalTools.isSylowOf_of_card (hT.le.trans hKL) (hT.card_eq.trans heq)
    exact Item1116Proof.not_le_centralizer_of_isSylowOf hstd hTL (hT.le.trans hKe)
  rw [← hxL, hx] at hdvd hne
  have hdK : d ∈ sec11K L e := hstd.d_mem_sec11K h.inf_eq
  have hd3 : orderOf d = 3 := Item1117Proof.orderOf_d h
  have h3K : 3 ∣ Nat.card (sec11K L e) := by
    have := Subgroup.orderOf_dvd_natCard (sec11K L e) hdK
    rwa [hd3] at this
  have hpos : 1 ≤ (Nat.card (sec11K L e)).factorization 3 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3K
  have hle : (Nat.card (sec11K L e)).factorization 3 ≤ 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    by_contra h2
    push Not at h2
    have : 3 ^ 3 ≤ 3 ^ (Nat.card (sec11K L e)).factorization 3 :=
      Nat.pow_le_pow_right (by norm_num) h2
    omega
  have h2 : (Nat.card (sec11K L e)).factorization 3 ≠ 2 := fun h2 => hne (by rw [h2]; norm_num)
  omega

theorem eq_of_case_two (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hK : AutThree1129) (h : Sec11Data G A c L a R Y d x s r g) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y')
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) (hx9 : orderOf x = 9)
    {X : Type} [Group X] (hX : IsList119 X)
    (hXe : Nonempty (sec11YA e Y' A ≃* Multiplicative (ZMod 3) × X)) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q)
    (hV : Q ⊓ Sec4.thetaQuotCentralizer Y' ≤ Subgroup.zpowers e) :
    Q = sec11P R g ⊓ Subgroup.centralizer {e} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hXe
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have hAe := h.mem_partTwoF.1
  have he3 : e ^ 3 = 1 := hAe.2 e heA
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hT1 := Item1117StepsProof.le_card_inf_centralizer h45 h113 h117 h hsc hrs heA hecd
  have hT2 := Item1117ResProof.card_inf_centralizer_le h45 h113 h117 h hsc hrs heA hecd
  rw [hx9] at hT2
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  have hQY : Q ≤ Subgroup.normalizer (Y' : Set G) :=
    le_normalizer_of_isPGroup h45 h.toTheoremFourHyp he1 he3 hQ3 hQ.le Y' hY'
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨ψ⟩ := Item1116Proof.nonempty_thetaQuot_equiv_commutator hY' hAC hAY hAc φ
  have hQle := hK G Y' (sec11K L e) c ⟨X, inferInstance, hX, ⟨ψ⟩⟩ (hAY h.mem_A)
    (hAe.2 c h.mem_A) (mem_thetaComponentsIn_sec11K_inf hstd)
    (kType119 G A c L e R Y' hstd d h.inf_eq hA')
    (card_sec11K_factorization_eq_one h45 h hx9 heA hecd hY' hKY') Q hQ3 hQY
  have hCe : Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y' : Subgroup G) ≤ 3 := by
    calc Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y' : Subgroup G) ≤
          Nat.card (Subgroup.zpowers e) := Subgroup.card_le_of_le hV
      _ = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  refine (Subgroup.eq_of_le_of_card_ge hTQ ?_).symm
  calc Nat.card Q ≤ 27 * Nat.card (Q ⊓ Sec4.thetaQuotCentralizer Y' : Subgroup G) := hQle
    _ ≤ 27 * 3 := Nat.mul_le_mul_left _ hCe
    _ ≤ Nat.card T := by omega

end Data

end Item1117Res4Proof

end CFSG.RankThree.PartTwo.Sec11
