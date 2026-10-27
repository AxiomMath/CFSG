module

public import CFSG.RankThree.PartTwo.Sec12.Item122
public import CFSG.RankThree.PartTwo.Sec12.Item123
public import CFSG.RankThree.PartTwo.Sec12.Item124
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_isPGroup {c : G} (hc : orderOf c = 3) {P : Subgroup G}
    (hP : IsPGroup 3 P) (hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    P ≤ Subgroup.centralizer ({c} : Set G) := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hg' : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (hPH hg) c).mp (Subgroup.mem_zpowers c)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_conj_mem_zpowers hc hgc hg')

omit [Finite G] in
theorem pCore_centralizer_ne_bot {c : G} (hc : orderOf c = 3) :
    CFSG.pCore 3 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ := by
  set C := Subgroup.centralizer ({c} : Set G)
  set c' : C := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hN : (Subgroup.zpowers c').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc'Z)
  have hc'3 : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc
  have hP : IsPGroup 3 (Subgroup.zpowers c') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
  have hle : Subgroup.zpowers c' ≤ CFSG.pCore 3 C := le_sSup ⟨hN, hP⟩
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hc'3
  norm_num at hc'3

theorem le_normalizer_of_mem_thetaComponentsAt (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {c : G} (hc : orderOf c = 3) {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    {P : Subgroup G} (hP : IsPGroup 3 P)
    (hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hc1 : c ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc; norm_num at hc
  have hS4 : SectionFourHyp C := hG.sectionFourHyp (centralizer_ne_top_of_theoremFourHyp hG hc1)
  obtain ⟨L', hL', rfl⟩ := hL
  have hPC := le_centralizer_of_isPGroup hc hP hPH
  have hres := h45 C hS4 (P.subgroupOf C) hP.comap_subtype
    (Or.inl (pCore_centralizer_ne_bot hc)) L' hL'
  intro g hg
  have hg' : (⟨g, hPC hg⟩ : C) ∈ Subgroup.normalizer (L' : Set C) :=
    hres (Subgroup.mem_subgroupOf.mpr hg)
  exact (Sec13.coe_mem_normalizer_map_iff C).mpr hg'

theorem sylow_le_normalizer_of_item4_5 (h45 : Sec4.Item4_5) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec12Std G A c L → ∀ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
          P ≤ Subgroup.normalizer (L : Set G) := by
  intro G _ _ A c L h P hP
  exact le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.orderOf_c
    h.mem_thetaComponentsAt hP.isPGroup (hP.le.trans inf_le_right)

theorem Sec12Std.card_inf_eq_nine (h122 : Item122) {A L : Subgroup G} {c : G}
    (h : Sec12Std G A c L) : Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hZ := card_center_thetaQuot_eq_three_of_item122 h122 h
  have hB3 : IsPGroup 3 (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
  have hBL := card_inf_le_card_center_thetaQuot hB3 inf_le_right (L := L)
  rw [hZ] at hBL
  have hA27 : Nat.card A = 27 := h.isE27.2
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hc3 := h.orderOf_c
  have hcT : c ∈ A ⊓ L := ⟨h.mem_A, h.mem_L⟩
  have hcB : c ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨h.mem_A, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)⟩
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  ·
    exfalso
    rw [pow_zero] at hk
    have h1 := (Subgroup.card_eq_one).mp hk
    rw [h1] at hcT
    exact h.ne_one hcT
  ·
    exfalso
    have hTc : A ⊓ L = Subgroup.zpowers c := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcT) ?_).symm
      rw [hk, Nat.card_zpowers, hc3, pow_one]
    have hTB : A ⊓ L ≤ A ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hTc]
      exact Subgroup.zpowers_le.mpr hcB
    have hAB : A ⊓ Subgroup.centralizer (L : Set G) = A :=
      (sup_eq_left.mpr hTB).symm.trans h.sup_eq
    have := h.card_B
    rw [hAB, hA27] at this
    norm_num at this
  · rw [hk]
    norm_num
  ·
    exfalso
    have hAL : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA27]; norm_num)
    have hBL' : A ⊓ Subgroup.centralizer (L : Set G) ⊓ L =
        A ⊓ Subgroup.centralizer (L : Set G) := by
      refine inf_eq_left.mpr (le_trans inf_le_left ?_)
      rw [← hAL]
      exact inf_le_right
    rw [hBL', h.card_B] at hBL
    norm_num at hBL

section Lift

variable {L : Type*} [Group L] [Finite L]

theorem injOn_mk_of_coprime (N : Subgroup L) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {S : Subgroup L} (hS : IsPGroup 3 S) : Set.InjOn (QuotientGroup.mk' N) (S : Set L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx y hy hxy
  have hxy' : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
  have hS' : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdisj : Disjoint S N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN))
  have h1 : x⁻¹ * y = 1 := (Subgroup.disjoint_def.mp hdisj) hS' hxy'
  rw [inv_mul_eq_one] at h1
  exact h1

theorem exists_isPGroup_normalizer_moves (N : Subgroup L) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {T : Subgroup L} (hT : IsPGroup 3 T) {xb : L ⧸ N} (hx3 : IsPGroup 3 (Subgroup.zpowers xb))
    (hxT : xb ∈ Subgroup.normalizer ((T.map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) :
      Set (L ⧸ N)))
    {t : L} (hmove : xb * (t : L ⧸ N) * xb⁻¹ ≠ (t : L ⧸ N)) :
    ∃ x ∈ Subgroup.normalizer (T : Set L), IsPGroup 3 (Subgroup.zpowers x) ∧
      x * t * x⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  set Tb : Subgroup (L ⧸ N) := T.map π with hTb
  have hTb3 : IsPGroup 3 Tb := hT.map π
  have hxTb : Subgroup.zpowers xb ≤ Subgroup.normalizer (Tb : Set (L ⧸ N)) :=
    Subgroup.zpowers_le.mpr hxT
  set Rb : Subgroup (L ⧸ N) := Subgroup.zpowers xb ⊔ Tb with hRb
  have hRb3 : IsPGroup 3 Rb := hx3.to_sup_of_normal_right' hTb3 hxTb
  have hRbN : Rb ≤ Subgroup.normalizer (Tb : Set (L ⧸ N)) := sup_le hxTb Subgroup.le_normalizer
  set Q : Subgroup L := Rb.comap π with hQ
  have hTQ : T ≤ Q := fun y hy => le_sup_right (b := Tb) (a := Subgroup.zpowers xb) ⟨y, hy, rfl⟩
  obtain ⟨S, hTS⟩ := (hT.comap_subtype (K := Q)).exists_le_sylow
  set S' : Subgroup L := (S : Subgroup Q).map Q.subtype with hS'
  have hS'3 : IsPGroup 3 S' := S.isPGroup'.map Q.subtype
  have hS'Q : S' ≤ Q := Subgroup.map_subtype_le _
  have hTS' : T ≤ S' := fun y hy => ⟨⟨y, hTQ hy⟩, hTS (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hinj := injOn_mk_of_coprime N hN hS'3
  have hQcard : Nat.card Q = Nat.card N * Nat.card Rb :=
    QuotientGroup.card_preimage_mk N (Rb : Set (L ⧸ N))
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hRb3
  have hScard : Nat.card S' = Nat.card Rb := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity, hQcard,
      hr, Nat.factorization_mul (by
        intro h0
        rw [h0] at hN
        exact hN (dvd_zero 3)) (by positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.prime_three.factorization_pow,
      Finsupp.single_eq_same,
      zero_add]
  have hmap : S'.map π = Rb := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr hS'Q) ?_
    change Nat.card Rb ≤ Nat.card (↑(S'.map π) : Set (L ⧸ N))
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    exact hScard.ge
  have hxRb : xb ∈ Rb := le_sup_left (b := Tb) (Subgroup.mem_zpowers xb)
  rw [← hmap] at hxRb
  obtain ⟨x, hxS, hxx⟩ := hxRb
  have hS'T : S' ≤ Subgroup.normalizer (T : Set L) := by
    intro s hs
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hsu : s * u * s⁻¹ ∈ S' := S'.mul_mem (S'.mul_mem hs (hTS' hu)) (S'.inv_mem hs)
    have hπs : π s ∈ Subgroup.normalizer (Tb : Set (L ⧸ N)) :=
      hRbN (hmap ▸ Subgroup.mem_map_of_mem π hs)
    have hπu : π (s * u * s⁻¹) ∈ Tb := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hπs (π u)).mp ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hπu
    have he : u' = s * u * s⁻¹ := hinj (hTS' hu') hsu hu'e
    rw [← he]
    exact hu'
  refine ⟨x, hS'T hxS, hS'3.to_le (Subgroup.zpowers_le.mpr hxS), fun he => hmove ?_⟩
  have h1 := congrArg π he
  rw [map_mul, map_mul, map_inv, hxx] at h1
  exact h1

end Lift

theorem isQuasisimple_thetaQuot_of_mem {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {c x : G} (hx : x * c = c * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hcx : Commute x c := hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, rfl⟩
    rw [(hcx.zpow_right n).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c n
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : y = c ^ n := by
      rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group, ← hn, (hcx.inv_left.zpow_right n).eq,
        inv_mul_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers c n

theorem Sec12Std.exists_mem_inf_moves (h122 : Item122) (h45 : Sec4.Item4_5)
    (hK : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G} (h : Sec12Std G A c L)
    {P : Subgroup G} (hP : IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := h.isE27.1.2
  set N := aschbacherSolvableCore 3 L with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  set π := QuotientGroup.mk' N with hπ
  set T : Subgroup L := (A ⊓ L).subgroupOf L with hTdef
  have hT9 : Nat.card T = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans
      (h.card_inf_eq_nine h122)
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  set Tb : Subgroup (L ⧸ N) := T.map π with hTbdef
  have hinjT := injOn_mk_of_coprime N hN3 hT3
  have hTb9 : Nat.card Tb = 9 := by
    rw [← hT9]
    change Nat.card (↑(T.map π) : Set (L ⧸ N)) = Nat.card (T : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinjT]
  have hTbe : CFSG.Assembly.IsElemAbelian 3 Tb := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      apply Subtype.ext
      change (u : L ⧸ N) * v = v * u
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcommA _ (Subgroup.mem_subgroupOf.mp hu').1 _
        (Subgroup.mem_subgroupOf.mp hv').1)
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hexpA _ (Subgroup.mem_subgroupOf.mp hu).1)
      rw [this, map_one]
  have hZ3 := card_center_thetaQuot_eq_three_of_item122 h122 h
  set c' : L := ⟨c, h.mem_L⟩ with hc'
  have hc'T : c' ∈ T := Subgroup.mem_subgroupOf.mpr ⟨h.mem_A, h.mem_L⟩
  have hc'Z : c' ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer g.2))
  have hπcZ : π c' ∈ Subgroup.center (L ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨c', hc'Z, rfl⟩
  have hc'3 : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact h.orderOf_c
  have hπc1 : π c' ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hN3
    have h' := orderOf_dvd_natCard (⟨c', h1⟩ : N)
    rwa [Subgroup.orderOf_mk, hc'3] at h'
  have hZT : Subgroup.center (L ⧸ N) ≤ Tb := by
    have hle : Subgroup.zpowers (π c') ≤ Subgroup.center (L ⧸ N) :=
      Subgroup.zpowers_le.mpr hπcZ
    have hπc3 : orderOf (π c') = 3 := by
      refine orderOf_eq_prime ?_ hπc1
      have hc'p : c' ^ 3 = 1 := by rw [← hc'3]; exact pow_orderOf_eq_one c'
      rw [← map_pow, hc'p, map_one]
    have heq : Subgroup.zpowers (π c') = Subgroup.center (L ⧸ N) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hZ3, Nat.card_zpowers, hπc3])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr ⟨c', hc'T, rfl⟩
  obtain ⟨xb, hxN, hx3, tb, htb, hmove⟩ :=
    hK _ (isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt) (h122 G A c L h) Tb hTbe
      hTb9 hZT
  obtain ⟨t, htT, rfl⟩ := htb
  obtain ⟨x, hxT, hx3', hxt⟩ := exists_isPGroup_normalizer_moves N hN3 hT3 hx3 hxN hmove
  have hxL : (x : G) ∈ L := x.2
  have hxAL : (x : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyT : (⟨y, hy.2⟩ : L) ∈ T := Subgroup.mem_subgroupOf.mpr hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hxT _).mp hyT
    exact Subgroup.mem_subgroupOf.mp h1
  have hBx : ∀ b ∈ A ⊓ Subgroup.centralizer (L : Set G), (x : G) * b * (x : G)⁻¹ = b :=
    fun b hb => by
      rw [Subgroup.mem_centralizer_iff.mp hb.2 _ hxL, mul_inv_cancel_right]
  have hxA : (x : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have hBN : A ⊓ Subgroup.centralizer (L : Set G) ≤
        Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun b hb => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hcommA b hb.1 y hy.1, mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyA : y ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hb.1) hy.1) hb.1
          simpa [mul_assoc] using this
        rwa [hcommA b hb.1 y hyA, mul_inv_cancel_right] at hy
    have ha' : a ∈ ((A ⊓ Subgroup.centralizer (L : Set G) ⊔ A ⊓ L : Subgroup G) : Set G) := by
      rw [h.sup_eq]
      exact ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at ha'
    obtain ⟨b, hb, y, hy, rfl⟩ := ha'
    have e : (x : G) * (b * y) * (x : G)⁻¹ = ((x : G) * b * (x : G)⁻¹) *
        ((x : G) * y * (x : G)⁻¹) := by group
    rw [e, hBx b hb]
    exact A.mul_mem hb.1 ((Subgroup.mem_normalizer_iff.mp hxAL y).mp hy).1
  have hxH : (x : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hxL))
  set W := Subgroup.normalizer (A : Set G) with hW
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hPL : P ≤ Subgroup.normalizer (L : Set G) :=
    sylow_le_normalizer_of_item4_5 h45 G A c L h P hP
  set Y := P ⊔ (L ⊓ W) with hY
  have hLC : L ⊓ W ≤ W ⊓ H := fun y hy => ⟨hy.2, mem_normalizer_zpowers_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hy.1))⟩
  have hYWH : Y ≤ W ⊓ H := sup_le hP.le hLC
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hPL (inf_le_left.trans Subgroup.le_normalizer)
  have hPY : IsSylowOf 3 P Y := hP.of_le le_sup_left hYWH
  have hxY : (x : G) ∈ Y := le_sup_right (a := P) ⟨hxL, hxA⟩
  obtain ⟨Q, hQ⟩ := hPY
  have hxp : IsPGroup 3 ((Subgroup.zpowers (x : G)).subgroupOf Y) :=
    (hx3'.map L.subtype).comap_subtype.of_equiv (by
      rw [MonoidHom.map_zpowers]
      exact MulEquiv.refl _)
  obtain ⟨Q', hQ'⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q' Q
  have hxQ' : (⟨x, hxY⟩ : Y) ∈ (Q' : Subgroup Y) :=
    hQ' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
  have hgx : g * ⟨x, hxY⟩ * g⁻¹ ∈ (Q : Subgroup Y) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hxQ'
  have hgxP : (g : G) * x * (g : G)⁻¹ ∈ P := hQ ▸ ⟨_, hgx, rfl⟩
  have hgL : (g : G) ∈ Subgroup.normalizer (L : Set G) := hYL g.2
  have hgA : (g : G) ∈ W := (hYWH g.2).1
  refine ⟨(g : G) * x * (g : G)⁻¹, ⟨hgxP, (Subgroup.mem_normalizer_iff.mp hgL _).mp hxL⟩,
    (g : G) * t * (g : G)⁻¹, ⟨(Subgroup.mem_normalizer_iff.mp hgA _).mp
      (Subgroup.mem_subgroupOf.mp htT).1, (Subgroup.mem_normalizer_iff.mp hgL _).mp t.2⟩,
    fun he => hxt (Subtype.ext ?_)⟩
  have he' : (x : G) * t * (x : G)⁻¹ = t := by
    have := congrArg (fun z => (g : G)⁻¹ * z * g) he
    simpa [mul_assoc] using this
  simpa using he'

theorem item123_of_inputs (h41 : Sec4.Item4_1) (h43 : Sec4.Item4_3) (h45 : Sec4.Item4_5)
    (hcov : Sec4.Census.CoverInputs46) (hK1 : KFacts.KS12CoverExclusion)
    (hK2 : KFacts.KS12NormalizerMoves) : Item123 := by
  have h122 := item122_of h41 h43 hcov hK1
  exact item123_of (sylow_le_normalizer_of_item4_5 h45)
    (fun _ _ _ _ _ _ h => h.card_inf_eq_nine h122)
    (fun _ _ _ _ _ _ h _ hP => h.exists_mem_inf_moves h122 h45 hK2 hP)

theorem item124_of_inputs (h41 : Sec4.Item4_1) (h43 : Sec4.Item4_3) (h45 : Sec4.Item4_5)
    (hcov : Sec4.Census.CoverInputs46) (hK1 : KFacts.KS12CoverExclusion)
    (hK2 : KFacts.KS12NormalizerMoves) : Item124 :=
  item124_of_item123 (item123_of_inputs h41 h43 h45 hcov hK1 hK2)

end CFSG.RankThree.PartTwo.Sec12
