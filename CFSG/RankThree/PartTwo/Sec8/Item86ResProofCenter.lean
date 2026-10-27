module

public import CFSG.RankThree.PartTwo.KFacts.K72LStar
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofUnitary
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Timmesfeld.Orders
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {P : Subgroup G} {g : G}
    (h : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem three_dvd_card_projSL_two {m : ℕ} (hm : 1 ≤ m) :
    3 ∣ Nat.card (projSL 2 (GaloisField 2 m)) := by
  rw [Sec21.card_projSL_two m hm]
  refine Dvd.dvd.mul_left ?_ _
  have h := Nat.sub_one_dvd_pow_sub_one 4 m
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num at h ⊢
  exact h

theorem theta_inf_le_theta {L X K : Subgroup G} (hKL : K ≤ L) (hKX : K ≤ X) {m : ℕ}
    (hm : 2 ≤ m) (e : imageModTheta L K ≃* projSL 2 (GaloisField 2 m)) :
    (aschbacherSolvableCore 3 X).map X.subtype ⊓ K ≤
      (aschbacherSolvableCore 3 L).map L.subtype := by
  set θX := (aschbacherSolvableCore 3 X).map X.subtype with hθX
  set N := θX ⊓ K with hN
  set Kb := imageModTheta L K with hKb
  set Nb := imageModTheta L N with hNb
  have hNK : N ≤ K := inf_le_right
  have hNL : N ≤ L := hNK.trans hKL
  have hNbKb : Nb ≤ Kb := Subgroup.map_mono (fun y hy => hNK hy)
  have : IsSimpleGroup (projSL 2 (GaloisField 2 m)) := Sec21.isSimpleGroup_projSL_two hm
  have hsimple : IsSimpleGroup Kb := e.isSimpleGroup
  have hnorm : (Nb.subgroupOf Kb).Normal := by
    constructor
    intro u hu g
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    obtain ⟨κ, hκ, hκg⟩ := g.2
    obtain ⟨ν, hν, hνu⟩ := hu
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hκ hν
    have hκX : (κ : G) ∈ X := hKX hκ
    have hmem : (κ : G) * ν * (κ : G)⁻¹ ∈ N := by
      refine ⟨?_, K.mul_mem (K.mul_mem hκ (hNK hν)) (K.inv_mem hκ)⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (KFacts.normalizer_le_normalizer_theta X (Subgroup.le_normalizer hκX)) _).mp hν.1
    refine ⟨κ * ν * κ⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hκg, hνu]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nb.subgroupOf Kb) with hbot | htop
  ·
    have hNb1 : Nb = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact le_bot_iff.mp (fun y hy => hbot.le_bot (Subgroup.mem_inf.mpr ⟨hy, hNbKb hy⟩))
    intro ν hν
    have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨ν, hNL hν⟩ ∈ Nb :=
      ⟨⟨ν, hNL hν⟩, hν, rfl⟩
    rw [hNb1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact ⟨_, hmem, rfl⟩
  ·
    exfalso
    have hKbNb : Kb ≤ Nb := by
      rw [Subgroup.subgroupOf_eq_top] at htop
      exact htop
    have h1 : 3 ∣ Nat.card Kb := by
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_card_projSL_two (by omega)
    have h2 : Nat.card Kb ∣ Nat.card N := by
      have h4 : Nat.card Kb = Nat.card Nb := by rw [le_antisymm hNbKb hKbNb]
      rw [h4]
      exact card_imageModTheta_dvd hNL
    have h3 : Nat.card N ∣ Nat.card (aschbacherSolvableCore 3 X) := by
      have := Subgroup.card_dvd_of_le (inf_le_left : N ≤ θX)
      rwa [hθX, Subgroup.card_map_of_injective X.subtype_injective] at this
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore X ((h1.trans h2).trans h3)

omit [Finite G] in
theorem commute_pow_iff {x y : G} (hx3 : x ^ 3 = 1) {j : ℕ} (hj : j = 1 ∨ j = 2) :
    Commute (x ^ j) y ↔ Commute x y := by
  constructor
  · intro h
    rcases hj with rfl | rfl
    · simpa using h
    · have hx : x = (x ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
      rw [hx]
      exact h.pow_left 2
  · intro h
    exact h.pow_left j

omit [Finite G] in
theorem inf_centralizer_mul_pow_eq {L : Subgroup G} {c d : G} (hcL : ∀ y ∈ L, c * y = y * c)
    (hd3 : d ^ 3 = 1) (i : ℕ) {j : ℕ} (hj : j = 1 ∨ j = 2) :
    L ⊓ Subgroup.centralizer ({c ^ i * d ^ j} : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hy => ?_
  have hci : Commute (c ^ i) y := (Commute.pow_left (hcL y hy) i)
  have key : Commute (c ^ i * d ^ j) y ↔ Commute (d ^ j) y := by
    constructor
    · intro h
      have h1 : c ^ i * (d ^ j * y) = c ^ i * (y * d ^ j) := by
        calc c ^ i * (d ^ j * y) = (c ^ i * d ^ j) * y := (mul_assoc _ _ _).symm
          _ = y * (c ^ i * d ^ j) := h.eq
          _ = (y * c ^ i) * d ^ j := (mul_assoc _ _ _).symm
          _ = (c ^ i * y) * d ^ j := by rw [hci.eq]
          _ = c ^ i * (y * d ^ j) := mul_assoc _ _ _
      exact mul_left_cancel h1
    · intro h
      exact hci.mul_left h
  rw [show (y * (c ^ i * d ^ j) = c ^ i * d ^ j * y) ↔ Commute (c ^ i * d ^ j) y from
    ⟨fun h => h.symm, fun h => h.eq.symm⟩, key, commute_pow_iff hd3 hj]
  exact ⟨fun h => h.eq.symm, fun h => h.symm⟩

end Helpers

section Preimage

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def preimageTheta (X T : Subgroup G) : Subgroup G :=
  ((imageModTheta X T).comap (QuotientGroup.mk' (aschbacherSolvableCore 3 X))).map X.subtype

theorem mem_preimageTheta_iff {X T : Subgroup G} (hTX : T ≤ X) {z : G} :
    z ∈ preimageTheta X T ↔ z ∈ X ∧ ∃ t ∈ T,
      t⁻¹ * z ∈ (aschbacherSolvableCore 3 X).map X.subtype := by
  constructor
  · rintro ⟨z', ⟨t', ht', hz'⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht'
    refine ⟨z'.2, t', ht', ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hz'
    exact ⟨_, hz', rfl⟩
  · rintro ⟨hzX, t, ht, w, hw, hwt⟩
    refine ⟨⟨z, hzX⟩, ⟨⟨t, hTX ht⟩, ht, ?_⟩, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨t, hTX ht⟩ : X)⁻¹ * ⟨z, hzX⟩ = w := Subtype.ext hwt.symm
    rw [this]
    exact hw

theorem le_preimageTheta {X T : Subgroup G} (hTX : T ≤ X) : T ≤ preimageTheta X T := by
  intro t ht
  rw [mem_preimageTheta_iff hTX]
  exact ⟨hTX ht, t, ht, by rw [inv_mul_cancel]; exact one_mem _⟩

theorem not_three_dvd_card_preimageTheta {X T : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup 2 T) :
    ¬ 3 ∣ Nat.card (preimageTheta X T) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := preimageTheta X T) 3 h3
  have hy3 : (y : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    omega
  obtain ⟨hyX, t, ht, hyθ⟩ := (mem_preimageTheta_iff hTX).mp y.2
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 X) with hq
  have himT : IsPGroup 2 (imageModTheta X T) := by
    have hT' : IsPGroup 2 (T.subgroupOf X) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
    exact hT'.map q
  have hyt : q ⟨y, hyX⟩ = q ⟨t, hTX ht⟩ := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwt⟩ := hyθ
    have : (⟨y, hyX⟩ : X)⁻¹ * ⟨t, hTX ht⟩ = w⁻¹ := by
      apply Subtype.ext
      change (y : G)⁻¹ * t = (w : G)⁻¹
      rw [show (w : G) = t⁻¹ * y from hwt]
      group
    rw [this]
    exact (aschbacherSolvableCore 3 X).inv_mem hw
  have hmem : q ⟨y, hyX⟩ ∈ imageModTheta X T := by
    rw [hyt]
    exact ⟨⟨t, hTX ht⟩, ht, rfl⟩
  obtain ⟨k, hk⟩ := himT ⟨_, hmem⟩
  have hk' : q ⟨y, hyX⟩ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hq3 : q ⟨y, hyX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyX⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hq1 : q ⟨y, hyX⟩ = 1 := by
    have h1 : orderOf (q ⟨y, hyX⟩) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hq3)
    have h2 : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  set z : aschbacherSolvableCore 3 X := ⟨⟨y, hyX⟩, hq1⟩ with hz
  have hz3 : z ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa [hz] using hy3))
  have hz1 : z ≠ 1 := fun h1 => hy1 (by
    have := congrArg (fun w : aschbacherSolvableCore 3 X => ((w : X) : G)) h1
    simpa [hz] using this)
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hdvd : orderOf z ∣ Nat.card (aschbacherSolvableCore 3 X) := orderOf_dvd_natCard z
  rw [hoz] at hdvd
  exact KFacts.not_three_dvd_card_aschbacherSolvableCore X hdvd

theorem mem_normalizer_preimageTheta {X T : Subgroup G} (hTX : T ≤ X) {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer (preimageTheta X T : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro z hz
  obtain ⟨hzX, t, ht, hzθ⟩ := (mem_preimageTheta_iff hTX).mp hz
  rw [mem_preimageTheta_iff hTX]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX z).mp hzX, g * t * g⁻¹,
    (Subgroup.mem_normalizer_iff.mp hgT t).mp ht, ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (KFacts.normalizer_le_normalizer_theta X hgX) _).mp hzθ
  have e : (g * t * g⁻¹)⁻¹ * (g * z * g⁻¹) = g * (t⁻¹ * z) * g⁻¹ := by group
  rw [e]
  exact h1

theorem mem_normalizer_preimageTheta_of_mem {X T : Subgroup G} (hTX : T ≤ X) {g : G}
    (hg : g ∈ Sec4.thetaQuotCentralizer X) :
    g ∈ Subgroup.normalizer (preimageTheta X T : Set G) := by
  obtain ⟨hgX, hgθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hg
  apply mem_normalizer_of_conj_mem
  intro z hz
  obtain ⟨hzX, t, ht, hzθ⟩ := (mem_preimageTheta_iff hTX).mp hz
  rw [mem_preimageTheta_iff hTX]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX z).mp hzX, t, ht, ?_⟩
  have e : t⁻¹ * (g * z * g⁻¹) = (t⁻¹ * z) * (z⁻¹ * (g * z * g⁻¹)) := by group
  rw [e]
  exact Subgroup.mul_mem _ hzθ (hgθ z hzX)

end Preimage

section Trivial

variable {G : Type} [Group G] [Finite G]

theorem card_imageModTheta_eq_of_mem_thetaQuotCentralizer {X : Subgroup G} {c : G}
    (hc : c ∈ Sec4.thetaQuotCentralizer X) (hc3 : c ^ 3 = 1)
    (hX : Group.IsPerfect (X ⧸ aschbacherSolvableCore 3 X)) :
    Nat.card (imageModTheta X (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer {c}))) =
      Nat.card (X ⧸ aschbacherSolvableCore 3 X) := by
  have hcN := (Sec6.mem_thetaQuotCentralizer_iff.mp hc).1
  have htriv : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) = 1 := by
    obtain ⟨y, hy, hyc⟩ := hc
    have hyc' : y = ⟨c, hcN⟩ := Subtype.ext hyc
    subst hyc'
    exact hy
  have htop : barCentralizer (Subgroup.zpowers c) X = ⊤ := by
    ext y
    simp [KFacts.mem_barCentralizer_zpowers_iff hcN, htriv]
  rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hcN ⟨1, by rw [pow_one]; exact hc3⟩,
    htop, inSubgroup_perfectResidual_of_isPerfect (Group.IsPerfect.top_iff.mpr hX),
    Subgroup.card_top]

theorem false_of_isGammaIndex_of_card_eq {A X : Subgroup G} {x : G} {m : ℕ}
    (h : IsGammaIndex A X x m)
    (hcard : Nat.card (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({x} : Set G)))) =
        Nat.card (X ⧸ aschbacherSolvableCore 3 X)) : False := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex h
  have htype := isGammaType_of_isGammaIndex h
  obtain ⟨-, -, -, ⟨k, hk, hkm, he, hSU⟩ | ⟨-, ⟨eL⟩⟩⟩ := h
  · have hF := sigF4_of_reeF4 hm ⟨k, hk, hkm, he⟩
    have hU := unitarySig_of_isoSUThree (by omega) hSU
    have := two_eq (profile_of_eq hU.profile hcard.symm) hF.profile
    omega
  · obtain ⟨r, hr, hcL⟩ := card_projSL_two_eq (g := 3 * m) (by omega)
    have h2 : Nat.card (X ⧸ aschbacherSolvableCore 3 X) = 2 ^ (3 * m) * r := by
      rw [← hcard, Nat.card_congr eL.toEquiv, hcL]
    rcases sig_of_isGammaType hm htype with hS | hS | hS | hS | hS
    all_goals
      obtain ⟨r', hr', h'⟩ := hS.profile.two
      have := eq_of_two_pow_mul_odd hr' hr (h'.symm.trans h2)
      omega

end Trivial

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
