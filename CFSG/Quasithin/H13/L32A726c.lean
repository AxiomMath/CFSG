module

public import CFSG.Quasithin.H13.L32A726b
public import CFSG.Quasithin.H13.L32A715a
public import CFSG.Quasithin.H13.L32A714a
public import CFSG.Quasithin.H13.NQCoreP134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_or_eq_of_index_two_726 {S M T : Subgroup G} (hSM : S ≤ M) (hMT : M ≤ T)
    (h2 : (S.subgroupOf T).index = 2) : M = S ∨ M = T := by
  have hmul := Subgroup.relIndex_mul_relIndex S M T hSM hMT
  rw [show S.relIndex T = 2 from h2] at hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hmul) with h | h
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hSM
  · right
    rw [h] at hmul
    have h1 : M.relIndex T = 1 := by omega
    exact le_antisymm hMT (Subgroup.relIndex_eq_one.mp h1)

omit [Finite G] in
theorem isSylowTwoOf_of_le_726 {S X Y : Subgroup G} (hS : IsSylowTwoOf S X) (hSY : S ≤ Y)
    (hYX : Y ≤ X) : IsSylowTwoOf S Y := by
  refine ⟨hSY, hS.2.1, fun h2 => hS.2.2 ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex S Y X hSY hYX
  exact h2.trans (Dvd.intro _ hmul)

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers_726 (d : G) :
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hc : Commute g d := hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk, (hc.zpow_right k).eq, mul_inv_cancel_right]
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hc' : Commute g (d ^ k) := hc.zpow_right k
    calc d ^ k = g⁻¹ * (d ^ k) * g := by
          rw [mul_assoc, ← hc'.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hk]
      _ = x := by group

omit [Finite G] in
theorem pCoreOf_ne_bot_of_le_centralizer_726 {d : G} (hd1 : d ≠ 1) (hd2 : d * d = 1)
    {G0 : Subgroup G} (hdG0 : d ∈ G0) (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) :
    pCoreOf 2 G0 ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers d) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1
  have hle : Subgroup.zpowers d ≤ pCoreOf 2 G0 :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hdG0)
      (hG0.trans (centralizer_le_normalizer_zpowers_726 d)) hp
  intro h
  rw [h] at hle
  exact hd1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers d)))

omit [Finite G] in
theorem normalizer_le_normalizer_char_726 {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at h

omit [Finite G] in
theorem conjClosure_eq_of_le_normalizer_726 {Z M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (Z : Set G)) : conjClosure Z M = Z := by
  apply le_antisymm
  · rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hM hh) z).mp hz
  · intro z hz
    exact Subgroup.subset_closure ⟨1, M.one_mem, z, hz, by group⟩

omit [Finite G] in
theorem commutator_sup_pCoreOf_eq_o2z_726 {K : Subgroup G}
    (hP : IsPOnePlusTwo 3 (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) :
    ⁅K, K⁆ ⊔ pCoreOf 2 K = o2z K := by
  have hQK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hQZ : pCoreOf 2 K ≤ o2z K := fun q hq => mem_o2z_iff.mpr ⟨hQK hq, fun y hy => by
    have h1 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hy) _).mp (inv_mem hq)
    rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
    exact mul_mem hq h1⟩
  apply le_antisymm
  · refine sup_le ?_ hQZ
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact comm_mem_o2z hP x hx y hy
  · refine o2z_le_of_comm_mem hP le_sup_right fun x hx y hy => ?_
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy)

section Ctx

variable {T L V H D : Subgroup G}

theorem pCoreOf_k_ne_bot_726 (hc : Ctx726 G T L V H D) : pCoreOf 2 (oTwoUpper H) ≠ ⊥ := by
  intro h
  have hK : CharTwo (oTwoUpper H) :=
    CT.CharTwo.of_normal (charTwo_h_726 hc) (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H))
  have hle : oTwoUpper H ≤ pCoreOf 2 (oTwoUpper H) := fun k hk => hK ⟨hk, by
    rw [h]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Subgroup.mem_bot.mp hx, one_mul, mul_one]⟩
  rw [h] at hle
  have hK1 : oTwoUpper H = ⊥ := le_bot_iff.mp hle
  have h1 : ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).index ∣ 1 := by
    have := Subgroup.index_dvd_card ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H))
    rwa [Subgroup.card_eq_one.mpr hK1] at this
  rw [Subgroup.index_eq_card, (isPOnePlusTwo_K hc.three).2.1] at h1
  norm_num at h1

theorem pCoreOf_h_ne_bot_726 (hc : Ctx726 G T L V H D) : pCoreOf 2 H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  apply pCoreOf_k_ne_bot_726 hc
  have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (oTwoUpper_le H))
      ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  rw [h] at hle
  exact le_bot_iff.mp hle

theorem normalizer_le_of_le_normalizer_726 (hc : Ctx726 G T L V H D) {C : Subgroup G}
    (hC : C ≠ ⊥) (hCp : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ H :=
  (hc.max_two_local.2 _ ⟨C, hC, hCp, rfl⟩ hHC).le

theorem normalizer_l1_le_726 (hc : Ctx726 G T L V H D) :
    Subgroup.normalizer (L32A.l1 T L V : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  calc Subgroup.normalizer (L32A.l1 T L V : Set G)
      ≤ Subgroup.normalizer (pCoreOf 2 (L32A.l1 T L V) : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 _
    _ ≤ H := normalizer_le_of_le_normalizer_726 hc hc.o2_l1_ne (pCoreOf_isPGroup 2 _)
          (hc.l1_normal.trans (normalizer_le_normalizer_pCoreOf 2 _))

theorem not_le_normalizer_l1_726 (hc : Ctx726 G T L V H D) {G0 : Subgroup G}
    (hG0H : ¬ G0 ≤ H) : ¬ G0 ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) :=
  fun h => hG0H (h.trans (normalizer_l1_le_726 hc))

theorem l1_le_k_726 (hc : Ctx726 G T L V H D) : L32A.l1 T L V ≤ oTwoUpper H := by
  rw [hc.l1_eq]
  exact (oTwoUpper_le _).trans (o2z_le _)

theorem isSQTKCat_of_pCoreOf_ne_bot_726 (hc : Ctx726 G T L V H D) {X : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) : CFSG.SectionRank.IsSQTKCat ↥X := by
  have := hc.setting.hyp.fsu.simple
  exact (QuasithinUnique.qtkeCore_of_cat hc.setting.hyp.fsu.nonabelian
    hc.setting.hyp.fsu.qtke).1 _ hX

theorem isSQTKIn_of_pCoreOf_ne_bot_726 (hc : Ctx726 G T L V H D) {X : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) : IsSQTKIn X := by
  have := hc.setting.hyp.fsu.simple
  exact InternalSec.sqtkGroup_of_localSQTK (QuasithinUnique.qtkeCore_of_cat
    hc.setting.hyp.fsu.nonabelian hc.setting.hyp.fsu.qtke).1 hX

theorem exists_card_k_726 (hc : Ctx726 G T L V H D) :
    ∃ a : ℕ, Nat.card (oTwoUpper H) = 2 ^ a * 27 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 27 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, (isPOnePlusTwo_K hc.three).2.1]
    norm_num
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (oTwoUpper H)).exists_card_eq
  refine ⟨a, ?_⟩
  have h1 := Subgroup.card_mul_index ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 (oTwoUpper H))).toEquiv, ha,
    ← Subgroup.relIndex, hidx] at h1
  exact h1.symm

theorem card_sylow_three_k_726 (hc : Ctx726 G T L V H D) (S : Sylow 3 ↥(oTwoUpper H)) :
    Nat.card S = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, hcardK⟩ := exists_card_k_726 hc
  rw [Sylow.card_eq_multiplicity, hcardK]
  have h1 : (2 ^ a * 27).factorization 3 = 3 := by
    rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num),
      show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]
  rw [h1]
  norm_num

theorem exists_sylow_three_k_726 (hc : Ctx726 G T L V H D) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsPGroup 3 ↥P ∧ Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥(oTwoUpper H)))
  refine ⟨(S : Subgroup ↥(oTwoUpper H)).map (oTwoUpper H).subtype, Subgroup.map_subtype_le _,
    (S.isPGroup').map _, ?_⟩
  rw [Subgroup.card_map_of_injective (oTwoUpper H).subtype_injective]
  exact card_sylow_three_k_726 hc S

theorem commutator_sup_eq_l1_sup_726 (hc : Ctx726 G T L V H D) :
    ⁅oTwoUpper H, oTwoUpper H⁆ ⊔ pCoreOf 2 (oTwoUpper H) =
      L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) := by
  have hP := isPOnePlusTwo_K hc.three
  have hQZ : pCoreOf 2 (oTwoUpper H) ≤ o2z (oTwoUpper H) := by
    rw [← commutator_sup_pCoreOf_eq_o2z_726 hP]
    exact le_sup_right
  have hZ3 : ∀ z ∈ o2z (oTwoUpper H), z ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := fun z hz =>
    pow_three_mem_K hc.three z (o2z_le _ hz)
  rw [commutator_sup_pCoreOf_eq_o2z_726 hP, hc.l1_eq]
  exact (oTwoUpper_sup_pCoreOf_eq hQZ hZ3).symm

theorem isXi_td_726 (hc : Ctx726 G T L V H D) {Td : Subgroup G} (hTd : Td ≤ T)
    (hirr : ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
      W ≤ oTwoUpper H → Td ≤ Subgroup.normalizer (W : Set G) →
      W = L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H) :
    IsXi Td (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := isPOnePlusTwo_K hc.three
  have hTK : Td ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTd.trans (t_le_normalizer_k_726 hc)
  have hfrat := commutator_sup_eq_l1_sup_726 hc
  refine ⟨(A4.oTwoUpper_oTwoUpper H).symm, hTK, ?_, 3, Nat.prime_three, by norm_num,
    pow_three_mem_K hc.three, Or.inr ⟨?_, ?_⟩, ?_⟩
  ·
    have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (oTwoUpper H ⊔ Td) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 _) (hTK.trans (normalizer_le_normalizer_pCoreOf 2 _)))
        (pCoreOf_isPGroup 2 _)
    intro hb
    rw [hb] at hle
    exact pCoreOf_k_ne_bot_726 hc (le_bot_iff.mp hle)
  · rw [Subgroup.relIndex, Subgroup.index_eq_card, hP.2.1]
  · intro hle
    obtain ⟨a, b, hab⟩ := Heis.exists_comm_ne_one hP
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_subgroupOf.mpr (hle ?_)
    exact Subgroup.commutator_mem_commutator a'.2 b'.2
  · intro W hW hWK hTW
    rw [hfrat] at hW ⊢
    exact hirr W hW hWK hTW

theorem le_normalizer_k_of_irreducible_726 (h3x : NQCore.Prop134ThreeExtraspecial)
    (hc : Ctx726 G T L V H D) {Td G0 : Subgroup G} (hTd : Td ≤ T) (hsyl : IsSylowTwoOf Td G0)
    (hKG0 : oTwoUpper H ≤ G0) (hG0 : pCoreOf 2 G0 ≠ ⊥)
    (hirr : ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
      W ≤ oTwoUpper H → Td ≤ Subgroup.normalizer (W : Set G) →
      W = L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H) :
    G0 ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  obtain ⟨P, hPK, hP3, hP27⟩ := exists_sylow_three_k_726 hc
  have hidx : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 27 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, (isPOnePlusTwo_K hc.three).2.1]
    norm_num
  exact h3x G G0 Td (oTwoUpper H) P (isSQTKCat_of_pCoreOf_ne_bot_726 hc hG0) hG0 hsyl hKG0
    (isXi_td_726 hc hTd hirr) hidx hPK hP3 hP27

theorem false_of_irreducible_726 (h3x : NQCore.Prop134ThreeExtraspecial)
    (hc : Ctx726 G T L V H D) {Td G0 : Subgroup G} (hTd : Td ≤ T) (hsyl : IsSylowTwoOf Td G0)
    (hKG0 : oTwoUpper H ≤ G0) (hG0 : pCoreOf 2 G0 ≠ ⊥) (hG0H : ¬ G0 ≤ H)
    (hirr : ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
      W ≤ oTwoUpper H → Td ≤ Subgroup.normalizer (W : Set G) →
      W = L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H) : False := by
  have hN := le_normalizer_k_of_irreducible_726 h3x hc hTd hsyl hKG0 hG0 hirr
  apply not_le_normalizer_l1_726 hc hG0H
  rw [hc.l1_eq]
  exact (hN.trans (normalizer_le_normalizer_o2z _)).trans (normalizer_le_normalizer_oTwoUpper _)

theorem pCoreOf_h_le_td_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {W : Subgroup G}
    (hW1 : L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W) (hW2 : W ≤ oTwoUpper H)
    (hTdW : T ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hne1 : W ≠ L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H)) (hne2 : W ≠ oTwoUpper H) :
    pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := t_le_h_726 hc
  have hQT : pCoreOf 2 H ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_h_726 hc)
  have hQK : pCoreOf 2 H ⊓ oTwoUpper H ≤ pCoreOf 2 (oTwoUpper H) := by
    rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le H) (le_normalizer_oTwoUpper H)]
    exact fun x hx => ⟨hx.2, hx.1⟩
  have key : ∀ q ∈ pCoreOf 2 H, ∀ w ∈ W, q * w * q⁻¹ ∈ W := by
    intro q hq w hw
    have hwK : w ∈ oTwoUpper H := hW2 hw
    have h1 : q * w * q⁻¹ * w⁻¹ ∈ pCoreOf 2 H := by
      have : w * q⁻¹ * w⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (oTwoUpper_le H hwK)) _).mp (inv_mem hq)
      rw [show q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) by group]
      exact mul_mem hq this
    have h2 : q * w * q⁻¹ * w⁻¹ ∈ oTwoUpper H := by
      have : q * w * q⁻¹ ∈ oTwoUpper H := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_oTwoUpper H (pCoreOf_le 2 H hq)) w).mp hwK
      exact mul_mem this (inv_mem hwK)
    have h3 : q * w * q⁻¹ * w⁻¹ ∈ W := hW1 (Subgroup.mem_sup_right (hQK ⟨h1, h2⟩))
    have h4 := mul_mem h3 hw
    rwa [show q * w * q⁻¹ * w⁻¹ * w = q * w * q⁻¹ by group] at h4
  have hQW : pCoreOf 2 H ≤ Subgroup.normalizer (W : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key q hq w hw, fun hw => ?_⟩
    have h := key q⁻¹ (inv_mem hq) _ hw
    rwa [show q⁻¹ * (q * w * q⁻¹) * q⁻¹⁻¹ = w by group] at h
  have hR1T : pCoreOf 2 (L32A.l1 T L V ⊔ T) ≤ T := by
    have hL1H : L32A.l1 T L V ≤ H := (l1_le_k_726 hc).trans (oTwoUpper_le H)
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_le_726 (isSylowTwoOf_h_726 hc) le_sup_right (sup_le hL1H hTH))
  have hsup : T ⊓ Subgroup.centralizer ({d} : Set G) ⊔ pCoreOf 2 H ≤ T :=
    sup_le inf_le_left hQT
  rcases eq_or_eq_of_index_two_726 le_sup_left hsup (relIndex_td_726 hc hdD hdV htT htd) with
    h | h
  · rw [← h]
    exact le_sup_right
  · exfalso
    have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
      rw [← h]
      exact sup_le hTdW hQW
    rcases hc.r1_irred W hW1 hW2 (hR1T.trans hTW) with h' | h'
    · exact hne1 h'
    · exact hne2 h'

theorem td_le_hd_726 (hc : Ctx726 G T L V H D) (d : G) :
    T ⊓ Subgroup.centralizer ({d} : Set G) ≤ H ⊓ Subgroup.centralizer ({d} : Set G) :=
  inf_le_inf_right _ (t_le_h_726 hc)

theorem k_le_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    oTwoUpper H ≤ H ⊓ Subgroup.centralizer ({d} : Set G) :=
  le_inf (oTwoUpper_le H) (k_le_centralizer_726 hc hdD)

theorem d_mem_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    d ∈ H ⊓ Subgroup.centralizer ({d} : Set G) :=
  ⟨d_le_h_726 hc hdD, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem ne_one_of_not_mem_v1_726 {T V : Subgroup G} {d : G} (hdV : d ∉ fsuV1 T V) : d ≠ 1 :=
  fun h => hdV (h ▸ Subgroup.one_mem _)

theorem pCoreOf_g0_ne_bot_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) : pCoreOf 2 G0 ≠ ⊥ :=
  pCoreOf_ne_bot_of_le_centralizer_726 (ne_one_of_not_mem_v1_726 hdV) hd2
    (hHdG0 (d_mem_hd_726 hc hdD)) hG0

theorem isSylowTwoOf_td_g0_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({d} : Set G)) G0 :=
  isSylowTwoOf_of_le_726 (isSylowTwoOf_td_726 hc hdD hdV htT htd)
    ((td_le_hd_726 hc d).trans hHdG0) hG0

theorem pCoreOf_h_le_td_of_g0_726 (h3x : NQCore.Prop134ThreeExtraspecial)
    (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1)
    {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) (hG0H : ¬ G0 ≤ H) :
    pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G) := by
  by_cases hirr : ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
      W ≤ oTwoUpper H → T ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (W : Set G) →
      W = L32A.l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H
  · exact (false_of_irreducible_726 h3x hc inf_le_left
      (isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0) ((k_le_hd_726 hc hdD).trans hHdG0)
      (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0) hG0H hirr).elim
  · push Not at hirr
    obtain ⟨W, hW1, hW2, hW3, hne1, hne2⟩ := hirr
    exact pCoreOf_h_le_td_726 hc hdD hdV htT htd hW1 hW2 hW3 hne1 hne2

theorem pCoreOf_hd_eq_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set G)) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      ((hd_normal_726 hc hdD hdV).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 (hQ.trans (td_le_hd_726 hc d))
      (inf_le_left.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem normalizer_char_le_726 (hc : Ctx726 G T L V H D) {C : Subgroup G}
    (hCQ : C ≤ pCoreOf 2 H) (hC : C ≠ ⊥) (hchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact normalizer_le_of_le_normalizer_726 hc hC ((pCoreOf_isPGroup 2 H).to_le hCQ)
    ((le_normalizer_pCoreOf 2 H).trans (normalizer_le_normalizer_char_726 hCQ hchar))

theorem cgsIn_le_726 (hc : Ctx726 G T L V H D) {d : G} {G0 : Subgroup G}
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) :
    cgsIn G0 (pCoreOf 2 H) ≤ H ⊓ Subgroup.centralizer ({d} : Set G) :=
  iSup_le fun _ => iSup_le fun hCQ => iSup_le fun hC => iSup_le fun hchar =>
    fun _ hx => ⟨normalizer_char_le_726 hc hCQ hC hchar hx.2, hG0 hx.1⟩

theorem isTwoRadicalIn_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G))
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) :
    IsTwoRadicalIn G0 (pCoreOf 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
    le_antisymm (normalizer_le_of_le_normalizer_726 hc (pCoreOf_h_ne_bot_726 hc)
      (pCoreOf_isPGroup 2 H) (le_normalizer_pCoreOf 2 H)) (le_normalizer_pCoreOf 2 H)
  refine ⟨(hQ.trans (td_le_hd_726 hc d)).trans hHdG0, pCoreOf_h_ne_bot_726 hc, ?_⟩
  have heq : G0 ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) =
      H ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hNQ]
    apply le_antisymm
    · exact fun x hx => ⟨hx.2, hG0 hx.1⟩
    · exact fun x hx => ⟨hHdG0 hx, hx.1⟩
  rw [heq, pCoreOf_hd_eq_726 hc hdD hdV hQ]

theorem hypC23_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V)
    (hd2 : d * d = 1) {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G))
    (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) :
    HypC23 G0 (pCoreOf 2 H) (H ⊓ Subgroup.centralizer ({d} : Set G)) where
  sqtk := isSQTKIn_of_pCoreOf_ne_bot_726 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0)
  radical := isTwoRadicalIn_726 hc hdD hdV hHdG0 hG0 hQ
  le := hHdG0
  cgs := cgsIn_le_726 hc hG0
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [conjClosure_eq_of_le_normalizer_726 (inf_le_left.trans (le_normalizer_pCoreOf 2 H))]
    refine ⟨le_rfl, pCoreOf_isPGroup 2 H, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num

end Ctx

end CFSG.Quasithin.H13.L32A
