module

public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.H13.L32AC47f
public import CFSG.Quasithin.Background.F918Fine4Hat6
public import CFSG.Quasithin.EmptyFaithful.S14610Hat6

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (A6 D0 N1 N2 parab conjK mem_parab)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_inf_le_of_le {H K : Subgroup G} (hKH : K ≤ H) :
    pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_inf_left
  have hkP : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (Subgroup.le_normalizer (hKH hk))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp hkP x)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, K.mul_mem (K.mul_mem hk h2) (K.inv_mem hk)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) h2) hk
    simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_pi_of_hat {K : Subgroup G} (hhat : IsHat (cStar K) A6) :
    ∃ π : ↥K →* A6, Function.Surjective π ∧ ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ oTwoZIn K := by
  obtain ⟨-, -, ⟨φ⟩⟩ := IsHat.of_mulEquiv (cStarEquiv K) hhat
  set Kq := ↥K ⧸ CFSG.pCore 2 ↥K
  refine ⟨φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Kq)).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K))), φ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)), fun k => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨k, h, rfl⟩
  · rintro ⟨k', hk', hkk⟩
    rwa [← Subtype.ext hkk]

theorem isSolvable_parab_sup {K T : Subgroup G} {π : ↥K →* A6} (hπ : Function.Surjective π)
    {N : Subgroup A6} (hN : Nat.card N = 24) (hT2 : IsPGroup 2 T)
    (hTB : T ≤ Subgroup.normalizer (parab π N : Set G)) {c : ℕ} (hK : Nat.card K = 1080 * 2 ^ c) :
    Group.IsSolvable ↥(parab π N ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := parab π N with hB
  have hidx : N.index = 15 := by
    have := N.card_mul_index
    rw [hN, Alt6.card_A6] at this
    omega
  have hBc : Nat.card B = 72 * 2 ^ c := by
    have h1 : Nat.card B = Nat.card (N.comap π) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have h2 := (N.comap π).card_mul_index
    rw [Subgroup.index_comap_of_surjective N hπ, hidx, hK] at h2
    rw [h1]
    omega
  set P := B ⊔ T with hP
  have hBP : B ≤ P := le_sup_left
  have hPn : P ≤ Subgroup.normalizer (B : Set G) := sup_le (Subgroup.le_normalizer) hTB
  have hBn : (B.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPn
  have hQ : IsPGroup 2 (↥P ⧸ B.subgroupOf P) := by
    intro q
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hp' : p ∈ (↑(B ⊔ T) : Set G) := hp
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B T hTB] at hp'
    obtain ⟨b, hb, t, ht, rfl⟩ := hp'
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have hbt : (QuotientGroup.mk (⟨b * t, hp⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) =
        QuotientGroup.mk (⟨t, Subgroup.mem_sup_right ht⟩ : ↥P) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      have e : t⁻¹ * b⁻¹ * t = t⁻¹ * b⁻¹ * t⁻¹⁻¹ := by rw [inv_inv]
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hTB (T.inv_mem ht)) _).mp (B.inv_mem hb)
    rw [hbt, ← QuotientGroup.mk_pow]
    have : (⟨t, Subgroup.mem_sup_right ht⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hPc : Nat.card P = 2 ^ (m + 3 + c) * 3 ^ 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf P), hm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hBc, pow_add, pow_add]
    ring
  have := Fintype.ofFinite ↥P
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hPc])

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem l1_le_oTwoZIn (h28 : Lemma14_7_28) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (h3 : Nat.card (Subgroup.center (cStar K)) = 3) :
    l1 T L V ≤ oTwoZIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set N := CFSG.pCore 2 ↥H with hN
  set Kb := modO2Image H K with hKb
  set Z := (Subgroup.center ↥Kb).map Kb.subtype with hZ
  have hZc : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective Kb.subtype_injective, ← h3]
    exact (card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)).symm
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : (Z.subgroupOf Kb).Normal := by
    rw [hZ, map_subtype_subgroupOf']
    infer_instance
  have hZs : Z.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le _) hKbs hZn
  have hle := le_oddCore_of_isSubnormal hZs (by rw [hZc]; decide)
  have hZL : Z = modO2Image H (l1 T L V) := by
    rcases h28 G T L V H S with h0 | h1
    · rw [h0, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hZc
      omega
    · rw [h1] at hle
      have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := h1 ▸ odd_card_oddCore
      have hd := card_modO2Image_dvd_three hL1H hL3 hoddL
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hZc]
      exact Nat.le_of_dvd (by norm_num) hd
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxL1 : x ∈ l1 T L V := Subgroup.subset_closure hx
  have hxH : x ∈ H := hL1H hxL1
  have hxZ : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) ∈ Z := by
    rw [hZL]
    exact ⟨⟨x, hxH⟩, hxL1, rfl⟩
  obtain ⟨⟨y, hyKb⟩, hyc, hyx⟩ := hxZ
  obtain ⟨k, hkK, hky⟩ := hyKb
  have hyx' : y = (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) := hyx
  have hxk : (⟨x, hxH⟩ : ↥H)⁻¹ * k ∈ N := by
    have h1 : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) = QuotientGroup.mk k := by
      rw [← hyx']
      exact hky.symm
    exact QuotientGroup.eq.mp h1
  have hK'n : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hxK : x ∈ K := by
    set o : ↥H := (⟨x, hxH⟩ : ↥H)⁻¹ * k with ho
    have hxo : (⟨x, hxH⟩ : ↥H) = k * o⁻¹ := by rw [ho]; group
    have hkk : (QuotientGroup.mk k : ↥H ⧸ K.subgroupOf H) = 1 :=
      (QuotientGroup.eq_one_iff k).mpr hkK
    have hmx : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) =
        QuotientGroup.mk o⁻¹ := by
      rw [hxo, QuotientGroup.mk_mul, hkk, one_mul]
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥H) ⟨o⁻¹, N.inv_mem hxk⟩
    have hon : o⁻¹ ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hd1 : orderOf (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hmx, ← QuotientGroup.mk_pow, hon, QuotientGroup.mk_one]
    have hd2 : orderOf (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ∣
        orderOf x := by
      rw [← Subgroup.orderOf_mk x hxH]
      exact orderOf_map_dvd (QuotientGroup.mk' (K.subgroupOf H)) _
    have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hx.2)
    have hmk := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
    exact hmk
  refine mem_oTwoZIn_iff_commutator.mpr ⟨hxK, fun w hw => ?_⟩
  have hwH : w ∈ H := hKH hw
  have hcomm : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) *
      QuotientGroup.mk (⟨w, hwH⟩ : ↥H) = QuotientGroup.mk (⟨w, hwH⟩ : ↥H) *
      QuotientGroup.mk (⟨x, hxH⟩ : ↥H) := by
    have hwKb : (QuotientGroup.mk (⟨w, hwH⟩ : ↥H) : ↥H ⧸ N) ∈ Kb := ⟨⟨w, hwH⟩, hw, rfl⟩
    have := Subgroup.mem_center_iff.mp hyc ⟨_, hwKb⟩
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h'
    rw [hyx'] at h'
    exact h'.symm
  have hN' : (⟨x, hxH⟩ : ↥H) * ⟨w, hwH⟩ * (⟨x, hxH⟩ : ↥H)⁻¹ * (⟨w, hwH⟩ : ↥H)⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, hcomm, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    group
  refine pCoreOf_inf_le_of_le hKH ⟨?_, ?_⟩
  · rw [hN] at hN'
    exact ⟨_, hN', rfl⟩
  · exact K.mul_mem (K.mul_mem (K.mul_mem hxK hw) (K.inv_mem hxK)) (K.inv_mem hw)

theorem lemma14_7_47_hat6_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h28 : Lemma14_7_28) (h29 : Thm14_7_29)
    (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (hHat : F918Fine4Hat6) : Lemma14_7_47_Hat6 := by
  intro G _ _ T L V H S K hK hH hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  obtain ⟨-, -, -, hF⟩ := h30 G T L V H S K hK
  rw [conjClosure_T_eq_self hTK, ← hH] at hF
  have hSQ := sqtkGroup_of_setting S
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have hnf := hHat G T V L (fsuV1 T V) V H K hF hSQ (conjClosure_T_eq_self hTK)
    (IsHat.of_mulEquiv ((cStarEquiv K).trans eA) hhat)
  have hL1Z := l1_le_oTwoZIn h28 S (relIndex_l1 h1222 h1332 h1334 S.hyp) hK hKn hhat.2.1
  obtain ⟨π₀, hπ₀, hker₀⟩ := exists_pi_of_hat hhat
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hTK' : (T ⊓ K).subgroupOf K = T.subgroupOf K := Subgroup.inf_subgroupOf_right T K
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := hTK' ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := Alt6.exists_conj_map_eq_D0 π₀ hπ₀ hS2 hSi
  set π : ↥K →* A6 := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ oTwoZIn K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = D0 := by
    rw [← hhD, Subgroup.map_map]
  have hfus : ∀ t (ht : t ∈ T) (x : ↥K), orderOf (π x) = 3 →
      ∃ k : ↥K, π (conjK (hTK ht) x) = π (k * x * k⁻¹) := by
    intro t ht x hx
    by_contra hne
    push Not at hne
    apply hnf t ht
    refine ⟨x, x.2, ?_, ?_, fun k hk hZ => ?_⟩
    · have := (hker (x ^ 3)).mp (by rw [map_pow, ← hx, pow_orderOf_eq_one])
      simpa using this
    · intro hxZ
      rw [(hker x).mpr hxZ, orderOf_one] at hx
      omega
    · apply hne ⟨k, hk⟩
      have h1 := (hker ((⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ * conjK (hTK ht) x)).mpr hZ
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.mp h1).symm
  obtain ⟨hT1, hT2, hZ1, hZ2, hKB⟩ := Alt6.exists_parabolics π hπ (oTwoZIn_le_self K) hker hTK
    (hTK.trans (normalizer_le_normalizer_oTwoZIn K)) hD hfus
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hcK : Nat.card K = 1080 * 2 ^ c := by
    obtain ⟨-, h3, ⟨φ⟩⟩ := hhat
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hc,
      ← Nat.card_congr (cStarEquiv K).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (cStar K)), h3,
      Nat.card_congr φ.toEquiv, Alt6.card_A6]
  have hT2' : IsPGroup 2 T := hTsylH.2.1
  have hsolv1 := isSolvable_parab_sup hπ Alt6.card_N1 hT2' hT1 hcK
  have hsolv2 := isSolvable_parab_sup hπ Alt6.card_N2 hT2' hT2 hcK
  have hHg : H ≤ A6.g1 T V := S.hz.2.1
  have hBK : ∀ N : Subgroup A6, parab π N ≤ K := fun N => Subgroup.map_subtype_le _
  have hM1 := h29 G T L V S.hyp (parab π N1 ⊔ T)
    (sup_le (hL1Z.trans (hZ1.trans le_sup_left)) le_sup_right)
    ((sup_le ((hBK N1).trans hKH) hTH).trans hHg) hsolv1
  have hM2 := h29 G T L V S.hyp (parab π N2 ⊔ T)
    (sup_le (hL1Z.trans (hZ2.trans le_sup_left)) le_sup_right)
    ((sup_le ((hBK N2).trans hKH) hTH).trans hHg) hsolv2
  apply S.hz.2.2
  rw [hH]
  refine sup_le (hKB.trans (sup_le_sup le_sup_left le_sup_left |>.trans (sup_le hM1 hM2)))
    (sup_le (hL1Z.trans (hZ1.trans (le_sup_left.trans hM1))) (le_sup_right.trans hM1))

end Setting

end CFSG.Quasithin.H13.L32A.C
