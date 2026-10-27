module

public import CFSG.Quasithin.H13.L32A715a
public import CFSG.Quasithin.H13.L32A714a
public import CFSG.Quasithin.H13.L32ASk4

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Faithful

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_one_of_centralizes_two {X : Subgroup Γ} [hXn : X.Normal]
    (hO2 : CFSG.pCore 2 Γ = ⊥) (hq : ∀ g : Γ, ∃ k : ℕ, g ^ 2 ^ k ∈ X)
    {g : Γ} {m : ℕ} (hg : g ^ 2 ^ m = 1) (hgc : g ∈ Subgroup.centralizer (X : Set Γ)) :
    g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.centralizer (X : Set Γ) with hN
  set Q : Subgroup ↥N := X.subgroupOf N with hQ
  have hQc : Q ≤ Subgroup.center ↥N := by
    intro x hx
    refine Subgroup.mem_center_iff.mpr fun n => Subtype.ext ?_
    have hxX : (x : Γ) ∈ X := Subgroup.mem_subgroupOf.mp hx
    exact (Subgroup.mem_centralizer_iff.mp n.2 _ hxX).symm
  have hQn : Q.Normal := Subgroup.normal_subgroupOf
  have hp2 : IsPGroup 2 (↥N ⧸ Q) := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective Q y
    obtain ⟨k, hk⟩ := hq (n : Γ)
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  have hnilQ : Group.IsNilpotent (↥N ⧸ Q) := hp2.isNilpotent
  have hnil : Group.IsNilpotent ↥N :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Q)
      (by rw [QuotientGroup.ker_mk']; exact hQc)
  have hg1 : (⟨g, hgc⟩ : ↥N) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hg)
  have hg2 : IsPGroup 2 ↥(Subgroup.zpowers (⟨g, hgc⟩ : ↥N)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨m, Subtype.ext ?_⟩
    change ((⟨g, hgc⟩ : ↥N) ^ n) ^ 2 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg1, one_zpow]
  obtain ⟨P, hP⟩ := hg2.exists_le_sylow
  have hNn : N.Normal := inferInstance
  have hle := Sylow.map_le_pCore hNn hnil 2 P
  rw [hO2] at hle
  have hgP : g ∈ (P : Subgroup ↥N).map N.subtype :=
    ⟨⟨g, hgc⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  exact Subgroup.mem_bot.mp (hle hgP)

theorem center_eq_of_normal_card_three {X N : Subgroup Γ} (hX : IsPOnePlusTwo 3 ↥X)
    (hNX : N ≤ X) (hNn : N.Normal) (hN3 : Nat.card N = 3) :
    (Subgroup.center ↥X).map X.subtype = N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' := N.subgroupOf X with hN'
  have hN'n : N'.Normal := Subgroup.Normal.subgroupOf hNn X
  have hcardN' : Nat.card N' = 3 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact hN3
  have hXp : IsPGroup 3 ↥X := IsPGroup.of_card (n := 3) (by rw [hX.2.1])
  have hnil : Group.IsNilpotent ↥X := hXp.isNilpotent
  have hne : N' ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardN'
    norm_num at hcardN'
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hle : N' ⊓ Subgroup.center ↥X = N' := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    have hdvd : Nat.card ↥(N' ⊓ Subgroup.center ↥X) ∣ 3 :=
      hcardN' ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hinf
    · rw [h3, hcardN']
  have hNZ : N' ≤ Subgroup.center ↥X := hle ▸ inf_le_right
  have hNZ' : N' = Subgroup.center ↥X :=
    Subgroup.eq_of_le_of_card_ge hNZ (by
      rw [hcardN']
      exact (Heis.card_center hX).le)
  rw [← hNZ', hN', Subgroup.map_subgroupOf_eq_of_le hNX]

end Faithful

section Star

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_modO2Image_iff {H A : Subgroup G} {x : ↥H ⧸ CFSG.pCore 2 ↥H} :
    x ∈ modO2Image H A ↔ ∃ a : ↥H, (a : G) ∈ A ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = x := by
  rw [modO2Image, Subgroup.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, Subgroup.mem_subgroupOf.mp ha, h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, Subgroup.mem_subgroupOf.mpr ha, h⟩⟩

omit [Finite G] in
theorem modO2Image_mono {H A B : Subgroup G} (h : A ≤ B) : modO2Image H A ≤ modO2Image H B :=
  Subgroup.map_mono fun x hx => (h hx : (x : G) ∈ B)

omit [Finite G] in
theorem modO2Image_sup_of_le_pCoreOf {H A Q : Subgroup G} (hAH : A ≤ H)
    (hQH : Q ≤ pCoreOf 2 H) : modO2Image H (A ⊔ Q) = modO2Image H A := by
  have hQ : modO2Image H Q = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := mem_modO2Image_iff.mp hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨b, hb, hba⟩ := hQH ha
    have : b = a := Subtype.ext hba
    rw [← this]
    exact hb
  rw [modO2Image, Subgroup.subgroupOf_sup hAH (hQH.trans (pCoreOf_le 2 H)), Subgroup.map_sup]
  change modO2Image H A ⊔ modO2Image H Q = modO2Image H A
  rw [hQ, sup_bot_eq]

omit [Finite G] in
theorem irr_star {H K A T : Subgroup G} (hKH : K ≤ H) (hAK : A ≤ K) (hTH : T ≤ H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hirr : ∀ W : Subgroup G, A ≤ W → W ≤ K → T ≤ Subgroup.normalizer (W : Set G) →
      W = A ∨ W = K)
    (W' : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) (hAW : modO2Image H A ≤ W')
    (hWK : W' ≤ modO2Image H K)
    (hTW : modO2Image H T ≤ Subgroup.normalizer (W' : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    W' = modO2Image H A ∨ W' = modO2Image H K := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set W := (W'.comap (toStar H K hKH)).map K.subtype with hW
  have hmemW : ∀ g : G, g ∈ W ↔ ∃ hg : g ∈ K, π ⟨g, hKH hg⟩ ∈ W' := by
    intro g
    rw [hW, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hAW' : A ≤ W := fun a ha =>
    (hmemW a).mpr ⟨hAK ha, hAW (mem_modO2Image_iff.mpr ⟨⟨a, hKH (hAK ha)⟩, ha, rfl⟩)⟩
  have hWK' : W ≤ K := fun g hg => ((hmemW g).mp hg).1
  have hconj : ∀ t ∈ T, ∀ g ∈ W, t * g * t⁻¹ ∈ W := by
    intro t ht g hg
    obtain ⟨hgK, hgW⟩ := (hmemW g).mp hg
    have htg : t * g * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ht) g).mp hgK
    refine (hmemW _).mpr ⟨htg, ?_⟩
    have ht' : π ⟨t, hTH ht⟩ ∈ modO2Image H T := mem_modO2Image_iff.mpr ⟨⟨t, hTH ht⟩, ht, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTW ht') _).mp hgW
    have e : (⟨t * g * t⁻¹, hKH htg⟩ : ↥H) = ⟨t, hTH ht⟩ * ⟨g, hKH hgK⟩ * ⟨t, hTH ht⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact h1
  have hTW' : T ≤ Subgroup.normalizer (W : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hconj t ht g
    · intro h
      have := hconj t⁻¹ (T.inv_mem ht) _ h
      simpa [mul_assoc] using this
  rcases hirr W hAW' hWK' hTW' with he | he
  · left
    refine le_antisymm (fun x hx => ?_) hAW
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image_iff.mp (hWK hx)
    have hkW : (k : G) ∈ W := (hmemW _).mpr ⟨hk, by exact hx⟩
    rw [he] at hkW
    exact mem_modO2Image_iff.mpr ⟨k, hkW, rfl⟩
  · right
    refine le_antisymm hWK fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image_iff.mp hx
    have hkW : (k : G) ∈ W := by rw [he]; exact hk
    obtain ⟨_, h2⟩ := (hmemW _).mp hkW
    exact h2

end Star

section Two

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem oTwoUpper_top_normal (Γ : Type*) [Group Γ] : (oTwoUpper (⊤ : Subgroup Γ)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))

omit [Finite G] in
theorem modO2Image_normal {A : Subgroup G}
    (hHA : H ≤ Subgroup.normalizer (A : Set G)) : (modO2Image H A).Normal := by
  have hn : (A.subgroupOf H).Normal := by
    refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHA g.2) n).mp (Subgroup.mem_subgroupOf.mp hn)
    simpa using h1
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem lemma14_7_15_two (h331 : Stmt3_3_1) (hThm : Thm14_5_3) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h75 : Lemma14_7_5) (S : Setting147 G T L V H)
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    (Subgroup.center ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))).map
        (oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))).subtype = modO2Image H (l1 T L V) ∧
    ∃ y ∈ modO2Image H T,
      y ∈ Subgroup.centralizer (modO2Image H (l1 T L V) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧
      y ^ 2 ≠ 1 ∧ y ^ 4 = 1 ∧
      (∀ r ∈ modO2Image H T,
        r ∈ Subgroup.centralizer (modO2Image H (l1 T L V) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) →
        r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) ∧
      (∀ x ∈ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)),
        y ^ 2 * x * (y ^ 2)⁻¹ * x ∈ modO2Image H (l1 T L V)) ∧
      (∀ W : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), modO2Image H (l1 T L V) ≤ W →
        W ≤ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) → (∀ w ∈ W, y * w * y⁻¹ ∈ W) →
        W = modO2Image H (l1 T L V) ∨ W = oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL1K, -, -, hirrK, hHL1⟩ := lemma14_7_15_one h331 hThm h1222 h1332 h1334 S hK
  set Γ := ↥H ⧸ CFSG.pCore 2 ↥H with hΓ
  set X := oTwoUpper (⊤ : Subgroup Γ) with hX
  have hXn : X.Normal := oTwoUpper_top_normal Γ
  set L1s := modO2Image H (l1 T L V) with hL1s
  set Ts := modO2Image H T with hTs
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hL1n : L1s.Normal := modO2Image_normal hHL1
  obtain ⟨-, -, hcard3, -, hR1C, hidx, -⟩ := h75 G T L V H S hL1n
  have hL1X : L1s ≤ X := by
    rw [hX, ← modO2Image_oTwoUpper]
    exact modO2Image_mono hL1K
  have hcen : (Subgroup.center ↥X).map X.subtype = L1s :=
    center_eq_of_normal_card_three hK hL1X hL1n hcard3
  refine ⟨hcen, ?_⟩
  set ρ : Γ →* MulAut ↥X := MulAut.conjNormal with hρdef
  have hρ : ∀ (g : Γ) (x : ↥X), ((ρ g x : ↥X) : Γ) = g * x * g⁻¹ := fun g x =>
    MulAut.conjNormal_apply g x
  have hmemZ : ∀ x : ↥X, x ∈ Subgroup.center ↥X ↔ (x : Γ) ∈ L1s := by
    intro x
    rw [← hcen]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hfixZ : ∀ g : Γ, (∀ z ∈ Subgroup.center ↥X, ρ g z = z) ↔
      g ∈ Subgroup.centralizer (L1s : Set Γ) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h z hz
      have hzX := hL1X hz
      have h1 := congrArg Subtype.val (h ⟨z, hzX⟩ ((hmemZ ⟨z, hzX⟩).mpr hz))
      rw [hρ] at h1
      calc z * g = g * z * g⁻¹ * g := by rw [h1]
        _ = g * z := by group
    · intro h z hz
      apply Subtype.ext
      rw [hρ, ← h z ((hmemZ z).mp hz)]
      group
  have hO2 : CFSG.pCore 2 Γ = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hq : ∀ g : Γ, ∃ k : ℕ, g ^ 2 ^ k ∈ X := fun g =>
    exists_pow_mem_oTwoUpper ⊤ (Subgroup.mem_top g)
  have hT2 : IsPGroup 2 ↥T := S.hyp.fsu.sylow.1
  have hTs2 : IsPGroup 2 ↥Ts :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  have hfaith : ∀ g ∈ Ts, ρ g = 1 → g = 1 := by
    intro g hg h1
    obtain ⟨m, hm⟩ := hTs2 ⟨g, hg⟩
    have hm' : g ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine eq_one_of_centralizes_two hO2 hq hm' ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (congrArg (fun φ : MulAut ↥X => φ ⟨x, hx⟩) h1)
    simp only [MulAut.one_apply] at h2
    rw [hρ] at h2
    calc x * g = g * x * g⁻¹ * g := by rw [h2]
      _ = g * x := by group
  set 𝒯 := Ts.map ρ with h𝒯def
  have h𝒯 : IsPGroup 2 ↥𝒯 := hTs2.map ρ
  have hirr : ∀ W : Subgroup ↥X, Subgroup.center ↥X ≤ W → (∀ t ∈ 𝒯, ∀ w ∈ W, t w ∈ W) →
      W = Subgroup.center ↥X ∨ W = ⊤ := by
    intro W hZW hW
    have hA : modO2Image H (l1 T L V ⊔ pCoreOf 2 (oTwoUpper H)) = L1s :=
      modO2Image_sup_of_le_pCoreOf hL1H
        (by rw [pCoreOf_eq_inf_pCoreOf hKH (le_normalizer_oTwoUpper H)]; exact inf_le_right)
    have hKs : modO2Image H (oTwoUpper H) = X := modO2Image_oTwoUpper H
    have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      hTH.trans (le_normalizer_oTwoUpper H)
    have hAK : l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H :=
      sup_le hL1K (pCoreOf_le 2 _)
    have hZW' : L1s ≤ W.map X.subtype := by
      rw [← hcen]
      exact Subgroup.map_mono hZW
    have hTW' : Ts ≤ Subgroup.normalizer ((W.map X.subtype : Subgroup Γ) : Set Γ) := by
      have key : ∀ t ∈ Ts, ∀ w ∈ W.map X.subtype, t * w * t⁻¹ ∈ W.map X.subtype := by
        intro t ht w hw
        obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
        exact ⟨ρ t w', hW _ ⟨t, ht, rfl⟩ w' hw', hρ t w'⟩
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact key t ht w
      · intro h
        have := key t⁻¹ (Ts.inv_mem ht) _ h
        simpa [mul_assoc] using this
    rcases irr_star hKH hAK hTH hTK hirrK (W.map X.subtype) (by rw [hA]; exact hZW')
        (by rw [hKs]; exact Subgroup.map_subtype_le W) hTW' with he | he
    · left
      apply Subgroup.map_injective X.subtype_injective
      rw [he, hA, hcen]
    · right
      apply Subgroup.map_injective X.subtype_injective
      rw [he, hKs, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnot : ∃ t ∈ 𝒯, ¬ ∀ z ∈ Subgroup.center ↥X, t z = z := by
    by_contra hno
    push Not at hno
    have hle : Ts ≤ Ts ⊓ Subgroup.centralizer (L1s : Set Γ) := fun t ht =>
      ⟨ht, (hfixZ t).mp (hno _ ⟨t, ht, rfl⟩)⟩
    have heq : modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T)) = Ts := by
      rw [hR1C]
      exact le_antisymm inf_le_left hle
    rw [heq, Subgroup.relIndex_self] at hidx
    norm_num at hidx
  obtain ⟨y', hy'𝒯, hy'Z, hy'2, hy'4⟩ := Heis.exists_order_four hK h𝒯 hirr hnot
  obtain ⟨y, hyT, rfl⟩ := Subgroup.mem_map.mp hy'𝒯
  have hyC : y ∈ Subgroup.centralizer (L1s : Set Γ) := (hfixZ y).mp hy'Z
  have hy4 : y ^ 4 = 1 :=
    hfaith _ (Ts.pow_mem hyT 4) (by rw [map_pow]; exact hy'4)
  have hy2 : y ^ 2 ≠ 1 := fun h => hy'2 (by rw [← map_pow, h, map_one])
  have hr2 : ρ (y ^ 2) * ρ (y ^ 2) = 1 := by
    rw [← map_mul, ← pow_add]
    exact (by rw [show 2 + 2 = 4 by norm_num, hy4, map_one])
  have hrZ : ∀ z ∈ Subgroup.center ↥X, ρ (y ^ 2) z = z :=
    (hfixZ _).mpr (Subgroup.pow_mem _ hyC 2)
  have hrne : ρ (y ^ 2) ≠ 1 := fun h => hy2 (hfaith _ (Ts.pow_mem hyT 2) h)
  have hrinv := Heis.inverts_of_involution hK hr2 hrZ hrne
  refine ⟨y, hyT, hyC, hy2, hy4, ?_, ?_, ?_⟩
  ·
    intro r hrT hrC hr2' hr1
    have h1 : ρ r * ρ r = 1 := by rw [← map_mul, ← sq, hr2', map_one]
    have h2 : ∀ z ∈ Subgroup.center ↥X, ρ r z = z := (hfixZ r).mpr hrC
    have h3 : ρ r ≠ 1 := fun h => hr1 (hfaith r hrT h)
    obtain ⟨m, hm⟩ := hTs2 ⟨r * y ^ 2, Ts.mul_mem hrT (Ts.pow_mem hyT 2)⟩
    have hm' : (ρ r * ρ (y ^ 2)) ^ 2 ^ m = 1 := by
      rw [← map_mul, ← map_pow]
      have := congrArg Subtype.val hm
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [this, map_one]
    have he := Heis.eq_of_involutions hK h1 hr2 h2 hrZ h3 hrne hm'
    have h4 : ρ (r * (y ^ 2)⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
    have h5 := hfaith _ (Ts.mul_mem hrT (Ts.inv_mem (Ts.pow_mem hyT 2))) h4
    exact mul_inv_eq_one.mp h5
  ·
    intro x hx
    have h1 := hrinv ⟨x, hx⟩
    rw [hmemZ, Subgroup.coe_mul, hρ] at h1
    exact h1
  ·
    intro W hLW hWX hyW
    by_contra hne
    push Not at hne
    have hψZ : ∀ z ∈ Subgroup.center ↥X, ρ y z = z := hy'Z
    have hψ4 : (ρ y) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    have hψ2 : (ρ y) ^ 2 ≠ 1 := hy'2
    set W' := W.subgroupOf X with hW'
    have hZW' : Subgroup.center ↥X ≤ W' := fun z hz =>
      Subgroup.mem_subgroupOf.mpr (hLW ((hmemZ z).mp hz))
    have hW'Z : W' ≠ Subgroup.center ↥X := by
      intro h
      apply hne.1
      apply le_antisymm _ hLW
      intro w hw
      have h1 : (⟨w, hWX hw⟩ : ↥X) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
      rw [h] at h1
      exact (hmemZ _).mp h1
    have hW't : W' ≠ ⊤ := by
      intro h
      apply hne.2
      refine le_antisymm hWX fun x hx => ?_
      have h1 : (⟨x, hx⟩ : ↥X) ∈ W' := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    refine Heis.not_invariant_of_order_four hK hψZ hψ4 hψ2 hZW' hW'Z hW't fun w hw => ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hρ]
    exact hyW _ (Subgroup.mem_subgroupOf.mp hw)

end Two

end CFSG.Quasithin.H13.L32A
