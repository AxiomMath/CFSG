module

public import CFSG.Quasithin.H13.L32AC32f
public import CFSG.Quasithin.Background.E6SevenThree

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.SBc5SL2

section Generic

variable {Y : Type} [Group Y]

theorem exists_orderOf_normalizer_sylow {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X)
    {Q : Subgroup X} (hQ : IsSylowTwoOf Q ⊤) :
    ∃ h ∈ Subgroup.normalizer (Q : Set X), orderOf h = 2 ^ n - 1 := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := SBc6.exists_sl2_equiv_of_psl hX
  have : Finite X := Finite.of_equiv _ φ.toEquiv
  have hU' : IsSylowTwoOf ((Uplus F).map φ.toMonoidHom) ⊤ := by
    obtain ⟨-, hp, hidx⟩ := isSylowTwoOf_Uplus hn hFcard
    refine ⟨le_top, hp.map _, ?_⟩
    have e1 : ((Uplus F).subgroupOf ⊤).index = (Uplus F).index :=
      Subgroup.relIndex_top_right (Uplus F)
    have e2 : (((Uplus F).map φ.toMonoidHom).subgroupOf ⊤).index =
        ((Uplus F).map φ.toMonoidHom).index := Subgroup.relIndex_top_right _
    have e3 : ((Uplus F).map φ.toMonoidHom).index = (Uplus F).index :=
      Subgroup.index_map_equiv _ φ
    rw [e2, e3]
    rwa [e1] at hidx
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hU' hQ
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hdmN : dm a ∈ Subgroup.normalizer (Uplus F : Set (SL2 F)) := by
    rw [normalizer_Uplus]
    exact dm_mem_Tplus a
  refine ⟨g * φ (dm a) * g⁻¹, mem_normalizer_of_conj_mem_fin fun q hq => ?_, ?_⟩
  · rw [hg, B6.mem_conjSub] at hq ⊢
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hq
    have e : g⁻¹ * (g * φ (dm a) * g⁻¹ * q * (g * φ (dm a) * g⁻¹)⁻¹) * g =
        φ.toMonoidHom (dm a * u * (dm a)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hue]
      simp only [MulEquiv.coe_toMonoidHom]
      group
    rw [e]
    exact Subgroup.mem_map.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp hdmN u).mp hu, rfl⟩
  · have hdm1 : ∀ c : Fˣ, dm c = 1 ↔ c = 1 := fun c => ⟨fun h => by
        have := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
        simp only [E6.coe_dm', Matrix.SpecialLinearGroup.coe_one] at this
        exact Units.ext (by simpa using this), fun h => by rw [h, E6.dm_one']⟩
    have hdm : orderOf (dm a) = orderOf a :=
      orderOf_eq_orderOf_iff.mpr fun k => by rw [E6.dm_pow', hdm1]
    rw [show g * φ (dm a) * g⁻¹ = MulAut.conj g (φ (dm a)) from rfl, MulEquiv.orderOf_eq,
      MulEquiv.orderOf_eq, hdm, ha, Nat.card_units, hFcard]

theorem pow_eq_one_of_mul {N₁ N₂ : Subgroup Y} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hi : ∀ z ∈ N₁, z ∈ N₂ → z = 1) {a b : Y} (ha : a ∈ N₁) (hb : b ∈ N₂) {m : ℕ}
    (h : (a * b) ^ m = 1) : a ^ m = 1 := by
  have hcomm : Commute a b := hc a ha b hb
  rw [hcomm.mul_pow] at h
  have h1 : a ^ m = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h
  exact hi _ (pow_mem ha m) (h1 ▸ inv_mem (pow_mem hb m))

theorem mem_of_pow_two [Finite Y] {N S : Subgroup Y} (hS : IsSylowIn 2 S N) {b : Y}
    (hbN : b ∈ N) (hbS : b ∈ Subgroup.normalizer (S : Set Y)) {m : ℕ} (hb : b ^ 2 ^ m = 1) :
    b ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hb)
  have hR : IsPGroup 2 ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hRS : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set Y) :=
    Subgroup.zpowers_le.mpr hbS
  have hsup : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers b) := hS.isPGroup.to_sup_of_normal_left' hR hRS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hsup
  have hle : S ⊔ Subgroup.zpowers b ≤ N := sup_le hS.le (Subgroup.zpowers_le.mpr hbN)
  have hdvd : S.relIndex (S ⊔ Subgroup.zpowers b) ∣ S.relIndex N :=
    ⟨_, (Subgroup.relIndex_mul_relIndex S (S ⊔ Subgroup.zpowers b) N le_sup_left hle).symm⟩
  have hdvd2 : S.relIndex (S ⊔ Subgroup.zpowers b) ∣ 2 ^ k :=
    hk ▸ Subgroup.relIndex_dvd_card S (S ⊔ Subgroup.zpowers b)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hne
    exact hS.not_dvd_relIndex ((hj ▸ dvd_pow_self 2 hne).trans hdvd)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))

theorem eq_one_of_conj_mul {S : Subgroup Y} (hS : IsPGroup 2 ↥S) {k t : Y} (hk3 : k ^ 3 = 1)
    (h1 : t * k * t⁻¹ * k⁻¹ ∈ S) (h2 : t * k * t⁻¹ * k ∈ S) : k = 1 := by
  have hk2 : k * k ∈ S := by
    have := mul_mem (inv_mem h1) h2
    rwa [show (t * k * t⁻¹ * k⁻¹)⁻¹ * (t * k * t⁻¹ * k) = k * k by group] at this
  have hkS : k ∈ S := by
    have e : k = (k * k)⁻¹ := by
      rw [pow_three] at hk3
      calc k = (k * k)⁻¹ * (k * (k * k)) := by group
        _ = (k * k)⁻¹ := by rw [hk3, mul_one]
    rw [e]
    exact inv_mem hk2
  obtain ⟨j, hj⟩ := hS ⟨k, hkS⟩
  have hkj : k ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h3 : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
  have hcop : Nat.Coprime (orderOf k) (2 ^ j) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right j (by norm_num))
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hkj))

theorem mem_normalizer_of_inner [Finite Y] {N P S : Subgroup Y} {n : ℕ} (hN : IsPSL 2 2 n ↥N)
    (hNs : ¬ Group.IsSolvable ↥N) (hZ : Subgroup.center ↥N = ⊥)
    (hPN : P ≤ Subgroup.normalizer (N : Set Y)) (hP : Group.IsSolvable ↥P)
    (hS : IsSylowIn 2 S N) (hSP : S ≤ P) {p k : Y} (hp : p ∈ P) (hk : k ∈ N)
    (hpk : ∀ m ∈ N, p * m * p⁻¹ = k * m * k⁻¹) : k ∈ Subgroup.normalizer (S : Set Y) := by
  let θ : ↥P →* MulAut ↥N := N.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  let c : ↥N →* MulAut ↥N := MulAut.conj
  let D : Subgroup ↥N := θ.range.comap c
  have hRs : Group.IsSolvable ↥θ.range :=
    Group.isSolvable_of_surjective (f := θ.rangeRestrict) θ.rangeRestrict_surjective
  have hDs : Group.IsSolvable ↥D := by
    let f : ↥D →* ↥θ.range := (c.comp D.subtype).codRestrict θ.range fun d => d.2
    have hf : Function.Injective f := by
      intro d₁ d₂ h
      have h1 : c d₁ = c d₂ := congrArg Subtype.val h
      have hz : ((d₁ : ↥N)⁻¹ * d₂) ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun φ : MulAut ↥N => φ g) h1
        simp only [c, MulAut.conj_apply] at h2
        calc g * ((d₁ : ↥N)⁻¹ * d₂) = (d₁ : ↥N)⁻¹ * ((d₁ : ↥N) * g * (d₁ : ↥N)⁻¹) * d₂ := by
              group
          _ = (d₁ : ↥N)⁻¹ * ((d₂ : ↥N) * g * (d₂ : ↥N)⁻¹) * d₂ := by rw [h2]
          _ = (d₁ : ↥N)⁻¹ * d₂ * g := by group
      rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hz
      exact Subtype.ext hz
    exact Group.isSolvable_of_isSolvable_injective (f := f) hf
  set Q : Subgroup ↥N := S.subgroupOf N with hQdef
  have hQ : IsSylowTwoOf Q ⊤ := by
    refine ⟨le_top, hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm, ?_⟩
    have e : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right Q
    rw [e]
    exact hS.not_dvd_relIndex
  have hQD : Q ≤ D := fun s hs => ⟨⟨(s : Y), hSP hs⟩, MulEquiv.ext fun _ => Subtype.ext rfl⟩
  rcases SBc6.overgroup_of_psl hN hQ hQD with h | h
  · have : Group.IsSolvable ↥(⊤ : Subgroup ↥N) := h ▸ hDs
    exact absurd (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
      (MulEquiv.surjective _)) hNs
  · have hkD : (⟨k, hk⟩ : ↥N) ∈ D :=
      ⟨⟨p, hp⟩, MulEquiv.ext fun m => Subtype.ext (hpk m m.2)⟩
    have hkQ := h hkD
    refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
    have hsQ : (⟨s, hS.le hs⟩ : ↥N) ∈ Q := hs
    exact (Subgroup.mem_normalizer_iff.mp hkQ _).mp hsQ

end Generic

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isSolvable_l1T_star (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T)) := by
  have hLT : Group.IsSolvable ↥(l1 T L V ⊔ T) := by
    rw [sup_comm]
    exact isSolvable_of_isTwoThree (isTwoThree_card_sup (relIndex_l1 h1222 h1332 h1334 S.hyp)
      S.hyp.fsu.sylow.1 (Setting147.T_le_N_l1 S h1332))
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have : Group.IsSolvable ↥((l1 T L V ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLTH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.isSolvable_of_surjective
    (f := MonoidHom.subgroupMap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      ((l1 T L V ⊔ T).subgroupOf H)) (MonoidHom.subgroupMap_surjective _ _)

namespace CtxL2

variable {K : Subgroup G} {t₀ : G} {n : ℕ} (C : CtxL2 T L V H K t₀ n)
include C

theorem isPSL_kb : IsPSL 2 2 n ↥(modO2Image H K) := by
  obtain ⟨e⟩ := C.nonempty_equiv
  exact IsPSL.of_mulEquiv e C.hP

theorem mem_normalizer_szS1_of_inner (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1)
    {k : ↥H ⧸ CFSG.pCore 2 ↥H} (hkK : k ∈ modO2Image H K)
    (hk : ∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image H A ≤ modO2Image H B :=
    fun h => Subgroup.map_mono fun _ hz => h hz
  have := isSolvable_l1T_star h1222 h1332 h1334 C.S
  have hP : Group.IsSolvable ↥(modO2Image H (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : _ ≤ modO2Image H (l1 T L V ⊔ T)))
      (Subgroup.inclusion_injective _)
  refine mem_normalizer_of_inner C.isPSL_kb
    (not_isSolvable_of_mem_cComp (modO2Image_mem_cComp C.hK)) C.center_kb inf_le_right hP
    C.isSylowIn_szS1 (fun s hs => ⟨hmono le_sup_right hs.1, Subgroup.le_normalizer hs.2⟩)
    ⟨hmono le_sup_left (mem_modO2Image'.mpr ⟨_, hy, rfl⟩), (C.mk_mem_normalizers hy hy3).1⟩
    hkK hk

theorem mk_l1_mem_normalizer_szS1 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (y : G) (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  obtain ⟨k₁, hk₁K, -, -, -, -, -, hk₁, -⟩ := C.decomp hA37 hy hy3
  have hk := C.mem_normalizer_szS1_of_inner h1222 h1332 h1334 hy hy3 hk₁K hk₁
  refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
  rw [hk₁ s hs.2]
  exact (Subgroup.mem_normalizer_iff.mp hk s).mp hs

theorem k₁_mem_szB1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {y : G}
    (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hkK : k ∈ modO2Image H K)
    (hk : ∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
      m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ szB1 T H K :=
  ⟨C.mem_normalizer_szS1_of_inner h1222 h1332 h1334 hy hy3 hkK hk, hkK⟩

theorem k₂_mem_szB2 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {y : G}
    (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hkK : k ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
    (hk : ∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * m *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ = k * m * k⁻¹) :
    k ∈ (szB1 T H K).map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
        _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ with htb
  rw [← C.kb'_eq] at hkK hk
  obtain ⟨k', hk'K, rfl⟩ := Subgroup.mem_map.mp hkK
  obtain ⟨hy', hy'3⟩ := C.conj_l1 h1332 hy hy3
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ =
      tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb := by
    rw [htb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hk'' : ∀ m ∈ modO2Image H K,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩ * m *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * y * t₀, Setting147.l1H' C.S hy'⟩)⁻¹ =
          k' * m * k'⁻¹ := by
    intro m hm
    have h1 := hk (tb * m * tb⁻¹) (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply] at h1
    rw [e]
    calc tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb * m *
          (tb⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * tb)⁻¹ =
          tb⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
            (tb * m * tb⁻¹) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹) * tb := by group
      _ = tb⁻¹ * (tb * k' * tb⁻¹ * (tb * m * tb⁻¹) * (tb * k' * tb⁻¹)⁻¹) * tb := by rw [h1]
      _ = k' * m * k'⁻¹ := by group
  exact Subgroup.mem_map.mpr ⟨k', C.k₁_mem_szB1 h1222 h1332 h1334 hy' hy'3 hk'K hk'', rfl⟩

end CtxL2

end CFSG.Quasithin.H13.L32A.C
