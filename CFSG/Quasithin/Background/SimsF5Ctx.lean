module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bA

public section

namespace CFSG.Quasithin.SimsF5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42Aut
open U42F431

section Homs

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] noncomputable def ctxJB (j₁ : ↥P1h →* G) (j₂ : ↥P2h →* G) (hr₁ : j₁.range = M₁)
    (hr₂ : j₂.range = M₂)
    (hB : ∀ b : ↥Bh, j₁ (Subgroup.inclusion Bh_le_P1h b) = j₂ (Subgroup.inclusion Bh_le_P2h b)) :
    ↥Bh →* ↥(M₁ ⊓ M₂) :=
  (j₁.comp (Subgroup.inclusion Bh_le_P1h)).codRestrict (M₁ ⊓ M₂) fun b =>
    ⟨hr₁ ▸ ⟨_, rfl⟩, by
      show j₁ (Subgroup.inclusion Bh_le_P1h b) ∈ M₂
      rw [hB]
      exact hr₂ ▸ ⟨_, rfl⟩⟩

@[expose] noncomputable def autIsoOfHoms (j₁ : ↥P1h →* G) (j₂ : ↥P2h →* G) (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) (hr₁ : j₁.range = M₁) (hr₂ : j₂.range = M₂)
    (hB : ∀ b : ↥Bh, j₁ (Subgroup.inclusion Bh_le_P1h b) = j₂ (Subgroup.inclusion Bh_le_P2h b))
    (hI : ∀ g ∈ M₁ ⊓ M₂, ∃ b : ↥Bh, j₁ (Subgroup.inclusion Bh_le_P1h b) = g) :
    AutIso M₁ M₂ where
  φ1 := (MonoidHom.ofInjective h₁).trans (MulEquiv.subgroupCongr hr₁)
  φ2 := (MonoidHom.ofInjective h₂).trans (MulEquiv.subgroupCongr hr₂)
  φ12 := MulEquiv.ofBijective (ctxJB j₁ j₂ hr₁ hr₂ hB)
    ⟨fun a b hab => by
      have h : j₁ (Subgroup.inclusion Bh_le_P1h a) = j₁ (Subgroup.inclusion Bh_le_P1h b) :=
        congrArg Subtype.val hab
      exact Subgroup.inclusion_injective _ (h₁ h),
     fun g => by
      obtain ⟨b, hb⟩ := hI g.1 g.2
      exact ⟨b, Subtype.ext hb⟩⟩
  comm1 g := rfl
  comm2 g := Subtype.ext (hB g)

end Homs

section Ctx

theorem ctx_isPGroup_That : IsPGroup 2 That :=
  IsPGroup.of_card (n := 7) (by rw [card_That]; norm_num)

theorem xA_mem_of_normal_P1h {N : Subgroup Ah} (hN : N ≤ P1h)
    (hn : ∀ p ∈ P1h, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (h2 : IsPGroup 2 N) (hne : N ≠ ⊥) : xA ∈ N := by
  have hTP : That ≤ P1h := That_le_Bh.trans Bh_le_P1h
  have hnorm : That ≤ Subgroup.normalizer (N : Set Ah) := fun t ht =>
    Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn' => hn t (hTP ht) n hn', fun hn' => by
      have := hn t⁻¹ (P1h.inv_mem (hTP ht)) _ hn'
      simpa [mul_assoc] using this⟩
  have hsup : IsPGroup 2 ↥(N ⊔ That) := h2.to_sup_of_normal_left' ctx_isPGroup_That hnorm
  have hle : N ⊔ That ≤ P1h := sup_le hN hTP
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hdvd : Nat.card ↥(N ⊔ That) ∣ 1152 := card_P1h ▸ Subgroup.card_dvd_of_le hle
  have hk7 : k ≤ 7 := by
    rw [hk] at hdvd
    by_contra hk7
    have h8 : 2 ^ 8 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  have heq : N ⊔ That = That := by
    symm
    refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
    rw [card_That, hk]
    calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
      _ = 128 := by norm_num
  have hNT : N ≤ That := heq ▸ le_sup_left
  have : Group.IsNilpotent ↥That := ctx_isPGroup_That.isNilpotent
  have hnormal : (N.subgroupOf That).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne' : N.subgroupOf That ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hyN : (y : Ah) ∈ N := hy.1
  have hyC : ∀ t ∈ That, (y : Ah) * t = t * y := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩).symm
  rcases center_That y.2 hyC with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy1
  · rw [← h]
    exact hyN

theorem VA_le_of_normal_P2h {N : Subgroup Ah} (hn : ∀ p ∈ P2h, ∀ n ∈ N, p * n * p⁻¹ ∈ N)
    (hx : xA ∈ N) : VA ≤ N := by
  rw [VA, Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  have h : p ∈ MulAction.orbit ↥U42.P2 (0 : Fin 45) := by rw [U42.orbit_P2]; exact hp
  obtain ⟨g, hg⟩ := h
  have hgA : incl (g : U42.Y) ∈ P2h := by
    have : (g : U42.Y) ∈ P2h.comap incl := by rw [comap_P2h]; exact g.2
    exact this
  have hc := hn _ hgA xA hx
  rw [← sA_zero, sA_conj] at hc
  have hg' : ((incl (g : U42.Y) : Ah) : Equiv.Perm (Fin 45)) 0 = p := hg
  rw [hg'] at hc
  exact hc

theorem ctx_check : (U42F431.evalW [1, 0, 2, 0, 1]).getD 0 0 = 0 ∧
    (U42F431.evalW [1, 0, 2, 0, 1]).getD 15 0 = 34 ∧
    compL (compL (compL (tpL 34) (tpL 15)) (compL (tpL 34) (tpL 15))) (compL (tpL 34) (tpL 15)) =
        List.range 45 ∧ compL (tpL 34) (tpL 15) ≠ List.range 45 := by
  decide +kernel

theorem not_VA_le_of_normal_P1h {N : Subgroup Ah}
    (hn : ∀ p ∈ P1h, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (h2 : IsPGroup 2 N) (hV : VA ≤ N) : False := by
  obtain ⟨c0, c15, h3, h1⟩ := ctx_check
  set m : Ah := incl ⟨U42.wordP [1, 0, 2, 0, 1], U42.wordP_mem _⟩ with hm
  have hmrep : RepL (U42F431.evalW [1, 0, 2, 0, 1]) ((m : Ah) : Equiv.Perm (Fin 45)) :=
    U42.repL_wordP _
  have hmA : m ∈ P1h := mem_P1h_of_repL hmrep c0
  have h15L : (15 : Fin 45) ∈ U42.L0S := show (15 : Fin 45).val ∈ U42F431.L0 by decide
  have h15 : sA 15 ∈ N := hV (Subgroup.subset_closure ⟨15, h15L, rfl⟩)
  have hc := hn _ hmA _ h15
  rw [sA_conj] at hc
  have hm15 : ((m : Ah) : Equiv.Perm (Fin 45)) 15 = 34 := by
    apply Fin.ext
    rw [← hmrep.2 15]
    exact c15
  rw [hm15] at hc
  have hprod : sA 34 * sA 15 ∈ N := N.mul_mem hc h15
  obtain ⟨k, hk⟩ := h2 ⟨_, hprod⟩
  have hk' : (sA 34 * sA 15) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hrep : RepL (compL (tpL 34) (tpL 15)) ((((sA 34 * sA 15 : Ah)) : Equiv.Perm (Fin 45))) :=
    repL_mul (U42.repL_sT 34) (U42.repL_sT 15)
  have hcube : (sA 34 * sA 15) ^ 3 = 1 := by
    refine Subtype.ext (eq_of_repL ?_ (repL_one 45))
    rw [← h3]
    have := repL_mul (repL_mul hrep hrep) hrep
    simpa [pow_succ, mul_assoc] using this
  have hne1 : sA 34 * sA 15 ≠ 1 := fun h => by
    apply h1
    have h' : RepL (List.range 45) ((((sA 34 * sA 15 : Ah)) : Equiv.Perm (Fin 45))) := by
      rw [h]
      exact repL_one 45
    exact repL_unique hrep h'
  have hdvd3 := orderOf_dvd_of_pow_eq_one hcube
  have hdvd2 := orderOf_dvd_of_pow_eq_one hk'
  have h1' : orderOf (sA 34 * sA 15) = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
  exact hne1 (orderOf_eq_one_iff.1 h1')

end Ctx

section Main

theorem ctx_exists_central {X : Type} [Group X] [Finite X] {T U : Subgroup X} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hn : T ≤ Subgroup.normalizer (U : Set X)) (hU : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ t ∈ T, u * t = t * u := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(y : X), hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩).symm

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}

theorem toG_xB_sq (iso : AutIso M₁ M₂) : iso.toG xB ^ 2 = 1 := by
  have h : xB * xB = 1 := Subtype.ext (by
    show xA * xA = 1
    exact Subtype.ext (U42.x45_mul_self))
  rw [pow_two, ← AutIso.toG_mul, h]
  exact AutIso.toG_one iso

theorem toG_xB_ne_one (iso : AutIso M₁ M₂) : iso.toG xB ≠ 1 := by
  intro h
  rw [← AutIso.toG_one iso] at h
  have h' := congrArg (fun b : ↥Bh => ((b : Ah) : Equiv.Perm (Fin 45))) (AutIso.toG_injective iso h)
  exact U42.xY_ne_one (Subtype.ext h')

theorem toG_xB_mem_centerOf (iso : AutIso M₁ M₂) : iso.toG xB ∈ centerOf (M₁ ⊓ M₂) := by
  refine ⟨iso.toG_mem xB, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bh, iso.toG b = g := ⟨iso.phiB.symm ⟨g, hg⟩, by
    simp [AutIso.toG]⟩
  rw [← AutIso.toG_mul, ← AutIso.toG_mul]
  congr 1
  exact Subtype.ext ((mul_xA_comm_iff (b : Ah)).2 (Bh_le_P1h b.2))

theorem pCoreOf_sup_eq_bot (iso : AutIso M₁ M₂)
    (hcz : Subgroup.centralizer ({iso.toG xB} : Set G) ≤ M₁) : pCoreOf 2 (M₁ ⊔ M₂) = ⊥ := by
  set z := iso.toG xB with hz
  set Q := pCoreOf 2 (M₁ ⊔ M₂) with hQ
  have hQ2 : IsPGroup 2 ↥Q := (CFSG.pCore_isPGroup (p := 2) (G := ↥(M₁ ⊔ M₂))).map _
  have hQn : ∀ g ∈ M₁ ⊔ M₂, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hg q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hq
    have := (CFSG.pCore_normal (p := 2) (G := ↥(M₁ ⊔ M₂))).conj_mem y hy ⟨g, hg⟩
    exact ⟨_, this, rfl⟩
  by_contra hne
  have hzM : z ∈ M₁ ⊔ M₂ := Subgroup.mem_sup_left (iso.toG_mem xB).1
  have hZ2 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (toG_xB_sq iso) (toG_xB_ne_one iso)
  have hZN : Subgroup.zpowers z ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => hQn z hzM n hn, fun hn => ?_⟩
    have := hQn z⁻¹ (Subgroup.inv_mem _ hzM) _ hn
    simpa [mul_assoc] using this
  have hT2 := hQ2.to_sup_of_normal_left' hZ2 hZN
  have hTn : Q ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hZN
  obtain ⟨u, huQ, hu1, huc⟩ := ctx_exists_central hT2 le_sup_left hTn hne
  have huz : u * z = z * u := huc z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have huM₁ : u ∈ M₁ := hcz (Subgroup.mem_centralizer_singleton_iff.2 huz)
  set N₁ : Subgroup Ah := (Q.comap iso.toG1).map P1h.subtype with hN₁
  have hN₁le : N₁ ≤ P1h := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hN₁mem : ∀ b : ↥P1h, (b : Ah) ∈ N₁ ↔ iso.toG1 b ∈ Q := by
    intro b
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rwa [Subtype.ext hbb'] at hb'
    · intro hb
      exact ⟨b, hb, rfl⟩
  have hN₁n : ∀ p ∈ P1h, ∀ n ∈ N₁, p * n * p⁻¹ ∈ N₁ := by
    intro p hp n hn
    obtain ⟨b, hb, rfl⟩ := hn
    have hb' : iso.toG1 b ∈ Q := hb
    have := hQn (iso.toG1 ⟨p, hp⟩) (Subgroup.mem_sup_left (iso.phi1 ⟨p, hp⟩).2) _ hb'
    refine (hN₁mem (⟨p, hp⟩ * b * ⟨p, hp⟩⁻¹)).2 ?_
    simpa [map_mul, map_inv] using this
  have hN₁2 : IsPGroup 2 ↥N₁ := by
    have h1 : IsPGroup 2 ↥(Q.comap iso.toG1) :=
      hQ2.comap_of_injective iso.toG1 (AutIso.toG1_injective iso)
    exact h1.map _
  have hN₁ne : N₁ ≠ ⊥ := by
    intro h
    obtain ⟨b, hb⟩ : ∃ b : ↥P1h, iso.toG1 b = u := ⟨iso.phi1.symm ⟨u, huM₁⟩, by
      simp [AutIso.toG1]⟩
    have hbN : (b : Ah) ∈ N₁ := (hN₁mem b).2 (hb ▸ huQ)
    rw [h, Subgroup.mem_bot] at hbN
    apply hu1
    rw [← hb, show b = 1 from Subtype.ext hbN, map_one]
  have hxN₁ : xA ∈ N₁ := xA_mem_of_normal_P1h hN₁le hN₁n hN₁2 hN₁ne
  have hzQ : z ∈ Q := by
    have h := (hN₁mem (Subgroup.inclusion Bh_le_P1h xB)).1 hxN₁
    rwa [AutIso.toG1_inclusion] at h
  set N₂ : Subgroup Ah := (Q.comap iso.toG2).map P2h.subtype with hN₂
  have hN₂mem : ∀ b : ↥P2h, (b : Ah) ∈ N₂ ↔ iso.toG2 b ∈ Q := by
    intro b
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rwa [Subtype.ext hbb'] at hb'
    · intro hb
      exact ⟨b, hb, rfl⟩
  have hN₂n : ∀ p ∈ P2h, ∀ n ∈ N₂, p * n * p⁻¹ ∈ N₂ := by
    intro p hp n hn
    obtain ⟨b, hb, rfl⟩ := hn
    have hb' : iso.toG2 b ∈ Q := hb
    have := hQn (iso.toG2 ⟨p, hp⟩) (Subgroup.mem_sup_right (iso.phi2 ⟨p, hp⟩).2) _ hb'
    refine (hN₂mem (⟨p, hp⟩ * b * ⟨p, hp⟩⁻¹)).2 ?_
    simpa [map_mul, map_inv] using this
  have hxN₂ : xA ∈ N₂ := by
    refine (hN₂mem (Subgroup.inclusion Bh_le_P2h xB)).2 ?_
    rw [AutIso.toG2_inclusion]
    exact hzQ
  have hVN₂ : VA ≤ N₂ := VA_le_of_normal_P2h hN₂n hxN₂
  have hVN₁ : VA ≤ N₁ := by
    intro v hv
    have hvB : v ∈ Bh := VA_le_Bh hv
    have h2 := (hN₂mem (Subgroup.inclusion Bh_le_P2h ⟨v, hvB⟩)).1 (hVN₂ hv)
    rw [AutIso.toG2_inclusion] at h2
    have h1 := (hN₁mem (Subgroup.inclusion Bh_le_P1h ⟨v, hvB⟩)).2
      (by rw [AutIso.toG1_inclusion]; exact h2)
    exact h1
  exact not_VA_le_of_normal_P1h hN₁n hN₁2 hVN₁

@[expose] noncomputable def autCtxOf (iso : AutIso M₁ M₂) {z : G} (hz : iso.toG xB = z)
    (hres : pResidual 2 G = ⊤) (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁)
    (hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁)
    (hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂) : AutCtx G M₁ M₂ z where
  res := hres
  iso := iso
  o2 := pCoreOf_sup_eq_bot iso (hz ▸ hcz)
  z2 := hz ▸ toG_xB_sq iso
  z1 := hz ▸ toG_xB_ne_one iso
  zc := hz ▸ toG_xB_mem_centerOf iso
  cz := hcz
  N1 := hN1
  N2 := hN2

end Main

end CFSG.Quasithin.SimsF5
