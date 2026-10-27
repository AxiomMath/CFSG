module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38AbsA

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {H : Type*} [Group H] [Finite H] {Ω : Type*} [Finite Ω] [MulAction H Ω]

theorem factorization_3024_three : (3024 : ℕ).factorization 3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three,
    show (3024 : ℕ) = 3 ^ 3 * 112 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_378_two : (378 : ℕ).factorization 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two, show (378 : ℕ) = 2 * 189 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem no_E27_of_card_3024 {C : Subgroup H} (hC : Nat.card C = 3024)
    {y : H} (hyC : y ∈ C) (hy : orderOf y = 9)
    {E : Subgroup H} (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) : ¬ E ≤ C := by
  intro hEC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardE' : Nat.card (E.subgroupOf C) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hE27]
  let Q : Sylow 3 C := Sylow.ofCard (E.subgroupOf C)
    (by rw [hcardE', hC, factorization_3024_three]; norm_num)
  obtain ⟨y', hy'⟩ : ∃ y' : C, (y' : H) = y := ⟨⟨y, hyC⟩, rfl⟩
  have hy'ord : orderOf y' = 9 := by
    rw [← Subgroup.orderOf_coe, hy', hy]
  have hP : IsPGroup 3 (Subgroup.zpowers y') := by
    rw [IsPGroup.iff_card]
    refine ⟨2, ?_⟩
    rw [Nat.card_zpowers, hy'ord]
    norm_num
  obtain ⟨P, hPy⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  have hgQ : MulAut.conj g • (P : Subgroup C) = (Q : Subgroup C) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hy'Q : MulAut.conj g • y' ∈ E.subgroupOf C := by
    have hmem : y' ∈ (P : Subgroup C) := hPy (Subgroup.mem_zpowers y')
    have h1 := Subgroup.smul_mem_pointwise_smul y' (MulAut.conj g) _ hmem
    rw [hgQ] at h1
    exact h1
  have hmemE : ((MulAut.conj g y' : C) : H) ∈ E := Subgroup.mem_subgroupOf.mp hy'Q
  have hord : orderOf (MulAut.conj g y' : C) = 9 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y').trans hy'ord
  have hord9 : orderOf ((MulAut.conj g y' : C) : H) = 9 := (Subgroup.orderOf_coe _).trans hord
  have hdvd := orderOf_dvd_of_pow_eq_one (hE.2 _ hmemE)
  rw [hord9] at hdvd
  norm_num at hdvd

theorem eq_of_mem_zpowers_involution {G : Type*} [Group G] {s x : G} (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (hx : x ∈ Subgroup.zpowers s) (hx1 : x ≠ 1) : x = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : s ^ (k % 2) = s ^ k := by
    have := zpow_mod_orderOf s k
    rw [ho] at this
    exact_mod_cast this
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact absurd hk.symm hx1
  · rw [h1, zpow_one] at hk
    exact hk.symm

theorem conj_of_involution_378 {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 378)
    {s u : G} (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ c : G, c * s * c⁻¹ = u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hos : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hou : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  let P : Sylow 2 G := Sylow.ofCard (Subgroup.zpowers s)
    (by rw [Nat.card_zpowers, hos, hG, factorization_378_two]; norm_num)
  let Q : Sylow 2 G := Sylow.ofCard (Subgroup.zpowers u)
    (by rw [Nat.card_zpowers, hou, hG, factorization_378_two]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hgQ : MulAut.conj g • (P : Subgroup G) = (Q : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hmem : s ∈ (P : Subgroup G) := Subgroup.mem_zpowers s
  have h1 := Subgroup.smul_mem_pointwise_smul s (MulAut.conj g) _ hmem
  rw [hgQ] at h1
  have hx1 : MulAut.conj g s ≠ 1 := by
    intro h
    apply hs1
    apply (MulAut.conj g).injective
    rw [map_one]
    exact h
  refine ⟨g, ?_⟩
  have h3 : MulAut.conj g s = u := eq_of_mem_zpowers_involution hu2 hu1 h1 hx1
  rw [MulAut.conj_apply] at h3
  exact h3

theorem card_fix_odd (hΩ : Nat.card Ω = 513) {V : Subgroup H} (hV : IsPGroup 2 V) :
    Odd (Nat.card {p : Ω // ∀ v ∈ V, v • p = p}) := by
  have hmod := hV.card_modEq_card_fixedPoints Ω
  have hcongr : Nat.card (MulAction.fixedPoints V Ω) = Nat.card {p : Ω // ∀ v ∈ V, v • p = p} :=
    Nat.card_congr (Equiv.subtypeEquivRight
      (fun p => ⟨fun h v hv => h ⟨v, hv⟩, fun h g => h g.1 g.2⟩))
  rw [hcongr, hΩ] at hmod
  unfold Nat.ModEq at hmod
  exact Nat.odd_iff.mpr (by omega)

theorem smul_fix_mem {V E : Subgroup H} (hEV : E ≤ Subgroup.normalizer (V : Set H)) (e : E)
    {p : Ω} (hp : ∀ v ∈ V, v • p = p) : ∀ v ∈ V, v • ((e : H) • p) = (e : H) • p := by
  intro v hv
  have hconj : (e : H)⁻¹ * v * (e : H) ∈ V :=
    (Subgroup.mem_normalizer_iff''.mp (hEV e.2) v).mp hv
  have key : v * (e : H) = (e : H) * ((e : H)⁻¹ * v * (e : H)) := by group
  rw [← mul_smul, key, mul_smul, hp _ hconj]

abbrev fixActC {V E : Subgroup H} (hEV : E ≤ Subgroup.normalizer (V : Set H)) :
    MulAction E {p : Ω // ∀ v ∈ V, v • p = p} where
  smul e p := ⟨(e : H) • p.1, smul_fix_mem hEV e p.2⟩
  one_smul p := Subtype.ext (one_smul H p.1)
  mul_smul e f p := Subtype.ext (mul_smul (e : H) (f : H) p.1)

theorem exists_common_fixed {V E : Subgroup H} (hEV : E ≤ Subgroup.normalizer (V : Set H))
    (hE3 : IsPGroup 3 E) (h : ¬ 3 ∣ Nat.card {p : Ω // ∀ v ∈ V, v • p = p}) :
    ∃ p : Ω, (∀ v ∈ V, v • p = p) ∧ ∀ e ∈ E, e • p = p := by
  letI := fixActC (Ω := Ω) hEV
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hE3.card_modEq_card_fixedPoints {p : Ω // ∀ v ∈ V, v • p = p}
  have hne : Nat.card (MulAction.fixedPoints E {p : Ω // ∀ v ∈ V, v • p = p}) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact h ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  refine ⟨p.1, p.2, fun e he => ?_⟩
  have h1 := congrArg Subtype.val (hp ⟨e, he⟩)
  exact h1

theorem exists_two_fixed (hΩ : Nat.card Ω = 513)
    (hA : ∀ (E : Subgroup H), IsElemAbelian 3 E → Nat.card E = 27 → ∀ ω : Ω, ¬ ∀ e ∈ E, e • ω = ω)
    {V E : Subgroup H} (hVp : IsPGroup 2 V) (hEV : E ≤ Subgroup.normalizer (V : Set H))
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ a b : Ω, a ≠ b ∧ ∀ v ∈ V, v • a = a ∧ v • b = b := by
  have hodd := Nat.odd_iff.mp (card_fix_odd hΩ hVp)
  have h3 : 3 ∣ Nat.card {p : Ω // ∀ v ∈ V, v • p = p} := by
    by_contra h
    obtain ⟨p, _, hpE⟩ := exists_common_fixed hEV hE.isPGroup h
    exact hA E hE hE27 p hpE
  haveI : Nontrivial {p : Ω // ∀ v ∈ V, v • p = p} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne {p : Ω // ∀ v ∈ V, v • p = p}
  exact ⟨x.1, y.1, fun h => hxy (Subtype.ext h), fun v hv => ⟨x.2 v hv, y.2 v hv⟩⟩

theorem card_eq_two_of_fix2 (hH : Nat.card H = 99283968)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    (hΩ : Nat.card Ω = 513) {V : Subgroup H} (hVp : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    {a b : Ω} (hab : a ≠ b) (hfix : ∀ v ∈ V, v • a = a ∧ v • b = b) :
    Nat.card V = 2 := by
  have hKc : Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) = 378 := by
    have hK := card_pairStabilizer h2 hab
    rw [hΩ, hH] at hK
    have h1 : Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) * 262656
        = 378 * 262656 := by
      calc Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) * 262656
          = Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) *
              (513 - 1) * 513 := by norm_num [mul_assoc]
        _ = 99283968 := hK
        _ = 378 * 262656 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hVK : V ≤ MulAction.stabilizer H a ⊓ MulAction.stabilizer H b := fun v hv =>
    ⟨MulAction.mem_stabilizer_iff.mpr (hfix v hv).1, MulAction.mem_stabilizer_iff.mpr (hfix v hv).2⟩
  have hdvd : Nat.card V ∣ 378 := by
    rw [← hKc]
    exact Subgroup.card_dvd_of_le hVK
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hVp
  have hn1 : n ≤ 1 := by
    by_contra hc
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    rw [← hn] at h4
    have h5 := h4.trans hdvd
    norm_num at h5
  rcases (by omega : n = 0 ∨ n = 1) with h0 | h1
  · exfalso
    apply hV1
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, h0, pow_zero]
  · rw [hn, h1, pow_one]

theorem card_pairStab_378 (hH : Nat.card H = 99283968)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    (hΩ : Nat.card Ω = 513) {a b : Ω} (hab : a ≠ b) :
    Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) = 378 := by
  have hK := card_pairStabilizer h2 hab
  rw [hΩ, hH] at hK
  have h1 : Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) * 262656
      = 378 * 262656 := by
    calc Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) * 262656
        = Nat.card (MulAction.stabilizer H a ⊓ MulAction.stabilizer H b : Subgroup H) *
            (513 - 1) * 513 := by norm_num [mul_assoc]
      _ = 99283968 := hK
      _ = 378 * 262656 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

theorem involution_conj_sigma (hH : Nat.card H = 99283968)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    (hΩ : Nat.card Ω = 513) {ω0 ω1 : Ω} (hne : ω0 ≠ ω1) {σ : H} (hσ2 : σ ^ 2 = 1)
    (hσ1 : σ ≠ 1) (hσ0 : σ • ω0 = ω0) (hσ1' : σ • ω1 = ω1)
    {t : H} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) {a b : Ω} (hab : a ≠ b)
    (hta : t • a = a) (htb : t • b = b) :
    ∃ k : H, k * σ * k⁻¹ = t := by
  obtain ⟨g, hga, hgb⟩ := h2 a b ω0 ω1 hab hne
  have ht0 : (g * t * g⁻¹) • ω0 = ω0 := by
    rw [← hga, ← mul_smul, show g * t * g⁻¹ * g = g * t by group, mul_smul, hta]
  have ht0' : (g * t * g⁻¹) • ω1 = ω1 := by
    rw [← hgb, ← mul_smul, show g * t * g⁻¹ * g = g * t by group, mul_smul, htb]
  have hKc := card_pairStab_378 hH h2 hΩ hne
  have hσK : σ ∈ (MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hσ0, MulAction.mem_stabilizer_iff.mpr hσ1'⟩
  have htK : g * t * g⁻¹ ∈ (MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H) :=
    ⟨MulAction.mem_stabilizer_iff.mpr ht0, MulAction.mem_stabilizer_iff.mpr ht0'⟩
  have hs2K : (⟨σ, hσK⟩ : ↥(MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H))
      ^ 2 = 1 := Subtype.ext (by simpa using hσ2)
  have hs1K : (⟨σ, hσK⟩ : ↥(MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H))
      ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  have hu2' : (g * t * g⁻¹) ^ 2 = 1 := by
    have h := ht2
    rw [pow_two] at h ⊢
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hu1' : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hu2K : (⟨g * t * g⁻¹, htK⟩ : ↥(MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H))
      ^ 2 = 1 := Subtype.ext (by simpa using hu2')
  have hu1K : (⟨g * t * g⁻¹, htK⟩ : ↥(MulAction.stabilizer H ω0 ⊓ MulAction.stabilizer H ω1 : Subgroup H))
      ≠ 1 := fun h => hu1' (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := conj_of_involution_378 hKc hs2K hs1K hu2K hu1K
  have hc' : (c : H) * σ * (c : H)⁻¹ = g * t * g⁻¹ := congrArg Subtype.val hc
  refine ⟨g⁻¹ * (c : H), ?_⟩
  calc g⁻¹ * (c : H) * σ * (g⁻¹ * (c : H))⁻¹ = g⁻¹ * ((c : H) * σ * (c : H)⁻¹) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hc']
    _ = t := by group

theorem no_E27_normalizes_two
    (hΩ : Nat.card Ω = 513) (hH : Nat.card H = 99283968)
    (h2 : ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ g : H, g • a = a' ∧ g • b = b')
    (hA : ∀ (E : Subgroup H), IsElemAbelian 3 E → Nat.card E = 27 → ∀ ω : Ω, ¬ ∀ e ∈ E, e • ω = ω)
    {ω0 ω1 : Ω} (hne : ω0 ≠ ω1) {σ : H} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσ0 : σ • ω0 = ω0) (hσ1' : σ • ω1 = ω1)
    (hC : Nat.card (Subgroup.centralizer ({σ} : Set H)) = 3024)
    {y : H} (hyC : y ∈ Subgroup.centralizer ({σ} : Set H)) (hy : orderOf y = 9)
    {V E : Subgroup H} (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEV : E ≤ Subgroup.normalizer (V : Set H)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := hV.isPGroup
  obtain ⟨a, b, hab, hfix⟩ := exists_two_fixed hΩ hA hVp hEV hE hE27
  have hV2 : Nat.card V = 2 := card_eq_two_of_fix2 hH h2 hΩ hVp hV1 hab hfix
  obtain ⟨t, htV, ht1⟩ : ∃ t ∈ V, t ≠ 1 := by
    by_contra hcon
    apply hV1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have ht2 : t ^ 2 = 1 := hV.2 t htV
  have hVt : Subgroup.zpowers t = V := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htV)
    exact le_of_eq (by rw [hV2, Nat.card_zpowers, orderOf_eq_prime ht2 ht1])
  have hEcomm : ∀ e ∈ E, e * t = t * e := by
    intro e he
    have hconj : e * t * e⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hEV he) t).mp htV
    have hne1 : e * t * e⁻¹ ≠ 1 := by
      intro h
      apply ht1
      calc t = e⁻¹ * (e * t * e⁻¹) * e := by group
        _ = 1 := by rw [h]; group
    have heq : e * t * e⁻¹ = t :=
      eq_of_mem_zpowers_involution ht2 ht1 (by rw [hVt]; exact hconj) hne1
    calc e * t = (e * t * e⁻¹) * e := by group
      _ = t * e := by rw [heq]
  obtain ⟨k, hk⟩ := involution_conj_sigma hH h2 hΩ hne hσ2 hσ1 hσ0 hσ1' ht2 ht1 hab
    (hfix t htV).1 (hfix t htV).2
  have hσk : σ = k⁻¹ * t * k := by
    rw [← hk]
    group
  have hE' : IsElemAbelian 3 (E.map (MulAut.conj k⁻¹).toMonoidHom) := hE.map _
  have hE'27 : Nat.card (E.map (MulAut.conj k⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hE27]
  have hE'C : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ Subgroup.centralizer ({σ} : Set H) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have hcj : (MulAut.conj k⁻¹).toMonoidHom e = k⁻¹ * e * k := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    have hcomm : t * e = e * t := (hEcomm e he).symm
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs, hσk, hcj]
    calc k⁻¹ * t * k * (k⁻¹ * e * k) = k⁻¹ * (t * e) * k := by group
      _ = k⁻¹ * (e * t) * k := by rw [hcomm]
      _ = k⁻¹ * e * k * (k⁻¹ * t * k) := by group
  exact no_E27_of_card_3024 hC hyC hy hE' hE'27 hE'C

end CFSG.RankThree.PartTwo.Sec4.Item434U38
