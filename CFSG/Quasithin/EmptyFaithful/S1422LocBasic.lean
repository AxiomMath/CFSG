module

public import CFSG.Quasithin.EmptyFaithful.S1422Recog

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Cards

variable {G : Type*} [Group G] [Finite G]

theorem card_eq_card_mul_relIndex {H K : Subgroup G} (h : H ≤ K) :
    Nat.card K = Nat.card H * H.relIndex K := by
  have h1 := Subgroup.card_mul_index H
  have h2 := Subgroup.card_mul_index K
  have h3 := Subgroup.relIndex_mul_index h
  have hK : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK)
  rw [h2, mul_assoc, h3, h1]

omit [Finite G] in
theorem odd_relIndex_of_le {T H K : Subgroup G} (hTH : T ≤ H) (hHK : H ≤ K)
    (hTK : ¬ 2 ∣ (T.subgroupOf K).index) : Odd (H.relIndex K) := by
  have h := Subgroup.relIndex_mul_relIndex T H K hTH hHK
  have hdvd : H.relIndex K ∣ (T.subgroupOf K).index := Dvd.intro_left _ h
  rcases Nat.even_or_odd (H.relIndex K) with he | ho
  · exact absurd ((even_iff_two_dvd.mp he).trans hdvd) hTK
  · exact ho

omit [Finite G] in
theorem card_eq_card_oTwoQuot_mul (H : Subgroup G) :
    Nat.card H = Nat.card (oTwoQuot ↥H) * Nat.card (pCoreOf 2 H) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  have h2 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 ↥H) :=
    Nat.card_congr
      ((CFSG.Open.pCore 2 ↥H).equivMapOfInjective H.subtype H.subtype_injective).symm.toEquiv
  rw [h2]
  exact h1

end Cards

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem T_le_Mc (S : Setting1422 T M Y H) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  S.T_le_H.trans S.H_le_centralizer

omit [Finite G] in
theorem le_normalizer_of_forall_conj_mem {L K : Subgroup G}
    (h : ∀ g ∈ L, ∀ x ∈ K, g * x * g⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (L.inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem omegaOneCenter_comm {a b : G} (ha : a ∈ quasithinOmegaOneCenter T)
    (hb : b ∈ quasithinOmegaOneCenter T) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T ha).2 b
    (quasithinOmegaOneCenter_le_center T hb).1).symm

omit [Finite G] in
theorem mem_Mc_comm {z c : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hc : c ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : c * z = z * c :=
  (Subgroup.mem_centralizer_iff.mp hc z hz).symm

omit [Finite G] in
theorem mem_Mc_of_mem {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    z ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hw => (omegaOneCenter_comm hz hw).symm

omit [Finite G] in
theorem mem_pCoreOf_Mc {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) :
    z ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  have hle : Subgroup.zpowers z ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.zpowers_le.mpr (mem_Mc_of_mem hz)
  have hnorm : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg c hc => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hgz : g * z * g⁻¹ = z := by
      have := mem_Mc_comm hz hg
      rw [this]
      group
    rw [← conj_zpow, hgz]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hz2 hz1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm hp
    (Subgroup.mem_zpowers z)

theorem charTwo_Mc (S : Setting1422 T M Y H) :
    CharTwo (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  obtain ⟨z, hz, hz1, hz2, -⟩ := S.exists_z
  have hne : pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≠ ⊥ := by
    intro h
    have := mem_pCoreOf_Mc hz hz1 hz2
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  exact charTwo_of_le S.hyp.qtke.2.1 P (hP.le.trans S.T_le_Mc) le_rfl
    ⟨hP.le.trans S.T_le_Mc, hne⟩

theorem pCoreOf_Mc_le (S : Setting1422 T M Y H) :
    pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ pCoreOf 2 H := by
  obtain ⟨P, hP⟩ := S.exists_sylow
  have h := not_dvd_index_subgroupOf_of_sylow P (hP.le.trans S.T_le_Mc)
  rw [hP] at h
  exact pCoreOf_le_pCoreOf_of_sylow S.H_le_centralizer S.hyp.sylow.1 S.T_le_H h

@[expose] def centralizerModZ (T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
    ∀ q ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
      x * q * x⁻¹ * q⁻¹ ∈ quasithinOmegaOneCenter T}
  one_mem' := ⟨Subgroup.one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun q hq => ?_⟩
    have h1 := hyc q hq
    have h2 := hxc q hq
    have h3 : x * (y * q * y⁻¹ * q⁻¹) * x⁻¹ = y * q * y⁻¹ * q⁻¹ := by
      have := mem_Mc_comm h1 hx
      calc x * (y * q * y⁻¹ * q⁻¹) * x⁻¹ = (x * (y * q * y⁻¹ * q⁻¹)) * x⁻¹ := rfl
        _ = ((y * q * y⁻¹ * q⁻¹) * x) * x⁻¹ := by rw [this]
        _ = y * q * y⁻¹ * q⁻¹ := by group
    have h4 : x * y * q * (x * y)⁻¹ * q⁻¹ =
        (x * (y * q * y⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
    rw [h4, h3]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    rintro x ⟨hx, hxc⟩
    refine ⟨Subgroup.inv_mem _ hx, fun q hq => ?_⟩
    have h1 := hxc q hq
    have h2 : x⁻¹ * q * (x⁻¹)⁻¹ * q⁻¹ = x⁻¹ * (x * q * x⁻¹ * q⁻¹)⁻¹ * x := by group
    rw [h2]
    have h3 : (x * q * x⁻¹ * q⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T := Subgroup.inv_mem _ h1
    have h5 := mem_Mc_comm h3 (Subgroup.inv_mem _ hx)
    have h4 : x⁻¹ * (x * q * x⁻¹ * q⁻¹)⁻¹ * x = (x * q * x⁻¹ * q⁻¹)⁻¹ := by
      calc x⁻¹ * (x * q * x⁻¹ * q⁻¹)⁻¹ * x = ((x * q * x⁻¹ * q⁻¹)⁻¹ * x⁻¹) * x := by rw [h5]
        _ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by group
    rw [h4]
    exact h3

omit [Finite G] in
theorem centralizerModZ_le_Mc (T : Subgroup G) :
    centralizerModZ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun _ h => h.1

omit [Finite G] in
theorem Mc_le_normalizer_centralizerModZ (T : Subgroup G) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (centralizerModZ T : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun g hg x hx => ?_
  obtain ⟨hxM, hxc⟩ := hx
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxM) (Subgroup.inv_mem _ hg), fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (Subgroup.inv_mem _ hg)) q).mp hq
    simpa using this
  have h1 := hxc _ hq'
  have h2 : g * x * g⁻¹ * q * (g * x * g⁻¹)⁻¹ * q⁻¹ =
      g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
  rw [h2]
  have h3 : g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ =
      x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹ := by
    rw [mem_Mc_comm h1 hg]
    group
  rw [h3]
  exact h1

theorem exists_pow_two_pow_eq_one_of_mem_centralizerModZ (S : Setting1422 T M Y H) {y : G}
    (hy : y ∈ centralizerModZ T) : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 2 (by norm_num)
  have hdvd : 2 ^ a ∣ orderOf y := ⟨m, hord⟩
  have hs : orderOf (y ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hord]
    simp
  have hy' : y ^ 2 ^ a ∈ centralizerModZ T := Subgroup.pow_mem _ hy _
  obtain ⟨hy'M, hy'c⟩ := hy'
  have hodd : Odd m := Nat.odd_iff.mpr (by omega)
  have hym : (y ^ 2 ^ a) ^ m = 1 := by rw [← hs]; exact pow_orderOf_eq_one _
  have hcent : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
      (y ^ 2 ^ a) * q = q * (y ^ 2 ^ a) := by
    intro q hq
    set y' := y ^ 2 ^ a with hy'def
    set w := y' * q * y'⁻¹ * q⁻¹ with hwdef
    have hw : w ∈ quasithinOmegaOneCenter T := hy'c q hq
    have hqM : q ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    have hconj : y' * q * y'⁻¹ = w * q := by rw [hwdef]; group
    have hpow : ∀ k : ℕ, y' ^ k * q * (y' ^ k)⁻¹ = w ^ k * q := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hcw : y' * w ^ k = w ^ k * y' := by
          have := mem_Mc_comm (Subgroup.pow_mem _ hw k) hy'M
          exact this
        calc y' ^ (k + 1) * q * (y' ^ (k + 1))⁻¹
            = y' * (y' ^ k * q * (y' ^ k)⁻¹) * y'⁻¹ := by group
          _ = y' * (w ^ k * q) * y'⁻¹ := by rw [ih]
          _ = (y' * w ^ k * y'⁻¹) * (y' * q * y'⁻¹) := by group
          _ = w ^ k * (w * q) := by
            rw [hconj, hcw]
            group
          _ = w ^ (k + 1) * q := by group
    have h1 := hpow m
    rw [hym] at h1
    have h2 : w ^ m = 1 := by
      have : q = w ^ m * q := by simpa using h1
      exact mul_right_cancel (b := q) (this.symm.trans (one_mul q).symm)
    have hw2 : w ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hw
    obtain ⟨j, hj⟩ := hodd
    have hw1 : w = 1 := by
      have : w ^ m = w := by
        rw [hj, pow_succ, pow_mul, hw2, one_pow, one_mul]
      rw [← this]
      exact h2
    have hy'q : y' * q * y'⁻¹ = q := by rw [hconj, hw1, one_mul]
    calc y' * q = (y' * q * y'⁻¹) * y' := by group
      _ = q * y' := by rw [hy'q]
  have hmem : y ^ 2 ^ a ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    (charTwo_Mc S) ⟨hy'M, Subgroup.mem_centralizer_iff.mpr fun q hq => (hcent q hq).symm⟩
  have hQ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) 2
    (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
  obtain ⟨k, hk⟩ := hQ2 ⟨_, hmem⟩
  have hk' : (y ^ 2 ^ a) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hmk : m ∣ 2 ^ k := hs ▸ orderOf_dvd_of_pow_eq_one hk'
  have hm1 : m = 1 := by
    have hcop : Nat.Coprime m (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)))
    exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl m) hmk
  refine ⟨a, ?_⟩
  rw [hm1] at hs
  exact orderOf_eq_one_iff.mp hs

theorem mem_pCoreOf_Mc_of_comm_mem (S : Setting1422 T M Y H) {x : G}
    (hx : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hxc : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
      x * q * x⁻¹ * q⁻¹ ∈ quasithinOmegaOneCenter T) :
    x ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  have hp : IsPGroup 2 (centralizerModZ T) := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem_centralizerModZ S c.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizerModZ_le_Mc T)
    (Mc_le_normalizer_centralizerModZ T) hp ⟨hx, hxc⟩

theorem pCoreOf_H_le_Mc (S : Setting1422 T M Y H)
    (hcomm : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T) :
    pCoreOf 2 H ≤ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  intro x hx
  exact mem_pCoreOf_Mc_of_comm_mem S (S.H_le_centralizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H hx))
    fun q hq => hcomm x hx q (S.pCoreOf_Mc_le hq)

theorem pCoreOf_H_eq_Mc (S : Setting1422 T M Y H)
    (hcomm : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T) :
    pCoreOf 2 H = pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
  le_antisymm (S.pCoreOf_H_le_Mc hcomm) S.pCoreOf_Mc_le

theorem Mc_le_normalizer_pCoreOf_H (S : Setting1422 T M Y H)
    (hcomm : ∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  rw [S.pCoreOf_H_eq_Mc hcomm]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

end Setting1422

end CFSG.Quasithin
