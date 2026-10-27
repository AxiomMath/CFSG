module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalVertex
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalThree
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5TransvG

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_conj_mem_of_sylow_p {p : ℕ} [hp : Fact p.Prime] {K T : Subgroup G} (hTK : T ≤ K)
    (hT : IsPGroup p T) (hidx : ¬ p ∣ T.relIndex K) {y : G} (hy : y ∈ K) (hyp : y ^ p = 1) :
    ∃ g ∈ K, (g : G)⁻¹ * y * g ∈ T := by
  have hT' : IsPGroup p (T.subgroupOf K) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  set P := hT'.toSylow hidx
  have hzp : IsPGroup p (Subgroup.zpowers (⟨y, hy⟩ : K)) := by
    have h1 : orderOf (⟨y, hy⟩ : K) ∣ p ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hyp))
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  have hy' : (⟨y, hy⟩ : K) ∈ ((g • P : Sylow p K) : Subgroup K) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  refine ⟨g, g.2, ?_⟩
  have hP : ((P : Sylow p K) : Subgroup K) = T.subgroupOf K := IsPGroup.toSylow_coe _ _
  rw [hP, Subgroup.mem_subgroupOf] at hy'
  have e : (((MulAut.conj g)⁻¹ • (⟨y, hy⟩ : K) : K) : G) = (g : G)⁻¹ * y * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rwa [e] at hy'

theorem exists_conj_mem_X (F : Frame L1 L2 S D X) {y : G} (hy : y ∈ P1 L1 L2 S) (hy5 : y ^ 5 = 1) :
    ∃ g ∈ P1 L1 L2 S, g⁻¹ * y * g ∈ X := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXP : X ≤ P1 L1 L2 S := F.X_le.trans le_sup_left
  have hXp : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by rw [F.X_card]; simp)
  obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup.exists_card_eq
  have hP : Nat.card (P1 L1 L2 S) = 15 * 2 ^ k := by
    rw [card_P1 F, hk]
  have h2 := Subgroup.relIndex_mul_card (H := X) (K := P1 L1 L2 S)
  rw [inf_eq_left.mpr hXP, F.X_card, hP] at h2
  have hrel : X.relIndex (P1 L1 L2 S) = 3 * 2 ^ k := by omega
  have hidx : ¬ 5 ∣ X.relIndex (P1 L1 L2 S) := by
    rw [hrel]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
      omega
  exact exists_conj_mem_of_sylow_p hXP hXp hidx hy hy5

theorem conj_mem_X_Q1 (F : Frame L1 L2 S D X) {p x : G} (hp : p ∈ P1 L1 L2 S) (hx : x ∈ X) :
    ∃ y ∈ X, ∃ o ∈ Q1 L1 L2 S, p * x * p⁻¹ = y * o := by
  obtain ⟨x', hx', b, hb, rfl⟩ := F.exists_mul p hp
  obtain ⟨y, hy, o, ho, hyo⟩ := F.conj_mem_X_mul hb hx
  have hN := P1_le_normalizer_Q1 L1 L2 S
  have hx'P : x' ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx'
  refine ⟨x' * y * x'⁻¹, X.mul_mem (X.mul_mem hx' hy) (X.inv_mem hx'),
    x' * o * x'⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hN hx'P) o).mp (F.pCore_L1_le_Q1 ho)
  · have : x' * b * x * (x' * b)⁻¹ = x' * (b * x * b⁻¹) * x'⁻¹ := by group
    rw [this, hyo]
    group

theorem inv_of_involution_P1 (F : Frame L1 L2 S D X) {a : G} (ha : a ∈ P1 L1 L2 S)
    (ha2 : a * a ∈ Q1 L1 L2 S) (haQ : a ∉ Q1 L1 L2 S) {x : G} (hx : x ∈ X) :
    ∃ q ∈ Q1 L1 L2 S, a * x * a⁻¹ = x⁻¹ * q := by
  have hN := P1_le_normalizer_Q1 L1 L2 S
  have hconj : ∀ p ∈ P1 L1 L2 S, ∀ q ∈ Q1 L1 L2 S, p * q * p⁻¹ ∈ Q1 L1 L2 S := fun p hp q hq =>
    (Subgroup.mem_normalizer_iff.mp (hN hp) q).mp hq
  have hconj' : ∀ p ∈ P1 L1 L2 S, ∀ q ∈ Q1 L1 L2 S, p⁻¹ * q * p ∈ Q1 L1 L2 S := fun p hp q hq => by
    simpa using hconj p⁻¹ ((P1 L1 L2 S).inv_mem hp) q hq
  obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup ⟨a * a, F.Q1_le_S ha2⟩
  have hk' : (a * a) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have ha_pow : a ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hk'
  have hAp : IsPGroup 2 (Subgroup.zpowers a) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : orderOf a ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one ha_pow
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨c, hcP, hc⟩ := exists_conj_le_sylow_two F.sylow_P1
    ((Subgroup.zpowers_le).mpr ha) hAp
  have hs : c * a * c⁻¹ ∈ S := by
    refine hc ?_
    rw [mem_conjSub]
    have : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    rw [this]
    exact Subgroup.mem_zpowers a
  have hs2 : (c * a * c⁻¹) * (c * a * c⁻¹) ∈ Q1 L1 L2 S := by
    have := hconj c hcP _ ha2
    have e : c * (a * a) * c⁻¹ = (c * a * c⁻¹) * (c * a * c⁻¹) := by group
    rwa [e] at this
  have hsQ : c * a * c⁻¹ ∉ Q1 L1 L2 S := by
    intro h
    apply haQ
    have := hconj' c hcP _ h
    have e : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    rwa [e] at this
  obtain ⟨y, hy, o, ho, hyo⟩ := conj_mem_X_Q1 F hcP hx
  obtain ⟨q, hq, hsy⟩ := F.inv_of_involution hs hs2 hsQ hy
  set s := c * a * c⁻¹ with hs_def
  have hxP : x ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx
  have hsP : s ∈ P1 L1 L2 S := F.mem_P1_of_mem_S hs
  have hy' : y = c * x * c⁻¹ * o⁻¹ := eq_mul_inv_of_mul_eq hyo.symm
  have hyinv : y⁻¹ = o * (c * x⁻¹ * c⁻¹) := by rw [hy']; group
  have e1 : a * x * a⁻¹ = c⁻¹ * (s * y * s⁻¹) * (s * o * s⁻¹) * c := by
    calc a * x * a⁻¹ = c⁻¹ * s * (c * x * c⁻¹) * s⁻¹ * c := by rw [hs_def]; group
      _ = c⁻¹ * s * (y * o) * s⁻¹ * c := by rw [hyo]
      _ = c⁻¹ * (s * y * s⁻¹) * (s * o * s⁻¹) * c := by group
  have hso : s * o * s⁻¹ ∈ Q1 L1 L2 S := hconj s hsP o ho
  refine ⟨x * (c⁻¹ * o * c) * x⁻¹ * (c⁻¹ * (q * (s * o * s⁻¹)) * c), ?_, ?_⟩
  · refine (Q1 L1 L2 S).mul_mem (hconj x hxP _ (hconj' c hcP o ho)) (hconj' c hcP _ ?_)
    exact (Q1 L1 L2 S).mul_mem hq hso
  · rw [e1, hsy, hyinv]
    group

omit [Finite G] in
theorem mem_conjSub_of_mem' {h n : G} {V : Subgroup G} (hn : n ∈ V) : h * n * h⁻¹ ∈ conjSub h V := by
  rw [mem_conjSub]
  have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
  rwa [e]

omit [Finite G] in
theorem mem_normalizer_conjSub {h n : G} {V : Subgroup G} (hn : n ∈ Subgroup.normalizer (V : Set G)) :
    h * n * h⁻¹ ∈ Subgroup.normalizer ((conjSub h V : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjSub, mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp hn (h⁻¹ * y * h)
  have e : h⁻¹ * (h * n * h⁻¹ * y * (h * n * h⁻¹)⁻¹) * h = n * (h⁻¹ * y * h) * n⁻¹ := by group
  rw [e]
  exact this

theorem exists_conj_stab_false_X (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {x : G} (hx : x ∈ stab δ) (hx5 : x ^ 5 = 1) :
    ∃ h : G, conjSub h (stab δ) = P1 L1 L2 S ∧ conjSub h (Qv δ) = Q1 L1 L2 S ∧ h * x * h⁻¹ ∈ X := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hδ
  have hxP : g * x * g⁻¹ ∈ P1 L1 L2 S := by
    rw [← hg1]; exact mem_conjSub_of_mem' hx
  have hx5' : (g * x * g⁻¹) ^ 5 = 1 := by
    have := conj_pow (a := g) (b := x) (i := 5)
    rw [this, hx5]; group
  obtain ⟨p, hp, hpx⟩ := exists_conj_mem_X F hxP hx5'
  have hpn : p⁻¹ ∈ Subgroup.normalizer (P1 L1 L2 S : Set G) :=
    Subgroup.le_normalizer ((P1 L1 L2 S).inv_mem hp)
  have hpQ : p⁻¹ ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    P1_le_normalizer_Q1 L1 L2 S ((P1 L1 L2 S).inv_mem hp)
  refine ⟨p⁻¹ * g, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg1]; exact conjSub_eq_of_mem_normalizer hpn
  · rw [conjSub_mul, hg2]; exact conjSub_eq_of_mem_normalizer hpQ
  · have : p⁻¹ * g * x * (p⁻¹ * g)⁻¹ = p⁻¹ * (g * x * g⁻¹) * p := by group
    rw [this]
    simpa using hpx

theorem five_centralizes_of_transvection (F : Frame L1 L2 S D X)
    {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hN : stab δ ≤ Subgroup.normalizer (V : Set G))
    (hQV : Qv δ ≤ Subgroup.centralizer (V : Set G)) {a : G} (ha : a ∈ stab δ) (haQ : a ∉ Qv δ)
    (ha2 : a ^ 2 ∈ Qv δ) (hidx : (V ⊓ Subgroup.centralizer {a}).relIndex V ≤ 2)
    {x : G} (hx : x ∈ stab δ) (hx5 : x ^ 5 = 1) : x ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨h, hh1, hh2, hhx⟩ := exists_conj_stab_false_X F hδ hx hx5
  set V' := conjSub h V with hV'
  set a' := h * a * h⁻¹ with ha'
  set x' := h * x * h⁻¹ with hx'
  have ha'P : a' ∈ P1 L1 L2 S := by rw [← hh1]; exact mem_conjSub_of_mem' ha
  have hsq : ∀ e ∈ V, e ^ 2 = 1 := hV.2
  have hV2 : ∀ e ∈ V', e * e = 1 := by
    intro e he
    rw [hV', mem_conjSub] at he
    have h1 := hsq _ he
    have hcp := conj_pow (a := h⁻¹) (b := e) (i := 2)
    simp only [inv_inv] at hcp
    have h2 : e ^ 2 = h * ((h⁻¹ * e * h) ^ 2) * h⁻¹ := by rw [hcp]; group
    rw [← pow_two, h2, h1]; group
  have hxN : x' ∈ Subgroup.normalizer (V' : Set G) := mem_normalizer_conjSub (hN hx)
  have haN : a' ∈ Subgroup.normalizer (V' : Set G) := mem_normalizer_conjSub (hN ha)
  have hQc : Q1 L1 L2 S ≤ Subgroup.centralizer (V' : Set G) := by
    rw [hV', conjSub_centralizer, ← hh2]
    exact conjSub_mono h hQV
  have ha'Q : a' ∉ Q1 L1 L2 S := by
    intro hm
    rw [← hh2, ha', mem_conjSub] at hm
    apply haQ
    have e : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rwa [e] at hm
  have ha'2 : a' * a' ∈ Q1 L1 L2 S := by
    rw [← hh2]
    have e : a' * a' = h * a ^ 2 * h⁻¹ := by rw [ha', pow_two]; group
    rw [e]
    exact mem_conjSub_of_mem' ha2
  obtain ⟨q, hq, hinv⟩ := inv_of_involution_P1 F ha'P ha'2 ha'Q hhx
  have hx5' : x' ^ 5 = 1 := by
    have := conj_pow (a := h) (b := x) (i := 5)
    rw [hx', this, hx5]; group
  have hidx' : (V' ⊓ Subgroup.centralizer {a'}).relIndex V' ≤ 2 := by
    have hc : conjSub h (Subgroup.centralizer {a}) = Subgroup.centralizer {a'} := by
      ext y
      rw [mem_conjSub, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
        ha']
      constructor
      · intro hy
        calc y * (h * a * h⁻¹) = h * ((h⁻¹ * y * h) * a) * h⁻¹ := by group
          _ = h * (a * (h⁻¹ * y * h)) * h⁻¹ := by rw [hy]
          _ = h * a * h⁻¹ * y := by group
      · intro hy
        calc (h⁻¹ * y * h) * a = h⁻¹ * (y * (h * a * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * a * h⁻¹) * y) * h := by rw [hy]
          _ = a * (h⁻¹ * y * h) := by group
    rw [← hc, hV', ← conjSub_inf, relIndex_conjSub]
    exact hidx
  have hz2 : a' * a' ∈ Subgroup.centralizer (V' : Set G) := hQc ha'2
  have hqc : q ∈ Subgroup.centralizer (V' : Set G) := hQc hq
  have key := FA5.centralizes_of_inverted_transvection hV2 hxN haN hqc hx5' hz2 hinv hidx'
  rw [hV', conjSub_centralizer, mem_conjSub] at key
  have e : h⁻¹ * x' * h = x := by rw [hx']; group
  rwa [e] at key

end CFSG.Quasithin.Kleidman.F204
