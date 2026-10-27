module

public import CFSG.Quasithin.Background.B6Sections
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.C2Nine

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

section Basic

theorem mem_pCore_iff_mem_pCoreOf {K : Subgroup G} (y : ↥K) :
    y ∈ CFSG.pCore 2 ↥K ↔ (y : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff y).symm

private theorem mk_commute_iff {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (a b : H) :
    (QuotientGroup.mk a : H ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a ↔
      a * b * a⁻¹ * b⁻¹ ∈ N := by
  have e : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : H ⧸ N) =
      ⁅(QuotientGroup.mk a : H ⧸ N), (QuotientGroup.mk b : H ⧸ N)⁆ := by
    simp [commutatorElement_def]
  rw [← QuotientGroup.eq_one_iff, e]
  exact commutatorElement_eq_one_iff_mul_comm.symm

theorem mem_oTwoZIn_iff {K : Subgroup G} {x : G} :
    x ∈ oTwoZIn K ↔ x ∈ K ∧ ∀ w ∈ K, x * w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
  unfold oTwoZIn preimageModTwoCore
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun w hw => ?_⟩
    have hy' := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hy)
      (QuotientGroup.mk (⟨w, hw⟩ : ↥K))
    have := (mk_commute_iff (CFSG.pCore 2 ↥K) y ⟨w, hw⟩).mp hy'.symm
    exact (mem_pCore_iff_mem_pCoreOf _).mp this
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    exact ((mk_commute_iff (CFSG.pCore 2 ↥K) ⟨x, hx⟩ w).mpr
      ((mem_pCore_iff_mem_pCoreOf _).mpr (hc w w.2))).symm

theorem oTwoZIn_le (K : Subgroup G) : oTwoZIn K ≤ K := fun _ hx => (mem_oTwoZIn_iff.mp hx).1

theorem pCoreOf_le_oTwoZIn (K : Subgroup G) : pCoreOf 2 K ≤ oTwoZIn K := by
  intro x hx
  have hxK : x ∈ K := pCoreOf_le 2 K hx
  refine mem_oTwoZIn_iff.mpr ⟨hxK, fun w hw => ?_⟩
  have h1 : w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hw) _).mp
      ((pCoreOf 2 K).inv_mem hx)
  have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 K).mul_mem hx h1

theorem normalizer_le_normalizer_oTwoZIn (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoZIn K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oTwoZIn K,
      g * x * g⁻¹ ∈ oTwoZIn K := by
    intro g hg x hx
    obtain ⟨hxK, hxc⟩ := mem_oTwoZIn_iff.mp hx
    have hgc : g ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 K hg
    refine mem_oTwoZIn_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxK, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg)
        w).mp hw
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hgc _).mp (hxc _ hw')
    have e : g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (K : Set G)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Basic

section Quasisimple

theorem mk_mem_center_of_mem_oTwoZIn {K : Subgroup G} {y : ↥K} (hy : (y : G) ∈ oTwoZIn K) :
    (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  unfold oTwoZIn preimageModTwoCore at hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  have : z = y := Subtype.ext hzy
  subst this
  exact Subgroup.mem_comap.mp hz

theorem mem_oTwoZIn_of_mk_mem_center {K : Subgroup G} {y : ↥K}
    (hy : (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :
    (y : G) ∈ oTwoZIn K := by
  unfold oTwoZIn preimageModTwoCore
  exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_comap.mpr hy, rfl⟩

private theorem eq_of_central_ratio {P : Type*} [Group P] (hP : commutator P = ⊤) (φ : P →* P)
    (h : ∀ x, φ x * x⁻¹ ∈ Subgroup.center P) (x : P) : φ x = x := by
  have hcomm : ∀ a b : P, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨z₁, hz₁, ha⟩ : ∃ z₁ ∈ Subgroup.center P, φ a = z₁ * a :=
      ⟨φ a * a⁻¹, h a, by group⟩
    obtain ⟨z₂, hz₂, hb⟩ : ∃ z₂ ∈ Subgroup.center P, φ b = z₂ * b :=
      ⟨φ b * b⁻¹, h b, by group⟩
    have k1 : ∀ g : P, z₁ * g * z₁⁻¹ = g := fun g => by
      rw [← Subgroup.mem_center_iff.1 hz₁ g]; group
    have k2 : ∀ g : P, z₂ * g * z₂⁻¹ = g := fun g => by
      rw [← Subgroup.mem_center_iff.1 hz₂ g]; group
    rw [map_commutatorElement, ha, hb]
    calc ⁅z₁ * a, z₂ * b⁆ = (z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹) * b⁻¹ * z₂⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a * z₂ * b * a⁻¹ * b⁻¹ * z₂⁻¹ := by rw [k1]
      _ = a * (z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹) := by group
      _ = a * (b * a⁻¹ * b⁻¹) := by rw [k2]
      _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group
  have hle : commutator P ≤ φ.eqLocus (MonoidHom.id P) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact hcomm g₁ g₂
  exact hle (by rw [hP]; trivial)

variable [Finite G]

theorem normal_le_oTwoZIn_or_eq {K N : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hNK : N ≤ K)
    (hn : K ≤ Subgroup.normalizer (N : Set G)) : N ≤ oTwoZIn K ∨ N = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hq' : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  have hmapn : ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with h | h
  · left
    intro x hx
    have hxK : x ∈ K := hNK hx
    exact mem_oTwoZIn_of_mk_mem_center (y := ⟨x, hxK⟩)
      (h (Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hx, rfl⟩))
  · right
    refine C2Nine.eq_of_perfect_of_pow_mem hperf hNK hNn fun k hk => ?_
    have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := h ▸ Subgroup.mem_top _
    obtain ⟨n, hnN, hnk⟩ := Subgroup.mem_map.mp hk'
    have hq2 : n⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hnk
    have hq3 : (n : G)⁻¹ * k ∈ pCoreOf 2 K := (mem_pCore_iff_mem_pCoreOf _).mp hq2
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 K ⟨_, hq3⟩
    have ha' : ((n : G)⁻¹ * k) ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have hnN' : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hnN
    obtain ⟨n', hn'N, hpow⟩ := A4.exists_pow_mul_eq hnN'
      (hn (K.mul_mem (K.inv_mem n.2) hk)) (2 ^ a)
    refine ⟨a, ?_⟩
    have e : k = (n : G) * ((n : G)⁻¹ * k) := by group
    rw [e, hpow, ha', mul_one]
    exact hn'N

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_mem_oTwoZIn {K : Subgroup G} {c : G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hc : c ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ oTwoZIn K) :
    ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  let ψ : ↥K ≃* ↥K := K.normalizerMonoidHom ⟨c, hc⟩
  have hψ : ∀ y : ↥K, ((ψ y : ↥K) : G) = c * y * c⁻¹ := fun y =>
    K.normalizerMonoidHom_apply_apply_coe ⟨c, hc⟩ y
  have hψc : CFSG.pCore 2 ↥K ≤ (CFSG.pCore 2 ↥K).comap ψ.toMonoidHom :=
    Subgroup.characteristic_iff_le_comap.1 inferInstance ψ
  let ψ' : (↥K ⧸ CFSG.pCore 2 ↥K) →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    QuotientGroup.map _ _ ψ.toMonoidHom hψc
  have hψ' : ∀ y : ↥K, ψ' (QuotientGroup.mk y) = QuotientGroup.mk (ψ y) := fun y =>
    QuotientGroup.map_mk _ _ _ _ y
  have key : ∀ p, ψ' p * p⁻¹ ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro p
    induction p using QuotientGroup.induction_on with
    | H y =>
      rw [hψ', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      apply mk_mem_center_of_mem_oTwoZIn
      have := h y y.2
      simpa [hψ y, mul_assoc] using this
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  have hid := eq_of_central_ratio Group.IsPerfect.commutator_eq_top ψ' key
  intro k hk
  have h1 := hid (QuotientGroup.mk ⟨k, hk⟩)
  rw [hψ'] at h1
  have h2 : (QuotientGroup.mk (ψ ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]
  have h3 := (mem_pCore_iff_mem_pCoreOf _).mp ((QuotientGroup.eq_one_iff _).mp h2)
  simpa [hψ, mul_assoc] using h3

theorem inf_le_oTwoZIn_of_not_le {X K D : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKX : K ≤ X)
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (hKD : ¬ K ≤ D) : D ⊓ K ≤ oTwoZIn K := by
  rcases normal_le_oTwoZIn_or_eq hperf hq inf_le_right (fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hXD (hKX hk), Subgroup.le_normalizer hk⟩)
    with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left : K ≤ D) hKD

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_inf_le {X K D : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hDX : D ≤ X)
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (hDK : D ⊓ K ≤ oTwoZIn K) :
    ∀ d ∈ D, ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  intro d hd
  refine commutator_mem_pCoreOf_of_mem_oTwoZIn hq (hXK (hDX hd)) fun k hk => hDK ⟨?_, ?_⟩
  · have h1 : k * d⁻¹ * k⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hXD (hKX hk)) _).mp (D.inv_mem hd)
    have e : d * k * d⁻¹ * k⁻¹ = d * (k * d⁻¹ * k⁻¹) := by group
    rw [e]
    exact D.mul_mem hd h1
  · have h1 : d * k * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXK (hDX hd)) k).mp hk
    exact K.mul_mem h1 (K.inv_mem hk)

end Quasisimple

section Centralizing

variable [Finite G]

omit [Finite G] in
private theorem mem_normalizer_of_conj {S : Subgroup G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (h' : ∀ x ∈ S, g⁻¹ * x * g ∈ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  have := h' _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {e : G} {k : ℕ} (he : e ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers e) := by
  have hd : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one he
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_odd_mul_two_elt (c : G) :
    ∃ a b : G, c = b * a ∧ a ∈ Subgroup.zpowers c ∧ b ∈ Subgroup.zpowers c ∧
      (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨s, t, ht, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ s) t := (Nat.coprime_two_left.2 ht).pow_left s
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨u, hu⟩ := (Nat.modEq_zero_iff_dvd).1 he0
  obtain ⟨w, hw⟩ := Nat.modEq_iff_dvd.1 he1
  refine ⟨c ^ ((1 : ℤ) - e), c ^ e, ?_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _,
    Subgroup.pow_mem _ (Subgroup.mem_zpowers c) e, ⟨s, ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_add]
    simp
  · have hexp : ((1 : ℤ) - e) * ((2 ^ s : ℕ) : ℤ) = (orderOf c : ℤ) * w := by
      have h : (1 : ℤ) - e = t * w := by exact_mod_cast hw
      rw [h, hm]
      push_cast
      ring
    rw [← zpow_natCast, ← zpow_mul, hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : (c ^ e) ^ t = 1 := by
      rw [← pow_mul, hu, show 2 ^ s * u * t = orderOf c * u by rw [hm]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat ht (orderOf_dvd_of_pow_eq_one h1)

theorem le_sup_of_isSylowTwoOf {E N T : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hT : IsSylowTwoOf T E)
    (hpow : ∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ N) : E ≤ N ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd1 : (N ⊔ T).relIndex E ∣ T.relIndex E :=
    Subgroup.relIndex_dvd_of_le_left E le_sup_right
  have hd2 : (N ⊔ T).relIndex E ∣ N.relIndex E :=
    Subgroup.relIndex_dvd_of_le_left E le_sup_left
  have hNn : (N.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have hp : IsPGroup 2 (↥E ⧸ N.subgroupOf E) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hNi : N.relIndex E = 2 ^ n := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hn
  rw [hNi] at hd2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have hj0 : j = 0 := by
    by_contra hne
    apply hT.2.2
    have h2 : 2 ∣ (N ⊔ T).relIndex E := hj ▸ dvd_pow_self 2 hne
    exact h2.trans hd1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

theorem isSylowTwoOf_pCoreOf_and_le_of_centralizes {X K E : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K)
    (hEX : E ≤ X) (hcent : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    IsSylowTwoOf (pCoreOf 2 E) E ∧ E ≤ (E ⊓ K) ⊔ pCoreOf 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ E)
    IsPGroup.of_bot
  have hEN : E ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer he, hXK (hEX he)⟩
  have hpowE : ∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ E ⊓ K := fun e he => by
    obtain ⟨k, hk⟩ := hpow e (hEX he)
    exact ⟨k, E.pow_mem he _, hk⟩
  have hET : E ≤ (E ⊓ K) ⊔ T := le_sup_of_isSylowTwoOf hEN hT hpowE
  have hPE : pCoreOf 2 K ⊓ E ≤ pCoreOf 2 E :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right (fun e he =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨normalizer_le_normalizer_pCoreOf 2 K (hXK (hEX he)), Subgroup.le_normalizer he⟩)
      ((pCoreOf_isPGroup 2 K).to_le inf_le_left)
  have hPT : pCoreOf 2 E ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hconjN : ∀ y ∈ E ⊓ K, ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro y hy t ht
    have htE : t ∈ E := hT.1 ht
    have h1 : t * y * t⁻¹ * y⁻¹ ∈ pCoreOf 2 K := hcent t htE y hy.2
    have h2 : y * t * y⁻¹ * t⁻¹ ∈ pCoreOf 2 K ⊓ E := by
      refine ⟨?_, E.mul_mem (E.mul_mem (E.mul_mem hy.1 htE) (E.inv_mem hy.1)) (E.inv_mem htE)⟩
      have e : y * t * y⁻¹ * t⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 K).inv_mem h1
    have e : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact T.mul_mem (hPT (hPE h2)) ht
  have hconjE : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := by
    intro e he t ht
    have he' : e ∈ ((((E ⊓ K) ⊔ T : Subgroup G)) : Set G) := hET he
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (E ⊓ K) T (hT.1.trans hEN)] at he'
    obtain ⟨y, hy, s, hs, rfl⟩ := he'
    have e : y * s * t * (y * s)⁻¹ = y * (s * t * s⁻¹) * y⁻¹ := by group
    rw [e]
    exact hconjN y hy _ (T.mul_mem (T.mul_mem hs ht) (T.inv_mem hs))
  have hEnT : E ≤ Subgroup.normalizer (T : Set G) := fun e he =>
    mem_normalizer_of_conj (hconjE e he) fun t ht => by
      simpa using hconjE e⁻¹ (E.inv_mem he) t ht
  have hTP : T ≤ pCoreOf 2 E := le_pCoreOf_of_le_normalizer 2 hT.1 hEnT hT.2.1
  have heq : pCoreOf 2 E = T := le_antisymm hPT hTP
  rw [heq]
  exact ⟨hT, hET⟩

theorem mem_pCoreOf_of_centralizes {X K E : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K)
    (hEX : E ≤ X) (hXE : X ≤ Subgroup.normalizer (E : Set G))
    (hcent : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 K) {e : G} (he : e ∈ E) {k : ℕ}
    (hek : e ^ 2 ^ k = 1) : e ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := (isSylowTwoOf_pCoreOf_and_le_of_centralizes hXK hpow hEX hcent).1
  have hzp := isPGroup_zpowers_of_pow_eq_one hek
  have hsup : IsPGroup 2 (pCoreOf 2 E ⊔ Subgroup.zpowers e : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS.2.1 hzp
      (Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 E he))
  have hle := (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _
    (sup_le (pCoreOf_le 2 E) (Subgroup.zpowers_le.mpr he)) hsup le_sup_left
  have heP : e ∈ pCoreOf 2 E := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 E).trans hEX)
    (hXE.trans (normalizer_le_normalizer_pCoreOf 2 E)) (pCoreOf_isPGroup 2 E) heP

theorem le_pCoreOf_sup_oTwoZIn_of_centralizes {X K E : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ K)
    (hEX : E ≤ X) (hXE : X ≤ Subgroup.normalizer (E : Set G))
    (hcent : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    E ≤ pCoreOf 2 X ⊔ oTwoZIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := (isSylowTwoOf_pCoreOf_and_le_of_centralizes hXK hpow hEX hcent).2
  have hEK : E ⊓ K ≤ oTwoZIn K := fun x hx =>
    mem_oTwoZIn_iff.mpr ⟨hx.2, fun w hw => hcent x hx.1 w hw⟩
  have hPX : pCoreOf 2 E ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 E).trans hEX)
      (hXE.trans (normalizer_le_normalizer_pCoreOf 2 E)) (pCoreOf_isPGroup 2 E)
  rw [sup_comm]
  exact hle.trans (sup_le_sup hEK hPX)

theorem exists_odd_pow_mem_pCoreOf_of_mem_oTwoZIn {K : Subgroup G} {z : G}
    (hz : z ∈ oTwoZIn K) : ∃ m : ℕ, Odd m ∧ z ^ m ∈ pCoreOf 2 K := by
  obtain ⟨s, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨m, hm, ?_⟩
  have h2 : (z ^ m) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hKE : K ≤ Subgroup.normalizer (oTwoZIn K : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoZIn K)
  exact mem_pCoreOf_of_centralizes Subgroup.le_normalizer (fun x hx => ⟨0, by simpa using hx⟩)
    (oTwoZIn_le K) hKE (fun e he w hw => (mem_oTwoZIn_iff.mp he).2 w hw)
    ((oTwoZIn K).pow_mem hz m) h2

end Centralizing

end CFSG.Quasithin.SmithC27
