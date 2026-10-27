module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs
public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem IsSL27OverE49.center_eq_bot {Q : Type} [Group Q] [Finite Q] (h : IsSL27OverE49 Q) :
    Subgroup.center Q = ⊥ := by
  classical
  obtain ⟨E, -, hEcard, hcent, hEn, ⟨f⟩⟩ := h
  have hQE : Nat.card (Q ⧸ E) = 336 := by
    rw [Nat.card_congr f.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
      Nat.card_zmod]
    decide
  have hZE : Subgroup.center Q ≤ E := by
    intro z hz
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro e _
    exact Subgroup.mem_center_iff.1 hz e
  by_contra hne
  by_cases hEZ : E ≤ Subgroup.center Q
  · have htop : E = ⊤ := by
      rw [← hcent, eq_top_iff]
      intro q _
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_center_iff.1 (hEZ he) q).symm
    have h1 : Nat.card (Q ⧸ E) = 1 := by
      rw [htop]
      exact Subgroup.index_top
    omega
  obtain ⟨e₀, he₀E, he₀Z⟩ := Set.not_subset.1 hEZ
  have h7 : Nat.Prime 7 := by norm_num
  have hZcard : Nat.card (Subgroup.center Q) = 7 := by
    have hdvd : Nat.card (Subgroup.center Q) ∣ 7 ^ 2 := by
      rw [show (7 : ℕ) ^ 2 = 49 by norm_num, ← hEcard]
      exact Subgroup.card_dvd_of_le hZE
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow h7).1 hdvd
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk')) hne
    · simpa using hk'
    · exfalso
      have : Subgroup.center Q = E :=
        Subgroup.eq_of_le_of_card_ge hZE (by rw [hk', hEcard]; norm_num)
      exact he₀Z (this ▸ he₀E)
  have hSE : Subgroup.center Q ⊔ Subgroup.zpowers e₀ ≤ E :=
    sup_le hZE ((Subgroup.zpowers_le).2 he₀E)
  have hS : Subgroup.center Q ⊔ Subgroup.zpowers e₀ = E := by
    refine Subgroup.eq_of_le_of_card_ge hSE ?_
    have hdvd : Nat.card ↥(Subgroup.center Q ⊔ Subgroup.zpowers e₀) ∣ 7 ^ 2 := by
      rw [show (7 : ℕ) ^ 2 = 49 by norm_num, ← hEcard]
      exact Subgroup.card_dvd_of_le hSE
    have h7d : 7 ∣ Nat.card ↥(Subgroup.center Q ⊔ Subgroup.zpowers e₀) := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hne7 : Nat.card ↥(Subgroup.center Q ⊔ Subgroup.zpowers e₀) ≠ 7 := by
      intro h7'
      have := Subgroup.eq_of_le_of_card_ge
        (le_sup_left : Subgroup.center Q ≤ Subgroup.center Q ⊔ Subgroup.zpowers e₀)
        (by rw [h7', hZcard])
      exact he₀Z (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow h7).1 hdvd
    interval_cases k
    · rw [hk'] at h7d
      norm_num at h7d
    · exact absurd (by simpa using hk') hne7
    · rw [hk', hEcard]
      norm_num
  have := hEn
  let φ : Q →* MulAut ↥E := MulAut.conjNormal
  have hker : φ.ker = E := by
    ext q
    rw [MonoidHom.mem_ker]
    constructor
    · intro hq
      rw [← hcent, Subgroup.mem_centralizer_iff]
      intro e he
      have h1 := congrArg (fun a : MulAut ↥E => ((a ⟨e, he⟩ : ↥E) : Q)) hq
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc e * q = (q * e * q⁻¹) * q := by rw [h1]
        _ = q * e := by group
    · intro hq
      rw [← hcent, Subgroup.mem_centralizer_iff] at hq
      refine MulEquiv.ext fun e => Subtype.ext ?_
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hq e e.2]
      group
  have hrange : Nat.card φ.range = 336 := by
    rw [← hQE, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  have hle : Nat.card φ.range ≤ Nat.card E := by
    refine Nat.card_le_card_of_injective (fun α : φ.range => (α : MulAut ↥E) ⟨e₀, he₀E⟩) ?_
    rintro ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ h12
    have h12' : q₁ * e₀ * q₁⁻¹ = q₂ * e₀ * q₂⁻¹ := by
      have := congrArg Subtype.val h12
      simpa [φ, MulAut.conjNormal_apply] using this
    have hq : q₂⁻¹ * q₁ ∈ E := by
      rw [← hcent, Subgroup.mem_centralizer_iff]
      have hc : Subgroup.center Q ⊔ Subgroup.zpowers e₀ ≤
          Subgroup.centralizer ({q₂⁻¹ * q₁} : Set Q) := by
        refine sup_le (Subgroup.center_le_centralizer _) ((Subgroup.zpowers_le).2 ?_)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : q₁ * e₀ = q₂ * e₀ * q₂⁻¹ * q₁ := by rw [← h12']; group
        calc e₀ * (q₂⁻¹ * q₁) = q₂⁻¹ * (q₂ * e₀ * q₂⁻¹ * q₁) := by group
          _ = q₂⁻¹ * (q₁ * e₀) := by rw [this]
          _ = q₂⁻¹ * q₁ * e₀ := by group
      intro e he
      rw [← hS] at he
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hc he))
    have h1 : φ (q₂⁻¹ * q₁) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hq
    apply Subtype.ext
    show φ q₁ = φ q₂
    have : q₁ = q₂ * (q₂⁻¹ * q₁) := by group
    rw [this, map_mul, h1, mul_one]
  rw [hrange, hEcard] at hle
  omega

namespace L1295B

theorem commutator_pCoreOf_seven_ne_bot {Γ : Type} [Group Γ] [Finite Γ] {X K A : Subgroup Γ}
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hpow : ∀ x ∈ X, ∃ j : ℕ, x ^ 2 ^ j ∈ K) (hE : IsSL27OverE49 ↥K) (hO2 : pCoreOf 2 X = ⊥)
    (hAX : A ≤ X) (hA : A ≠ ⊥) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ⁅pCoreOf 7 X, A⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := hE.center_eq_bot
  obtain ⟨E', ⟨-, hEp⟩, -, hcent, hEn, -⟩ := hE
  set P := pCoreOf 7 X with hP
  have hPn : X ≤ Subgroup.normalizer (P : Set Γ) := LieType.BorelTits.le_normalizer_pCoreOf 7 X
  set E := E'.map K.subtype with hEdef
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hE7 : IsPGroup 7 E := by
    rintro ⟨_, e, he, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h1 := hEp e he
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact congrArg Subtype.val h1
  have hKE : K ≤ Subgroup.normalizer (E : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨k, hk⟩ * e * ⟨k, hk⟩⁻¹, hEn.conj_mem e he _, rfl⟩
    · rintro ⟨e, he, hee⟩
      refine ⟨⟨k, hk⟩⁻¹ * e * ⟨k, hk⟩, ?_, ?_⟩
      · have := hEn.conj_mem e he (⟨k, hk⟩⁻¹)
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hee ⊢
        rw [hee]
        group
  have hEP : E ≤ P :=
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 7 hEK hKE hE7).trans
      (LieType.BorelTits.le_pCoreOf_of_le_normalizer 7
        ((LieType.BorelTits.pCoreOf_le 7 K).trans hKX)
        (hXK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 7 K))
        (LieType.BorelTits.pCoreOf_isPGroup 7 K))
  intro hc
  have hAP : ∀ a ∈ A, ∀ p ∈ P, a * p = p * a := by
    intro a ha p hp
    have h1 : p * a * p⁻¹ * a⁻¹ = 1 := by
      have := Subgroup.commutator_mem_commutator hp ha
      rw [hc, Subgroup.mem_bot, commutatorElement_def] at this
      exact this
    have h2 : p * a = a * p := by
      calc p * a = (p * a * p⁻¹ * a⁻¹) * (a * p) := by group
        _ = a * p := by rw [h1, one_mul]
    exact h2.symm
  have hdE : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ E := by
    intro a ha k hk
    have hdK : a * k * a⁻¹ * k⁻¹ ∈ K := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hk)
      exact (Subgroup.mem_normalizer_iff.1 (hXK (hAX ha)) k).1 hk
    have hdP : ∀ p ∈ P, (a * k * a⁻¹ * k⁻¹) * p = p * (a * k * a⁻¹ * k⁻¹) := by
      intro p hp
      have hkp : k⁻¹ * p * k ∈ P := by
        have := (Subgroup.mem_normalizer_iff.1 (hPn (Subgroup.inv_mem _ (hKX hk))) p).1 hp
        simpa using this
      have h1 := hAP a ha p hp
      have h2 := hAP a ha _ hkp
      have h1' : a⁻¹ * p = p * a⁻¹ := by
        calc a⁻¹ * p = a⁻¹ * (p * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * p) * a⁻¹ := by rw [h1]
          _ = p * a⁻¹ := by group
      have h2' : a⁻¹ * (k⁻¹ * p * k) = (k⁻¹ * p * k) * a⁻¹ := by
        calc a⁻¹ * (k⁻¹ * p * k) = a⁻¹ * ((k⁻¹ * p * k) * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * (k⁻¹ * p * k)) * a⁻¹ := by rw [h2]
          _ = (k⁻¹ * p * k) * a⁻¹ := by group
      calc (a * k * a⁻¹ * k⁻¹) * p = a * k * (a⁻¹ * (k⁻¹ * p * k)) * k⁻¹ := by group
        _ = a * k * ((k⁻¹ * p * k) * a⁻¹) * k⁻¹ := by rw [h2']
        _ = (a * p) * k * a⁻¹ * k⁻¹ := by group
        _ = (p * a) * k * a⁻¹ * k⁻¹ := by rw [h1]
        _ = p * (a * k * a⁻¹ * k⁻¹) := by group
    have hmem : (⟨_, hdK⟩ : ↥K) ∈ Subgroup.centralizer (E' : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      apply Subtype.ext
      exact (hdP (e : Γ) (hEP ⟨e, he, rfl⟩)).symm
    rw [hcent] at hmem
    exact ⟨_, hmem, rfl⟩
  have hAK : ∀ a ∈ A, ∀ k ∈ K, k * a = a * k := by
    intro a ha k hk
    obtain ⟨d, hdE', hdd⟩ : ∃ d, d ∈ E ∧ d = a * k * a⁻¹ * k⁻¹ := ⟨_, hdE a ha k hk, rfl⟩
    have hda : a * d = d * a := hAP a ha d (hEP hdE')
    have hd7 : d ^ 7 = 1 := by
      obtain ⟨e, he, rfl⟩ := hdE'
      have := congrArg Subtype.val (hEp e he)
      simpa using this
    have hak : a * k * a⁻¹ = d * k := by rw [hdd, inv_mul_cancel_right]
    have ha2 : a * a = 1 := by rw [← sq]; exact hA2 a ha
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have h1 : k = d * (d * k) := by
      calc k = (a * a) * k * (a * a) := by rw [ha2, one_mul, mul_one]
        _ = a * (a * k * a⁻¹) * a⁻¹ := by rw [hainv]; simp only [mul_assoc]
        _ = a * (d * k) * a⁻¹ := by rw [hak]
        _ = (a * d) * k * a⁻¹ := by simp only [mul_assoc]
        _ = (d * a) * k * a⁻¹ := by rw [hda]
        _ = d * (a * k * a⁻¹) := by simp only [mul_assoc]
        _ = d * (d * k) := by rw [hak]
    have hd2 : d * d = 1 := by
      have h2 : (d * d) * k = 1 * k := by rw [one_mul, mul_assoc, ← h1]
      exact mul_right_cancel h2
    have hd1 : d = 1 := by
      have h7 := orderOf_dvd_of_pow_eq_one hd7
      have h2 := orderOf_dvd_of_pow_eq_one (show d ^ 2 = 1 by rw [sq]; exact hd2)
      have h1' : orderOf d ∣ 1 := by
        have := Nat.dvd_gcd h7 h2
        simpa using this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1')
    have h3 : a * k * a⁻¹ = k := by rw [hak, hd1, one_mul]
    calc k * a = (a * k * a⁻¹) * a := by rw [h3]
      _ = a * k := inv_mul_cancel_right _ _
  set Y := X ⊓ Subgroup.centralizer (K : Set Γ) with hY
  have hY2 : IsPGroup 2 Y := by
    intro y
    obtain ⟨j, hj⟩ := hpow y y.2.1
    refine ⟨j, Subtype.ext ?_⟩
    have hyc : (y : Γ) ^ 2 ^ j ∈ Subgroup.centralizer (K : Set Γ) :=
      Subgroup.pow_mem _ y.2.2 _
    have hz : (⟨_, hj⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hyc k k.2
    rw [hZ, Subgroup.mem_bot] at hz
    simpa using congrArg Subtype.val hz
  have hYn : X ≤ Subgroup.normalizer (Y : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
      intro x hx y hy
      refine Subgroup.mem_inf.2
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy.1) (Subgroup.inv_mem _ hx), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : x⁻¹ * k * x ∈ K := by
        have := (Subgroup.mem_normalizer_iff.1 (hXK (Subgroup.inv_mem _ hx)) k).1 hk
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hy.2 _ hk'
      calc k * (x * y * x⁻¹) = x * ((x⁻¹ * k * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * k * x)) * x⁻¹ := by rw [h1]
        _ = x * y * x⁻¹ * k := by group
    intro y
    refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
    have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hy
    simpa [mul_assoc] using this
  have hYO : Y ≤ pCoreOf 2 X :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hYn hY2
  rw [hO2] at hYO
  apply hA
  rw [eq_bot_iff]
  intro a ha
  exact hYO ⟨hAX ha, Subgroup.mem_centralizer_iff.2 fun k hk => hAK a ha k hk⟩

section Act

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem conjClosure_le_normalizer (h : HypF91 T V L V₁ Vp H) :
    conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
  h.conjClosure_Vp_le_pCoreOf.trans
    ((LieType.BorelTits.pCoreOf_le 2 H).trans h.H_normalizes_V₁)

theorem actH_eq_one_of_mem (h : HypF91 T V L V₁ Vp H) {x : ↥H} (hx : (x : G) ∈ pCoreOf 2 H) :
    actH h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) x = 1 := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) := ⟨h.isElemAbelian_tilde⟩
  have hUN := conjClosure_le_normalizer h
  refine MulEquiv.ext fun w => ?_
  rw [MulAut.one_apply]
  obtain ⟨a, haU, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hUN (a : G) haU := Subtype.ext hau.symm
  rw [hw, actH_modMk h.H_normalizes_V₁ hUN (le_normalizer_conjClosure Vp H) x haU]
  apply Subtype.ext
  show secMk _ _ ⟨(x : G) * a * (x : G)⁻¹, _⟩ = secMk _ _ ⟨(a : G), _⟩
  symm
  rw [secMk_eq_secMk_iff]
  have := h.commutator_conjClosure_le (a : G)⁻¹ (inv_mem haU) x hx
  have e : (a : G)⁻¹ * (x : G) * ((a : G)⁻¹)⁻¹ * (x : G)⁻¹ =
      (a : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) := by group
  rw [e] at this
  exact this

theorem mem_pCoreOf_of_actH_eq_one (h : HypF91 T V L V₁ Vp H) {x : ↥H}
    (hx : actH h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) x = 1) :
    (x : G) ∈ pCoreOf 2 H := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) := ⟨h.isElemAbelian_tilde⟩
  have hUN := conjClosure_le_normalizer h
  rw [h.pCoreOf_eq_centralizerMod]
  refine ⟨x.2, h.H_normalizes_V₁ x.2, fun u hu => ?_⟩
  have key := actH_modMk h.H_normalizes_V₁ hUN (le_normalizer_conjClosure Vp H) x hu
  rw [hx, MulAut.one_apply] at key
  have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hUN hu⟩ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(x : G) * u * (x : G)⁻¹, hUN
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H x.2) u).mp hu)⟩ :=
    congrArg Subtype.val key
  have h2 := secMk_eq_secMk_iff.mp h1
  have e : (x : G) * u * (x : G)⁻¹ * u⁻¹ = u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ := by
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hUN hu) _).mp h2

theorem nonempty_mulEquiv_autOn (h : HypF91 T V L V₁ Vp H) {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      ↥(autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := actH h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) with hφ
  set ψ : ↥K →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) := φ.comp (Subgroup.inclusion hKH)
    with hψ
  have hrange : ψ.range = autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp H)) := by
    rw [autOn_tilde_eq_map_actH h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) hKH, hψ,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ.ker = CFSG.pCore 2 ↥K := by
    apply le_antisymm
    · set N : Subgroup ↥K := (pCoreOf 2 H).subgroupOf K with hN
      have hNn : N.Normal := by
        refine ⟨fun n hn k => ?_⟩
        rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
        have hkH : (k : G) ∈ H := hKH k.2
        have := (Subgroup.mem_normalizer_iff.1
          (LieType.BorelTits.le_normalizer_pCoreOf 2 H hkH) n).1 hn
        simpa using this
      have hNp : IsPGroup 2 N := by
        intro x
        have hx : ((x : ↥K) : G) ∈ pCoreOf 2 H := x.2
        obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hx⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxQ : (x : G) ∈ pCoreOf 2 H := mem_pCoreOf_of_actH_eq_one h hx
      have hxN : x ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf]
        exact hxQ
      exact LieType.BorelTits.le_pCore 2 hNn hNp hxN
    · intro x hx
      rw [MonoidHom.mem_ker]
      apply actH_eq_one_of_mem h
      have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
        assumption
      have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
      exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
        (hHK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (LieType.BorelTits.pCoreOf_isPGroup 2 K) hx1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

end Act

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {n : ℕ} {V₁ K₁ : Subgroup G}

theorem false_of_e49 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1)
    (hU : IsMulCommutative ↥(u128 V V₁)) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hF := L1286.hypF98_of_abelian h1222 h37 h38 h39 hcx.hyp hV₁ hU hHz
  have hF1 := hF.toHypF91
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) :=
    hV₁.2.2.trans (normalizer_le_of_lOne_le h1222 h37 h38 hcx.hyp hn hV₁ hLK hK)
  have hT2 : IsPGroup 2 T := hcx.hyp.hyp.sylow.1
  have hKH : K₁ ≤ K₁ ⊔ T := le_sup_left
  have hHK : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  have hUT := hF1.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))) := commGroupOfElemAbelian hUT
  have hsq : ∀ w : ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using hUT.2 w w.2)
  set φ := actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) with hφ
  have hXeq : autOn (tildeOf V₁ (K₁ ⊔ T)) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) =
      ((K₁ ⊔ T).subgroupOf (K₁ ⊔ T)).map φ :=
    autOn_tilde_eq_map_actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) le_rfl
  have hKeq : autOn (tildeOf V₁ K₁) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) =
      (K₁.subgroupOf (K₁ ⊔ T)).map φ :=
    autOn_tilde_eq_map_actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) hKH
  set X := autOn (tildeOf V₁ (K₁ ⊔ T)) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) with hX
  set Kp := autOn (tildeOf V₁ K₁) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) with hKp
  have hKpX : Kp ≤ X := by
    rw [hKeq, hXeq, Subgroup.subgroupOf_self]
    exact Subgroup.map_mono le_top
  have hXK :
      X ≤ Subgroup.normalizer (Kp : Set (MulAut ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))))) := by
    have hn : (K₁.subgroupOf (K₁ ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
    rw [hKeq, hXeq, Subgroup.subgroupOf_self, ← Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.le_normalizer_map φ
  have hpow : ∀ x ∈ X, ∃ j : ℕ, x ^ 2 ^ j ∈ Kp := by
    intro x hx
    rw [hXeq] at hx
    obtain ⟨h, -, rfl⟩ := hx
    obtain ⟨j, hj⟩ := L1286.exists_two_pow_mem_of_mem_sup hT2 hTK h.2
    refine ⟨j, ?_⟩
    rw [hKeq, ← map_pow]
    exact ⟨h ^ 2 ^ j, Subgroup.mem_subgroupOf.2 (by simpa using hj), rfl⟩
  have hEKp : IsSL27OverE49 ↥Kp := by
    obtain ⟨e⟩ := nonempty_mulEquiv_autOn hF1 hKH hHK
    exact IsSL27OverE49.of_mulEquiv e hE
  have hO2 : pCoreOf 2 X = ⊥ :=
    pCoreOf_autOn_eq_bot_of_isTwoReducedIn (lemma12_8_4_one h1222 hcx.hyp hV₁ hHz).G22_four
  obtain ⟨-, B, -, hBQ⟩ := hF.F916_3
  obtain ⟨⟨hB2, hBr⟩, hBc⟩ := hBQ
  have hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    kq_le_iff.2 ⟨_, hB2, commSeries_eq_bot_of_le (by norm_num) hBc, hBr⟩
  have hne : qhatOf X ≠ ⊤ := fun h => by
    rw [h] at hq
    exact absurd hq (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have hr2 : r ≤ 2 := by
    rw [← hr] at hq
    exact_mod_cast hq
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr.symm hr2
  obtain ⟨-, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hD := commutator_pCoreOf_seven_ne_bot hKpX hXK hpow hEKp hO2 hA2.le hA2.ne_bot
    hA2.isElemAbelian2.2
  have h7 := (D2_13 hsq hr.symm hA (p := 7) (by norm_num) rfl hD).1
  omega

end L1295B

end CFSG.Quasithin.H13
