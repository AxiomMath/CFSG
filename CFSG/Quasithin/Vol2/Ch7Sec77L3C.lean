module

public import CFSG.Quasithin.Background.HSL3Fix3
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S146D1
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch7Sec77Cases1

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem eq_one_of_odd_of_pow_two_pow {z : G} (hz : Odd (orderOf z)) {k : ℕ} (hk : z ^ 2 ^ k = 1) :
    z = 1 := by
  have h1 : orderOf z ∣ Nat.gcd (2 ^ k) (orderOf z) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) dvd_rfl
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hz)),
    Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem relIndex_centralizer_eq_ncard (X : Subgroup G) (θ : G) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex X =
      {g : G | ∃ x ∈ X, x * θ * x⁻¹ = g}.ncard := by
  classical
  let _ : MulAction ↥X G := MulAction.compHom G ((MulAut.conj).comp X.subtype)
  have hsmul : ∀ (x : ↥X) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun x g => rfl
  have hstab : MulAction.stabilizer ↥X θ =
      (Subgroup.centralizer ({θ} : Set G)).subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (x : G) * θ = (x : G) * θ * (x : G)⁻¹ * x := by group
        _ = θ * x := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have horb : MulAction.orbit ↥X θ = {g : G | ∃ x ∈ X, x * θ * x⁻¹ = g} := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x θ).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ θ⟩
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horb]

theorem relIndex_le_of_forall_conj {X Y : Subgroup G} {θ : G}
    (h : ∀ x ∈ X, ∃ y ∈ Y, x * θ * x⁻¹ = y * θ * y⁻¹) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex X ≤
      (Subgroup.centralizer ({θ} : Set G)).relIndex Y := by
  rw [relIndex_centralizer_eq_ncard, relIndex_centralizer_eq_ncard]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro g ⟨x, hx, rfl⟩
  obtain ⟨y, hy, e⟩ := h x hx
  exact ⟨y, hy, e.symm⟩

theorem exists_conj_eq_of_comm_mem {N : Subgroup G} {θ g : G} (hN2 : IsPGroup 2 N)
    (hθo : Odd (orderOf θ)) (hθN : θ ∈ Subgroup.normalizer (N : Set G))
    (hgN : g ∈ Subgroup.normalizer (N : Set G))
    (hg : ∀ n : ℕ, g * θ ^ n * g⁻¹ * (θ ^ n)⁻¹ ∈ N) :
    ∃ p ∈ N, g * θ * g⁻¹ = p * θ * p⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzg⟩ := exists_mem_normalizer_of_conj_le (A := Subgroup.zpowers θ)
    (by rw [Nat.card_zpowers]; exact hθo) hN2 ((Subgroup.zpowers_le).mpr hθN) hgN (by
      intro a ha
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, θ ^ n = a := (mem_powers_iff_mem_zpowers).mpr ha
      have e : g * θ ^ n * g⁻¹ = (g * θ ^ n * g⁻¹ * (θ ^ n)⁻¹) * θ ^ n := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hg n))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers θ) n)))
  have h1 : z * g * θ * (z * g)⁻¹ ∈ Subgroup.zpowers θ :=
    (Subgroup.mem_normalizer_iff.1 hzg θ).1 (Subgroup.mem_zpowers θ)
  have h2 : z * g * θ * (z * g)⁻¹ * θ⁻¹ ∈ N := by
    have e : z * g * θ * (z * g)⁻¹ * θ⁻¹ =
        z * (g * θ ^ 1 * g⁻¹ * (θ ^ 1)⁻¹) * (θ * z⁻¹ * θ⁻¹) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hz (hg 1)) ((Subgroup.mem_normalizer_iff.1 hθN _).1 (N.inv_mem hz))
  have h4 : z * g * θ * (z * g)⁻¹ * θ⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := hN2 ⟨_, h2⟩
    have hk' : (z * g * θ * (z * g)⁻¹ * θ⁻¹) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    refine eq_one_of_odd_of_pow_two_pow ?_ hk'
    have hmem : z * g * θ * (z * g)⁻¹ * θ⁻¹ ∈ Subgroup.zpowers θ :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers θ))
    exact Odd.of_dvd_nat hθo (orderOf_dvd_of_mem_zpowers hmem)
  refine ⟨z⁻¹, N.inv_mem hz, ?_⟩
  have e5 : z * g * θ * (z * g)⁻¹ = θ := by
    calc z * g * θ * (z * g)⁻¹ = (z * g * θ * (z * g)⁻¹ * θ⁻¹) * θ := by group
      _ = θ := by rw [h4, one_mul]
  calc g * θ * g⁻¹ = z⁻¹ * (z * g * θ * (z * g)⁻¹) * z := by group
    _ = z⁻¹ * θ * z⁻¹⁻¹ := by rw [e5, inv_inv]

theorem card_mul_card_le_of_inf_eq_bot {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card C := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : G) * p.2, C.mul_mem (hA p.1.2) (hB p.2.2)⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
  have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have e : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    rw [e]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h2
  have ha : a' = a := Subtype.ext h2
  subst ha
  have hb : b = b' := Subtype.ext (mul_left_cancel h1)
  rw [hb]

omit [Finite G] in
theorem card_eq_of_surjective_ker {U Z : Subgroup G} {X : Type*} [Group X] (hZU : Z ≤ U)
    (β : ↥U →* X) (hβ : Function.Surjective β) (hker : β.ker = Z.subgroupOf U) :
    Nat.card U = Nat.card Z * Nat.card X := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
  rw [h1, mul_comm]

theorem card_eq_two_of_card_statedSL {F : Type} [Field F] [Finite F]
    (h : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168) : Nat.card F = 2 := by
  rw [card_statedSL_three1527d] at h
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  by_contra hne
  have h3 : 3 ≤ Nat.card F := by omega
  set q := Nat.card F with hqdef
  have h27 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left h3 3
  have h9 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
  have h8 : 8 ≤ q ^ 2 - 1 := by omega
  have h26 : 26 ≤ q ^ 3 - 1 := by omega
  have : 27 * (8 * 26) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul h27 (Nat.mul_le_mul h8 h26)
  omega

theorem card_statedSL_three_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem eq_one_of_pow_two_pow_of_commute {t g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {k : ℕ} (ht : t ^ 2 ^ k = 1) (hg : g ^ 3 = 1) (hg1 : g ≠ 1) (hc : t * g = g * t) : t = 1 := by
  induction k generalizing t with
  | zero => simpa using ht
  | succ k ih =>
    have hs : (t ^ 2 ^ k) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact ht
    have hcs : t ^ 2 ^ k * g = g * t ^ 2 ^ k := ((Commute.pow_left hc (2 ^ k))).eq
    rcases SL3Six.eq_one_or_eq_one_of_commute hs hg hcs with h | h
    · exact ih h hc
    · exact absurd h hg1

omit [Finite G] in
theorem card_eq_two_of_isModO2Surj {K : Subgroup G} {F : Type} [Field F] [Finite F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj K α)
    (hKX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168) : Nat.card F = 2 := by
  refine card_eq_two_of_card_statedSL ?_
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hα.2).toEquiv]
  exact hKX

omit [Finite G] in
theorem c134Q_le_pCoreOf {K X : Subgroup G} (hKX : K ≤ X) : c134Q X K ≤ pCoreOf 2 X := by
  unfold c134Q
  rw [Subgroup.commutator_le]
  intro a ha k hk
  rw [commutatorElement_def]
  have hk' : k ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X (hKX hk)
  have h1 : k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 X :=
    (Subgroup.mem_normalizer_iff.1 hk' _).1 ((pCoreOf 2 X).inv_mem ha)
  have e : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 X).mul_mem ha h1

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [← CFSG.Quasithin.A1b.conjSub_eq_iff_mem_normalizer] at hA hB ⊢
  unfold CFSG.Quasithin.A1b.conjSub at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem relIndex_le_of_c134Two {K R : Subgroup G} {θ : G} (hθK : θ ∈ K) (hθ3 : θ ^ 3 = 1)
    (hθO : θ ∉ pCoreOf 2 K) (hθR : θ ∈ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hOR : pCoreOf 2 K ≤ R)
    (hKX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168) (hi : IsC134Case 2 (K ⊔ R) R K) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex R ≤ 8 * 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({θ} : Set G) with hCdef
  have hne : ∀ {A B : Subgroup G}, A.relIndex B ≠ 0 := fun {A B} =>
    (A.subgroupOf B).index_ne_zero_of_finite
  have hθo : Odd (orderOf θ) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hθ3)
  have hθKN : θ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hθK
  have h1 : C.relIndex R ≤ C.relIndex (R ⊓ K) := by
    refine relIndex_le_of_forall_conj fun x hx => exists_conj_eq_of_comm_mem
      (hR2.to_le inf_le_left) hθo
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hθR, hθKN⟩)
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hRN hx⟩) fun n => ?_
    have hθn : θ ^ n ∈ Subgroup.normalizer (R : Set G) := Subgroup.pow_mem _ hθR n
    refine ⟨?_, ?_⟩
    · have h2 : θ ^ n * x⁻¹ * (θ ^ n)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.1 hθn _).1 (R.inv_mem hx)
      have e : x * θ ^ n * x⁻¹ * (θ ^ n)⁻¹ = x * (θ ^ n * x⁻¹ * (θ ^ n)⁻¹) := by group
      rw [e]
      exact R.mul_mem hx h2
    · have h2 : x * θ ^ n * x⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 (hRN hx) _).1 (K.pow_mem hθK n)
      exact K.mul_mem h2 (K.inv_mem (K.pow_mem hθK n))
  have hOKR : pCoreOf 2 K ≤ R ⊓ K := le_inf hOR (pCoreOf_le 2 K)
  have h2 : C.relIndex (R ⊓ K) ≤ 8 * C.relIndex (pCoreOf 2 K) := by
    have h3 : C.relIndex (R ⊓ K) ≤ (C ⊓ pCoreOf 2 K).relIndex (R ⊓ K) :=
      Subgroup.relIndex_le_of_le_left inf_le_left hne
    have h4 := Subgroup.relIndex_mul_relIndex _ _ _
      (inf_le_right : C ⊓ pCoreOf 2 K ≤ pCoreOf 2 K) hOKR
    rw [Subgroup.inf_relIndex_right] at h4
    have h5 : (pCoreOf 2 K).relIndex (R ⊓ K) ≤ 8 := by
      have h6 := Subgroup.relIndex_mul_relIndex _ _ _ hOKR (inf_le_right : R ⊓ K ≤ K)
      have h7 : (pCoreOf 2 K).relIndex K = 168 := by
        rw [Subgroup.relIndex, subgroupOf_pCoreOf_eq]
        exact hKX
      rw [h7] at h6
      obtain ⟨b, hb⟩ := (hR2.to_le (inf_le_left : R ⊓ K ≤ R)).exists_card_eq
      have h8 : (pCoreOf 2 K).relIndex (R ⊓ K) ∣ 2 ^ b := hb ▸ Subgroup.relIndex_dvd_card _ _
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8
      have h9 : 2 ^ c ∣ 8 * 21 := by
        rw [← hc]
        exact ⟨_, h6.symm⟩
      have h10 : 2 ^ c ∣ 8 :=
        Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left c (by norm_num)) h9
      rw [hc]
      exact Nat.le_of_dvd (by norm_num) h10
    calc C.relIndex (R ⊓ K) ≤ (C ⊓ pCoreOf 2 K).relIndex (R ⊓ K) := h3
      _ = C.relIndex (pCoreOf 2 K) * (pCoreOf 2 K).relIndex (R ⊓ K) := h4.symm
      _ ≤ C.relIndex (pCoreOf 2 K) * 8 := Nat.mul_le_mul_left _ h5
      _ = 8 * C.relIndex (pCoreOf 2 K) := mul_comm _ _
  set QK := c134Q (K ⊔ R) K with hQKdef
  have hQKO : QK ≤ pCoreOf 2 (K ⊔ R) := c134Q_le_pCoreOf le_sup_left
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
    have hKn : (K.subgroupOf (K ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hRN)
    exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
      (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn)
  have hKQK : ∀ k ∈ K, k ∈ Subgroup.normalizer (QK : Set G) := fun k hk =>
    mem_normalizer_commutator (le_normalizer_pCoreOf 2 (K ⊔ R) ((le_sup_left : K ≤ K ⊔ R) hk))
      (Subgroup.le_normalizer hk)
  have h3 : C.relIndex (pCoreOf 2 K) ≤ C.relIndex QK := by
    refine relIndex_le_of_forall_conj fun x hx => exists_conj_eq_of_comm_mem
      ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le hQKO) hθo (hKQK θ hθK)
      (hKQK x (pCoreOf_le 2 K hx)) fun n => ?_
    have h4 := Subgroup.commutator_mem_commutator (hOK hx) (K.pow_mem hθK n)
    rwa [commutatorElement_def] at h4
  have h4 : C.relIndex QK ≤ 16 := by
    obtain ⟨⟨n, F, hFf, hFt, α, -, hα, ⟨-, -, β, hβs, hβk, hβe⟩⟩, -⟩ := hi
    have hF2 : Nat.card F = 2 := card_eq_two_of_isModO2Surj hα hKX
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
    have hQK64 : Nat.card QK = 64 := by
      have h5 := card_eq_of_surjective_ker bot_le β hβs hβk
      rw [Subgroup.card_bot, one_mul, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_fun, Nat.card_fin, Nat.card_fin, hF2] at h5
      rw [h5]
      norm_num
    set g : Matrix (Fin 3) (Fin 3) F :=
      (((α ⟨θ, hθK⟩ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) with hgdef
    have hg3 : g * g * g = 1 := by
      have e1 : (α ⟨θ, hθK⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨θ, hθK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
        rw [this, map_one]
      have e2 := congrArg (fun y : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =>
        ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) e1
      simpa [pow_succ, hgdef] using e2
    have hg1 : g ≠ 1 := by
      intro h
      apply hθO
      have h5 : α ⟨θ, hθK⟩ = 1 := Subtype.ext (Units.ext (by simpa [hgdef] using h))
      have h6 : (⟨θ, hθK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
        rw [← hα.2]
        exact h5
      exact coe_mem_pCoreOf h6
    obtain ⟨σ⟩ : Nonempty (F ≃+* ZMod 2) := by
      let _ : Fintype F := Fintype.ofFinite F
      exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF2]; simp)⟩
    have hfix : Nat.card {v : Fin 3 → F // g.mulVec v = v} = 2 := by
      have hg3' : g.map σ * g.map σ * g.map σ = 1 := by
        rw [← Matrix.map_mul, ← Matrix.map_mul, hg3, Matrix.map_one σ (map_zero σ) (map_one σ)]
      have hg1' : g.map σ ≠ 1 := by
        intro h
        apply hg1
        ext i j
        have h2 := congrFun (congrFun h i) j
        simp only [Matrix.map_apply] at h2
        have h3 : g i j = σ.symm ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
          rw [← h2, RingEquiv.symm_apply_apply]
        rw [h3]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have h5 := SL3Six.card_fix_three (g.map σ) hg3' hg1'
      rw [← h5, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      have hm : ∀ v : Fin 3 → F, ∀ i, σ (g.mulVec v i) = (g.map σ).mulVec (fun j => σ (v j)) i :=
        fun v i => RingHom.map_mulVec σ.toRingHom g v i
      refine Nat.card_congr
        { toFun := fun v => ⟨fun j => σ (v.1 j), ?_⟩
          invFun := fun w => ⟨fun j => σ.symm (w.1 j), ?_⟩
          left_inv := fun v => Subtype.ext (funext fun j => σ.symm_apply_apply _)
          right_inv := fun w => Subtype.ext (funext fun j => σ.apply_symm_apply _) }
      · funext i
        rw [← hm, v.2]
      · funext i
        apply σ.injective
        rw [hm, σ.apply_symm_apply]
        have : (fun j => σ (σ.symm (w.1 j))) = w.1 := funext fun j => σ.apply_symm_apply _
        rw [this]
        exact congrFun w.2 i
    set eβ := Equiv.ofBijective β ⟨hβi, hβs⟩ with heβ
    have hθQK := hKQK θ hθK
    have hfixed : ∀ w : Fin 2 → Fin 3 → F, (∀ i, g.mulVec (w i) = w i) →
        (eβ.symm (Multiplicative.ofAdd w) : G) ∈ C := by
      intro w hw
      set u := eβ.symm (Multiplicative.ofAdd w) with hu
      have huQ : θ * (u : G) * θ⁻¹ ∈ QK := (Subgroup.mem_normalizer_iff.1 hθQK _).1 u.2
      have h5 : β ⟨θ * (u : G) * θ⁻¹, huQ⟩ = β u := by
        have hβu : β u = Multiplicative.ofAdd w := eβ.apply_symm_apply _
        apply Multiplicative.toAdd.injective
        funext i
        rw [hβe ⟨θ, hθK⟩ u ⟨θ * (u : G) * θ⁻¹, huQ⟩ rfl i, hβu]
        exact hw i
      have h6 : (⟨θ * (u : G) * θ⁻¹, huQ⟩ : ↥QK) = u := hβi h5
      have h7 : θ * (u : G) * θ⁻¹ = u := congrArg Subtype.val h6
      rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
      calc (u : G) * θ = θ * (u : G) * θ⁻¹ * θ := by rw [h7]
        _ = θ * u := by group
    have hcard4 : 4 ≤ Nat.card ↥(C ⊓ QK) := by
      set Fx := {v : Fin 3 → F // g.mulVec v = v}
      have h5 : Nat.card (Fx × Fx) = 4 := by rw [Nat.card_prod, hfix]
      rw [← h5]
      refine Nat.card_le_card_of_injective
        (fun p => ⟨eβ.symm (Multiplicative.ofAdd ![p.1.1, p.2.1]),
        hfixed _ (by rw [Fin.forall_fin_two]; exact ⟨by simpa using p.1.2, by simpa using p.2.2⟩),
        (eβ.symm (Multiplicative.ofAdd ![p.1.1, p.2.1])).2⟩) ?_
      intro p q hpq
      have h6 : eβ.symm (Multiplicative.ofAdd ![p.1.1, p.2.1]) =
          eβ.symm (Multiplicative.ofAdd ![q.1.1, q.2.1]) := by
        apply Subtype.ext
        have := congrArg (fun x : ↥(C ⊓ QK) => (x : G)) hpq
        simpa using this
      have h7 := congrArg Multiplicative.toAdd (eβ.symm.injective h6)
      simp only [toAdd_ofAdd] at h7
      have h8 := congrFun h7 0
      have h9 := congrFun h7 1
      simp at h8 h9
      exact Prod.ext (Subtype.ext h8) (Subtype.ext h9)
    have h5 := Subgroup.card_mul_index (C.subgroupOf QK)
    rw [hQK64] at h5
    have h6 : Nat.card ↥(C.subgroupOf QK) = Nat.card ↥(C ⊓ QK) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h6] at h5
    have h7 : C.relIndex QK = (C.subgroupOf QK).index := rfl
    rw [h7]
    nlinarith
  calc C.relIndex R ≤ C.relIndex (R ⊓ K) := h1
    _ ≤ 8 * C.relIndex (pCoreOf 2 K) := h2
    _ ≤ 8 * C.relIndex QK := Nat.mul_le_mul_left _ h3
    _ ≤ 8 * 16 := Nat.mul_le_mul_left _ h4

end CFSG.Quasithin.H13.Sec77
