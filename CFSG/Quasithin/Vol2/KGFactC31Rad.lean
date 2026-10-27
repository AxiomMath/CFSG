module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {A : Type} [Group A]

theorem exists_mem_normalizer_of_lt [Finite A] {R Q : Subgroup A} (hQ : IsPGroup 2 Q)
    (hRQ : R < Q) : ∃ q ∈ Q, q ∈ Subgroup.normalizer (R : Set A) ∧ q ∉ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
  have hRQle : R ≤ Q := le_of_lt hRQ
  have hlt : R.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply (lt_iff_le_not_ge.mp hRQ).2
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ R.subgroupOf Q := by rw [h]; trivial
    exact this
  obtain ⟨⟨q, hqQ⟩, hqN, hqR⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨q, hqQ, ?_, fun h => hqR (Subgroup.mem_subgroupOf.mpr h)⟩
  rw [Subgroup.mem_normalizer_iff] at hqN ⊢
  intro r
  constructor
  · intro hr
    have h1 := (hqN ⟨r, hRQle hr⟩).mp (Subgroup.mem_subgroupOf.mpr hr)
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro hr
    have hrQ : r ∈ Q := by
      have h1 : q * r * q⁻¹ ∈ Q := hRQle hr
      have : r = q⁻¹ * (q * r * q⁻¹) * q := by group
      rw [this]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hqQ) h1) hqQ
    have h1 := (hqN ⟨r, hrQ⟩).mpr (by rw [Subgroup.mem_subgroupOf]; simpa using hr)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1

variable {M₀ R M V : Subgroup A}

theorem eq_centralizer_of_isPGroup [Finite A] (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hM₀V : M₀ ≤ Subgroup.normalizer (V : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) (hRC : R ≤ Subgroup.centralizer (V : Set A))
    (hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A))) :
    R = Subgroup.centralizer (V : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Subgroup.centralizer (V : Set A) with hQ
  by_contra hne
  have hlt : R < Q := lt_of_le_of_ne hRC hne
  obtain ⟨q, hqQ, hqN, hqR⟩ := exists_mem_normalizer_of_lt hC2 hlt
  have hM₀Q : M₀ ≤ Subgroup.normalizer (Q : Set A) :=
    hM₀V.trans (normalizer_le_normalizer_centralizer V)
  have hle : M₀ ⊓ Q ≤ pCoreOf 2 M₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hM₀Q hm))
      (hC2.to_le inf_le_right)
  have hP : Q ⊓ Subgroup.normalizer (R : Set A) ≤
      CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
    rintro p ⟨hpQ, hpN⟩
    have hpM₀ : p ∈ Subgroup.normalizer (M₀ : Set A) := hMN (hNR hpN)
    refine ⟨hNR hpN, hpM₀, normalizer_le_normalizer_pCoreOf 2 M₀ hpM₀, fun x hx => hle ⟨?_, ?_⟩⟩
    · have h1 : p * x⁻¹ * p⁻¹ ∈ M₀ := (Subgroup.mem_normalizer_iff.mp hpM₀ _).mp (M₀.inv_mem hx)
      have h2 := M₀.mul_mem hx h1
      rwa [show x * (p * x⁻¹ * p⁻¹) = x * p * x⁻¹ * p⁻¹ by group] at h2
    · have h1 : x * p * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hM₀Q hx) p).mp hpQ
      exact Q.mul_mem h1 (Q.inv_mem hpQ)
  have hRP : R ≤ Q ⊓ Subgroup.normalizer (R : Set A) := le_inf hRC Subgroup.le_normalizer
  have heq := eq_of_isSylowTwoOf_le hsyl hRP hP (hC2.to_le inf_le_left)
  have hqP : q ∈ Q ⊓ Subgroup.normalizer (R : Set A) := ⟨hqQ, hqN⟩
  rw [heq] at hqP
  exact hqR hqP

theorem centralizer_eq_of_comm {U W : Subgroup A} (hUW : U ≤ W)
    (hWC : W ≤ Subgroup.centralizer (U : Set A))
    (hab : ∀ a ∈ Subgroup.centralizer (U : Set A), ∀ b ∈ Subgroup.centralizer (U : Set A),
      a * b = b * a) :
    Subgroup.centralizer (W : Set A) = Subgroup.centralizer (U : Set A) := by
  refine le_antisymm (Subgroup.centralizer_le hUW) fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact hab w (hWC hw) c hc

theorem false_of_normal_pGroup [Finite A] (hR : IsPGroup 2 ↥R)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {Q : Subgroup A} (hQ : IsPGroup 2 ↥Q)
    (hQN : Q ≤ Subgroup.normalizer (R : Set A))
    (hNQ : Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (Q : Set A))
    (hQR : ¬ Q ≤ R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrad := pCoreOf_normalizer_eq hR hMN hM₀R hsyl hNR
  apply hQR
  rw [← hrad]
  exact le_pCoreOf_of_le_normalizer 2 hQN hNQ hQ

theorem false_of_sylow_witness [Finite A] (hR : IsPGroup 2 ↥R)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {q : A}
    (hqN : q ∈ Subgroup.normalizer (R : Set A)) (hq2 : q * q ∈ R) (hqR : q ∉ R)
    (hcomm : ∀ m ∈ M₀, m * q * m⁻¹ * q⁻¹ ∈ R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR ⟨q * q, hq2⟩
  have hk' : q ^ 2 ^ (k + 1) = 1 := by
    have h1 : (q * q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hzq : IsPGroup 2 ↥(Subgroup.zpowers q) := fun ⟨g, hg⟩ => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k + 1, Subtype.ext ?_⟩
    show (q ^ i) ^ 2 ^ (k + 1) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  have hP2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers q) :=
    IsPGroup.to_sup_of_normal_left' hR hzq ((Subgroup.zpowers_le).mpr hqN)
  have hle : M₀ ⊓ R ≤ pCoreOf 2 M₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hM₀R hm))
      (hR.to_le inf_le_right)
  have hqM₀ : q ∈ Subgroup.normalizer (M₀ : Set A) := hMN (hNR hqN)
  have hqS : q ∈ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
    refine ⟨hNR hqN, hqM₀, normalizer_le_normalizer_pCoreOf 2 M₀ hqM₀,
      fun m hm => hle ⟨?_, hcomm m hm⟩⟩
    have h1 : q * m⁻¹ * q⁻¹ ∈ M₀ := (Subgroup.mem_normalizer_iff.mp hqM₀ _).mp (M₀.inv_mem hm)
    have h2 := M₀.mul_mem hm h1
    rwa [show m * (q * m⁻¹ * q⁻¹) = m * q * m⁻¹ * q⁻¹ by group] at h2
  have hPS : R ⊔ Subgroup.zpowers q ≤ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) :=
    sup_le hsyl.1 ((Subgroup.zpowers_le).mpr hqS)
  have heq := eq_of_isSylowTwoOf_le hsyl le_sup_left hPS hP2
  apply hqR
  have : q ∈ R ⊔ Subgroup.zpowers q := le_sup_right (a := R) (Subgroup.mem_zpowers q)
  rwa [heq] at this

@[expose] def sectionCent (R : Subgroup A) {q : A} (hq : q ∈ Subgroup.normalizer (R : Set A)) :
    Subgroup A where
  carrier := {g | g ∈ Subgroup.normalizer (R : Set A) ∧ g * q * g⁻¹ * q⁻¹ ∈ R}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
    have h1 : g * (h * q * h⁻¹ * q⁻¹) * g⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp hhq
    have : g * h * q * (g * h)⁻¹ * q⁻¹ = g * (h * q * h⁻¹ * q⁻¹) * g⁻¹ * (g * q * g⁻¹ * q⁻¹) := by
      group
    rw [this]
    exact R.mul_mem h1 hgq
  inv_mem' := by
    rintro g ⟨hg, hgq⟩
    refine ⟨Subgroup.inv_mem _ hg, ?_⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer (R : Set A) := Subgroup.inv_mem _ hg
    have h1 : g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hgi _).mp (R.inv_mem hgq)
    have h2 : q⁻¹ * (g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹) * q⁻¹⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hq) _).mp h1
    have : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ = q * (q⁻¹ * (g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹) * q⁻¹⁻¹) *
        q⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp hq _).mp h2

theorem le_of_perfect_of_relIndex_le [Finite A] {K H N : Subgroup A} (hKN : K ≤ N)
    (hperf : ⁅K, K⁆ = K) (hi : H.relIndex N ≤ 4) : K ≤ H := by
  set H' := H.subgroupOf N with hH'
  let φ : ↥N →* Equiv.Perm (↥N ⧸ H') := MulAction.toPermHom ↥N (↥N ⧸ H')
  have hsolv : Group.IsSolvable (Equiv.Perm (↥N ⧸ H')) :=
    Equiv.Perm.isSolvable (by rw [← Subgroup.index_eq_card]; exact hi)
  let ψ : ↥K →* Equiv.Perm (↥N ⧸ H') := φ.comp (Subgroup.inclusion hKN)
  have hcommK : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hperf]
  have hf : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have hcommR : commutator ↥ψ.range = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hf, ← Subgroup.map_commutator,
      ← commutator_def, hcommK]
  have hsub := subsingleton_of_perfect_solvable hcommR inferInstance
  intro k hk
  have hk1 : ψ ⟨k, hk⟩ = 1 := congrArg Subtype.val (Subsingleton.elim (ψ.rangeRestrict ⟨k, hk⟩) 1)
  have hker : Subgroup.inclusion hKN ⟨k, hk⟩ ∈ φ.ker := hk1
  rw [← Subgroup.normalCore_eq_ker] at hker
  have h2 := Subgroup.normalCore_le H' hker
  rw [hH', Subgroup.mem_subgroupOf] at h2
  exact h2

theorem orbSub_eq_of_zpowers [Finite A] {x y t : A} (hy : y ∈ Subgroup.zpowers x)
    (hx : x ∈ Subgroup.zpowers y) : orbSub y t = orbSub x t := by
  have key : ∀ {a b : A}, a ∈ Subgroup.zpowers b → orbSub a t ≤ orbSub b t := by
    intro a b hab
    rw [orbSub, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have hj : a ^ j ∈ Subgroup.zpowers b := Subgroup.pow_mem _ hab j
    rw [← mem_powers_iff_mem_zpowers] at hj
    obtain ⟨k, hk⟩ := hj
    have hk' : b ^ k = a ^ j := hk
    show a ^ j * t * (a ^ j)⁻¹ ∈ orbSub b t
    rw [← hk']
    exact conj_mem_orbSub b t k
  exact le_antisymm (key hy) (key hx)

theorem mem_zpowers_of_prime [Finite A] {x y : A} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := (Subgroup.zpowers_le).mpr hy
  have hdvd : orderOf y ∣ p := hx ▸ orderOf_dvd_of_mem_zpowers hy
  have hoy : orderOf y = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hoy, hx])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem bad_of_zpowers [Finite A] {x y t : A} (hy : y ∈ Subgroup.zpowers x)
    (hx : x ∈ Subgroup.zpowers y) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    x * t * x⁻¹ ≠ t ∧ ∀ j : ℕ, t * (x ^ j * t * x⁻¹ ^ j) = x ^ j * t * x⁻¹ ^ j * t := by
  refine ⟨fun h => hmove ?_, fun j => ?_⟩
  · have hxC : x ∈ Subgroup.centralizer ({t} : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      calc s * x = x * s * x⁻¹ * x := by rw [h]
        _ = x * s := by group
    have hyC := ((Subgroup.zpowers_le).mpr hxC) hy
    have := Subgroup.mem_centralizer_iff.mp hyC t rfl
    rw [← this, mul_inv_cancel_right]
  · have hj : x ^ j ∈ Subgroup.zpowers y := Subgroup.pow_mem _ hx j
    rw [← mem_powers_iff_mem_zpowers] at hj
    obtain ⟨k, hk⟩ := hj
    have hk' : y ^ k = x ^ j := hk
    have h1 := hcomm k
    rw [inv_pow, hk'] at h1
    rw [inv_pow]
    exact h1

theorem summand_of_card64 [Finite A] {M₀ R V : Subgroup A} (hV : Nat.card V ≤ 64) :
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k →
      k ≤ 2 := by
  intro m k hm _ h
  obtain ⟨-, -, -, -, -, β, hβ, -, -⟩ := h
  have hcard := Nat.card_le_card_of_surjective β hβ
  have hc : Nat.card (Multiplicative (Fin k → Fin m → ZMod 2)) = 2 ^ (k * m) := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card, ← pow_mul, mul_comm]
  rw [hc] at hcard
  by_contra hk
  have h2 : 2 ^ (3 * 3) ≤ 2 ^ (k * m) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) (by omega))
  omega

end CFSG.Quasithin.KGC31

end
