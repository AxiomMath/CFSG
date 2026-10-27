module

public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139L42
public import CFSG.Quasithin.H13.NQCoreP134Setup
public import CFSG.Quasithin.Background.E6ElevenComp

public section

namespace CFSG.Quasithin.H13.L139

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def InnerOn (K : Subgroup G) (t ℓ : G) : Prop :=
  ℓ ∈ K ∧ ∀ x ∈ K, (t * x * t⁻¹)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ pCoreOf 2 K

abbrev piK (K : Subgroup G) : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)

theorem mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ piK K x = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [show y = x from Subtype.ext hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem conj_mem {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) {x : G}
    (hx : x ∈ K) : t * x * t⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp ht x).mp hx

theorem InnerOn.pi_conj {K : Subgroup G} {t ℓ : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (h : InnerOn K t ℓ) (x : ↥K) :
    piK K ⟨t * x * t⁻¹, conj_mem ht x.2⟩ = piK K ⟨ℓ, h.1⟩ * piK K x * (piK K ⟨ℓ, h.1⟩)⁻¹ := by
  have h1 := (mem_pCoreOf_iff (K := K)
    ((⟨t * x * t⁻¹, conj_mem ht x.2⟩ : ↥K)⁻¹ * (⟨ℓ, h.1⟩ * x * (⟨ℓ, h.1⟩ : ↥K)⁻¹))).mp (h.2 x x.2)
  rw [map_mul, map_inv, map_mul, map_mul, map_inv] at h1
  exact inv_mul_eq_one.mp h1

theorem eq_one_of_forall_commute {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥) {a : Q}
    (h : ∀ b : Q, a * b = b * a) : a = 1 := by
  have : a ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun b => (h b).symm
  rwa [hZ, Subgroup.mem_bot] at this

section Hom

variable {K R : Subgroup G} (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
  (hR : R ≤ Subgroup.normalizer (K : Set G)) (hin : ∀ t ∈ R, ∃ ℓ, InnerOn K t ℓ)

include hR in
theorem innerOn_unique (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) {t ℓ ℓ' : G} (htR : t ∈ R)
    (h : InnerOn K t ℓ) (h' : InnerOn K t ℓ') : piK K ⟨ℓ, h.1⟩ = piK K ⟨ℓ', h'.1⟩ := by
  have hc : ∀ x : ↥K, piK K ⟨ℓ, h.1⟩ * piK K x * (piK K ⟨ℓ, h.1⟩)⁻¹ =
      piK K ⟨ℓ', h'.1⟩ * piK K x * (piK K ⟨ℓ', h'.1⟩)⁻¹ := fun x =>
    (h.pi_conj (hR htR) x).symm.trans (h'.pi_conj (hR htR) x)
  have h1 := eq_one_of_forall_commute hZ (a := (piK K ⟨ℓ', h'.1⟩)⁻¹ * piK K ⟨ℓ, h.1⟩) fun b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) b
    have := hc x
    calc (piK K ⟨ℓ', h'.1⟩)⁻¹ * piK K ⟨ℓ, h.1⟩ * piK K x
        = (piK K ⟨ℓ', h'.1⟩)⁻¹ * (piK K ⟨ℓ, h.1⟩ * piK K x * (piK K ⟨ℓ, h.1⟩)⁻¹) *
          piK K ⟨ℓ, h.1⟩ := by group
      _ = (piK K ⟨ℓ', h'.1⟩)⁻¹ * (piK K ⟨ℓ', h'.1⟩ * piK K x * (piK K ⟨ℓ', h'.1⟩)⁻¹) *
          piK K ⟨ℓ, h.1⟩ := by rw [this]
      _ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) x * ((piK K ⟨ℓ', h'.1⟩)⁻¹ * piK K ⟨ℓ, h.1⟩) := by
          group
  rw [inv_mul_eq_one] at h1
  exact h1.symm

@[expose] noncomputable def innerRep (t : ↥R) : G := Classical.choose (hin t t.2)

theorem innerRep_spec (t : ↥R) : InnerOn K t (innerRep hin t) := Classical.choose_spec (hin t t.2)

@[expose] noncomputable def innerVal (t : ↥R) : ↥K ⧸ CFSG.pCore 2 ↥K :=
  piK K ⟨innerRep hin t, (innerRep_spec hin t).1⟩

include hR in
theorem innerVal_conj (t : ↥R) (x : ↥K) :
    innerVal hin t * piK K x * (innerVal hin t)⁻¹ =
      piK K ⟨(t : G) * x * (t : G)⁻¹, conj_mem (hR t.2) x.2⟩ :=
  ((innerRep_spec hin t).pi_conj (hR t.2) x).symm

include hR hZ in
theorem innerVal_of_mem (t : ↥R) (htK : (t : G) ∈ K) : innerVal hin t = piK K ⟨t, htK⟩ := by
  have hself : InnerOn K t t := ⟨htK, fun x _ => by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  exact innerOn_unique hR hZ t.2 (innerRep_spec hin t) hself

include hR hZ in
theorem innerVal_mul (t t' : ↥R) : innerVal hin (t * t') = innerVal hin t * innerVal hin t' := by
  obtain ⟨hℓ, hcon⟩ := innerRep_spec hin t
  obtain ⟨hℓ', hcon'⟩ := innerRep_spec hin t'
  set ℓ := innerRep hin t
  set ℓ' := innerRep hin t'
  have hO : ∀ y ∈ pCoreOf 2 K, (t : G) * y * (t : G)⁻¹ ∈ pCoreOf 2 K := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hR t.2)) y).mp hy
  have hprod : InnerOn K ((t * t' : ↥R) : G) (ℓ * ℓ') := by
    refine ⟨K.mul_mem hℓ hℓ', fun x hx => ?_⟩
    have h1 := hcon' x hx
    have h2 := hcon (ℓ' * x * ℓ'⁻¹) (K.mul_mem (K.mul_mem hℓ' hx) (K.inv_mem hℓ'))
    have h3 := hO _ h1
    have h4 := (pCoreOf 2 K).mul_mem h3 h2
    convert h4 using 1
    simp only [Subgroup.coe_mul]
    group
  have := innerOn_unique hR hZ (t * t').2 (innerRep_spec hin (t * t')) hprod
  rw [innerVal, this]
  rfl

@[expose] noncomputable def innerHom : ↥R →* ↥K ⧸ CFSG.pCore 2 ↥K where
  toFun := innerVal hin
  map_one' := by
    have : innerVal hin 1 = piK K ⟨1, K.one_mem⟩ :=
      innerVal_of_mem hZ hR hin 1 K.one_mem
    rw [this]
    exact map_one _
  map_mul' := innerVal_mul hZ hR hin

end Hom

theorem center_GL4 : Subgroup.center L42.GL4 = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  have hu : u = 1 := by
    have h : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
    exact h u
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem center_eq_bot_of_mulEquiv {Q : Type*} [Group Q] (e : Q ≃* L42.GL4) :
    Subgroup.center Q = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center L42.GL4 := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [center_GL4, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (hx'.trans (map_one e).symm)

theorem card_eq_64 {k m : ℕ} (h : 2 ^ k * m = 20160) (hm : ¬ 2 ∣ m) : 2 ^ k = 64 := by
  have hk : k ≤ 14 := by
    by_contra hk
    have h1 : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h; omega
    have h3 : 2 ^ k ≤ 2 ^ k * m := Nat.le_mul_of_pos_right _ h2
    omega
  interval_cases k <;> omega

variable [Finite G]

theorem l42_false {T X P K : Subgroup G} (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    (hX9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X) (hP3 : IsPGroup 3 P)
    (hP9 : Nat.card P = 9) (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ K)
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* L42.GL4) (hin : ∀ t ∈ T, ∃ ℓ, InnerOn K t ℓ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := center_eq_bot_of_mulEquiv e
  set π := piK K with hπ
  set ι := innerHom hZ hTK hin with hι
  have hPK : P ≤ K := hPX.trans hXK
  obtain ⟨hpX, hSyl⟩ := NQCore.sylow_of_card_eq_relIndex hX (p := 3) (by norm_num) hPX hP3
    (hP9.trans hX9.symm)
  have hS : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo hT le_top
  have hmul := NQCore.mul_subset_of_sylow hS le_top hX (by norm_num) hpX hSyl
  have hirr := NQCore.irr_of_sylow hS le_top hX (by norm_num) hpX hSyl
  have hPab : ⁅P, P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥P)
      (by rw [hP9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    have h' : a * b = b * a := congrArg Subtype.val h
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h'
  set S : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := ι.range with hSdef
  set PK : Subgroup ↥K := P.subgroupOf K with hPKdef
  set Pb : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := PK.map π with hPbdef
  have hcardQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 := by
    rw [Nat.card_congr e.toEquiv, L42.card_GL4]
  have hιK : ∀ (t : ↥T) (htK : (t : G) ∈ K), ι t = π ⟨t, htK⟩ := fun t htK =>
    innerVal_of_mem hZ hTK hin t htK
  have hS64 : 36 < Nat.card S := by
    have hsyl : IsSylowTwoOf (T ⊓ K) K := by
      have hKn : (K.subgroupOf (K ⊔ T)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
        exact sup_le Subgroup.le_normalizer hTK
      exact E6.isSylowTwoOf_inf_of_subnormal' (isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right)
        le_sup_left hKn.isSubnormal
    set M : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((T ⊓ K).subgroupOf K).map π with hM
    have hMS : M ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1⟩, ?_⟩
      exact hιK ⟨x, hx.1⟩ x.2
    have hM2 : IsPGroup 2 M := by
      have h2 : IsPGroup 2 ((T ⊓ K).subgroupOf K) :=
        hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      exact h2.map π
    have hMidx : ¬ 2 ∣ M.index := fun h =>
      hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
    obtain ⟨k, hk⟩ := hM2.exists_card_eq
    have hcm := M.card_mul_index
    rw [hk, hcardQ] at hcm
    have h64 := card_eq_64 hcm hMidx
    have := Subgroup.card_le_of_le hMS
    omega
  have hPb9 : Nat.card Pb = 9 := by
    have hinj : Function.Injective (π.comp PK.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx2 : ((x : ↥K) : G) ∈ pCoreOf 2 K := (mem_pCoreOf_iff (x : ↥K)).mpr hx
      have hx3 : ((x : ↥K) : G) ∈ P := x.2
      have h2 : IsPGroup 2 ↥(pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
      obtain ⟨m, hm⟩ := h2 ⟨_, hx2⟩
      obtain ⟨n, hn⟩ := hP3 ⟨_, hx3⟩
      have hm' : ((x : ↥K) : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hn' : ((x : ↥K) : G) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h1 : ((x : ↥K) : G) = 1 := by
        have := pow_gcd_eq_one.mpr ⟨hm', hn'⟩
        rwa [show Nat.gcd (2 ^ m) (3 ^ n) = 1 from
          Nat.Coprime.pow m n (by norm_num), pow_one] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
    rw [hPbdef, show PK.map π = (π.comp PK.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype], MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top, hPKdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hP9]
  have hPS : ∀ s ∈ S, ∀ x ∈ Pb, ∃ y ∈ Pb, ∃ s' ∈ S, s * x = y * s' := by
    rintro _ ⟨t, rfl⟩ _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy, s₁, hs₁, htp⟩ := hmul t t.2 p hp
    have hyK : y ∈ K := hPK hy
    have htpK : (t : G) * p * (t : G)⁻¹ ∈ K := conj_mem (hTK t.2) p.2
    have hst : s₁ * (t : G)⁻¹ ∈ K := by
      have : s₁ * (t : G)⁻¹ = y⁻¹ * ((t : G) * p * (t : G)⁻¹) := by
        rw [show s₁ = y⁻¹ * ((t : G) * p) by rw [htp]; group]
        group
      rw [this]
      exact K.mul_mem (K.inv_mem hyK) htpK
    refine ⟨π ⟨y, hyK⟩, ⟨⟨y, hyK⟩, hy, rfl⟩, ι ⟨s₁, hs₁⟩, ⟨⟨s₁, hs₁⟩, rfl⟩, ?_⟩
    have h1 := innerVal_conj hTK hin t p
    have h2 := hιK (⟨s₁, hs₁⟩ * t⁻¹) hst
    have h3 : (⟨(t : G) * p * (t : G)⁻¹, htpK⟩ : ↥K) = ⟨y, hyK⟩ * ⟨s₁ * (t : G)⁻¹, hst⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, ← htp]
    have h4 : innerVal hin t * π p = π ⟨y, hyK⟩ * ι ⟨s₁, hs₁⟩ := by
      calc innerVal hin t * π p = (innerVal hin t * π p * (innerVal hin t)⁻¹) * innerVal hin t := by
            group
        _ = π ⟨y, hyK⟩ * π ⟨s₁ * (t : G)⁻¹, hst⟩ * innerVal hin t := by
            rw [h1, h3, map_mul]
        _ = π ⟨y, hyK⟩ * ι (⟨s₁, hs₁⟩ * t⁻¹) * innerVal hin t := by
            rw [h2]
            rfl
        _ = π ⟨y, hyK⟩ * ι ⟨s₁, hs₁⟩ := by
            rw [map_mul, map_inv]
            show π ⟨y, hyK⟩ * (ι ⟨s₁, hs₁⟩ * (innerVal hin t)⁻¹) * innerVal hin t = _
            group
    exact h4
  have hconjP : ∀ t : ↥T, (t : G) ∈ Subgroup.normalizer (P : Set G) →
      ∀ p : ↥K, (p : G) ∈ P → ι t * π p * (ι t)⁻¹ = π ⟨(t : G) * p * (t : G)⁻¹,
        conj_mem (hTK t.2) p.2⟩ := fun t _ p _ => innerVal_conj hTK hin t p
  have hirrb : ∀ U : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), U ≤ Pb →
      S ⊓ Subgroup.normalizer (Pb : Set _) ≤ Subgroup.normalizer (U : Set _) → U = ⊥ ∨ U = Pb := by
    intro U hUP hN
    set U' : Subgroup G := ((U.comap π).map K.subtype) ⊓ P with hU'
    have hmemU' : ∀ p : ↥K, (p : G) ∈ P → ((p : G) ∈ U' ↔ π p ∈ U) := by
      intro p hp
      constructor
      · rintro ⟨⟨q, hq, hqp⟩, -⟩
        rwa [show q = p from Subtype.ext hqp] at hq
      · intro h
        exact ⟨⟨p, h, rfl⟩, hp⟩
    have hιN : ∀ t : ↥T, (t : G) ∈ Subgroup.normalizer (P : Set G) →
        ι t ∈ S ⊓ Subgroup.normalizer (Pb : Set _) := by
      intro t htN
      have hfwd : ∀ u : ↥T, (u : G) ∈ Subgroup.normalizer (P : Set G) → ∀ z ∈ Pb,
          ι u * z * (ι u)⁻¹ ∈ Pb := by
        rintro u huN _ ⟨p, hp, rfl⟩
        rw [hconjP u huN p hp]
        exact ⟨_, (Subgroup.mem_normalizer_iff.mp huN p).mp hp, rfl⟩
      refine ⟨⟨t, rfl⟩, Subgroup.mem_normalizer_iff.mpr fun z => ⟨hfwd t htN z, fun hz => ?_⟩⟩
      have := hfwd t⁻¹ (inv_mem htN) _ hz
      rwa [map_inv, inv_inv, show (ι t)⁻¹ * (ι t * z * (ι t)⁻¹) * ι t = z by group] at this
    have hNU' : T ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U' : Set G) := by
      rintro t ⟨htT, htN⟩
      have hfwd : ∀ u : ↥T, (u : G) ∈ Subgroup.normalizer (P : Set G) → ∀ y ∈ U',
          (u : G) * y * (u : G)⁻¹ ∈ U' := by
        rintro u huN y ⟨⟨q, hq, rfl⟩, hyP⟩
        have hqP : ((q : ↥K) : G) ∈ P := hyP
        have hc := hconjP u huN q hqP
        have hU : ι u * π q * (ι u)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hN (hιN u huN)) _).mp hq
        rw [hc] at hU
        exact (hmemU' ⟨_, conj_mem (hTK u.2) q.2⟩
          ((Subgroup.mem_normalizer_iff.mp huN _).mp hqP)).mpr hU
      refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hfwd ⟨t, htT⟩ htN y, fun hy => ?_⟩
      have := hfwd (⟨t, htT⟩)⁻¹ (inv_mem htN) _ hy
      simp only [InvMemClass.coe_inv, inv_inv] at this
      rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at this
    rcases hirr U' (by rw [hPab]; exact bot_le) inf_le_right hNU' with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨p, hp, rfl⟩ := hUP hz
      have hpU' : (p : G) ∈ U' := (hmemU' p hp).mpr hz
      rw [h, hPab, Subgroup.mem_bot] at hpU'
      rw [Subgroup.mem_bot, show p = 1 from Subtype.ext hpU', map_one]
    · right
      refine le_antisymm hUP ?_
      rintro _ ⟨p, hp, rfl⟩
      have : (p : G) ∈ U' := by rw [h]; exact hp
      exact (hmemU' p hp).mp this
  have hS2 : IsPGroup 2 S := by
    rintro ⟨_, ⟨t, rfl⟩⟩
    obtain ⟨k, hk⟩ := hT.1 t
    exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hk, map_one]; rfl)⟩
  exact L42.fc1 e ⟨hPb9, hS2, hS64, hPS, hirrb⟩

end CFSG.Quasithin.H13.L139
