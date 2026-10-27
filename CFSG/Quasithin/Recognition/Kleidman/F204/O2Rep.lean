module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Coord
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Alg
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPU
public import CFSG.RankThree.PartOne.FTL.Frattini

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.OrderReductions.FrattiniAutomorphisms CFSG
  CFSG.QuasithinUnique.A5.Delta5

open scoped IsMulCommutative

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

instance instFactPGroupQ1 (L1 L2 S : Subgroup G) : Fact (IsPGroup 2 ↥(Q1 L1 L2 S)) :=
  ⟨pCoreOf_isPGroup 2 (P1 L1 L2 S)⟩

instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance instElemAbQ1 (L1 L2 S : Subgroup G) :
    IsElementaryAbelian 2 (↥(Q1 L1 L2 S) ⧸ frattini ↥(Q1 L1 L2 S)) :=
  isElementaryAbelian_quotient_frattini

abbrev UQ (L1 L2 S : Subgroup G) := Additive (↥(Q1 L1 L2 S) ⧸ frattini ↥(Q1 L1 L2 S))

instance instFiniteUQ (L1 L2 S : Subgroup G) : Module.Finite (ZMod 2) (UQ L1 L2 S) :=
  Module.Finite.of_finite

@[expose] def mu (q : ↥(Q1 L1 L2 S)) : UQ L1 L2 S := Additive.ofMul (QuotientGroup.mk q)

theorem mu_mul (a b : ↥(Q1 L1 L2 S)) : mu (a * b) = mu a + mu b := by
  simp [mu, QuotientGroup.mk_mul, ofMul_mul]

theorem mu_one : mu (1 : ↥(Q1 L1 L2 S)) = 0 := by
  simp [mu]

theorem mu_inv (a : ↥(Q1 L1 L2 S)) : mu a⁻¹ = - mu a := by
  simp [mu, QuotientGroup.mk_inv, ofMul_inv]

theorem mu_surj : Function.Surjective (mu (L1 := L1) (L2 := L2) (S := S)) := by
  intro u
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul u)
  exact ⟨q, by simp [mu, hq]⟩

theorem mu_eq_zero_iff (q : ↥(Q1 L1 L2 S)) : mu q = 0 ↔ q ∈ frattini ↥(Q1 L1 L2 S) := by
  unfold mu
  rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]

theorem mu_eq_iff (a b : ↥(Q1 L1 L2 S)) : mu a = mu b ↔ a⁻¹ * b ∈ frattini ↥(Q1 L1 L2 S) := by
  have : mu a = mu b ↔ mu (a⁻¹ * b) = 0 := by
    rw [mu_mul, mu_inv, neg_add_eq_zero]
  rw [this, mu_eq_zero_iff]

@[expose] noncomputable def toLE (L1 L2 S : Subgroup G) :
    MulAut (↥(Q1 L1 L2 S) ⧸ frattini ↥(Q1 L1 L2 S)) →* (UQ L1 L2 S ≃ₗ[ZMod 2] UQ L1 L2 S) where
  toFun φ := (MulEquiv.toAdditive φ).toLinearEquiv
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x)
  map_one' := by
    ext x
    rfl
  map_mul' φ ψ := by
    ext x
    rfl

@[expose] noncomputable def theta (L1 L2 S : Subgroup G) :
    ↥(P1 L1 L2 S) →* (UQ L1 L2 S ≃ₗ[ZMod 2] UQ L1 L2 S) :=
  (toLE L1 L2 S).comp ((quotientAutomorphism (frattini ↥(Q1 L1 L2 S))).comp
    ((Q1 L1 L2 S).normalizerMonoidHom.comp
      (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S))))

theorem theta_mu (g : ↥(P1 L1 L2 S)) (q : ↥(Q1 L1 L2 S)) (h : (g : G) * q * (g : G)⁻¹ ∈ Q1 L1 L2 S) :
    theta L1 L2 S g (mu q) = mu ⟨(g : G) * q * (g : G)⁻¹, h⟩ := by
  show Additive.ofMul (quotientAutomorphism (frattini ↥(Q1 L1 L2 S))
      ((Q1 L1 L2 S).normalizerMonoidHom (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) g))
      (QuotientGroup.mk q)) = _
  have h1 := quotientAutomorphism_apply (frattini ↥(Q1 L1 L2 S))
    ((Q1 L1 L2 S).normalizerMonoidHom (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) g)) q
  have h2 : ((Q1 L1 L2 S).normalizerMonoidHom (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) g))
      q = ⟨(g : G) * q * (g : G)⁻¹, h⟩ := Subtype.ext rfl
  rw [h2] at h1
  show Additive.ofMul (QuotientGroup.mk' _ q |> quotientAutomorphism (frattini ↥(Q1 L1 L2 S))
      ((Q1 L1 L2 S).normalizerMonoidHom (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) g))) = _
  rw [h1]
  rfl

theorem theta_mem_conj (g : ↥(P1 L1 L2 S)) (q : ↥(Q1 L1 L2 S)) :
    (g : G) * q * (g : G)⁻¹ ∈ Q1 L1 L2 S := by
  have := (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S g.2) (q : G)).mp q.2
  exact this

theorem theta_apply (g : ↥(P1 L1 L2 S)) (q : ↥(Q1 L1 L2 S)) :
    theta L1 L2 S g (mu q) = mu ⟨(g : G) * q * (g : G)⁻¹, theta_mem_conj g q⟩ :=
  theta_mu g q _

theorem Q1_mem_P1 {q : G} (hq : q ∈ Q1 L1 L2 S) : q ∈ P1 L1 L2 S :=
  pCoreOf_le 2 (P1 L1 L2 S) hq

theorem theta_Q1 {q0 : G} (hq0 : q0 ∈ Q1 L1 L2 S) :
    theta L1 L2 S ⟨q0, Q1_mem_P1 hq0⟩ = 1 := by
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨q, rfl⟩ := mu_surj u
  rw [theta_apply]
  have e : (⟨(q0 : G) * q * (q0 : G)⁻¹, theta_mem_conj ⟨q0, Q1_mem_P1 hq0⟩ q⟩ : ↥(Q1 L1 L2 S))
      = (⟨q0, hq0⟩ : ↥(Q1 L1 L2 S)) * q * (⟨q0, hq0⟩ : ↥(Q1 L1 L2 S))⁻¹ := rfl
  show mu _ = mu q
  simp only
  rw [e, mu_mul, mu_mul, mu_inv]
  abel

section Rel

variable (F : Frame L1 L2 S D X)
include F

theorem theta_rel {x0 a : G} (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (ha : a ∈ S) (haa : a * a = 1)
    (haQ : a ∉ Q1 L1 L2 S) :
    theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ ^ 5 = 1 ∧
      theta L1 L2 S ⟨a, F.mem_P1_of_mem_S ha⟩ * theta L1 L2 S ⟨a, F.mem_P1_of_mem_S ha⟩ = 1 ∧
      theta L1 L2 S ⟨a, F.mem_P1_of_mem_S ha⟩ * theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ *
        theta L1 L2 S ⟨a, F.mem_P1_of_mem_S ha⟩ =
        theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ ^ 4 := by
  set X0 : ↥(P1 L1 L2 S) := ⟨x0, F.mem_P1_of_mem_X hx0⟩ with hX0
  set A0 : ↥(P1 L1 L2 S) := ⟨a, F.mem_P1_of_mem_S ha⟩ with hA0
  have hX05 : X0 ^ 5 = 1 := Subtype.ext (by simpa using hx05)
  have hA0A0 : A0 * A0 = 1 := Subtype.ext (by simpa using haa)
  have hA0i : A0⁻¹ = A0 := inv_eq_of_mul_eq_one_right hA0A0
  have hX5 : theta L1 L2 S X0 ^ 5 = 1 := by rw [← map_pow, hX05, map_one]
  have hAA : theta L1 L2 S A0 * theta L1 L2 S A0 = 1 := by rw [← map_mul, hA0A0, map_one]
  refine ⟨hX5, hAA, ?_⟩
  obtain ⟨q, hq, hrel⟩ := F.inv_of_involution ha (by rw [haa]; exact (Q1 L1 L2 S).one_mem) haQ hx0
  set Qe : ↥(P1 L1 L2 S) := ⟨q, Q1_mem_P1 hq⟩ with hQe
  have hrel' : A0 * X0 * A0⁻¹ = X0⁻¹ * Qe := Subtype.ext (by simpa using hrel)
  have h1 := congrArg (theta L1 L2 S) hrel'
  have hAi : (theta L1 L2 S A0)⁻¹ = theta L1 L2 S A0 := inv_eq_of_mul_eq_one_right hAA
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, theta_Q1 hq, mul_one, hAi] at h1
  have hX4 : (theta L1 L2 S X0)⁻¹ = theta L1 L2 S X0 ^ 4 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hX5
  rw [← hX4]
  exact h1

theorem theta_x_ne {x0 : G} (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1) :
    ∃ u, theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ u ≠ u := by
  by_contra hcon
  push Not at hcon
  set X0 : ↥(P1 L1 L2 S) := ⟨x0, F.mem_P1_of_mem_X hx0⟩ with hX0
  set τ : MulAut ↥(Q1 L1 L2 S) := (Q1 L1 L2 S).normalizerMonoidHom
    (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) X0) with hτ
  have hX05 : X0 ^ 5 = 1 := Subtype.ext (by simpa using hx05)
  have hτ5 : τ ^ 5 = 1 := by
    have : τ = ((Q1 L1 L2 S).normalizerMonoidHom.comp
      (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S))) X0 := rfl
    rw [this, ← map_pow, hX05, map_one]
  have hτq : ∀ q : ↥(Q1 L1 L2 S), ((τ q : ↥(Q1 L1 L2 S)) : G) = x0 * q * x0⁻¹ := fun q => rfl
  have htriv : quotientAutomorphism (frattini ↥(Q1 L1 L2 S)) τ = 1 := by
    ext v
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 := hcon (mu q)
    rw [theta_apply] at h1
    have h2 : (⟨x0 * q * x0⁻¹, theta_mem_conj X0 q⟩ : ↥(Q1 L1 L2 S)) = τ q := Subtype.ext rfl
    rw [h2] at h1
    have h3 : (QuotientGroup.mk (τ q) : ↥(Q1 L1 L2 S) ⧸ frattini ↥(Q1 L1 L2 S)) =
        QuotientGroup.mk q := by
      have := congrArg Additive.toMul h1
      simpa [mu] using this
    show quotientAutomorphism (frattini ↥(Q1 L1 L2 S)) τ (QuotientGroup.mk' _ q) =
      (QuotientGroup.mk' _ q)
    rw [quotientAutomorphism_apply]
    exact h3
  have hτ1 : τ = 1 := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini (q := 2)
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hτ5 (by norm_num) htriv
  have hcent : x0 ∈ Subgroup.centralizer ((Q1 L1 L2 S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun m : MulAut ↥(Q1 L1 L2 S) => ((m ⟨h, hh⟩ : ↥(Q1 L1 L2 S)) : G)) hτ1
    simp only [hτq] at this
    have h' : x0 * h * x0⁻¹ = h := by simpa using this
    calc h * x0 = (x0 * h * x0⁻¹) * x0 := by rw [h']
      _ = x0 * h := by group
  have hx0Q : x0 ∈ Q1 L1 L2 S := F.charTwo_P1 ⟨F.mem_P1_of_mem_X hx0, hcent⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (P1 L1 L2 S) ⟨x0, hx0Q⟩
  have hk' : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨hk', hx05⟩
  rw [hg, pow_one] at this
  exact hx01 this

abbrev R0Q (L1 L2 S : Subgroup G) : Subgroup ↥(Q1 L1 L2 S) := (Q2 L1 L2 S).subgroupOf (Q1 L1 L2 S)

theorem card_Q1_quot_R0 : Nat.card (↥(Q1 L1 L2 S) ⧸ R0Q L1 L2 S) = 4 := by
  have hN : Q1 L1 L2 S ≤ Subgroup.normalizer ((Q2 L1 L2 S : Subgroup G) : Set G) := fun q hq =>
    P2_le_normalizer_Q2 L1 L2 S (Q1_mem_P2 F hq)
  have h1 := F1.relIndex_sup_eq_of_le_normalizer hN
  rw [Q1_sup_Q2 F, relIndex_Q2_S F] at h1
  rw [← Subgroup.index]
  exact h1.symm

theorem frattini_le_R0Q : frattini ↥(Q1 L1 L2 S) ≤ R0Q L1 L2 S := by
  obtain ⟨φ, hφk, T, hT4, hTin, -, -⟩ := exists_phi_Q1 F
  set φQ : ↥(Q1 L1 L2 S) →* Alt5 := φ.comp (Subgroup.inclusion
    (fun q hq => (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (Q1_le_B F hq))) with hφQ
  have hker : R0Q L1 L2 S = φQ.ker := by
    ext q
    rw [MonoidHom.mem_ker]
    exact (hφk ⟨(q : G), Q1_mem_P2 F q.2⟩).symm
  have hTq : ∀ q : ↥(Q1 L1 L2 S), φQ q ∈ T := fun q => hTin _ q.2
  have hsq : ∀ q : ↥(Q1 L1 L2 S), φQ q * φQ q = 1 := fun q => alt5_klein_sq hT4 (hTq q)
  have hcomm : ∀ q q' : ↥(Q1 L1 L2 S), φQ q * φQ q' = φQ q' * φQ q := by
    intro q q'
    have h := hsq (q * q')
    rw [map_mul] at h
    have e : φQ q * φQ q' = (φQ q * φQ q')⁻¹ := by
      rw [eq_comm, inv_eq_iff_mul_eq_one]; exact h
    calc φQ q * φQ q' = (φQ q * φQ q')⁻¹ := e
      _ = φQ q' * φQ q := by
        rw [mul_inv_rev]
        have h1 : (φQ q)⁻¹ = φQ q := by rw [inv_eq_iff_mul_eq_one]; exact hsq q
        have h2 : (φQ q')⁻¹ = φQ q' := by rw [inv_eq_iff_mul_eq_one]; exact hsq q'
        rw [h1, h2]
  rw [hker, frattini_eq_closure_commutator_union_powers (p := 2)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ (hc | ⟨x, rfl⟩)
  · have : _root_.commutator ↥(Q1 L1 L2 S) ≤ φQ.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g1 _ g2 _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h1 := hcomm g1 g2
      calc φQ g1 * φQ g2 * (φQ g1)⁻¹ * (φQ g2)⁻¹ = (φQ g1 * φQ g2) * ((φQ g1)⁻¹ * (φQ g2)⁻¹) := by
            group
        _ = (φQ g2 * φQ g1) * ((φQ g1)⁻¹ * (φQ g2)⁻¹) := by rw [h1]
        _ = 1 := by group
    exact this hc
  · show x ^ 2 ∈ φQ.ker
    rw [MonoidHom.mem_ker, map_pow, pow_two]
    exact hsq x

variable {Z : Subgroup G} (hZ : ZData L1 L2 S Z)
include hZ

theorem Z2_mem_P1 {a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) : a ∈ P1 L1 L2 S :=
  F.mem_P1_of_mem_S (F.Q2_le_S (F.Z2_le_Q2 hZ ha))

theorem finrank_range_theta_le {a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) :
    Module.finrank (ZMod 2) (LinearMap.range (((theta L1 L2 S ⟨a, Z2_mem_P1 F hZ ha⟩ :
      UQ L1 L2 S ≃ₗ[ZMod 2] UQ L1 L2 S) : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) -
        LinearMap.id)) ≤ 2 := by
  classical
  set t := theta L1 L2 S ⟨a, Z2_mem_P1 F hZ ha⟩ with ht
  set c : ↥(Q1 L1 L2 S) → UQ L1 L2 S := fun q => t (mu q) - mu q with hc
  have hrange : ((LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id) :
      Submodule (ZMod 2) (UQ L1 L2 S)) : Set (UQ L1 L2 S)) = Set.range c := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨q, rfl⟩ := mu_surj v
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨mu q, rfl⟩
  have hconst : ∀ q r : ↥(Q1 L1 L2 S), r ∈ R0Q L1 L2 S → c (q * r) = c q := by
    intro q r hr
    have hr2 : (r : G) ∈ Q2 L1 L2 S := hr
    have hcomm : a * (r : G) = (r : G) * a := F.Z2_comm hZ a ha r hr2
    have hconj : (⟨a * (r : G) * a⁻¹, theta_mem_conj ⟨a, Z2_mem_P1 F hZ ha⟩ r⟩ : ↥(Q1 L1 L2 S)) =
        r := Subtype.ext (by
      show a * (r : G) * a⁻¹ = r
      rw [hcomm]; group)
    have htr : t (mu r) = mu r := by
      rw [ht, theta_apply]
      show mu ⟨a * (r : G) * a⁻¹, _⟩ = mu r
      rw [hconj]
    simp only [hc, mu_mul, map_add, htr]
    abel
  have hcard : Nat.card (Set.range c) ≤ 4 := by
    let g : (↥(Q1 L1 L2 S) ⧸ R0Q L1 L2 S) → Set.range c :=
      Quotient.lift (fun q => (⟨c q, q, rfl⟩ : Set.range c)) (by
        intro q q' h
        have h1 : q⁻¹ * q' ∈ R0Q L1 L2 S := QuotientGroup.leftRel_apply.mp h
        have e : q' = q * (q⁻¹ * q') := by group
        apply Subtype.ext
        show c q = c q'
        rw [e, hconst q _ h1])
    have hg : Function.Surjective g := by
      rintro ⟨_, q, rfl⟩
      exact ⟨(q : ↥(Q1 L1 L2 S) ⧸ R0Q L1 L2 S), rfl⟩
    have := Nat.card_le_card_of_surjective g hg
    rw [card_Q1_quot_R0 F] at this
    exact this
  have hcard' : Nat.card (LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) -
      LinearMap.id)) ≤ 4 := by
    have : Nat.card (LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id)) =
        Nat.card (Set.range c) := by
      rw [← hrange]
      rfl
    rw [this]; exact hcard
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id))
  rw [Nat.card_zmod] at hpow
  rw [hpow] at hcard'
  by_contra hcon
  have h3 : 3 ≤ Module.finrank (ZMod 2) (LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) -
      LinearMap.id)) := by omega
  have : 2 ^ 3 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.range ((t : UQ L1 L2 S →ₗ[ZMod 2]
      UQ L1 L2 S) - LinearMap.id)) := Nat.pow_le_pow_right (by norm_num) h3
  omega

omit F hZ in
theorem mem_span_mu_image (R : Subgroup ↥(Q1 L1 L2 S)) {u : UQ L1 L2 S}
    (hu : u ∈ Submodule.span (ZMod 2) (mu '' (R : Set ↥(Q1 L1 L2 S)))) : ∃ r ∈ R, u = mu r := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨r, hr, rfl⟩ := hx; exact ⟨r, hr, rfl⟩
  | zero => exact ⟨1, R.one_mem, (mu_one).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨r1, hr1, rfl⟩ := hx
    obtain ⟨r2, hr2, rfl⟩ := hy
    exact ⟨r1 * r2, R.mul_mem hr1 hr2, (mu_mul r1 r2).symm⟩
  | smul c x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    have hc : c = 0 ∨ c = 1 := by
      revert c; decide
    rcases hc with rfl | rfl
    · exact ⟨1, R.one_mem, by rw [zero_smul, mu_one]⟩
    · exact ⟨r, hr, by rw [one_smul]⟩

theorem mem_Q2_of_fix {x0 a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1) (q : ↥(Q1 L1 L2 S))
    (hq : mu q ∈ O2Alg.fixSub (theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩)) : (q : G) ∈ Q2 L1 L2 S := by
  classical
  have haS : a ∈ S := F.Q2_le_S (F.Z2_le_Q2 hZ ha)
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  obtain ⟨hx5, htt, htx⟩ := theta_rel F hx0 hx05 haS haa haQ
  have hrk := finrank_range_theta_le F hZ ha
  have hne := theta_x_ne F hx0 hx05 hx01
  obtain ⟨hfix, -, hrk2⟩ := O2Alg.K_main _ _ hx5 htt htx hrk hne
  set t := theta L1 L2 S ⟨a, F.mem_P1_of_mem_S haS⟩ with ht
  set x := theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ with hx
  set W0 : Submodule (ZMod 2) (UQ L1 L2 S) :=
    Submodule.span (ZMod 2) (mu '' (R0Q L1 L2 S : Set ↥(Q1 L1 L2 S))) with hW0
  have htmuR : ∀ r : ↥(Q1 L1 L2 S), r ∈ R0Q L1 L2 S → t (mu r) = mu r := by
    intro r hr
    have hr2 : (r : G) ∈ Q2 L1 L2 S := hr
    have hcomm : a * (r : G) = (r : G) * a := F.Z2_comm hZ a ha r hr2
    have hconj : (⟨a * (r : G) * a⁻¹, theta_mem_conj ⟨a, F.mem_P1_of_mem_S haS⟩ r⟩ :
        ↥(Q1 L1 L2 S)) = r := Subtype.ext (by
      show a * (r : G) * a⁻¹ = r
      rw [hcomm]; group)
    rw [ht, theta_apply]
    show mu ⟨a * (r : G) * a⁻¹, _⟩ = mu r
    rw [hconj]
  have hKer : W0 ≤ LinearMap.ker ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id) := by
    rw [hW0, Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    show (t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) (mu r) - mu r = 0
    rw [LinearEquiv.coe_coe, htmuR r hr, sub_self]
  have hcardW : Nat.card (UQ L1 L2 S ⧸ W0) ≤ 4 := by
    let g : (↥(Q1 L1 L2 S) ⧸ R0Q L1 L2 S) → UQ L1 L2 S ⧸ W0 :=
      Quotient.lift (fun q => Submodule.Quotient.mk (mu q)) (by
        intro q q' h
        have h1 : q⁻¹ * q' ∈ R0Q L1 L2 S := QuotientGroup.leftRel_apply.mp h
        have e : q' = q * (q⁻¹ * q') := by group
        show (Submodule.Quotient.mk (mu q) : UQ L1 L2 S ⧸ W0) = Submodule.Quotient.mk (mu q')
        rw [e, mu_mul, Submodule.Quotient.mk_add]
        have : (Submodule.Quotient.mk (mu (q⁻¹ * q')) : UQ L1 L2 S ⧸ W0) = 0 :=
          (Submodule.Quotient.mk_eq_zero W0).mpr (Submodule.subset_span ⟨_, h1, rfl⟩)
        rw [this, add_zero])
    have hg : Function.Surjective g := by
      intro v
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective W0 v
      obtain ⟨q, rfl⟩ := mu_surj u
      exact ⟨(q : ↥(Q1 L1 L2 S) ⧸ R0Q L1 L2 S), rfl⟩
    have := Nat.card_le_card_of_surjective g hg
    rw [card_Q1_quot_R0 F] at this
    exact this
  have hfrW : Module.finrank (ZMod 2) (UQ L1 L2 S ⧸ W0) ≤ 2 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := UQ L1 L2 S ⧸ W0)
    rw [Nat.card_zmod] at hpow
    rw [hpow] at hcardW
    by_contra hcon
    have h3 : 3 ≤ Module.finrank (ZMod 2) (UQ L1 L2 S ⧸ W0) := by omega
    have : 2 ^ 3 ≤ 2 ^ Module.finrank (ZMod 2) (UQ L1 L2 S ⧸ W0) :=
      Nat.pow_le_pow_right (by norm_num) h3
    omega
  have h1 := Submodule.finrank_quotient_add_finrank W0
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id)
  have hWeq : W0 = LinearMap.ker ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id) :=
    Submodule.eq_of_le_of_finrank_le hKer (by omega)
  have hqker : mu q ∈ LinearMap.ker ((t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) - LinearMap.id) := by
    have h := hfix (mu q) hq
    show (t : UQ L1 L2 S →ₗ[ZMod 2] UQ L1 L2 S) (mu q) - mu q = 0
    rw [LinearEquiv.coe_coe, h, sub_self]
  rw [← hWeq] at hqker
  obtain ⟨r, hr, hqr⟩ := mem_span_mu_image (R0Q L1 L2 S) hqker
  have hfr : q⁻¹ * r ∈ frattini ↥(Q1 L1 L2 S) := (mu_eq_iff q r).mp hqr
  have hR : q⁻¹ * r ∈ R0Q L1 L2 S := frattini_le_R0Q F hfr
  have hqR : q ∈ R0Q L1 L2 S := by
    have := (R0Q L1 L2 S).mul_mem hr ((R0Q L1 L2 S).inv_mem hR)
    simpa using this
  exact hqR

omit hZ in
theorem theta_D_rel {x0 d : G} (hx0 : x0 ∈ X) (hd : d ∈ D) :
    theta L1 L2 S ⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ ^ 3 = 1 ∧
      theta L1 L2 S ⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ *
        theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ =
      theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩ *
        theta L1 L2 S ⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ := by
  constructor
  · rw [← map_pow]
    have : (⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ : ↥(P1 L1 L2 S)) ^ 3 = 1 :=
      Subtype.ext (by simpa using pow_three_of_mem_D F hd)
    rw [this, map_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (F.D_cent hd) x0 hx0).symm)

theorem theta_d_nontrivial {x0 a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    ∃ u, theta L1 L2 S ⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ u + u ∉
      O2Alg.fixSub (theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q, hq, hqQ2⟩ : ∃ q ∈ Q1 L1 L2 S, q ∉ Q2 L1 L2 S := by
    by_contra h
    push Not at h
    exact not_Q1_le_Q2 F h
  set D0 : ↥(P1 L1 L2 S) := ⟨d, (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)⟩ with hD0
  set q0 : ↥(Q1 L1 L2 S) := ⟨q, hq⟩ with hq0
  have h1 := hcon (mu q0)
  rw [theta_apply] at h1
  have hmem : ((⟨d * q * d⁻¹, theta_mem_conj D0 q0⟩ : ↥(Q1 L1 L2 S)) * q0⁻¹ : ↥(Q1 L1 L2 S)) =
      ⟨d * q * d⁻¹ * q⁻¹, (Q1 L1 L2 S).mul_mem (theta_mem_conj D0 q0) ((Q1 L1 L2 S).inv_mem hq)⟩ :=
    rfl
  have h2 : mu ((⟨d * q * d⁻¹, theta_mem_conj D0 q0⟩ : ↥(Q1 L1 L2 S)) * q0⁻¹) ∈
      O2Alg.fixSub (theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩) := by
    rw [mu_mul, mu_inv]
    rw [O2Alg.neg_eq_self']
    exact h1
  have := mem_Q2_of_fix F hZ ha haQ hx0 hx05 hx01 _ h2
  rw [hmem] at this
  exact hqQ2 (F.fpf hd hd1 (F.Q1_le_S hq) this)

theorem exists_y0 {x0 a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1) :
    ∃ y0 ∈ Frame.Z2 L1 L2 S Z, y0 ∈ Q1 L1 L2 S ∧ x0⁻¹ * y0 * x0 ∉ Q2 L1 L2 S := by
  by_contra hcon
  push Not at hcon
  have haS : a ∈ S := F.Q2_le_S (F.Z2_le_Q2 hZ ha)
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  have haP : a ∈ P1 L1 L2 S := F.mem_P1_of_mem_S haS
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  obtain ⟨hx5, htt, htx⟩ := theta_rel F hx0 hx05 haS haa haQ
  set x := theta L1 L2 S ⟨x0, hx0P⟩ with hx
  set t := theta L1 L2 S ⟨a, haP⟩ with ht
  have hconj : x * t * x ^ 4 = theta L1 L2 S ⟨x0 * a * x0⁻¹, (P1 L1 L2 S).mul_mem
      ((P1 L1 L2 S).mul_mem hx0P haP) ((P1 L1 L2 S).inv_mem hx0P)⟩ := by
    have hX0 : (⟨x0, hx0P⟩ : ↥(P1 L1 L2 S)) ^ 5 = 1 := Subtype.ext (by simpa using hx05)
    have hxi : x ^ 4 = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hx5
    rw [hxi, hx, ht, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hH : ∀ u, (x * t * x ^ 4) (t u + u) = t u + u := by
    intro u
    obtain ⟨q, rfl⟩ := mu_surj u
    have hqP : (q : G) ∈ P2 L1 L2 S := Q1_mem_P2 F q.2
    have hyq : a * (q : G) * a⁻¹ * (q : G)⁻¹ ∈ Q1 L1 L2 S :=
      (Q1 L1 L2 S).mul_mem (theta_mem_conj ⟨a, haP⟩ q) ((Q1 L1 L2 S).inv_mem q.2)
    have hyZ : a * (q : G) * a⁻¹ * (q : G)⁻¹ ∈ Frame.Z2 L1 L2 S Z := by
      have h1 : (q : G) * a⁻¹ * (q : G)⁻¹ ∈ Frame.Z2 L1 L2 S Z :=
        Z2_norm hqP ((Frame.Z2 L1 L2 S Z).inv_mem ha)
      have := (Frame.Z2 L1 L2 S Z).mul_mem ha h1
      simpa [mul_assoc] using this
    have hR := hcon _ hyZ hyq
    set yE : ↥(Q1 L1 L2 S) := ⟨a * (q : G) * a⁻¹ * (q : G)⁻¹, hyq⟩ with hyE
    have hsum : t (mu q) + mu q = mu yE := by
      rw [ht, theta_apply]
      have : (⟨a * (q : G) * a⁻¹, theta_mem_conj ⟨a, haP⟩ q⟩ : ↥(Q1 L1 L2 S)) * q⁻¹ = yE := rfl
      rw [← this, mu_mul, mu_inv, O2Alg.neg_eq_self']
    rw [hsum, hconj, theta_apply]
    have hcomm : (x0 * a * x0⁻¹) * (a * (q : G) * a⁻¹ * (q : G)⁻¹) =
        (a * (q : G) * a⁻¹ * (q : G)⁻¹) * (x0 * a * x0⁻¹) := by
      have h1 : a * (x0⁻¹ * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * x0) =
          (x0⁻¹ * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * x0) * a := F.Z2_comm hZ a ha _ hR
      calc (x0 * a * x0⁻¹) * (a * (q : G) * a⁻¹ * (q : G)⁻¹)
          = x0 * (a * (x0⁻¹ * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * x0)) * x0⁻¹ := by group
        _ = x0 * ((x0⁻¹ * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * x0) * a) * x0⁻¹ := by rw [h1]
        _ = (a * (q : G) * a⁻¹ * (q : G)⁻¹) * (x0 * a * x0⁻¹) := by group
    have hfix : (⟨(x0 * a * x0⁻¹) * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * (x0 * a * x0⁻¹)⁻¹,
        theta_mem_conj ⟨x0 * a * x0⁻¹, (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).mul_mem hx0P haP)
          ((P1 L1 L2 S).inv_mem hx0P)⟩ yE⟩ : ↥(Q1 L1 L2 S)) = yE := Subtype.ext (by
      show (x0 * a * x0⁻¹) * (a * (q : G) * a⁻¹ * (q : G)⁻¹) * (x0 * a * x0⁻¹)⁻¹ =
        a * (q : G) * a⁻¹ * (q : G)⁻¹
      rw [hcomm]; group)
    rw [hfix]
  have hall := O2Alg.K_prime x t hx5 htt htx hH
  obtain ⟨u, hu⟩ := theta_x_ne F hx0 hx05 hx01
  exact hu (hall u)

end Rel

end CFSG.Quasithin.Kleidman.F204
