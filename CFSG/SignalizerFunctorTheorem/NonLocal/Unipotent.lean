module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine

public section

open Module Module.End
open scoped commutatorElement
open Matrix

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {H X : Type*} [Group H]
  [Group X]

namespace ProjData

theorem pow_sub_one_eq_one_of_ker [Finite K] (P : ProjData K ι H X) (z : H) (hz : P.π z = 1) :
    z ^ (Nat.card K - 1) = 1 := by
  have := Fintype.ofFinite K
  obtain ⟨c, hc⟩ := (P.hker _).mp hz
  apply P.hρ
  apply Units.ext
  have hc1 : ((c : K)) ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
  rw [map_pow, Units.val_pow_eq_pow_val, hc, ← map_pow, hc1]
  simp

theorem not_dvd_card_ker [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r] (P : ProjData K ι H X)
    [Finite H] : ¬ r ∣ Nat.card P.π.ker := by
  have := Fintype.ofFinite K
  intro h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := P.π.ker) r h
  have h1 : (z : H) ^ (Nat.card K - 1) = 1 :=
    P.pow_sub_one_eq_one_of_ker z (MonoidHom.mem_ker.mp z.2)
  have h2 : r ∣ Nat.card K - 1 := by
    rw [← hz]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext h1)
  have hrq : r ∣ Nat.card K := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K r
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self r n.ne_zero
  have h3 : r ∣ 1 := by
    have h4 : 1 ≤ Nat.card K := Nat.card_pos
    have := Nat.dvd_sub hrq h2
    rwa [Nat.sub_sub_self h4] at this
  exact (Fact.out : r.Prime).one_lt.ne' (Nat.dvd_one.mp h3)

theorem ker_central (P : ProjData K ι H X) (z : H) (hz : P.π z = 1) (y : H) :
    z * y = y * z := by
  obtain ⟨c, hc⟩ := (P.hker _).mp hz
  apply P.hρ
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hc]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

end ProjData


theorem ProjData.eq_bot_of_isPGroup [Finite H] [Nonempty ι] [Finite K] {r : ℕ} [Fact r.Prime]
    [CharP K r] (P : ProjData K ι H X) {Γ : Type*} [Group Γ] (φH : Γ →* H)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g : Γ, ∀ n ∈ W, (P.ρ (φH g) : Matrix ι ι K) *ᵥ n ∈ W) → W = ⊥ ∨ W = ⊤)
    (V : Subgroup X) (hV : IsPGroup r V)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V) : V = ⊥ := by
  classical
  have : Finite X := Finite.of_surjective P.π P.hπ
  have hr : r.Prime := Fact.out
  let Vt : Subgroup H := V.comap P.π
  let π' : Vt →* V := (P.π.comp Vt.subtype).codRestrict V (fun h => h.2)
  have hπ'surj : Function.Surjective π' := by
    intro v
    obtain ⟨h, hh⟩ := P.hπ v
    exact ⟨⟨h, by simp [Vt, hh]⟩, Subtype.ext hh⟩
  let Zs : Subgroup Vt := π'.ker
  have hZsmem : ∀ y : Vt, y ∈ Zs ↔ P.π (y : H) = 1 := by
    intro y
    constructor
    · intro h; exact congrArg Subtype.val (MonoidHom.mem_ker.mp h)
    · intro h; exact MonoidHom.mem_ker.mpr (Subtype.ext h)
  have hcard : Nat.card Vt = Nat.card V * Nat.card Zs := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zs,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π' hπ'surj).toEquiv]
  have hZsr : ¬ r ∣ Nat.card Zs := by
    have h1 : Nat.card Zs = Nat.card P.π.ker := by
      refine Nat.card_congr
        (Equiv.ofBijective (fun z : Zs => (⟨(z : Vt).1, ?_⟩ : P.π.ker)) ⟨?_, ?_⟩)
      · exact (hZsmem z.1).mp z.2
      · intro a b hab
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      · intro w
        have hw := MonoidHom.mem_ker.mp w.2
        refine ⟨⟨⟨w.1, ?_⟩, (hZsmem _).mpr hw⟩, rfl⟩
        show P.π w.1 ∈ V
        rw [hw]; exact V.one_mem
    rw [h1]
    exact P.not_dvd_card_ker
  obtain ⟨b, hb⟩ := hV.exists_card_eq
  obtain ⟨S⟩ : Nonempty (Sylow r Vt) := inferInstance
  have hScard : Nat.card S = Nat.card V := by
    rw [S.card_eq_multiplicity, hcard, hb, Nat.factorization_mul (pow_pos hr.pos b).ne'
      Nat.card_pos.ne', Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hZsr, hr.factorization_self]
    simp
  have hq : ¬ r ∣ Nat.card K - 1 := by
    intro h
    have hrq : r ∣ Nat.card K := by
      have := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K r
      rw [Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self r n.ne_zero
    have h4 : 1 ≤ Nat.card K := Nat.card_pos
    have := Nat.dvd_sub hrq h
    rw [Nat.sub_sub_self h4] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have hSinj : Function.Injective (π'.comp (S : Subgroup Vt).subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs1 : (s : Vt) ∈ Zs := MonoidHom.mem_ker.mpr hs
    have hord : ∃ k, orderOf s = r ^ k := IsPGroup.iff_orderOf.mp S.isPGroup' s
    obtain ⟨k, hk⟩ := hord
    have h2 : orderOf (s : Vt) ∣ Nat.card K - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (P.pow_sub_one_eq_one_of_ker _ ((hZsmem _).mp hs1))
    have h3 : orderOf (s : Vt) = r ^ k := by
      rw [← hk]; exact (Subgroup.orderOf_coe s)
    rw [h3] at h2
    have hk0 : k = 0 := by
      by_contra hk0
      exact hq (dvd_trans (dvd_pow_self r hk0) h2)
    rw [hk0, pow_zero] at h3
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  have hSsurj : Function.Surjective (π'.comp (S : Subgroup Vt).subtype) := by
    have := (Function.Injective.bijective_of_nat_card_le hSinj (by rw [hScard])).2
    exact this
  have hSnormal : (S : Subgroup Vt).Normal := ⟨fun p hp y => by
    obtain ⟨p'', hp''⟩ := hSsurj (π' (y * p * y⁻¹))
    have hp''' : π' (p'' : Vt) = π' (y * p * y⁻¹) := hp''
    set c : Vt := y * p * y⁻¹ with hc
    have hz : c * (p'' : Vt)⁻¹ ∈ Zs := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp''', mul_inv_cancel]
    have hzc : ∀ w : Vt, (c * (p'' : Vt)⁻¹) * w = w * (c * (p'' : Vt)⁻¹) := fun w =>
      Subtype.ext (P.ker_central _ ((hZsmem _).mp hz) w.1)
    have hcomm : Commute (c * (p'' : Vt)⁻¹) (p'' : Vt) := hzc _
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨p, hp⟩
    obtain ⟨k', hk'⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' p''
    have hpk : p ^ (r ^ k) = 1 := by
      have := pow_orderOf_eq_one (⟨p, hp⟩ : S)
      rw [hk] at this
      exact congrArg Subtype.val this
    have hpk' : (p'' : Vt) ^ (r ^ k') = 1 := by
      have := pow_orderOf_eq_one p''
      rw [hk'] at this
      exact congrArg Subtype.val this
    have hcm : c ^ (r ^ (k + k')) = 1 := by
      rw [hc, conj_pow, pow_add, pow_mul, hpk]
      simp
    have hpm : (p'' : Vt) ^ (r ^ (k + k')) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hpk']
      simp
    have hzm : (c * (p'' : Vt)⁻¹) ^ (r ^ (k + k')) = 1 := by
      have h1 : c ^ (r ^ (k + k')) =
          (c * (p'' : Vt)⁻¹) ^ (r ^ (k + k')) * (p'' : Vt) ^ (r ^ (k + k')) := by
        have : c = (c * (p'' : Vt)⁻¹) * p'' := by group
        conv_lhs => rw [this]
        exact hcomm.mul_pow _
      rw [hcm, hpm, mul_one] at h1
      exact h1.symm
    have hzo : orderOf (c * (p'' : Vt)⁻¹) = 1 := by
      have h2 : orderOf (c * (p'' : Vt)⁻¹) ∣ r ^ (k + k') := orderOf_dvd_of_pow_eq_one hzm
      have h3 : orderOf (c * (p'' : Vt)⁻¹) ∣ Nat.card K - 1 := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext (P.pow_sub_one_eq_one_of_ker _ ((hZsmem _).mp hz))
      have hcop : Nat.Coprime (r ^ (k + k')) (Nat.card K - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hq)
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2
        (Nat.Coprime.coprime_dvd_right h3 hcop)) dvd_rfl
    have hz1 : c * (p'' : Vt)⁻¹ = 1 := orderOf_eq_one_iff.mp hzo
    have hcp : c = p'' := by
      calc c = (c * (p'' : Vt)⁻¹) * p'' := by group
        _ = p'' := by rw [hz1, one_mul]
    rw [hcp]
    exact p''.2⟩
  have hSchar : (S : Subgroup Vt).Characteristic := Sylow.characteristic_of_normal S hSnormal
  have hVtnorm : ∀ g : Γ, ∀ y ∈ Vt, φH g * y * (φH g)⁻¹ ∈ Vt := by
    intro g y hy
    show P.π (φH g * y * (φH g)⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hnorm g _ hy
  let conjG : Γ → (Vt ≃* Vt) := fun g =>
    { toFun := fun y => ⟨φH g * y * (φH g)⁻¹, hVtnorm g y y.2⟩
      invFun := fun y => ⟨(φH g)⁻¹ * y * φH g, by
        have := hVtnorm g⁻¹ y y.2
        simpa [map_inv] using this⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hSconj : ∀ (g : Γ) (p : Vt), p ∈ (S : Subgroup Vt) ↔ conjG g p ∈ (S : Subgroup Vt) := by
    intro g p
    have := hSchar.fixed (conjG g)
    constructor
    · intro hp
      have : p ∈ (S : Subgroup Vt).comap (conjG g).toMonoidHom := by rwa [this]
      exact this
    · intro hp
      have h2 : p ∈ (S : Subgroup Vt).comap (conjG g).toMonoidHom := hp
      rwa [this] at h2
  let W : Submodule K (ι → K) :=
    { carrier := {n | ∀ p : (S : Subgroup Vt), (P.ρ (p : Vt).1 : Matrix ι ι K) *ᵥ n = n}
      add_mem' := fun {a b} ha hb p => by rw [Matrix.mulVec_add, ha p, hb p]
      zero_mem' := fun p => by simp
      smul_mem' := fun c a ha p => by rw [Matrix.mulVec_smul, ha p] }
  have hWinv : ∀ g : Γ, ∀ n ∈ W, (P.ρ (φH g) : Matrix ι ι K) *ᵥ n ∈ W := by
    intro g n hn p
    have hp' : conjG g⁻¹ (p : Vt) ∈ (S : Subgroup Vt) := (hSconj g⁻¹ p).mp p.2
    have h1 := hn ⟨conjG g⁻¹ (p : Vt), hp'⟩
    have h2 : (P.ρ (p : Vt).1 : Matrix ι ι K) * (P.ρ (φH g) : Matrix ι ι K) =
        (P.ρ (φH g) : Matrix ι ι K) * (P.ρ (conjG g⁻¹ (p : Vt)).1 : Matrix ι ι K) := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
      congr 2
      simp [conjG, mul_assoc]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec]
    show (P.ρ (φH g) : Matrix ι ι K) *ᵥ ((P.ρ (conjG g⁻¹ (p : Vt)).1 : Matrix ι ι K) *ᵥ n) =
      (P.ρ (φH g) : Matrix ι ι K) *ᵥ n
    rw [h1]
  let _ : MulAction (S : Subgroup Vt) (ι → K) :=
    { smul := fun p n => (P.ρ (p : Vt).1 : Matrix ι ι K) *ᵥ n
      one_smul := fun n => by
        show (P.ρ ((1 : (S : Subgroup Vt)) : Vt).1 : Matrix ι ι K) *ᵥ n = n
        simp
      mul_smul := fun a b n => by
        show (P.ρ ((a * b : (S : Subgroup Vt)) : Vt).1 : Matrix ι ι K) *ᵥ n =
          (P.ρ (a : Vt).1 : Matrix ι ι K) *ᵥ ((P.ρ (b : Vt).1 : Matrix ι ι K) *ᵥ n)
        simp [Matrix.mulVec_mulVec] }
  have hfix := IsPGroup.card_modEq_card_fixedPoints S.isPGroup' (ι → K)
  have hrK : r ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K r
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self r n.ne_zero
  have hdN : r ∣ Nat.card (ι → K) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
    exact dvd_pow hrK Fintype.card_ne_zero
  have hdfix : r ∣ Nat.card (MulAction.fixedPoints (S : Subgroup Vt) (ι → K)) :=
    (Nat.ModEq.dvd_iff hfix dvd_rfl).mp hdN
  have hex : ∃ n : ι → K, n ≠ 0 ∧ n ∈ W := by
    by_contra hno
    push Not at hno
    have h0 : (0 : ι → K) ∈ MulAction.fixedPoints (S : Subgroup Vt) (ι → K) :=
      fun p => by show (P.ρ (p : Vt).1 : Matrix ι ι K) *ᵥ 0 = 0; simp
    have : Nonempty (MulAction.fixedPoints (S : Subgroup Vt) (ι → K)) := ⟨⟨0, h0⟩⟩
    have : Subsingleton (MulAction.fixedPoints (S : Subgroup Vt) (ι → K)) :=
      ⟨fun a b => by
        have hz : ∀ c : MulAction.fixedPoints (S : Subgroup Vt) (ι → K), c.1 = 0 := by
          intro c
          by_contra h
          exact hno c.1 h (fun p => c.2 p)
        exact Subtype.ext ((hz a).trans (hz b).symm)⟩
    have h1 : Nat.card (MulAction.fixedPoints (S : Subgroup Vt) (ι → K)) = 1 := Nat.card_unique
    rw [h1] at hdfix
    exact hr.one_lt.ne' (Nat.dvd_one.mp hdfix)
  obtain ⟨n₀, hn₀, hW0⟩ := hex
  rcases hirr W hWinv with hbot | htop
  · exfalso
    rw [hbot] at hW0
    exact hn₀ ((Submodule.mem_bot K).mp hW0)
  · have hSbot : (S : Subgroup Vt) = ⊥ := by
      rw [eq_bot_iff]
      intro p hp
      have hρ1 : (P.ρ (p : Vt).1 : Matrix ι ι K) = 1 := by
        ext i j
        have hj : (Pi.single j (1 : K) : ι → K) ∈ W := by rw [htop]; exact Submodule.mem_top
        have h2 := congrFun (hj ⟨p, hp⟩) i
        simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.one_apply, eq_comm] using h2
      have h3 : (p : Vt).1 = 1 := P.hρ (Units.ext (by simpa using hρ1))
      exact (Subgroup.mem_bot).mpr (Subtype.ext h3)
    have hV1 : Nat.card V = 1 := by rw [← hScard, hSbot]; simp
    exact Subgroup.eq_bot_of_card_eq V hV1

end CFSG.SignalizerFunctorTheorem.NonLocal
