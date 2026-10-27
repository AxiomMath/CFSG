module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

section ZModCoordinates

variable {p : ℕ} [hp : Fact p.Prime] {a : ℕ}

theorem zmod_prime_pow_pred_mul_eq_zero_iff (ha : 1 ≤ a) (s : ZMod (p ^ a)) :
    ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) * s = 0 ↔
      ∃ u : ZMod (p ^ a), s = (p : ZMod (p ^ a)) * u := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpa : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val s, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    have h' : p ^ (a - 1) * p ∣ p ^ (a - 1) * s.val := by rw [← hpa]; exact h
    have h1 : p ∣ s.val :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hp.out.pos _)).mp h'
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    rw [← ZMod.natCast_zmod_val s, hk, Nat.cast_mul]
  · rintro ⟨u, rfl⟩
    rw [← mul_assoc, ← Nat.cast_mul, ← hpa, ZMod.natCast_self, zero_mul]

theorem zmod_prime_mul_eq_zero_iff (ha : 1 ≤ a) (s : ZMod (p ^ a)) :
    (p : ZMod (p ^ a)) * s = 0 ↔
      ∃ u : ZMod (p ^ a), s = ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) * u := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpa : p ^ a = p * p ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val s, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    have h' : p * p ^ (a - 1) ∣ p * s.val := by rw [← hpa]; exact h
    have h1 : p ^ (a - 1) ∣ s.val := (Nat.mul_dvd_mul_iff_left hp.out.pos).mp h'
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    rw [← ZMod.natCast_zmod_val s, hk, Nat.cast_mul]
  · rintro ⟨u, rfl⟩
    rw [← mul_assoc, ← Nat.cast_mul, ← hpa, ZMod.natCast_self, zero_mul]

end ZModCoordinates

section Homocyclic

variable {p : ℕ} {a : ℕ}

theorem multiplicative_pow_eq_one_iff (c : Multiplicative (ZMod (p ^ a))) (m : ℕ) :
    c ^ m = 1 ↔ (m : ZMod (p ^ a)) * Multiplicative.toAdd c = 0 := by
  rw [← nsmul_eq_mul, ← toAdd_pow, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff]

variable {Q : Type*} [CommGroup Q]
  (e : Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))
include e

theorem homocyclic_pow_eq_one_iff (x : Q) (m : ℕ) :
    x ^ m = 1 ↔ (m : ZMod (p ^ a)) * Multiplicative.toAdd (e x).1 = 0 ∧
      (m : ZMod (p ^ a)) * Multiplicative.toAdd (e x).2 = 0 := by
  rw [← multiplicative_pow_eq_one_iff, ← multiplicative_pow_eq_one_iff, ← Prod.pow_fst,
    ← Prod.pow_snd, ← map_pow, ← Prod.mk_eq_one, Prod.mk.eta]
  exact (MulEquiv.map_eq_one_iff e).symm

theorem homocyclic_pow_prime_pow_eq_one (x : Q) : x ^ p ^ a = 1 := by
  rw [homocyclic_pow_eq_one_iff e, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul,
    zero_mul]
  exact ⟨rfl, rfl⟩

theorem homocyclic_isPGroup : IsPGroup p Q := fun x => ⟨a, homocyclic_pow_prime_pow_eq_one e x⟩

theorem homocyclic_pow_pred_eq_one_iff [Fact p.Prime] (ha : 1 ≤ a) (x : Q) :
    x ^ p ^ (a - 1) = 1 ↔ ∃ y : Q, x = y ^ p := by
  constructor
  · intro hx
    rw [homocyclic_pow_eq_one_iff e] at hx
    obtain ⟨u₁, hu₁⟩ := (zmod_prime_pow_pred_mul_eq_zero_iff ha _).mp hx.1
    obtain ⟨u₂, hu₂⟩ := (zmod_prime_pow_pred_mul_eq_zero_iff ha _).mp hx.2
    refine ⟨e.symm (Multiplicative.ofAdd u₁, Multiplicative.ofAdd u₂), ?_⟩
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_fst, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← hu₁]
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_snd, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← hu₂]
  · rintro ⟨y, rfl⟩
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel ha]
    exact homocyclic_pow_prime_pow_eq_one e y

theorem homocyclic_pow_eq_one_iff_exists [Fact p.Prime] (ha : 1 ≤ a) (w : Q) :
    w ^ p = 1 ↔ ∃ y : Q, w = y ^ p ^ (a - 1) := by
  constructor
  · intro hw
    rw [homocyclic_pow_eq_one_iff e] at hw
    obtain ⟨u₁, hu₁⟩ := (zmod_prime_mul_eq_zero_iff ha _).mp hw.1
    obtain ⟨u₂, hu₂⟩ := (zmod_prime_mul_eq_zero_iff ha _).mp hw.2
    refine ⟨e.symm (Multiplicative.ofAdd u₁, Multiplicative.ofAdd u₂), ?_⟩
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_fst, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← hu₁]
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_snd, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← hu₂]
  · rintro ⟨y, rfl⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha]
    exact homocyclic_pow_prime_pow_eq_one e y

end Homocyclic

@[expose] def autRestrict {G : Type*} [Group G] (K : Subgroup G)
    (hK : ∀ (α : MulAut G) (x : G), x ∈ K → α x ∈ K) : MulAut G →* MulAut K where
  toFun α :=
    { toFun := fun x => ⟨α x, hK α x x.2⟩
      invFun := fun x => ⟨α⁻¹ x, hK α⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self G α x)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self G α x)
      map_mul' := fun x y => Subtype.ext (map_mul α (x : G) (y : G)) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem autRestrict_apply {G : Type*} [Group G] (K : Subgroup G)
    (hK : ∀ (α : MulAut G) (x : G), x ∈ K → α x ∈ K) (α : MulAut G) (x : K) :
    ((autRestrict K hK α x : K) : G) = α x := rfl

theorem powMonoidHom_ker_invariant {G : Type*} [CommGroup G] (n : ℕ) (α : MulAut G) (x : G)
    (hx : x ∈ (powMonoidHom n : G →* G).ker) : α x ∈ (powMonoidHom n : G →* G).ker := by
  rw [MonoidHom.mem_ker, powMonoidHom_apply] at hx ⊢
  rw [← map_pow, hx, map_one]

@[expose] noncomputable def omegaAut {G : Type*} [CommGroup G] (n : ℕ) :
    MulAut G →* MulAut (powMonoidHom n : G →* G).ker :=
  autRestrict _ (powMonoidHom_ker_invariant n)

section Orders

variable {p : ℕ} [hp : Fact p.Prime] {a : ℕ} {Q : Type*} [CommGroup Q]
  (e : Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))
include e

theorem homocyclic_card : Nat.card Q = p ^ (2 * a) := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  change Nat.card (ZMod (p ^ a)) * Nat.card (ZMod (p ^ a)) = _
  rw [Nat.card_zmod, ← pow_add, two_mul]

theorem homocyclic_card_ker_pow_le (n : ℕ) (hn : 0 < n) :
    Nat.card (powMonoidHom n : Q →* Q).ker ≤ n ^ 2 := by
  classical
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set K := (powMonoidHom n : Multiplicative (ZMod (p ^ a)) →* _).ker with hK
  have hKcard : Nat.card K ≤ n := by
    have h1 := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ a))) hn
    calc Nat.card K = Nat.card {c : Multiplicative (ZMod (p ^ a)) // c ^ n = 1} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun c => by
            rw [hK, MonoidHom.mem_ker, powMonoidHom_apply])
      _ = (Finset.univ.filter fun c : Multiplicative (ZMod (p ^ a)) => c ^ n = 1).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ n := h1
  have hinj : Function.Injective fun x : (powMonoidHom n : Q →* Q).ker =>
      ((⟨(e x).1, by
          have hx := x.2
          rw [MonoidHom.mem_ker, powMonoidHom_apply] at hx
          rw [hK, MonoidHom.mem_ker, powMonoidHom_apply, ← Prod.pow_fst, ← map_pow, hx,
            map_one, Prod.fst_one]⟩ : K),
        (⟨(e x).2, by
          have hx := x.2
          rw [MonoidHom.mem_ker, powMonoidHom_apply] at hx
          rw [hK, MonoidHom.mem_ker, powMonoidHom_apply, ← Prod.pow_snd, ← map_pow, hx,
            map_one, Prod.snd_one]⟩ : K)) := by
    intro x y hxy
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
    exact Subtype.ext (e.injective (Prod.ext hxy.1 hxy.2))
  calc Nat.card (powMonoidHom n : Q →* Q).ker ≤ Nat.card (K × K) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card K * Nat.card K := Nat.card_prod _ _
    _ ≤ n * n := Nat.mul_le_mul hKcard hKcard
    _ = n ^ 2 := (sq n).symm

end Orders

theorem homocyclic_frattini_transport {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (ha : 1 ≤ a)
    {Q : Type*} [CommGroup Q]
    (e : Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))
    {H : Type*} [Group H] (ρ : H →* MulAut Q) :
    frattini Q = (powMonoidHom p : Q →* Q).range ∧
      ∃ θ : (Q ⧸ frattini Q) ≃* (powMonoidHom p : Q →* Q).ker,
        (∀ x : Q, (θ (x : Q ⧸ frattini Q) : Q) = x ^ p ^ (a - 1)) ∧
        Nat.card (Q ⧸ frattini Q) = p ^ 2 ∧ Nat.card (powMonoidHom p : Q →* Q).ker = p ^ 2 ∧
        (∀ (α : MulAut Q) (x : Q),
          (θ (α x : Q ⧸ frattini Q) : Q) = α (θ (x : Q ⧸ frattini Q))) ∧
        ((CFSG.SectionRank.Ccomm.autQuotient (frattini Q)).comp ρ).ker =
          ((omegaAut p).comp ρ).ker ∧
        Nonempty (((CFSG.SectionRank.Ccomm.autQuotient (frattini Q)).comp ρ).range ≃*
          ((omegaAut p).comp ρ).range) := by
  classical
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  have hQp : IsPGroup p Q := homocyclic_isPGroup e
  set B := (powMonoidHom p : Q →* Q).range with hB
  set Ω := (powMonoidHom p : Q →* Q).ker with hΩ
  have hkerB : (powMonoidHom (p ^ (a - 1)) : Q →* Q).ker = B := by
    ext x
    rw [MonoidHom.mem_ker, powMonoidHom_apply, homocyclic_pow_pred_eq_one_iff e ha, hB,
      MonoidHom.mem_range]
    simp only [powMonoidHom_apply, eq_comm]
  have hrangeΩ : (powMonoidHom (p ^ (a - 1)) : Q →* Q).range = Ω := by
    ext w
    rw [MonoidHom.mem_range, hΩ, MonoidHom.mem_ker, powMonoidHom_apply,
      homocyclic_pow_eq_one_iff_exists e ha]
    simp only [powMonoidHom_apply, eq_comm]
  have hΦ : frattini Q = B := by
    apply le_antisymm
    · have : Fact (IsPGroup p (Q ⧸ B)) := ⟨hQp.to_quotient B⟩
      have : IsElementaryAbelian p (Q ⧸ B) :=
        { toIsMulCommutative := ⟨⟨fun x y => mul_comm x y⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun q => by
            induction q using QuotientGroup.induction_on with
            | H x =>
              rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
              exact ⟨x, rfl⟩ }
      have h1 := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective B)
      rwa [CFSG.frattini_eq_bot_of_isElementaryAbelian (R := Q ⧸ B) (p := p),
        MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h1
    · rintro _ ⟨y, rfl⟩
      have : Fact (IsPGroup p Q) := ⟨hQp⟩
      exact CFSG.pth_power_mem_frattini_of_isPGroup y
  have hφmem : ∀ x : Q, (powMonoidHom (p ^ (a - 1)) : Q →* Q) x ∈ Ω := fun x => by
    rw [← hrangeΩ]
    exact ⟨x, rfl⟩
  set φ : Q →* Ω := (powMonoidHom (p ^ (a - 1)) : Q →* Q).codRestrict Ω hφmem with hφ
  have hφker : φ.ker = frattini Q := by
    rw [hΦ, ← hkerB]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ, ← Subtype.coe_inj]
    rfl
  have hφs : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    rw [← hrangeΩ] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  set θ : (Q ⧸ frattini Q) ≃* Ω := (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs) with hθdef
  have hθ : ∀ x : Q, (θ (x : Q ⧸ frattini Q) : Q) = x ^ p ^ (a - 1) := fun _ => rfl
  have hcardQ := homocyclic_card e
  have hprod := (powMonoidHom p : Q →* Q).ker.card_mul_index
  rw [Subgroup.index_ker] at hprod
  have hle1 := homocyclic_card_ker_pow_le e p hp.out.pos
  have hle2 := homocyclic_card_ker_pow_le e (p ^ (a - 1)) (pow_pos hp.out.pos _)
  rw [hkerB] at hle2
  have hΩcard : Nat.card Ω = p ^ 2 := by
    rw [hcardQ] at hprod
    have e2 : p ^ (2 * a) = p ^ 2 * (p ^ (a - 1)) ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [e2] at hprod
    by_contra hne
    have hlt : Nat.card Ω < p ^ 2 := lt_of_le_of_ne hle1 hne
    have : Nat.card Ω * Nat.card B < p ^ 2 * (p ^ (a - 1)) ^ 2 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hle2 (pow_pos (pow_pos hp.out.pos _) _)
    exact (ne_of_lt this) hprod
  have hquot : Nat.card (Q ⧸ frattini Q) = p ^ 2 := by
    rw [Nat.card_congr θ.toEquiv, hΩcard]
  have hequiv : ∀ (α : MulAut Q) (x : Q),
      (θ (α x : Q ⧸ frattini Q) : Q) = α (θ (x : Q ⧸ frattini Q)) := fun α x => by
    rw [hθ, hθ, map_pow]
  have hker : ((CFSG.SectionRank.Ccomm.autQuotient (frattini Q)).comp ρ).ker =
      ((omegaAut p).comp ρ).ker := by
    ext h
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h1
      refine MulEquiv.ext fun w => Subtype.ext ?_
      have hw : (w : Q) ∈ (powMonoidHom (p ^ (a - 1)) : Q →* Q).range := by
        rw [hrangeΩ]
        exact w.2
      obtain ⟨y, hy⟩ := hw
      have h2 := congrArg (fun f : MulAut (Q ⧸ frattini Q) => f (y : Q ⧸ frattini Q)) h1
      simp only [CFSG.SectionRank.Ccomm.autQuotient_mk, MulAut.one_apply] at h2
      have h3 := congrArg (fun q => (θ q : Q)) h2
      simp only [hθ] at h3
      change ρ h (w : Q) = (w : Q)
      rw [← hy, powMonoidHom_apply, map_pow, h3]
    · intro h1
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [CFSG.SectionRank.Ccomm.autQuotient_mk, MulAut.one_apply]
        apply θ.injective
        apply Subtype.ext
        rw [hθ, hθ, ← map_pow]
        have h2 := congrArg (fun f : MulAut Ω => ((f ⟨x ^ p ^ (a - 1), hφmem x⟩ : Ω) : Q)) h1
        simp only [MulAut.one_apply] at h2
        exact h2
  refine ⟨hΦ, θ, hθ, hquot, hΩcard, hequiv, hker, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange _))

end CFSG.Quasithin.H13.NQBlock
