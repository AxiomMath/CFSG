module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagRee
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

namespace TableBExcSmallRest

section OutCyclic

variable {R : Type*} [Group R]

theorem subset_inn_of_pow_eq_one (hR : GGOutCyclic R) {D : Set (MulAut R)} {m p : ℕ}
    (hD : ∀ δ ∈ D, δ ^ m = 1) (hpm : Nat.Coprime p m) {X : Subgroup (MulAut R)}
    (hXI : (X : Set (MulAut R)) ⊆
      (Subgroup.closure (Set.range (MulAut.conj : R →* MulAut R) ∪ D) : Set (MulAut R)))
    (hX : ∀ χ ∈ X, χ ^ p = 1) :
    (X : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  set N := (MulAut.conj : R →* MulAut R).range with hN
  obtain ⟨φ₀, hφ₀⟩ := hR
  set Q := QuotientGroup.mk' N with hQ
  have hzp : ∀ α : MulAut R, Q α ∈ Subgroup.zpowers (Q φ₀) := by
    intro α
    have h1 : Q α ∈ (N ⊔ Subgroup.zpowers φ₀).map Q := Subgroup.mem_map_of_mem Q (hφ₀ α)
    rwa [Subgroup.map_sup, hQ, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers] at h1
  have hcomm : ∀ x y : MulAut R ⧸ N, Commute x y := by
    intro x y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hzp α)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hzp β)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow_self _ i j
  have hI : ∀ χ ∈ Subgroup.closure (Set.range (MulAut.conj : R →* MulAut R) ∪ D),
      Q χ ^ m = 1 := by
    intro χ hχ
    induction hχ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | hx
      · have : Q (MulAut.conj r) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨r, rfl⟩
        rw [this, one_pow]
      · rw [← map_pow, hD x hx, map_one]
    | one => rw [map_one, one_pow]
    | mul x y _ _ hx hy => rw [map_mul, (hcomm _ _).mul_pow, hx, hy, one_mul]
    | inv x _ hx => rw [map_inv, inv_pow, hx, inv_one]
  intro χ hχ
  have h1 : Q χ ^ m = 1 := hI χ (hXI hχ)
  have h2 : Q χ ^ p = 1 := by rw [← map_pow, hX χ hχ, map_one]
  have h3 : orderOf (Q χ) = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rwa [hpm.gcd_eq_one, Nat.dvd_one] at this
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨r, hr⟩ := h3
  exact ⟨r, hr⟩

end OutCyclic

section Diag

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
  {H : Subgroup (LargeEvenChevGL A K)}

theorem diagHom_pow_conj_mem {a : Fin r → Kˣ}
    (ha : ∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) (k : ℕ) :
    ∀ h ∈ H, TableB.diagHom A K a ^ k * h * (TableB.diagHom A K a ^ k)⁻¹ ∈ H := by
  induction k with
  | zero => intro h hh; simpa using hh
  | succ k ih =>
    intro h hh
    have e : TableB.diagHom A K a ^ (k + 1) * h * (TableB.diagHom A K a ^ (k + 1))⁻¹ =
        TableB.diagHom A K a * (TableB.diagHom A K a ^ k * h * (TableB.diagHom A K a ^ k)⁻¹) *
          (TableB.diagHom A K a)⁻¹ := by group
    rw [e]
    exact ha _ (ih h hh)

theorem isDiagOf_pow_apply {φ : MulAut (LargeEvenCenterQuot H)} {a : Fin r → Kˣ}
    (hφ : TableB.IsDiagOf H φ a) (k : ℕ) (h : H) :
    (φ ^ k) (LargeEvenCenterMk H h) = LargeEvenCenterMk H
      ⟨TableB.diagHom A K a ^ k * h * (TableB.diagHom A K a ^ k)⁻¹,
        diagHom_pow_conj_mem hφ.1 k h h.2⟩ := by
  induction k with
  | zero =>
    rw [pow_zero, MulAut.one_apply]
    congr 1
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hφ.2 _ (hφ.1 _ (diagHom_pow_conj_mem hφ.1 k h h.2))]
    congr 1
    exact Subtype.ext (by simp only [pow_succ']; group)

theorem pow_card_units_eq_one_of_mem_diagImage [Finite K] {φ : MulAut (LargeEvenCenterQuot H)}
    (hφ : φ ∈ LargeEvenChevDiagImage A K H) : φ ^ Nat.card Kˣ = 1 := by
  obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hφ
  have hd : TableB.diagHom A K a ^ Nat.card Kˣ = 1 := by
    rw [← map_pow]
    have : a ^ Nat.card Kˣ = 1 := funext fun i => by
      rw [Pi.pow_apply, Pi.one_apply, pow_card_eq_one']
    rw [this, map_one]
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    show (φ ^ Nat.card Kˣ) (LargeEvenCenterMk H h) = (1 : MulAut _) (LargeEvenCenterMk H h)
    rw [isDiagOf_pow_apply ha, MulAut.one_apply]
    congr 1
    exact Subtype.ext (by simp only [hd, one_mul, inv_one, mul_one])

end Diag

theorem dvd_of_largeEvenSplit_twF4 {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .twF4)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hs ⊢
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · exact absurd h id
  · exact h
  · rcases h with h | h <;> cases h
  · exact absurd (show n = 1 from hn) (by omega)

theorem coprime_of_dvd_two_pow_add_one {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) : Nat.Coprime p (2 ^ n - 1) := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : p ∣ 2 := by
    have e : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by omega
    rw [e] at hpn
    exact (Nat.dvd_add_right h).mp hpn
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst hp2
  have e : 2 ^ n + 1 = 2 * 2 ^ (n - 1) + 1 := by
    rw [← pow_succ']
    congr 2
    omega
  rw [e] at hpn
  have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_mul_right 2 _)).mp hpn
  omega

section TwF4


@[expose] def GGTwF4RankInput : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → p ∣ 2 ^ (2 * a + 1) + 1 →
    ∀ E : Subgroup (ReeTag.F4.reeGamma K a), IsElemAbelian p E → Nat.card E < p ^ 3

theorem nonempty_twF4_equiv {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃* ReeTag.F4.reeGamma K a) := by
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv K a
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma ha hK
  have e₂ : DerivedCentralQuotient (reeFixedGroup Tag.F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) ≃*
      DerivedCentralQuotient (ReeTag.F4.reeGamma K a) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  exact ⟨e₁.trans (e₂.trans E)⟩

theorem largeEvenLabelAll_card_lt_twF4 (hF : GGTwF4RankInput) {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hpn := dvd_of_largeEvenSplit_twF4 ht hlab hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨e⟩ := nonempty_twF4_equiv ha K hK
  have hZ := center_eq_bot_of_mulEquiv e (ReeTag.large_Ree_fixed_group_center_trivial _ K hK)
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hcop : Nat.Coprime p (Nat.card Kˣ) := by
    rw [Nat.card_units, hK, hna]
    exact coprime_of_dvd_two_pow_add_one hp (by omega) hpn
  have hXinn := subset_inn_of_pow_eq_one (ggOutCyclic_twF4 ha K hK)
    (D := LargeEvenChevDiagImage LargeEvenCartanF4 K (LargeEvenTwF4H ((n - 1) / 2) K))
    (fun δ hδ => pow_card_units_eq_one_of_mem_diagImage hδ) hcop hXI (fun χ hχ => hX.2 χ hχ)
  exact card_lt_of_subset_inn hZ (fun A hA => card_lt_of_mulEquiv e
    (fun E hE => hF _ ha K hK p hp (by rw [hna]; exact hpn) E hE) hA) hXinn hX

end TwF4

@[expose] def GGTitsThreeRankInput : Prop :=
  ∀ E : Subgroup CFSG.Sporadic.Schreier.Tits.titsD, IsElemAbelian 3 E → Nat.card E < 3 ^ 3

theorem eq_three_of_largeEvenSplit_twF4der {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (ht : lab.tag = .twF4der) (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) :
    p = 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hs ⊢
  subst ht
  have hn : n = 1 := hlab.2.2
  subst hn
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h id
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  · rcases h with h | h <;> cases h
  · exact h

theorem largeEvenLabelAll_card_lt_twF4der
    (hT : GGTitsThreeRankInput) {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4der) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hp3 := eq_three_of_largeEvenSplit_twF4der hp ht hlab hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : n = 1 := hlab.2.2
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hm : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) := Finite.of_equiv _ e.symm.toEquiv
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4)
    (LargeEvenTwF4H 0 K)
  refine card_lt_of_subset_inn
    (center_eq_bot_of_mulEquiv e CFSG.Sporadic.Schreier.Tits.titsD_center)
    (fun A hA => card_lt_of_mulEquiv e (fun E hE => hT E hE) hA) (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end TableBExcSmallRest

end CFSG.StandardType
