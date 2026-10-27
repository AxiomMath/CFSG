module

public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.RankThreeCoreUniqueness.Helpers (finite_perfectResidual_map_eq)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

@[expose] def TwoExc (p : ℕ) (T : Type) [Group T] : Prop :=
  LieModel T .twistedF4 0 2 p

structure FixedFacts (p : ℕ) {T : Type} [Group T] (α : MulAut T) : Prop where
  fieldAutT : FieldAutT p α
  nonLocalized : NonLocalized (fixRes α)
  pElements : ∀ x ∈ fixSub α, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ fixRes α
  twoElements : (∀ x ∈ fixSub α, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ fixRes α) ∨ TwoExc p T

theorem statedLieAdmissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

@[expose] def FixModel (t : StatedLieTag) (n f₀ : ℕ) {T : Type} [Group T] (α : MulAut T) : Prop :=
  LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f₀ ∨
    (t = .twistedF4 ∧ n = 0 ∧ f₀ = 1 ∧
      LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .Tits 0 2 1)

@[expose] def TagFixedFacts (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α₀ : MulAut T, α₀ ^ p = 1 → α₀ ∉ innerAut T → LocalRankAut p T α₀ → FixModel t n f₀ α₀ →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α →
      (∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ α * (α₀ ^ s)⁻¹ ∈ innerAut T) → FixedFacts p α

theorem admissible_of_fixModel {T : Type} [Group T] {t : StatedLieTag} {n f₀ : ℕ} {α : MulAut T}
    (h : FixModel t n f₀ α) :
    StatedLieAdmissible t n 2 f₀ ∨ (t = .twistedF4 ∧ n = 0 ∧ f₀ = 1) := by
  rcases h with h | ⟨ht, hn, hf1, -⟩
  · exact Or.inl (statedLieAdmissible_of_lieModel h)
  · exact Or.inr ⟨ht, hn, hf1⟩

theorem mem_zpowers_zpow_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a : G}
    (hap : a ^ p = 1) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : a ∈ Subgroup.zpowers (a ^ s) := by
  have hcop : IsCoprime s (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime s.natAbs p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hs (Int.natCast_dvd.mpr h)
    exact this
  obtain ⟨x, y, hxy⟩ := hcop
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨x, ?_⟩
  rw [← zpow_mul]
  have h1 : s * x = 1 - y * p := by linarith
  rw [h1, zpow_sub, zpow_one, mul_comm y, zpow_mul, zpow_natCast, hap, one_zpow, inv_one,
    mul_one]


theorem le_normalizer_of_conj_mem {X : Type*} [Group X] (C S : Subgroup X)
    (h : ∀ x ∈ C, ∀ s ∈ S, x * s * x⁻¹ ∈ S) : C ≤ Subgroup.normalizer (S : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (C.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem fixRes_le_fixSub {T : Type} [Group T] (α : MulAut T) : fixRes α ≤ fixSub α :=
  Subgroup.map_subtype_le _

section Generic

variable {T C : Type} [Group T] [Group C] [Finite T] [Finite C]

omit [Finite T] [Finite C] in
@[expose] noncomputable def fixIso (φ : T ≃* C) (α : MulAut T) :
    ↥(fixSub α) ≃* ↥(fixSub (MulAut.congr φ α)) :=
  (Subgroup.equivMapOfInjective (fixSub α) φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (fixSub_congr φ α).symm)

omit [Finite T] [Finite C] in
theorem coe_fixIso (φ : T ≃* C) (α : MulAut T) (y : ↥(fixSub α)) :
    ((fixIso φ α y : ↥(fixSub (MulAut.congr φ α))) : C) = φ (y : T) := rfl

omit [Finite T] [Finite C] in
theorem nonLocalized_of_map_eq {φ : T ≃* C} {W : Subgroup T} {N : Subgroup C}
    (h : W.map φ.toMonoidHom = N) (hN : NonLocalized N) : NonLocalized W := by
  intro S hS hsolv hle
  refine hN (S.map φ.toMonoidHom) ?_ ?_ ?_
  · intro hbot
    exact hS ((Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp hbot)
  · exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective).surjective
  · rw [← h]
    refine le_normalizer_of_conj_mem _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    refine ⟨x * s * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hle hx) s).mp hs

theorem pElement_mem_of_index_dvd_pow {G : Type*} [Group G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (N : Subgroup G) [N.Normal] {k : ℕ} (hk : N.index ∣ q ^ k)
    {x : G} (hx : ∃ j : ℕ, orderOf x = p ^ j) : x ∈ N := by
  obtain ⟨j, hj⟩ := hx
  have hne : N.index ≠ 0 := by
    intro h0
    rw [h0] at hk
    exact pow_ne_zero _ hq.ne_zero (Nat.eq_zero_of_zero_dvd hk)
  have : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero hne
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ p ^ j := hj ▸ orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ q ^ k :=
    (_root_.orderOf_dvd_natCard _).trans (by change N.index ∣ q ^ k; exact hk)
  have hcop : Nat.Coprime (p ^ j) (q ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes hp hq).mpr hpq)
  have h3 : orderOf (QuotientGroup.mk' N x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

omit [Finite C] in
theorem fixRes_map_congr (φ : T ≃* C) (α : MulAut T) :
    (fixRes α).map φ.toMonoidHom = fixRes (MulAut.congr φ α) := by
  have : Finite C := Finite.of_equiv T φ.toEquiv
  set β := MulAut.congr φ α with hβ
  let e12 : ↥(fixSub α) ≃* ↥(fixSub β) := fixIso φ α
  have h1 : (perfectResidual ↥(fixSub α)).map e12.toMonoidHom = perfectResidual ↥(fixSub β) :=
    finite_perfectResidual_map_eq e12.toMonoidHom e12.surjective
  show ((perfectResidual ↥(fixSub α)).map (fixSub α).subtype).map φ.toMonoidHom =
    (perfectResidual ↥(fixSub β)).map (fixSub β).subtype
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite C] in
theorem mem_fixRes_of_transfer {φ : T ≃* C} {α : MulAut T} {q : ℕ}
    (h : ∀ x ∈ fixSub (MulAut.congr φ α), (∃ k : ℕ, orderOf x = q ^ k) →
      x ∈ fixRes (MulAut.congr φ α)) :
    ∀ x ∈ fixSub α, (∃ k : ℕ, orderOf x = q ^ k) → x ∈ fixRes α := by
  intro x hx hxp
  have hφx : φ x ∈ fixSub (MulAut.congr φ α) := by
    rw [fixSub_congr]
    exact ⟨x, hx, rfl⟩
  have hφp : ∃ k : ℕ, orderOf (φ x) = q ^ k := by
    obtain ⟨k, hk⟩ := hxp
    exact ⟨k, by rw [MulEquiv.orderOf_eq φ x, hk]⟩
  have hmem : φ x ∈ (fixRes α).map φ.toMonoidHom := by
    rw [fixRes_map_congr]
    exact h _ hφx hφp
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = x := φ.injective hyx
  rw [← this]
  exact hy

omit [Finite C] in
theorem fixedFacts_of_transfer {p : ℕ} (φ : T ≃* C) (α : MulAut T) (hF : FieldAutT p α)
    (hNL : NonLocalized (fixRes (MulAut.congr φ α)))
    (hP : ∀ x ∈ fixSub (MulAut.congr φ α), (∃ k : ℕ, orderOf x = p ^ k) →
      x ∈ fixRes (MulAut.congr φ α))
    (hP2 : (∀ x ∈ fixSub (MulAut.congr φ α), (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ fixRes (MulAut.congr φ α)) ∨ TwoExc p T) : FixedFacts p α :=
  ⟨hF, nonLocalized_of_map_eq (fixRes_map_congr φ α) hNL, mem_fixRes_of_transfer hP,
    hP2.imp_left mem_fixRes_of_transfer⟩

theorem fixedFacts_of_iso {p n f₀ : ℕ} {t : StatedLieTag} (φ : T ≃* C) (α : MulAut T)
    (hM : LieModel T t n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (N : Subgroup C)
    (hNΓ : N ≤ fixSub (MulAut.congr φ α))
    (hNnorm : (N.subgroupOf (fixSub (MulAut.congr φ α))).Normal) (hNperf : Group.IsPerfect ↥N)
    (hsolv : Group.IsSolvable (↥(fixSub (MulAut.congr φ α)) ⧸
      N.subgroupOf (fixSub (MulAut.congr φ α))))
    (hNL : NonLocalized N)
    (hP : ∀ x ∈ fixSub (MulAut.congr φ α), (∃ k : ℕ, orderOf x = p ^ k) → x ∈ N)
    (hP2 : (∀ x ∈ fixSub (MulAut.congr φ α), (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ N) ∨ TwoExc p T)
    (hX : LieModel (↥N ⧸ Subgroup.center ↥N) t n 2 f₀ ∨
      (t = .twistedF4 ∧ n = 0 ∧ f₀ = 1 ∧ LieModel (↥N ⧸ Subgroup.center ↥N) .Tits 0 2 1)) :
    FixedFacts p α := by
  set β := MulAut.congr φ α with hβ
  have hres : fixRes β = N := inSubgroup_perfectResidual_eq_of_normal hNΓ hNnorm hNperf hsolv
  let e12 : ↥(fixSub α) ≃* ↥(fixSub β) := fixIso φ α
  have hF : FieldAutT p α := by
    refine ⟨t, n, f₀, hf₀, hM, ?_⟩
    rcases hX with h | ⟨ht, hn, hf1, h⟩
    · exact Or.inl (lieModel_fixRes_congr e12
        (lieModel_fixRes_of_normal hNΓ hNnorm hNperf hsolv (MulEquiv.refl _) h))
    · exact Or.inr ⟨ht, hn, hf1, lieModel_fixRes_congr e12
        (lieModel_fixRes_of_normal hNΓ hNnorm hNperf hsolv (MulEquiv.refl _) h)⟩
  refine fixedFacts_of_transfer φ α hF (by rw [hres]; exact hNL)
    (fun x hx hxp => by rw [hres]; exact hP x hx hxp)
    (hP2.imp_left fun h x hx hx2 => by rw [hres]; exact h x hx hx2)

omit [Finite C] in
theorem fixRes_eq_fixSub_of_perfect {α : MulAut T} (h : Group.IsPerfect ↥(fixSub α)) :
    fixRes α = fixSub α := by
  have hN : ((fixSub α).subgroupOf (fixSub α)).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolv : Group.IsSolvable (↥(fixSub α) ⧸ (fixSub α).subgroupOf (fixSub α)) := by
    have : Subsingleton (↥(fixSub α) ⧸ (fixSub α).subgroupOf (fixSub α)) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (x⁻¹ * y).2
    exact inferInstance
  exact inSubgroup_perfectResidual_eq_of_normal le_rfl hN h hsolv

theorem fixedFacts_of_iso_of_eq {p n f₀ : ℕ} {t : StatedLieTag} (φ : T ≃* C) (α : MulAut T)
    (hM : LieModel T t n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (Γ N : Subgroup C)
    (hΓ : fixSub (MulAut.congr φ α) = Γ) (hNΓ : N ≤ Γ) (hNnorm : (N.subgroupOf Γ).Normal)
    (hNperf : Group.IsPerfect ↥N) (hsolv : Group.IsSolvable (↥Γ ⧸ N.subgroupOf Γ))
    (hNL : NonLocalized N) (hP : ∀ x ∈ Γ, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ N)
    (hP2 : (∀ x ∈ Γ, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ N) ∨ TwoExc p T)
    (hX : LieModel (↥N ⧸ Subgroup.center ↥N) t n 2 f₀ ∨
      (t = .twistedF4 ∧ n = 0 ∧ f₀ = 1 ∧ LieModel (↥N ⧸ Subgroup.center ↥N) .Tits 0 2 1)) :
    FixedFacts p α := by
  subst hΓ
  exact fixedFacts_of_iso φ α hM hf₀ N hNΓ hNnorm hNperf hsolv hNL hP hP2 hX

omit [Finite C] in
theorem exists_fixed_two_subgroup {α : MulAut T} (h : fixRes α ≠ ⊥) :
    ∃ U : Subgroup T, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ x ∈ U, α x = x := by
  have hperfR : Group.IsPerfect (perfectResidual ↥(fixSub α)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  have hperf : Group.IsPerfect ↥(fixRes α) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective (perfectResidual ↥(fixSub α)) (fixSub α).subtype
        (fixSub α).subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (perfectResidual ↥(fixSub α)) (fixSub α).subtype
        (fixSub α).subtype_injective).surjective
  have h2 : 2 ∣ Nat.card ↥(fixRes α) := by
    by_contra hodd
    have hsol : Group.IsSolvable ↥(fixRes α) :=
      CFSG.Milestones.odd_order_solvable (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
    have : Nontrivial ↥(fixRes α) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
    have := hperf
    exact Group.IsPerfect.not_isSolvable ↥(fixRes α) hsol
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(fixRes α)) 2 h2
  have hxT : orderOf (x : T) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx1 : (x : T) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxT; omega
  have hxfix : (x : T) ∈ fixSub α := (fixRes_le_fixSub α) x.2
  refine ⟨Subgroup.zpowers (x : T), fun hbot => hx1 (Subgroup.zpowers_eq_bot.mp hbot),
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxT, pow_one]), fun z hz => ?_⟩
  exact (Subgroup.zpowers_le.mpr hxfix) hz

theorem fixedFacts_of_simple {p n f₀ : ℕ} {t : StatedLieTag} (φ : T ≃* C) (α : MulAut T)
    (hM : LieModel T t n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) {X : Type} [Group X] [IsSimpleGroup X]
    (eX : ↥(fixSub (MulAut.congr φ α)) ≃* X) (hnab : ∃ a b : X, a * b ≠ b * a)
    (hNL : NonLocalized (fixSub (MulAut.congr φ α)))
    (hX : LieModel X t n 2 f₀ ∨ (t = .twistedF4 ∧ n = 0 ∧ f₀ = 1 ∧ LieModel X .Tits 0 2 1)) :
    FixedFacts p α := by
  set N := fixSub (MulAut.congr φ α) with hN
  have hperfX : Group.IsPerfect X := isPerfect_of_simple_nonabelian hnab
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_simple' hnab
  have hnorm : (N.subgroupOf N).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolv : Group.IsSolvable (↥N ⧸ N.subgroupOf N) := by
    have : Subsingleton (↥N ⧸ N.subgroupOf N) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (x⁻¹ * y).2
    exact inferInstance
  have eQ : ↥N ⧸ Subgroup.center ↥N ≃* X :=
    (centerQuotientCongr eX).trans (centerQuotientEquivSelf hZ)
  refine fixedFacts_of_iso φ α hM hf₀ N le_rfl hnorm hNperf hsolv hNL (fun x hx _ => hx)
    (Or.inl fun x hx _ => hx) ?_
  rcases hX with h | ⟨ht, hn, hf1, h⟩
  · exact Or.inl (lieModel_of_mulEquiv eQ.symm h)
  · exact Or.inr ⟨ht, hn, hf1, lieModel_of_mulEquiv eQ.symm h⟩

omit [Finite T] [Finite C] in
theorem congr_noninner_prime {p : ℕ} (hp : p.Prime) (e : T ≃* C) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    MulAut.congr e α ∉ innerAut C ∧ orderOf (MulAut.congr e α) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hinn : MulAut.congr e α ∉ innerAut C := fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hp' : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  exact ⟨hinn, orderOf_eq_prime hp' (fun h1 => hinn (h1 ▸ (innerAut C).one_mem))⟩

end Generic

end CFSG.RankThree.PartOne.FieldFix
