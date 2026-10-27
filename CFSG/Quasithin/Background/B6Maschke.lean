module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.B6

private theorem exists_invt_isCompl_of_coprime {p : ℕ} [Fact p.Prime] {T : Type*} [Group T]
    [Finite T] (hT : ¬ p ∣ Nat.card T) {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : Representation (ZMod p) T M) (N : Submodule (ZMod p) M)
    (hN : ∀ t, ∀ x ∈ N, ρ t x ∈ N) :
    ∃ N' : Submodule (ZMod p) M, (∀ t, ∀ x ∈ N', ρ t x ∈ N') ∧ IsCompl N N' := by
  have : NeZero (Nat.card T : ZMod p) :=
    ⟨fun h => hT ((ZMod.natCast_eq_zero_iff _ _).1 h)⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl
    (⟨N, fun t _ hx => hN t _ hx⟩ : Subrepresentation ρ)
  refine ⟨σ'.toSubmodule, fun t x hx => σ'.apply_mem_toSubmodule t hx, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hσ' ⊢
  exact ⟨congrArg Subrepresentation.toSubmodule hσ'.1,
    congrArg Subrepresentation.toSubmodule hσ'.2⟩

private theorem exists_invt_isCompl_of_commGroup {p : ℕ} [Fact p.Prime] {T Q : Type*} [Group T]
    [Finite T] [CommGroup Q] (hT : ¬ p ∣ Nat.card T) (hQ : ∀ x : Q, x ^ p = 1)
    (ρ : T →* MulAut Q) (B : Subgroup Q) (hB : ∀ t, ∀ x ∈ B, ρ t x ∈ B) :
    ∃ C : Subgroup Q, (∀ t, ∀ x ∈ C, ρ t x ∈ C) ∧ B ⊓ C = ⊥ ∧ B ⊔ C = ⊤ := by
  let : Module (ZMod p) (Additive Q) :=
    AddCommGroup.zmodModule (n := p) fun x => Additive.toMul.injective (hQ (Additive.toMul x))
  let ρ' : Representation (ZMod p) T (Additive Q) :=
    { toFun := fun t => (AddMonoidHom.mk'
        (fun x : Additive Q => Additive.ofMul (ρ t (Additive.toMul x)))
        (fun x y => by simp)).toZModLinearMap p
      map_one' := by
        ext x
        simp
      map_mul' := fun s t => by
        ext x
        simp }
  obtain ⟨N', hN', hcompl⟩ := exists_invt_isCompl_of_coprime hT ρ'
    (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup B)) (fun t x hx => hB t _ hx)
  refine ⟨{ carrier := {x | Additive.ofMul x ∈ N'}
            mul_mem' := fun {a b} ha hb => N'.add_mem ha hb
            one_mem' := N'.zero_mem
            inv_mem' := fun {a} ha => N'.neg_mem ha }, fun t x hx => hN' t _ hx, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact Additive.ofMul.injective (Submodule.disjoint_def.1 hcompl.disjoint _ hx.1 hx.2)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top (x := Additive.ofMul x))
    have hx : x = Additive.toMul y * Additive.toMul z := Additive.ofMul.injective hyz.symm
    rw [hx]
    exact Subgroup.mul_mem_sup hy hz

private theorem exists_invt_isCompl_of_section {p : ℕ} [Fact p.Prime] {T G : Type*} [Group T]
    [Finite T] [Group G] (hT : ¬ p ∣ Nat.card T) (ρ : T →* MulAut G) (N W : Subgroup G)
    (hNW : N ≤ W) (hpow : ∀ x : G, x ^ p ∈ N) (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hρN : ∀ t, ∀ x ∈ N, ρ t x ∈ N) (hρW : ∀ t, ∀ x ∈ W, ρ t x ∈ W) :
    ∃ W' : Subgroup G, N ≤ W' ∧ (∀ t, ∀ x ∈ W', ρ t x ∈ W') ∧ W ⊔ W' = ⊤ ∧ W ⊓ W' = N := by
  have hNn : N.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by simp [mul_assoc]
    rw [this]
    exact N.mul_mem (hcomm g n) hn⟩
  let : CommGroup (G ⧸ N) :=
    { (inferInstance : Group (G ⧸ N)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        rename_i x y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have := hcomm y⁻¹ x⁻¹
        simpa [mul_assoc] using this }
  have hQ : ∀ x : G ⧸ N, x ^ p = 1 := fun x => by
    induction x using QuotientGroup.induction_on
    rename_i g
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hpow g
  have he : ∀ t : T, N.map (ρ t : G →* G) = N := fun t => by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hρN t x hx
    · intro x hx
      refine ⟨ρ t⁻¹ x, hρN t⁻¹ x hx, ?_⟩
      show ρ t (ρ t⁻¹ x) = x
      rw [← MulAut.mul_apply, ← map_mul ρ, mul_inv_cancel, map_one, MulAut.one_apply]
  let ρbar : T →* MulAut (G ⧸ N) :=
    { toFun := fun t => QuotientGroup.congr N N (ρ t) (he t)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on
        simp
      map_mul' := fun s t => by
        ext x
        induction x using QuotientGroup.induction_on
        simp }
  obtain ⟨C, hCinv, hinf, hsup⟩ := exists_invt_isCompl_of_commGroup hT hQ ρbar
    (W.map (QuotientGroup.mk' N)) (fun t x hx => by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨ρ t w, hρW t w hw, rfl⟩)
  have h1 : (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = W := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.2 hNW]
  refine ⟨C.comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · intro n hn
    simp [(QuotientGroup.eq_one_iff n).2 hn]
  · intro t x hx
    have := hCinv t _ hx
    simpa [ρbar] using this
  · calc W ⊔ C.comap (QuotientGroup.mk' N)
        = (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ⊔
            C.comap (QuotientGroup.mk' N) := by rw [h1]
      _ = ((W.map (QuotientGroup.mk' N)) ⊔ C).comap (QuotientGroup.mk' N) :=
          Subgroup.comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective N)
      _ = ⊤ := by rw [hsup, Subgroup.comap_top]
  · calc W ⊓ C.comap (QuotientGroup.mk' N)
        = (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ⊓
            C.comap (QuotientGroup.mk' N) := by rw [h1]
      _ = ((W.map (QuotientGroup.mk' N)) ⊓ C).comap (QuotientGroup.mk' N) :=
          (Subgroup.comap_inf _ _ _).symm
      _ = N := by rw [hinf, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem exists_isCompl_of_coprime_section {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {K Φ W T : Subgroup Y} (hΦW : Φ ≤ W) (hWK : W ≤ K)
    (hpow : ∀ x ∈ K, x ^ p ∈ Φ) (hcomm : ⁅K, K⁆ ≤ Φ)
    (hTK : T ≤ Subgroup.normalizer (K : Set Y)) (hTΦ : T ≤ Subgroup.normalizer (Φ : Set Y))
    (hTW : T ≤ Subgroup.normalizer (W : Set Y)) (hT : IsPGroup 2 T) :
    ∃ W' : Subgroup Y, Φ ≤ W' ∧ W' ≤ K ∧ T ≤ Subgroup.normalizer (W' : Set Y) ∧
      W ⊔ W' = K ∧ W ⊓ W' = Φ := by
  have hpT : ¬ p ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Fact.out h))
  let ρ : T →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hTK)
  have hρ : ∀ (t : T) (k : K), ((ρ t k : K) : Y) = (t : Y) * k * (t : Y)⁻¹ := fun t k => rfl
  have hρinv : ∀ S : Subgroup Y, T ≤ Subgroup.normalizer (S : Set Y) →
      ∀ (t : T), ∀ k : K, (k : Y) ∈ S → ((ρ t k : K) : Y) ∈ S := fun S hS t k hk => by
    rw [hρ]
    exact (Subgroup.mem_normalizer_iff.1 (hS t.2) k).1 hk
  obtain ⟨W₁, hΦW₁, hinv, hsup, hinf⟩ := exists_invt_isCompl_of_section hpT ρ (Φ.subgroupOf K)
    (W.subgroupOf K) (fun x hx => hΦW hx) (fun x => hpow x x.2)
    (fun x y => hcomm (Subgroup.commutator_mem_commutator x.2 y.2))
    (fun t x hx => hρinv Φ hTΦ t x hx) (fun t x hx => hρinv W hTW t x hx)
  refine ⟨W₁.map K.subtype, ?_, Subgroup.map_subtype_le W₁, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hWK (hΦW hx)⟩, hΦW₁ hx, rfl⟩
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨ρ ⟨t, ht⟩ k, hinv ⟨t, ht⟩ k hk, hρ ⟨t, ht⟩ k⟩
    · rintro ⟨k, hk, hkh⟩
      refine ⟨ρ ⟨t⁻¹, T.inv_mem ht⟩ k, hinv _ k hk, ?_⟩
      have hkh' : (k : Y) = t * h * t⁻¹ := hkh
      show ((ρ ⟨t⁻¹, T.inv_mem ht⟩ k : K) : Y) = h
      rw [hρ]
      show t⁻¹ * (k : Y) * t⁻¹⁻¹ = h
      rw [hkh']
      group
  · refine le_antisymm (sup_le hWK (Subgroup.map_subtype_le W₁)) fun x hx => ?_
    have hx' : (⟨x, hx⟩ : K) ∈ W.subgroupOf K ⊔ W₁ := hsup ▸ Subgroup.mem_top _
    have hmap : x ∈ (W.subgroupOf K ⊔ W₁).map K.subtype := ⟨⟨x, hx⟩, hx', rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hWK] at hmap
  · have hmap := congrArg (Subgroup.map K.subtype) hinf
    rwa [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hWK,
      Subgroup.map_subgroupOf_eq_of_le (hΦW.trans hWK)] at hmap

end CFSG.Quasithin.B6
