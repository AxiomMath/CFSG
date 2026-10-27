module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
import CFSG.RankThree.Classical2.TwistedE6RationalOrder
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open

theorem le_of_commutator_index_eq_three_pow {M : Type*} [Group M] {R C E : Subgroup M}
    (hC : ⁅R, R⁆ = C) {k : ℕ} (hidx : (C.subgroupOf R).index = 3 ^ k) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hER : E ≤ R) (hE : ∀ x ∈ E, x ^ p = 1) : E ≤ C := by
  let N : Subgroup ↥R := C.subgroupOf R
  have : N.Normal := by
    have hNcomm : N = _root_.commutator ↥R := by
      change C.subgroupOf R = _root_.commutator ↥R
      rw [← hC, ← Subgroup.map_subtype_commutator R]
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [hNcomm, commutator_def]
    exact Subgroup.commutator_normal (⊤ : Subgroup ↥R) ⊤
  intro x hx
  have hxR : x ∈ R := hER hx
  let y : ↥R := ⟨x, hxR⟩
  let q : ↥R →* ↥R ⧸ N := QuotientGroup.mk' N
  have h1 : (q y) ^ (3 ^ k) = 1 := by
    rw [← hidx, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ N.index)).2 (Subgroup.pow_index_mem N y)
  have hyp : y ^ p = 1 := Subtype.ext (hE x hx)
  have h2 : (q y) ^ p = 1 := by
    rw [← map_pow, hyp, map_one]
  have hcop : Nat.Coprime (3 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have hdvd : orderOf (q y) ∣ Nat.gcd (3 ^ k) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
  have hy : y ∈ N := (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 hdvd)
  simpa using Subgroup.mem_subgroupOf.mp hy

theorem orderOf_ne_one_and_ne_two {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (h1 : ¬ p ∣ q - 1)
    (h2 : ¬ p ∣ q + 1) : orderOf (q : ZMod p) ≠ 1 ∧ orderOf (q : ZMod p) ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro h
    have hq1 : (q : ZMod p) = 1 := orderOf_eq_one_iff.1 h
    have hzero : ((q - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hq, hq1, Nat.cast_one, sub_self]
    exact h1 ((ZMod.natCast_eq_zero_iff (q - 1) p).1 hzero)
  · rintro h
    have hx2 : (q : ZMod p) ^ 2 = 1 := by
      rw [← h]
      exact pow_orderOf_eq_one _
    have hfac : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by
      have hsq : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) =
          (q : ZMod p) ^ 2 - 1 := by ring
      rw [hsq, hx2, sub_self]
    rcases mul_eq_zero.1 hfac with hq1 | hqm
    · have hq1' : (q : ZMod p) = 1 := sub_eq_zero.mp hq1
      have hone : orderOf (q : ZMod p) = 1 := orderOf_eq_one_iff.2 hq1'
      omega
    · have hqm' : (q : ZMod p) = -1 := add_eq_zero_iff_eq_neg.mp hqm
      have hzero : ((q + 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hqm']
        abel
      exact h2 ((ZMod.natCast_eq_zero_iff (q + 1) p).1 hzero)

theorem degCountTw_le_three {e : ℕ} (h1 : e ≠ 1) (h2 : e ≠ 2) : degCountTw e ≤ 3 := by
  by_cases h0 : degCountTw e = 0
  · omega
  · have h60 := le_sixty_of_degCountTw_pos (Nat.pos_of_ne_zero h0)
    interval_cases e <;> first | decide | omega

theorem card_le_of_le_ggFixGp_twistedE6
    {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Subgroup (ModGL (langTag .twistedE6) GGL)} (hER : E ≤ ggFixGp .twistedE6 f)
    (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ degCountTw (orderOf ((2 ^ f : ℕ) : ZMod p)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * f)
  let : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  have : IsScalarTower (ZMod 2) F GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  have : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hcardF : Nat.card F = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0), ← pow_mul, Nat.mul_comm]
  let σ : F →+* F := (iterateFrobeniusEquiv F 2 f).toRingHom
  have hσ : ∀ c, σ c = c ^ (2 ^ f) :=
    fun c => iterateFrobeniusEquiv_def F 2 f c
  obtain ⟨_, _, hder, ⟨k, hidx⟩, _, _, _⟩ :=
    (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf F hcardF σ hσ
      GGL (ggFrobT f) (ggFrobT_apply f))
  have hER' : E ≤ twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) := hER
  let E' : Subgroup (ModGL TwistTag.E6.tag GGL) := E
  let C : Subgroup (ModGL TwistTag.E6.tag GGL) :=
    (graphFixedRootGroup TwistTag.E6 F σ).map (baseChangeGL (algebraMap F GGL))
  have hEC : E' ≤ C :=
    le_of_commutator_index_eq_three_pow hder hidx hp (by omega) hER' hE.2
  let H := graphFixedRootGroup TwistTag.E6 F σ
  let φ : ↥H →* ModGL TwistTag.E6.tag GGL :=
    (baseChangeGL (τ := TwistTag.E6.tag) (R := F) (S := GGL)
      (algebraMap F GGL)).comp H.subtype
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (R := F) (S := GGL)
      (algebraMap F GGL)).comp (Subgroup.subtype_injective H)
  let E₁ : Subgroup ↥H := E'.comap φ
  have hE₁ : IsElemAbelian p E₁ := by
    constructor
    · refine IsMulCommutative.of_comm ?_
      intro a b
      apply Subtype.ext
      apply hφinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        (isMulCommutative_iff.1 hE.1 ⟨φ a, a.2⟩ ⟨φ b, b.2⟩)
    · intro a ha
      apply hφinj
      rw [map_pow, map_one]
      exact hE.2 (φ a) ha
  have hrange : φ.range = C := by
    dsimp only [φ]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmap : E₁.map φ = E' := by
    have hle : E' ≤ φ.range := by
      rw [hrange]
      exact hEC
    simpa [E₁] using Subgroup.map_comap_eq_self (f := φ) (H := E') hle
  have hcardE : Nat.card E₁ = Nat.card E' := by
    rw [← hmap, Subgroup.card_map_of_injective (K := E₁) hφinj]
  have hroot : twistedE6RootGroup F (iterateFrobeniusEquiv F 2 f) = H := rfl
  have hrank := rankLE_twistedE6 (ℓ := 2) (f := f) (K := F)
    (e := orderOf ((2 ^ f : ℕ) : ZMod p)) Nat.prime_two hf hcardF
    (iterateFrobeniusEquiv F 2 f) (fun c => iterateFrobeniusEquiv_def F 2 f c)
    hp (by omega) rfl
  rw [hroot] at hrank
  have hbound : Nat.card E₁ ≤ p ^ degCountTw (orderOf ((2 ^ f : ℕ) : ZMod p)) :=
    hrank E₁ hE₁
  rwa [hcardE] at hbound

theorem twE6TTRank_holds :
    ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime → 5 ≤ p → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
      ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
        IsElemAbelian p E → Nat.card E < p ^ 4 := by
  intro f hf p hp hp5 hq1 hq2 E hER hE
  obtain ⟨h1, h2⟩ := orderOf_ne_one_and_ne_two hp Nat.one_le_two_pow hq1 hq2
  calc Nat.card E ≤ p ^ degCountTw (orderOf ((2 ^ f : ℕ) : ZMod p)) :=
        card_le_of_le_ggFixGp_twistedE6 hf hp hp5 hER hE
    _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (degCountTw_le_three h1 h2)
    _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end CFSG.StandardType.LieKnownR2.ExcPos
