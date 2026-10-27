module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.PlaneSemidirect
import CFSG.RankThree.Coprime.HighTwoRankOddKernel
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly
open scoped commutatorElement

namespace PlaneCore

variable {B S D : Type} [Group B] [Group S] [Group D] [MulDistribMulAction B S]
  (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D)

theorem pRank_le_of_forall {p : ℕ} (hp : p.Prime) [Finite D] (F : Subgroup D) {m : ℕ}
    (h : ∀ E : Subgroup D, IsElementaryAbelian p E → E ≤ F → ∀ k : ℕ, Nat.card E = p ^ k →
      k ≤ m) : CFSG.pRank p F ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  apply csSup_le'
  rintro k ⟨E, hE, hk⟩
  have := hE
  refine h (E.map F.subtype) (IsElementaryAbelian.map_subtype (H := E))
    (by rintro _ ⟨e, -, rfl⟩; exact e.2) k ?_
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hk]

theorem card_frattini_quotient_le {p : ℕ} (hp : p.Prime) {P : Type} [Group P] [Finite P]
    (hPp : IsPGroup p P) (hPexp : ∀ x : P, x ^ p = 1) (hPcl : commutator P ≤ Subgroup.center P)
    (hPrank : ∀ E : Subgroup P, IsElementaryAbelian p E → ∀ k : ℕ, Nat.card E = p ^ k →
      k ≤ 2) : Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hPr : CFSG.pRank p P ≤ 2 := by
    apply csSup_le'
    rintro k ⟨E, hE, hk⟩
    have := hE
    exact hPrank E hE k hk
  have hQr : CFSG.pRank p (P ⧸ commutator P) ≤ 2 :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hPp hPexp hPcl).1 hPr
  have hQcard : Nat.card (P ⧸ commutator P) ≤ p ^ 2 := by
    have hexp' : ∀ q : P ⧸ commutator P, q ^ p = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => rw [← QuotientGroup.mk_pow, hPexp x, QuotientGroup.mk_one]
    have hEl : IsElementaryAbelian p (⊤ : Subgroup (P ⧸ commutator P)) :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hexp' x) }
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hPp.to_quotient (commutator P))
    have hk' : Nat.card (⊤ : Subgroup (P ⧸ commutator P)) = p ^ k := by
      rw [Subgroup.card_top]
      exact hk
    have := CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian hp.one_lt hEl hk'
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (this.trans hQr)
  have : Fact (IsPGroup p P) := ⟨hPp⟩
  exact (Nat.le_of_dvd Nat.card_pos
    (Subgroup.index_dvd_of_le (commutator_le_frattini_of_isPGroup (R := P) (p := p)))).trans hQcard

theorem commutator_le_center_of_critical {P : Type} [Group P] {D₀ : Subgroup P}
    (hcl : ⁅D₀, (⊤ : Subgroup P)⁆ ≤ D₀ ⊓ Subgroup.centralizer (D₀ : Set P)) :
    commutator D₀ ≤ Subgroup.center D₀ := by
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
  refine Subgroup.mem_center_iff.mpr fun z => ?_
  have hmem : ⁅(x : P), (y : P)⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
    Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : P) z.2)

variable [Finite B] [Finite S] [Finite D]

theorem card_le_sixteen {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hDp : IsPGroup p D)
    (hDexp : ∀ x : D, x ^ p = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hβ : Function.Injective β) (hS : IsPGroup 2 S)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3) {A : Type} [Group A]
    [Finite A] (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ 2 = 1) (f : A →* S)
    (hf : Function.Injective f) : Nat.card A ≤ 16 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 A)
  let ρ : S →* MulAut D := β.comp SemidirectProduct.inl
  have hρ : Function.Injective ρ := hβ.comp SemidirectProduct.inl_injective
  let _ : MulDistribMulAction A D := MulDistribMulAction.compHom D (ρ.comp f)
  have : FaithfulSMul A D := ⟨fun {a b} h => hf (hρ (MulEquiv.ext h))⟩
  have hexp : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hDexp
  have hcl : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ :=
    CFSG.RankThree.Coprime.lowerCentralSeries_two_eq_bot fun x y z =>
      (Subgroup.mem_center_iff.mp (hDcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y))) z).symm
  have hm : ∀ a : A, a ≠ 1 →
      CFSG.pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D) ≤ 3 := by
    intro a ha
    refine pRank_le_of_forall hp _ fun E hE hEF k hk => ?_
    refine (PlaneSemidirect.le_evenRank_of_fixed β hp hp2 hS (s := f a)
      (fun h => ha (hf (h.trans f.map_one.symm))) hE (fun e he' => ?_) hk).trans he
    exact hEF he' ⟨a, Subgroup.mem_zpowers a⟩
  have h := CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound
    (hp.odd_of_ne_two hp2) hDp hexp hcl n 3 hn hm
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h.1
    _ = 16 := by norm_num

end PlaneCore

end CFSG.RankThree.PartOne
