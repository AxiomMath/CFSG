module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_c_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.ZMod.Torsion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.6(a) from BG Section 5 -/

public theorem CFSG.sylow_le_Op_p'p_of_hasPLengthOne
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hplen : HasPLengthOne (p := p) G) (S : Sylow p G) :
    (S : Subgroup G) ≤ Op_p'p p G := by
  have hS_le_pElements : (S : Subgroup G) ≤ pElementsSubgroup p G := by
    intro x hx
    refine Subgroup.subset_closure ?_
    have hxP : IsPElement (p := p) (⟨x, hx⟩ : S) :=
      (IsPGroup.iff_orderOf (p := p) (G := S)).1 S.isPGroup' ⟨x, hx⟩
    rcases hxP with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      orderOf x = orderOf (⟨x, hx⟩ : (S : Subgroup G)) :=
        Subgroup.orderOf_coe (H := (S : Subgroup G)) ⟨x, hx⟩
      _ = p ^ n := hn
  exact hS_le_pElements.trans (pElementsSubgroup_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen)

public theorem CFSG.normalizer_sup_Op_p'p_eq_top_of_hasPLengthOne
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hplen : HasPLengthOne (p := p) G) (S : Sylow p G) :
    Subgroup.normalizer (S : Subgroup G) ⊔ Op_p'p p G = ⊤ := by
  exact Sylow.normalizer_sup_eq_top' (N := Op_p'p p G) S
    (sylow_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen S)

private theorem CFSG.pPrimeCore_le_Op_p'p
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] :
    pPrimeCore p G ≤ Op_p'p p G := by
  intro x hx
  change QuotientGroup.mk' (pPrimeCore p G) x ∈ pCore p (G ⧸ pPrimeCore p G)
  have hx1 : QuotientGroup.mk' (pPrimeCore p G) x = 1 :=
    (QuotientGroup.eq_one_iff (N := pPrimeCore p G) (x := x)).2 hx
  simp [hx1]


private theorem CFSG.quotient_Op_p'p_card_dvd_normalizer_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Sylow p G} (hplen : HasPLengthOne (p := p) G) :
    Nat.card (G ⧸ Op_p'p p G) ∣
      Nat.card (Subgroup.normalizer (S : Subgroup G) ⧸
        (Op_p'p p G).subgroupOf (Subgroup.normalizer (S : Subgroup G))) := by
  let N : Subgroup G := Subgroup.normalizer (S : Subgroup G)
  let L : Subgroup G := Op_p'p p G
  let : L.Normal := by
    dsimp [L]
    infer_instance
  have htop : N ⊔ L = ⊤ :=
    normalizer_sup_Op_p'p_eq_top_of_hasPLengthOne (G := G) (p := p) hplen S
  have hL_le_NL : L ≤ N ⊔ L := le_sup_right
  have hcard_map :
      Nat.card (N.map (QuotientGroup.mk' L)) =
        Nat.card (N ⧸ L.subgroupOf N) := by
    simpa [N, L] using natCard_map_mk'_eq N L
  have hmap_top : N.map (QuotientGroup.mk' L) = ⊤ := by
    calc
      N.map (QuotientGroup.mk' L) =
          N.map (QuotientGroup.mk' L) ⊔ L.map (QuotientGroup.mk' L) := by
            have hLmap : L.map (QuotientGroup.mk' L) = ⊥ := by
              exact QuotientGroup.map_mk'_self (N := L)
            simp [hLmap]
      _ = (N ⊔ L).map (QuotientGroup.mk' L) := by rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup G).map (QuotientGroup.mk' L) := by rw [htop]
      _ = (⊤ : Subgroup (G ⧸ L)) := by
            simpa using
              (Subgroup.map_top_of_surjective (f := QuotientGroup.mk' L)
                (QuotientGroup.mk'_surjective L))
  have hcard_eq :
      Nat.card (N ⧸ L.subgroupOf N) = Nat.card (G ⧸ L) := by
    calc
      Nat.card (N ⧸ L.subgroupOf N) = Nat.card (N.map (QuotientGroup.mk' L)) := hcard_map.symm
      _ = Nat.card (⊤ : Subgroup (G ⧸ L)) := by rw [hmap_top]
      _ = Nat.card (G ⧸ L) := by rw [Subgroup.card_top]
  change Nat.card (G ⧸ L) ∣ Nat.card (N ⧸ L.subgroupOf N)
  rw [hcard_eq]

private theorem CFSG.quotient_Op_p'p_card_dvd_automorphism_image_card
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {p : ℕ} [Fact p.Prime]
    {S : Sylow p G} (hplen : HasPLengthOne (p := p) G) :
    Nat.card (G ⧸ Op_p'p p G) ∣
      Nat.card ((Subgroup.normalizerMonoidHom (H := (S : Subgroup G))).range) := by
  let N : Subgroup G := Subgroup.normalizer (S : Subgroup G)
  let L : Subgroup G := Op_p'p p G
  let φ : N →* MulAut S := Subgroup.normalizerMonoidHom (H := (S : Subgroup G))
  have hquot_dvd :
      Nat.card (G ⧸ L) ∣ Nat.card (N ⧸ L.subgroupOf N) :=
    quotient_Op_p'p_card_dvd_normalizer_card (G := G) (p := p) (S := S) hplen
  have hS_le_L : (S : Subgroup G) ≤ L :=
    sylow_le_Op_p'p_of_hasPLengthOne (G := G) (p := p) hplen S
  have hcent_le_L : Subgroup.centralizer (S : Set G) ≤ L := by
    let T : Sylow p L := S.subtype hS_le_L
    have hcentralizer :=
      centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable (G := G)
        (inferInstance : Group.IsSolvable G) p T
    have hTG_eq : T.1.map L.subtype = (S : Subgroup G) := by
      simp [T, L, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hS_le_L]
    simpa [hTG_eq, L] using hcentralizer
  have hker_eq : φ.ker = (Subgroup.centralizer (S : Subgroup G)).subgroupOf N := by
    simpa [φ, N] using
      (Subgroup.normalizerMonoidHom_ker (H := (S : Subgroup G)))
  have hker_le_Lsub : φ.ker ≤ L.subgroupOf N := by
    intro x hx
    have hxC : x ∈ (Subgroup.centralizer (S : Subgroup G)).subgroupOf N := by
      simpa [hker_eq] using hx
    exact hcent_le_L hxC
  let Lbar : Subgroup (N ⧸ φ.ker) := (L.subgroupOf N).map (QuotientGroup.mk' φ.ker)
  let e : (N ⧸ φ.ker) ⧸ Lbar ≃* N ⧸ L.subgroupOf N :=
    QuotientGroup.quotientQuotientEquivQuotient (N := φ.ker) (M := L.subgroupOf N) hker_le_Lsub
  have hcard_tower :
      Nat.card (N ⧸ φ.ker) =
        Nat.card ((N ⧸ φ.ker) ⧸ Lbar) * Nat.card Lbar := by
    simpa using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := N ⧸ φ.ker) (s := Lbar))
  have hNquot_dvd_range :
      Nat.card (N ⧸ L.subgroupOf N) ∣ Nat.card φ.range := by
    refine ⟨Nat.card Lbar, ?_⟩
    calc
      Nat.card φ.range = Nat.card (N ⧸ φ.ker) := by
        exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
      _ = Nat.card ((N ⧸ φ.ker) ⧸ Lbar) * Nat.card Lbar := hcard_tower
      _ = Nat.card (N ⧸ L.subgroupOf N) * Nat.card Lbar := by
        rw [Nat.card_congr e.toEquiv]
  exact hquot_dvd.trans hNquot_dvd_range

private theorem CFSG.Op_p'p_quotient_pPrimeCore_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p (Op_p'p p G ⧸ (pPrimeCore p G).subgroupOf (Op_p'p p G)) := by
  let M : Subgroup G := pPrimeCore p G
  let L : Subgroup G := Op_p'p p G
  have hM_le_L : M ≤ L := by
    simpa [M, L] using (pPrimeCore_le_Op_p'p (G := G) (p := p))
  let Lbar : Subgroup (G ⧸ M) := L.map (QuotientGroup.mk' M)
  have hLbar_eq : Lbar = pCore p (G ⧸ M) := by
    dsimp [Lbar, L, M, Op_p'p]
    exact
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hLbar_p : IsPGroup p Lbar := by
    rw [hLbar_eq]
    exact pCore_isPGroup (p := p) (G := G ⧸ M)
  exact hLbar_p.of_equiv (quotientSubgroupRangeEquiv L M).symm

private theorem CFSG.prime_dvd_quotient_Op_p'p_of_ne
    {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hq_ne_p : q ≠ p) (hcard : q ∣ Nat.card (G ⧸ pPrimeCore p G)) :
    q ∣ Nat.card (G ⧸ Op_p'p p G) := by
  let M : Subgroup G := pPrimeCore p G
  let L : Subgroup G := Op_p'p p G
  have hM_le_L : M ≤ L := by
    simpa [M, L] using (pPrimeCore_le_Op_p'p (G := G) (p := p))
  let Lbar : Subgroup (G ⧸ M) := L.map (QuotientGroup.mk' M)
  let e : (G ⧸ M) ⧸ Lbar ≃* G ⧸ L :=
    QuotientGroup.quotientQuotientEquivQuotient (N := M) (M := L) hM_le_L
  have hLbar_card :
      Nat.card Lbar = Nat.card (L ⧸ M.subgroupOf L) := by
    simpa [Lbar, M, L] using natCard_map_mk'_eq L M
  have hLbar_p : IsPGroup p Lbar := by
    have hLp := Op_p'p_quotient_pPrimeCore_isPGroup (G := G) (p := p)
    exact hLp.of_equiv (quotientSubgroupRangeEquiv L M)
  obtain ⟨n, hLbar_card_pow⟩ := hLbar_p.exists_card_eq
  have hq_not_dvd_p : ¬ q ∣ p := by
    intro hqp
    have hp_eq_q : p = q := (Fact.out : Nat.Prime p).dvd_iff_eq (Fact.out : Nat.Prime q).ne_one |>.1 hqp
    exact hq_ne_p hp_eq_q.symm
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hq_eq_p : q = p := (Fact.out : Nat.Prime q).dvd_iff_eq (Fact.out : Nat.Prime p).ne_one |>.1 hpq
    exact hq_ne_p hq_eq_p
  have hcop_q_Lbar : Nat.Coprime q (Nat.card Lbar) := by
    rw [hLbar_card_pow]
    exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd hp_not_dvd_q
  have hcard_eq :
      Nat.card (G ⧸ M) = Nat.card ((G ⧸ M) ⧸ Lbar) * Nat.card Lbar := by
    simpa using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G ⧸ M) (s := Lbar))
  have hq_dvd_quot_lbar : q ∣ Nat.card ((G ⧸ M) ⧸ Lbar) := by
    apply hcop_q_Lbar.dvd_of_dvd_mul_right
    simpa [M, hcard_eq] using hcard
  have hquot_card_eq :
      Nat.card ((G ⧸ M) ⧸ Lbar) = Nat.card (G ⧸ L) :=
    Nat.card_congr e.toEquiv
  simpa [L, hquot_card_eq] using hq_dvd_quot_lbar

public theorem CFSG.theorem_5_6_a_high_rank_largest_prime
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hSrank : 3 ≤ groupRank (S : Subgroup G)) (hplen : HasPLengthOne (p := p) G) :
    IsLargestPrimeDivisor p (Nat.card (G ⧸ pPrimeCore p G)) := by
  classical
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd hp_dvd
  let M : Subgroup G := pPrimeCore p G
  let A : Subgroup (MulAut S) :=
    (Subgroup.normalizerMonoidHom (H := (S : Subgroup G))).range
  have hnormalizer_odd : Odd (Nat.card (Subgroup.normalizer (S : Set G))) := by
    exact odd_of_card_dvd hodd
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (S : Set G)))
  have hAodd : Odd (Nat.card A) := by
    exact odd_of_card_dvd hnormalizer_odd
      (Subgroup.card_range_dvd (Subgroup.normalizerMonoidHom (H := (S : Subgroup G))))
  have : Group.IsSolvable A := by
    let φ := Subgroup.normalizerMonoidHom (H := (S : Subgroup G))
    change Group.IsSolvable φ.range
    exact Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hM_coprime : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hcard_eq :
      Nat.card G = Nat.card (G ⧸ M) * Nat.card M := by
    simpa [M] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := M))
  have hp_dvd_quot : p ∣ Nat.card (G ⧸ M) := by
    exact hM_coprime.dvd_of_dvd_mul_right (hcard_eq ▸ hp_dvd)
  refine ⟨Fact.out, ?_, ?_⟩
  · simpa [M] using hp_dvd_quot
  · intro q hqprime hq_dvd
    by_cases hq_eq_p : q = p
    · simp [hq_eq_p]
    · have : Fact q.Prime := ⟨hqprime⟩
      have hq_dvd_quot_Op : q ∣ Nat.card (G ⧸ Op_p'p p G) :=
        prime_dvd_quotient_Op_p'p_of_ne
          (G := G) (p := p) (q := q) hq_eq_p hq_dvd
      have hquot_dvd_A :
          Nat.card (G ⧸ Op_p'p p G) ∣ Nat.card A :=
        quotient_Op_p'p_card_dvd_automorphism_image_card
          (G := G) (p := p) (S := S) hplen
      have hq_dvd_A : q ∣ Nat.card A := dvd_trans hq_dvd_quot_Op hquot_dvd_A
      obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q hq_dvd_A
      have hp_not_dvd_q : ¬ p ∣ q := by
        intro hpq
        exact hq_eq_p (((Fact.out : Nat.Prime q).dvd_iff_eq (Fact.out : Nat.Prime p).ne_one).1 hpq)
      have hcop_a : Nat.Coprime p (orderOf ((a : A) : MulAut S)) := by
        rw [Subgroup.orderOf_coe, haord]
        exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hp_not_dvd_q
      have horder_dvd : orderOf ((a : A) : MulAut S) ∣ p - 1 := by
        simpa using theorem_5_5_b
          (p := p) hpodd (R := S) hSnarrow hSrank (A := A) hAodd ((a : A) : MulAut S) a.2 hcop_a
      have hq_dvd_pred : q ∣ p - 1 := by
        simpa [Subgroup.orderOf_coe, haord] using horder_dvd
      have hq_le_pred : q ≤ p - 1 :=
        Nat.le_of_dvd (Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt) hq_dvd_pred
      omega
