module

public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Polynomial

theorem intertwine_of_polynomial_entries {τ : Tag} {L : Type} [Field L] {ι' : Type*}
    [Fintype ι'] {F F' : L → Module.End L (RootModule τ L)} {D : ℕ}
    (hF : ∀ a b : Label τ, ∃ p : L[X], p.natDegree ≤ D ∧
      ∀ c, F c (Finsupp.single b 1) a = p.eval c)
    (hF' : ∀ a b : Label τ, ∃ p : L[X], p.natDegree ≤ D ∧
      ∀ c, F' c (Finsupp.single b 1) a = p.eval c)
    (z : Module.End L (RootModule τ L)) (f : ι' → L) (hf : Function.Injective f)
    (hcard : D < Fintype.card ι') (hz : ∀ j, z * F' (f j) = F (f j) * z) (t : L) :
    z * F' t = F t * z := by
  classical
  choose p hpdeg hpval using hF
  choose p' hpdeg' hpval' using hF'
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  set P : L[X] := ∑ d, C (z (Finsupp.single d 1) a) * p' d b -
    ∑ d, p a d * C (z (Finsupp.single b 1) d) with hP
  have hev : ∀ c, P.eval c = (z * F' c) (Finsupp.single b 1) a -
      (F c * z) (Finsupp.single b 1) a := by
    intro c
    rw [end_mul_single_apply, end_mul_single_apply, hP, eval_sub, eval_finsetSum,
      eval_finsetSum]
    congr 1
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [eval_mul, eval_C, ← hpval', mul_comm]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [eval_mul, eval_C, ← hpval, mul_comm]
  have hdeg : P.natDegree ≤ D := by
    rw [hP]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sum_le_of_forall_le _ _ fun d _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (hpdeg' d b)
    · refine (natDegree_sum_le_of_forall_le _ _ fun d _ => ?_)
      exact (natDegree_mul_C_le _ _).trans (hpdeg a d)
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hf (fun j => ?_)
      (lt_of_le_of_lt hdeg hcard)
    rw [hev, hz j, sub_self]
  have := hev t
  rw [hP0, eval_zero, eq_comm, sub_eq_zero] at this
  exact this

theorem odd_E6_finite_root_inner_graph_pointwise_faithfulness (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (L : Type) [Field L] (ι : K →+* L)
    (z : ModGL TwistTag.E6.tag L) (hz : z ∈ adjointGroup TwistTag.E6.tag L) (ε : ℕ)
    (hε : ε < 2)
    (hpt : ∀ h ∈ (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι),
      z * (diagramMap TwistTag.E6 L ^ ε * h * (diagramMap TwistTag.E6 L ^ ε)⁻¹) * z⁻¹ = h) :
    ε = 0 ∧ z = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hcard3 : 3 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card] at hcard2 ⊢
    obtain ⟨m, hm⟩ := hK
    omega
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · refine ⟨rfl, ?_⟩
    have hKgt : (if TwistTag.E6.tag = .G2 then 3 else 2) < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      have : TwistTag.E6.tag ≠ .G2 := by decide
      simp only [this, ↓reduceIte]
      omega
    refine (Chevalley_large_finite_root_centralizer_faithfulness TwistTag.E6.tag K hKgt L ι).2.2.1
      z hz fun h hh => ?_
    have h1 := hpt h hh
    rw [pow_zero, one_mul, inv_one, mul_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · exfalso
    have hD : entryDegreeBound TwistTag.E6.tag < Fintype.card K := by
      have : TwistTag.E6.tag ≠ .G2 := by decide
      simp only [entryDegreeBound, this, ↓reduceIte]
      omega
    have hx : ∀ (i : Fin TwistTag.E6.tag.rank) (c : K),
        (z : Module.End L (RootModule TwistTag.E6.tag L)) *
          xOp TwistTag.E6.tag L (TwistTag.E6.perm i) (ι c) =
        xOp TwistTag.E6.tag L i (ι c) * z := fun i c => by
      have h1 := hpt _ ⟨xUnit _ K i c, xUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_xUnit, pow_one, diagramMap_mul_xUnit_mul_inv,
        mul_inv_eq_iff_eq_mul] at h1
      exact congrArg Units.val h1
    have hy : ∀ (i : Fin TwistTag.E6.tag.rank) (c : K),
        (z : Module.End L (RootModule TwistTag.E6.tag L)) *
          yOp TwistTag.E6.tag L (TwistTag.E6.perm i) (ι c) =
        yOp TwistTag.E6.tag L i (ι c) * z := fun i c => by
      have h1 := hpt _ ⟨yUnit _ K i c, yUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_yUnit, pow_one, diagramMap_mul_yUnit_mul_inv,
        mul_inv_eq_iff_eq_mul] at h1
      exact congrArg Units.val h1
    have hx' : ∀ (i : Fin TwistTag.E6.tag.rank) (t : L), z * xUnit TwistTag.E6.tag L
        (TwistTag.E6.perm i) t = xUnit TwistTag.E6.tag L i t * z := fun i t => by
      refine Units.ext ?_
      refine intertwine_of_polynomial_entries (F := xOp TwistTag.E6.tag L i)
        (F' := xOp TwistTag.E6.tag L (TwistTag.E6.perm i)) (D := entryDegreeBound _)
        (fun a b => ?_) (fun a b => ?_) _ ι ι.injective hD (fun c => hx i c) t
      · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) TwistTag.E6.tag i a b
        exact ⟨p, hp, fun c => (hpq c).1⟩
      · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) TwistTag.E6.tag
          (TwistTag.E6.perm i) a b
        exact ⟨p, hp, fun c => (hpq c).1⟩
    have hy' : ∀ (i : Fin TwistTag.E6.tag.rank) (t : L), z * yUnit TwistTag.E6.tag L
        (TwistTag.E6.perm i) t = yUnit TwistTag.E6.tag L i t * z := fun i t => by
      refine Units.ext ?_
      refine intertwine_of_polynomial_entries (F := yOp TwistTag.E6.tag L i)
        (F' := yOp TwistTag.E6.tag L (TwistTag.E6.perm i)) (D := entryDegreeBound _)
        (fun a b => ?_) (fun a b => ?_) _ ι ι.injective hD (fun c => hy i c) t
      · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) TwistTag.E6.tag i a b
        exact ⟨q, hq, fun c => (hpq c).2⟩
      · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) TwistTag.E6.tag
          (TwistTag.E6.perm i) a b
        exact ⟨q, hq, fun c => (hpq c).2⟩
    set zA : adjointGroup TwistTag.E6.tag L := ⟨z, hz⟩ with hzA
    have h0 : exactNormalAut TwistTag.E6.tag L 1 (RingEquiv.refl L) 0 = 1 :=
      (rootDiagAut_eq_exactNormalAut (τ := TwistTag.E6.tag) (K := L) 1).symm.trans
        ((rootDiagAutHom TwistTag.E6.tag L).map_one)
    have hperm : ∀ i : Fin TwistTag.E6.tag.rank,
        exactPerm TwistTag.E6.tag 1 i = TwistTag.E6.perm i := fun i => by
      rw [show exactPerm TwistTag.E6.tag 1 = TwistTag.E6.perm from pow_one _]
    have hN : MulAut.conj zA * exactNormalAut TwistTag.E6.tag L 1 (RingEquiv.refl L)
        ((⟨1, by decide⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
        MulAut.conj (1 : adjointGroup TwistTag.E6.tag L) *
          exactNormalAut TwistTag.E6.tag L 1 (RingEquiv.refl L)
            ((⟨0, by decide⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) := by
      change _ = MulAut.conj (1 : adjointGroup TwistTag.E6.tag L) * exactNormalAut
        TwistTag.E6.tag L 1 (RingEquiv.refl L) 0
      rw [h0, map_one, one_mul]
      refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
      · rw [MulAut.mul_apply, exactNormalAut_adjX, MulAut.one_apply]
        refine Subtype.ext ?_
        change z * (xUnit TwistTag.E6.tag L (exactPerm TwistTag.E6.tag 1 i)
          (((1 : Fin TwistTag.E6.tag.rank → Lˣ) (exactPerm TwistTag.E6.tag 1 i) : L) *
            (RingEquiv.refl L) c)) * z⁻¹ = xUnit TwistTag.E6.tag L i c
        have e1 : (((1 : Fin TwistTag.E6.tag.rank → Lˣ) (exactPerm TwistTag.E6.tag 1 i) : Lˣ) :
            L) * (RingEquiv.refl L) c = c := by simp
        rw [mul_inv_eq_iff_eq_mul, e1, hperm i]
        exact hx' i c
      · rw [MulAut.mul_apply, exactNormalAut_adjY, MulAut.one_apply]
        refine Subtype.ext ?_
        change z * (yUnit TwistTag.E6.tag L (exactPerm TwistTag.E6.tag 1 i)
          ((((1 : Fin TwistTag.E6.tag.rank → Lˣ) (exactPerm TwistTag.E6.tag 1 i))⁻¹ : Lˣ) *
            (RingEquiv.refl L) c)) * z⁻¹ = yUnit TwistTag.E6.tag L i c
        have e1 : ((((1 : Fin TwistTag.E6.tag.rank → Lˣ) (exactPerm TwistTag.E6.tag 1 i))⁻¹ :
            Lˣ) : L) * (RingEquiv.refl L) c = c := by simp
        rw [mul_inv_eq_iff_eq_mul, e1, hperm i]
        exact hy' i c
    have hparam := (params_eq_of_conj_mul_exactNormalAut_eq (Or.inl rfl) hN).2
    exact absurd (congrArg Fin.val hparam) (by decide)

end CFSG.RankThree.PartOne.KE
