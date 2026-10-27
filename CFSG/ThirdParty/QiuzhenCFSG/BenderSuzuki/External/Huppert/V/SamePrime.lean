module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.FrattiniQuotient

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
set_option backward.isDefEq.respectTransparency false in
/--
The still-missing source double-count, stripped of the representation wrapper:
Huppert's Frobenius partition evaluates the quotient-conjugation product
`M_Q(n)` as `n ^ |Q/N|`.  The theorem
`huppertMQ_double_count_representation_norm_eval` below is now only the formal
translation of this product statement into additive representation language.
-/
public theorem hkt_frobenius_partition_quotientConjNormal_prod_eq_pow
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact s.Prime]
    (_hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (_hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal]
    (_hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsMulCommutative N]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (_hN_elem : IsElementaryAbelian s N)
    (_hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (_hψ : ψ = invariantQuotientAut φ N _hNφ)
    (_hrp : r ≠ p)
    (_hquot_action_distinct :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
        orderOf ψ = p ∧
          Nat.card (Subgroup.zpowers ψ) = p ∧
            IsCyclic (Subgroup.zpowers ψ) ∧
              IsPGroup p (Subgroup.zpowers ψ) ∧
                ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (_hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ)) :
    ∀ n : N,
      let : CommGroup N := IsMulCommutative.instCommGroup
      let : Fintype (Q ⧸ N) := Fintype.ofFinite _
      (∏ x : Q ⧸ N, quotientConjNormal N x n) =
        n ^ Nat.card (Q ⧸ N) := by
  classical
  intro n
  let : CommGroup N := IsMulCommutative.instCommGroup
  let : Fintype (Q ⧸ N) := Fintype.ofFinite _
  have hcard : Nat.card (Subgroup.zpowers ψ) = p :=
    _hquot_action_distinct.2.2.1
  have hregular : ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N) :=
    _hquot_action_distinct.2.2.2.2.2
  let : MulDistribMulAction (Multiplicative (ZMod p)) (Q ⧸ N) :=
    MulDistribMulAction.compHom (Q ⧸ N) (zmodZPowersMulAutHom ψ hcard)
  let SD : Type u :=
    (Q ⧸ N) ⋊[zmodZPowersMulAutHom ψ hcard] Multiplicative (ZMod p)
  let : Finite SD :=
    Finite.of_equiv ((Q ⧸ N) × Multiplicative (ZMod p))
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
  let : Fintype SD := Fintype.ofFinite SD
  let : MulDistribMulAction SD N :=
    MulDistribMulAction.compHom N
      (huppertMQSemidirectMulAutHom φ N _hNφ _hperiod ψ _hψ hcard)
  let K : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inl :
        Q ⧸ N →* SD)
  let R : Subgroup SD :=
    MonoidHom.range
      (SemidirectProduct.inr :
        Multiplicative (ZMod p) →* SD)
  let : Fintype K := Fintype.ofFinite K
  let : Fintype R := Fintype.ofFinite R
  let ρ : Representation (ZMod s) SD (Additive N) :=
    Theory.Representation.ofElementaryAbelianAction (A := SD) (G := N) (p := s)
  have hfrob : IsFrobeniusGroupWithKernelComplement K R := by
    simpa [K, R, SD] using
      huppertMQSemidirect_isFrobenius (N := N) (ψ := ψ) hcard hregular
  have hRzero_ofMul (m : N) :
      subgroupSum ρ R (Additive.ofMul m) = 0 := by
    simpa [ρ, R, SD] using
      huppertMQSemidirect_complement_subgroupSum_eq_zero
        φ _hprod _hperiod N _hNφ _hN_elem ψ _hψ hcard m
  have hRzero (v : Additive N) : subgroupSum ρ R v = 0 := by
    simpa using hRzero_ofMul (Additive.toMul v)
  have hRsum_zero (v : Additive N) :
      (∑ g : Multiplicative (ZMod p),
          ρ (SemidirectProduct.inr
            (φ := zmodZPowersMulAutHom ψ hcard) g) v) = 0 := by
    let eR : Multiplicative (ZMod p) ≃ R :=
      { toFun := fun g =>
          ⟨SemidirectProduct.inr (φ := zmodZPowersMulAutHom ψ hcard) g, ⟨g, rfl⟩⟩
        invFun := fun x => (x : SD).right
        left_inv := by
          intro g
          simp
        right_inv := by
          intro x
          rcases x.property with ⟨g, hg⟩
          apply Subtype.ext
          change
            SemidirectProduct.inr (φ := zmodZPowersMulAutHom ψ hcard) ((x : SD).right) =
              (x : SD)
          rw [← hg]
          rfl }
    have hsumR :
        subgroupSum ρ R v =
          ∑ g : Multiplicative (ZMod p), ρ (eR g) v := by
      calc
        subgroupSum ρ R v
            = ∑ r : R, ρ r v := by
                simpa [ρ, R] using subgroupSum_eq_sum ρ R v
        _ = ∑ g : Multiplicative (ZMod p), ρ (eR g) v := by
                exact
                  (Fintype.sum_equiv eR
                    (fun g : Multiplicative (ZMod p) => ρ (eR g) v)
                    (fun r : R => ρ r v)
                    (by intro g; rfl)).symm
    have hz := hRzero v
    rw [hsumR] at hz
    simpa [eR] using hz
  have hconj_zero :
      ∀ x : K, subgroupSum ρ (R.conjBy (x : SD)) (Additive.ofMul n) = 0 := by
    intro x
    let v : Additive N := Additive.ofMul n
    calc
      subgroupSum ρ (R.conjBy (x : SD)) v
          = ∑ r : R, ρ ((x : SD) * (r : SD) * (x : SD)⁻¹) v := by
              simpa [v] using subgroupSum_conjBy_eq ρ R (x : SD) v
      _ = ρ (x : SD) (∑ r : R, ρ r (ρ ((x : SD)⁻¹) v)) := by
              simp [map_sum, ← Module.End.mul_apply, ← map_mul, mul_assoc]
      _ = ρ (x : SD) (subgroupSum ρ R (ρ ((x : SD)⁻¹) v)) := by
              have hsum :
                  (∑ r : R, ρ r (ρ ((x : SD)⁻¹) v)) =
                    subgroupSum ρ R (ρ ((x : SD)⁻¹) v) := by
                simpa [ρ, R] using (subgroupSum_eq_sum ρ R (ρ ((x : SD)⁻¹) v)).symm
              rw [hsum]
      _ = 0 := by
              rw [hRzero (ρ ((x : SD)⁻¹) v)]
              simp
  have hnorm_zero :
      (let : Fintype SD := Fintype.ofFinite SD
       ρ.norm (Additive.ofMul n)) = 0 := by
    let v : Additive N := Additive.ofMul n
    let eSD : (Q ⧸ N) × Multiplicative (ZMod p) ≃ SD :=
      (SemidirectProduct.equivProd
        (φ := zmodZPowersMulAutHom ψ hcard)).symm
    have hnorm_reindex :
        ρ.norm v =
          ∑ ab : (Q ⧸ N) × Multiplicative (ZMod p), ρ (eSD ab) v := by
      calc
        ρ.norm v = ∑ g : SD, ρ g v := by
          simp [Representation.norm]
        _ = ∑ ab : (Q ⧸ N) × Multiplicative (ZMod p), ρ (eSD ab) v := by
          exact
            (Fintype.sum_equiv eSD
              (fun ab : (Q ⧸ N) × Multiplicative (ZMod p) => ρ (eSD ab) v)
              (fun g : SD => ρ g v)
              (by intro ab; rfl)).symm
    have hpair :
        (∑ ab : (Q ⧸ N) × Multiplicative (ZMod p), ρ (eSD ab) v) =
          ∑ a : Q ⧸ N,
            ρ (SemidirectProduct.inl
              (φ := zmodZPowersMulAutHom ψ hcard) a)
              (∑ b : Multiplicative (ZMod p),
                ρ (SemidirectProduct.inr
                  (φ := zmodZPowersMulAutHom ψ hcard) b) v) := by
      calc
        (∑ ab : (Q ⧸ N) × Multiplicative (ZMod p), ρ (eSD ab) v)
            =
              ∑ ab : (Q ⧸ N) × Multiplicative (ZMod p),
                ρ (SemidirectProduct.inl
                    (φ := zmodZPowersMulAutHom ψ hcard) ab.1 *
                  SemidirectProduct.inr
                    (φ := zmodZPowersMulAutHom ψ hcard) ab.2) v := by
              apply Finset.sum_congr rfl
              intro ab _hab
              rcases ab with ⟨a, b⟩
              change ρ ((⟨a, b⟩ : SD)) v =
                ρ (SemidirectProduct.inl
                    (φ := zmodZPowersMulAutHom ψ hcard) a *
                  SemidirectProduct.inr
                    (φ := zmodZPowersMulAutHom ψ hcard) b) v
              rw [SemidirectProduct.mk_eq_inl_mul_inr]
        _ =
              ∑ ab : (Q ⧸ N) × Multiplicative (ZMod p),
                ρ (SemidirectProduct.inl
                    (φ := zmodZPowersMulAutHom ψ hcard) ab.1)
                  (ρ (SemidirectProduct.inr
                    (φ := zmodZPowersMulAutHom ψ hcard) ab.2) v) := by
              apply Finset.sum_congr rfl
              intro ab _hab
              rw [← Module.End.mul_apply, ← map_mul]
        _ =
              ∑ a : Q ⧸ N,
                ∑ b : Multiplicative (ZMod p),
                  ρ (SemidirectProduct.inl
                      (φ := zmodZPowersMulAutHom ψ hcard) a)
                    (ρ (SemidirectProduct.inr
                      (φ := zmodZPowersMulAutHom ψ hcard) b) v) := by
              rw [← Fintype.sum_prod_type']
        _ =
              ∑ a : Q ⧸ N,
                ρ (SemidirectProduct.inl
                  (φ := zmodZPowersMulAutHom ψ hcard) a)
                  (∑ b : Multiplicative (ZMod p),
                    ρ (SemidirectProduct.inr
                      (φ := zmodZPowersMulAutHom ψ hcard) b) v) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [map_sum]
    calc
      ρ.norm v
          = ∑ ab : (Q ⧸ N) × Multiplicative (ZMod p), ρ (eSD ab) v := hnorm_reindex
      _ = ∑ a : Q ⧸ N,
            ρ (SemidirectProduct.inl
              (φ := zmodZPowersMulAutHom ψ hcard) a)
              (∑ b : Multiplicative (ZMod p),
                ρ (SemidirectProduct.inr
                  (φ := zmodZPowersMulAutHom ψ hcard) b) v) := hpair
      _ = 0 := by
            simp [hRsum_zero v]
  have hkernel_sum :
      subgroupSum ρ K (Additive.ofMul n) =
        (Nat.card K : ZMod s) • Additive.ofMul n :=
    hkt_frobenius_kernel_sum_eq_card_smul_of_norm_and_conj_zero
      K R ρ hfrob (Additive.ofMul n) hconj_zero hnorm_zero
  have hkernel_bridge :
      subgroupSum ρ K (Additive.ofMul n) = Additive.ofMul (huppertMQ N n) := by
    simpa [ρ, K, SD] using
      huppertMQSemidirect_kernel_subgroupSum_eq_huppertMQ
        φ N _hNφ _hperiod _hN_elem ψ _hψ hcard n
  have hkernel_card : Nat.card K = Nat.card (Q ⧸ N) := by
    simpa [K, SD] using huppertMQSemidirect_kernel_card (N := N) (ψ := ψ) hcard
  apply Additive.ofMul.injective
  calc
    Additive.ofMul (∏ x : Q ⧸ N, quotientConjNormal N x n)
        = Additive.ofMul (huppertMQ N n) := by
            simp [huppertMQ]
    _ = subgroupSum ρ K (Additive.ofMul n) := hkernel_bridge.symm
    _ = (Nat.card K : ZMod s) • Additive.ofMul n := hkernel_sum
    _ = (Nat.card (Q ⧸ N) : ZMod s) • Additive.ofMul n := by
            rw [hkernel_card]
    _ = Additive.ofMul (n ^ Nat.card (Q ⧸ N)) := by
            simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

public theorem hkt_centralizer_eq_top_of_quotientConjNormal_trivial
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    [IsMulCommutative N]
    (htriv : ∀ x : Q ⧸ N, quotientConjNormal N x = 1) :
    Subgroup.centralizer (N : Set Q) = ⊤ := by
  apply hkt_centralizer_eq_top_of_conjNormal_trivial
  intro q
  have hq := htriv (QuotientGroup.mk' N q)
  rw [quotientConjNormal_mk'] at hq
  exact hq

/--
Huppert V.8.13 (3b), the still-unformalized Frobenius-partition double-count
in additive representation form: the two source evaluations of `M(Q)` evaluate
the quotient-conjugation norm as scalar multiplication by `|Q/N|`.
-/
public theorem huppertMQ_double_count_representation_norm_eval
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact s.Prime]
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsMulCommutative N]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hrp : r ≠ p)
    (hquot_action_distinct :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
        orderOf ψ = p ∧
          Nat.card (Subgroup.zpowers ψ) = p ∧
            IsCyclic (Subgroup.zpowers ψ) ∧
              IsPGroup p (Subgroup.zpowers ψ) ∧
                ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ)) :
    ∀ n : N,
      let : CommGroup N := IsMulCommutative.instCommGroup
      let : Fintype (Q ⧸ N) := Fintype.ofFinite _
      let : MulDistribMulAction (Q ⧸ N) N :=
        MulDistribMulAction.compHom N (quotientConjNormal N)
      (Theory.Representation.ofElementaryAbelianAction (A := Q ⧸ N) (G := N) (p := s)).norm
          (Additive.ofMul n) =
        (Nat.card (Q ⧸ N) : ZMod s) • Additive.ofMul n := by
  classical
  intro n
  let : CommGroup N := IsMulCommutative.instCommGroup
  let : Fintype (Q ⧸ N) := Fintype.ofFinite _
  let : MulDistribMulAction (Q ⧸ N) N :=
    MulDistribMulAction.compHom N (quotientConjNormal N)
  have hmq_eval : huppertMQ N n = n ^ Nat.card (Q ⧸ N) := by
    change
      (∏ x : Q ⧸ N, quotientConjNormal N x n) =
        n ^ Nat.card (Q ⧸ N)
    exact
      hkt_frobenius_partition_quotientConjNormal_prod_eq_pow
        φ hprod hperiod N hNφ hN_elem hs_ne_r ψ hψ hrp
        hquot_action_distinct hquot_zpowers_cyclic n
  calc
    (Theory.Representation.ofElementaryAbelianAction (A := Q ⧸ N) (G := N) (p := s)).norm
        (Additive.ofMul n)
        = Additive.ofMul (huppertMQ N n) := by
          exact (huppertMQ_eq_representation_norm N hN_elem n).symm
    _ = Additive.ofMul (n ^ Nat.card (Q ⧸ N)) := by
          rw [hmq_eval]
    _ = (Nat.card (Q ⧸ N) : ZMod s) • Additive.ofMul n := by
          simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

/--
Huppert V.8.13 (3b), multiplicative form of the Frobenius-partition
double-count: the additive norm evaluation gives `M_Q(n)=n^|Q/N|`.
The downstream triviality of quotient conjugation is proved separately from
this formula.
-/
public theorem huppertMQ_double_count_eval
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact s.Prime]
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsMulCommutative N]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hrp : r ≠ p)
    (hquot_action_distinct :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
        orderOf ψ = p ∧
          Nat.card (Subgroup.zpowers ψ) = p ∧
            IsCyclic (Subgroup.zpowers ψ) ∧
              IsPGroup p (Subgroup.zpowers ψ) ∧
                ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ)) :
    ∀ n : N, huppertMQ N n = n ^ Nat.card (Q ⧸ N) := by
  classical
  intro n
  apply Additive.ofMul.injective
  let : CommGroup N := IsMulCommutative.instCommGroup
  let : Fintype (Q ⧸ N) := Fintype.ofFinite _
  let : MulDistribMulAction (Q ⧸ N) N :=
    MulDistribMulAction.compHom N (quotientConjNormal N)
  calc
    Additive.ofMul (huppertMQ N n)
        =
          (Theory.Representation.ofElementaryAbelianAction (A := Q ⧸ N) (G := N) (p := s)).norm
            (Additive.ofMul n) := by
          exact huppertMQ_eq_representation_norm N hN_elem n
    _ = (Nat.card (Q ⧸ N) : ZMod s) • Additive.ofMul n := by
          exact
            huppertMQ_double_count_representation_norm_eval
              φ hprod hperiod N hNφ hN_elem hs_ne_r ψ hψ hrp
              hquot_action_distinct hquot_zpowers_cyclic n
    _ = Additive.ofMul (n ^ Nat.card (Q ⧸ N)) := by
          simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

/-- Huppert's `M(Q)` evaluation forces the quotient conjugation action to be
trivial.  The source double-count itself is isolated in
`huppertMQ_double_count_eval`. -/
public theorem huppertMQ_double_count_forces_quotientConjNormal_trivial
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact s.Prime]
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsMulCommutative N]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hrp : r ≠ p)
    (hquot_action_distinct :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
        orderOf ψ = p ∧
          Nat.card (Subgroup.zpowers ψ) = p ∧
            IsCyclic (Subgroup.zpowers ψ) ∧
              IsPGroup p (Subgroup.zpowers ψ) ∧
                ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ)) :
    ∀ x : Q ⧸ N, quotientConjNormal N x = 1 :=
  quotientConjNormal_trivial_of_huppertMQ_eval N hN_elem hs_ne_r
    (huppertMQ_double_count_eval φ hprod hperiod N hNφ hN_elem hs_ne_r
      ψ hψ hrp hquot_action_distinct hquot_zpowers_cyclic)

/--
The centralizer form of Huppert V.8.13 (3b), derived from the action-trivial
`M(Q)` core.  The surrounding proof combines this with the already-proved
maximal-branch fact `C_Q(N)=N`.
-/
public theorem huppertMQ_double_count_forces_lower_centralizer_top
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact s.Prime]
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hrp : r ≠ p)
    (hquot_action_distinct :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
        orderOf ψ = p ∧
          Nat.card (Subgroup.zpowers ψ) = p ∧
            IsCyclic (Subgroup.zpowers ψ) ∧
              IsPGroup p (Subgroup.zpowers ψ) ∧
                ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ)) :
    Subgroup.centralizer (N : Set Q) = ⊤ := by
  let : IsMulCommutative N := hN_elem.toIsMulCommutative
  exact hkt_centralizer_eq_top_of_quotientConjNormal_trivial N
    (huppertMQ_double_count_forces_quotientConjNormal_trivial
      φ hprod hperiod N hNφ hN_elem hs_ne_r ψ hψ hrp
      hquot_action_distinct hquot_zpowers_cyclic)

/-- Normalized Huppert V.8.13 (3d) product calculation.  If the original
restricted HKT automorphism followed by conjugation with a lift `b` fixes a
nontrivial lower-layer element, then the HKT product identity applied to `x*b`
and to `b` forces `x^p = 1`; the elementary-abelian exponent `s ≠ p` then
forces `x = 1`. -/
public theorem hkt_same_prime_product_identity_normalized_core
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    (hprime : Nat.Prime p)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Fact s.Prime] (hN_elem : IsElementaryAbelian s N)
    (hs_ne_p : s ≠ p)
    (b : Q) (hb_mod_N : φ b * b⁻¹ ∈ N)
    (x : N) (hx_ne_one : x ≠ 1)
    (hmixed :
      (invariantSubgroupAut φ N hNφ * MulAut.conjNormal (H := N) b) x = x) :
    False := by
  let : Fact p.Prime := ⟨hprime⟩
  let : IsMulCommutative N := hN_elem.toIsMulCommutative
  let F : Q → Q := fun q => φ q
  let B : ℕ → Q := fun m => ((List.range m).map (fun k ↦ F^[k] b)).prod
  let P : ℕ → Q := fun m => ((List.range m).map (fun k ↦ F^[k] ((x : Q) * b))).prod
  let c : Q := φ b * b⁻¹
  have hcN : c ∈ N := by simpa [c] using hb_mod_N
  have hφxN : φ (x : Q) ∈ N := (hNφ (x : Q)).mp x.2
  let y : Q := b * φ (x : Q) * b⁻¹
  have hyN : y ∈ N := by
    simpa [y] using (inferInstance : N.Normal).conj_mem (φ (x : Q)) hφxN b
  have hcy : c * y = y * c := by
    simpa [c, y] using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := N)).comm ⟨c, hcN⟩ ⟨y, hyN⟩)
  have hφb : φ b = c * b := by
    simp [c, mul_assoc]
  have hmixed_coe : φ (b * (x : Q) * b⁻¹) = (x : Q) := by
    simpa [invariantSubgroupAut, MulAut.conjNormal_apply, MulAut.conj_apply,
      mul_assoc] using congrArg Subtype.val hmixed
  have hφ_conj_eq_y : φ (b * (x : Q) * b⁻¹) = y := by
    calc
      φ (b * (x : Q) * b⁻¹)
          = φ b * φ (x : Q) * (φ b)⁻¹ := by
            simp [map_mul, mul_assoc]
      _ = c * y * c⁻¹ := by
            rw [hφb]
            simp [y, mul_inv_rev, mul_assoc]
      _ = y := by
            calc
              c * y * c⁻¹ = y * c * c⁻¹ := by rw [hcy]
              _ = y := by simp [mul_assoc]
  have hrel0 : b * φ (x : Q) * b⁻¹ = (x : Q) := by
    calc
      b * φ (x : Q) * b⁻¹ = y := rfl
      _ = φ (b * (x : Q) * b⁻¹) := hφ_conj_eq_y.symm
      _ = (x : Q) := hmixed_coe
  have hrel_iter (m : ℕ) :
      F^[m] b * F^[m + 1] (x : Q) * (F^[m] b)⁻¹ = F^[m] (x : Q) := by
    have h := congrArg (fun q : Q => (φ ^ m) q) hrel0
    simpa [F, hkt_mulAut_pow_apply_iterate φ m b,
      hkt_mulAut_pow_apply_iterate φ m (φ (x : Q)),
      hkt_mulAut_pow_apply_iterate φ m (x : Q),
      Function.iterate_succ_apply, map_mul, mul_assoc] using h
  have hB_succ (m : ℕ) : B (m + 1) = B m * F^[m] b := by
    simpa [B] using List.prod_range_succ (fun k ↦ F^[k] b) m
  have hP_succ (m : ℕ) : P (m + 1) = P m * F^[m] ((x : Q) * b) := by
    simpa [P] using List.prod_range_succ (fun k ↦ F^[k] ((x : Q) * b)) m
  have hterm (m : ℕ) :
      F^[m] ((x : Q) * b) = F^[m] (x : Q) * F^[m] b := by
    rw [← hkt_mulAut_pow_apply_iterate φ m ((x : Q) * b),
      ← hkt_mulAut_pow_apply_iterate φ m (x : Q),
      ← hkt_mulAut_pow_apply_iterate φ m b]
    simp
  have hB_conj : ∀ m : ℕ, B m * F^[m] (x : Q) * (B m)⁻¹ = (x : Q) := by
    intro m
    induction m with
    | zero =>
        simp [B, F]
    | succ m ih =>
        calc
          B (m + 1) * F^[m + 1] (x : Q) * (B (m + 1))⁻¹
              = B m * (F^[m] b * F^[m + 1] (x : Q) * (F^[m] b)⁻¹) *
                  (B m)⁻¹ := by
                rw [hB_succ]
                simp [mul_inv_rev, mul_assoc]
          _ = B m * F^[m] (x : Q) * (B m)⁻¹ := by
                rw [hrel_iter m]
          _ = (x : Q) := ih
  have hB_mul_iter (m : ℕ) : B m * F^[m] (x : Q) = (x : Q) * B m := by
    calc
      B m * F^[m] (x : Q)
          = (B m * F^[m] (x : Q) * (B m)⁻¹) * B m := by
            simp [mul_assoc]
      _ = (x : Q) * B m := by rw [hB_conj m]
  have hP_formula : ∀ m : ℕ, P m = (x : Q) ^ m * B m := by
    intro m
    induction m with
    | zero =>
        simp [P, B]
    | succ m ih =>
        calc
          P (m + 1) = P m * F^[m] ((x : Q) * b) := hP_succ m
          _ = ((x : Q) ^ m * B m) * (F^[m] (x : Q) * F^[m] b) := by
                rw [ih, hterm m]
          _ = (x : Q) ^ (m + 1) * B (m + 1) := by
                rw [hB_succ]
                calc
                  ((x : Q) ^ m * B m) * (F^[m] (x : Q) * F^[m] b)
                      = (x : Q) ^ m * (B m * F^[m] (x : Q)) * F^[m] b := by
                        simp [mul_assoc]
                  _ = (x : Q) ^ m * ((x : Q) * B m) * F^[m] b := by
                        rw [hB_mul_iter m]
                  _ = (x : Q) ^ (m + 1) * (B m * F^[m] b) := by
                        simp [pow_succ, mul_assoc]
  have hPp : P p = 1 := by
    simpa [P, F] using hprod ((x : Q) * b)
  have hBp : B p = 1 := by
    simpa [B, F] using hprod b
  have hxpowQ : (x : Q) ^ p = 1 := by
    have hformula := hP_formula p
    rw [hformula, hBp, mul_one] at hPp
    exact hPp
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    simpa using hxpowQ
  have hxs : x ^ s = 1 := by
    simpa using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p s N) x)
  have horder_p : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have horder_s : orderOf x ∣ s := orderOf_dvd_of_pow_eq_one hxs
  have hcop : Nat.Coprime p s :=
    (Nat.coprime_primes (Fact.out : Nat.Prime p) (Fact.out : Nat.Prime s)).2 (by
      intro hps
      exact hs_ne_p hps.symm)
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder_p horder_s
  exact hx_ne_one (orderOf_eq_one_iff.mp horder_one)

/--
Huppert V.8.13 (3b), isolated as the Frobenius-partition and `M(Q)`
double-count step: in the maximal elementary-layer branch, the elementary
prime of the quotient chief layer must equal the HKT period prime.
-/
public theorem hkt_frobenius_partition_forces_quotient_prime_eq_period
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    (hprime : Nat.Prime p) (_hp2 : p ≠ 2)
    (_hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (_hnon_nil : ¬ Group.IsNilpotent Q)
    (_hsolv : Group.IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (_hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (_hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (_hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (_hN_nil : Group.IsNilpotent N)
    (_hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (_hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (_hcenter_bot : Subgroup.center Q = ⊥)
    [Fact r.Prime] [Fact s.Prime]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (hcentralizer_N : Subgroup.centralizer (N : Set Q) = N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (_hquot_card_arith :
      ∃ n : ℕ,
        Nat.card (Q ⧸ N) = r ^ n ∧ n ≠ 0 ∧
          (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card (Q ⧸ N) → s = r) ∧
            (IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = r))
    (hquot_action_if_distinct :
      r ≠ p →
        fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
          orderOf ψ = p ∧
            Nat.card (Subgroup.zpowers ψ) = p ∧
              IsCyclic (Subgroup.zpowers ψ) ∧
                IsPGroup p (Subgroup.zpowers ψ) ∧
                  ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (_hquot_coprime_if_distinct :
      r ≠ p → Nat.Coprime p (Nat.card (Q ⧸ N)))
    (hquot_proposition_3_9_if_distinct :
      r ≠ p → IsCyclic (Subgroup.zpowers ψ))
    (_hlower_action_if_distinct :
      s ≠ p →
        fixedPointSubgroup
            (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ ∧
          orderOf (invariantSubgroupAut φ N hNφ) = p ∧
            Nat.card (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) = p ∧
              IsCyclic (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
                IsPGroup p (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
                  ActsRegularly (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) N) :
    r = p := by
  by_contra hne
  have hrp : r ≠ p := by
    intro h
    exact hne h
  have hquot_action_distinct := hquot_action_if_distinct hrp
  have hquot_zpowers_cyclic : IsCyclic (Subgroup.zpowers ψ) :=
    hquot_proposition_3_9_if_distinct hrp
  let : Fact p.Prime := ⟨hprime⟩
  have hcentralizer_top :
      Subgroup.centralizer (N : Set Q) = ⊤ :=
    huppertMQ_double_count_forces_lower_centralizer_top
      φ hprod _hperiod N hNφ hN_elem hs_ne_r ψ hψ hrp
      hquot_action_distinct hquot_zpowers_cyclic
  have hN_top : N = ⊤ := by
    simpa [hcentralizer_N] using hcentralizer_top
  exact hN_ne_top hN_top

/--
Huppert V.8.13 (3d), after the noncyclic elementary-abelian `p`-operator
group has produced a genuinely mixed fixed point.  This is the remaining
source calculation: combine the HKT product identity on `Q`, the fact that the
second coordinate is induced by conjugation with a lift `a`, and the mixed
fixed element on the lower elementary layer `N` to force the impossible
characteristic relation `s = p`.

The statement deliberately keeps the two automorphism coordinates as powers of
the specific source operators `invariantSubgroupAut φ N hNφ` and
`MulAut.conjNormal a`; the analogous statement for arbitrary commuting
fixed-point-free automorphisms would be false.
-/
public theorem hkt_same_prime_v812_product_identity_core
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p s : ℕ}
    (hprime : Nat.Prime p)
    (_hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Fact s.Prime] (hN_elem : IsElementaryAbelian s N)
    (hs_ne_p : s ≠ p)
    (a : Q) (ha_mod_N : φ a * a⁻¹ ∈ N)
    (z1 : Subgroup.zpowers (invariantSubgroupAut φ N hNφ))
    (z2 : Subgroup.zpowers (MulAut.conjNormal (H := N) a))
    (x : N) (hx_ne_one : x ≠ 1)
    (hmixed : ((z1 : MulAut N) * (z2 : MulAut N)) x = x)
    (hz1_top : Subgroup.zpowers z1 = ⊤)
    (_hz2_top : Subgroup.zpowers z2 = ⊤)
    (_hz1_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers z1)) N = ⊥)
    (_hz2_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers z2)) N = ⊥)
    (hz12_commute : Commute ((z1 : MulAut N)) ((z2 : MulAut N)))
    (_hz1_order : orderOf ((z1 : MulAut N)) = p)
    (_hz2_order : orderOf ((z2 : MulAut N)) = p) :
    False := by
  let : Fact p.Prime := ⟨hprime⟩
  let : IsMulCommutative N := hN_elem.toIsMulCommutative
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let β : MulAut N := MulAut.conjNormal (H := N) a
  have hprodα :
      ∀ n : N,
        ((List.range p).map (fun k ↦ (fun n : N => α n)^[k] n)).prod = 1 := by
    simpa [α] using hkt_product_identity_of_invariant_subgroup φ N hNφ hprod
  let αgen : Subgroup.zpowers α := ⟨α, Subgroup.mem_zpowers α⟩
  have hαgen_mem_z1 : αgen ∈ Subgroup.zpowers z1 := by
    simp [αgen, α, hz1_top]
  rcases Subgroup.mem_zpowers_iff.mp hαgen_mem_z1 with ⟨t, hz1_t_eq_αgen⟩
  have hz1_t_eq_α : ((z1 : MulAut N) ^ t) = α := by
    simpa [αgen] using
      congrArg (fun y : Subgroup.zpowers α => (y : MulAut N)) hz1_t_eq_αgen
  have hz2_mem : (z2 : MulAut N) ∈ Subgroup.zpowers β := by
    simp [β]
  rcases Subgroup.mem_zpowers_iff.mp hz2_mem with ⟨j, hz2_eq⟩
  have hz2_lift :
      MulAut.conjNormal (H := N) (a ^ j) = (z2 : MulAut N) := by
    calc
      MulAut.conjNormal (H := N) (a ^ j) = β ^ j := by
        simp [β, hkt_conjNormal_zpow_eq N a j]
      _ = (z2 : MulAut N) := hz2_eq
  have ha_mod_N_j : φ (a ^ j) * (a ^ j)⁻¹ ∈ N :=
    hkt_lift_zpow_mod_mem φ N a j ha_mod_N
  have hmixed_lift :
      ((z1 : MulAut N) * MulAut.conjNormal (H := N) (a ^ j)) x = x := by
    simpa [hz2_lift] using hmixed
  let γ : MulAut N := (z1 : MulAut N) * (z2 : MulAut N)
  have hγ_fixed : γ • x = x := by
    simpa [γ, MulAut.smul_def] using hmixed
  have hγt_fixed : (γ ^ t) x = x := by
    have hsmul : (γ ^ t) • x = x :=
      smul_eq_self_of_mem_zpowers (Subgroup.zpow_mem_zpowers γ t) hγ_fixed
    simpa [MulAut.smul_def] using hsmul
  have hγt_eq : γ ^ t = α * (z2 : MulAut N) ^ t := by
    calc
      γ ^ t = ((z1 : MulAut N) * (z2 : MulAut N)) ^ t := rfl
      _ = (z1 : MulAut N) ^ t * (z2 : MulAut N) ^ t := hz12_commute.mul_zpow t
      _ = α * (z2 : MulAut N) ^ t := by rw [hz1_t_eq_α]
  have hz2t_lift :
      MulAut.conjNormal (H := N) ((a ^ j) ^ t) = (z2 : MulAut N) ^ t := by
    calc
      MulAut.conjNormal (H := N) ((a ^ j) ^ t) =
          (MulAut.conjNormal (H := N) (a ^ j)) ^ t := by
        simp [hkt_conjNormal_zpow_eq N (a ^ j) t]
      _ = (z2 : MulAut N) ^ t := by rw [hz2_lift]
  have ha_mod_N_jt : φ ((a ^ j) ^ t) * ((a ^ j) ^ t)⁻¹ ∈ N :=
    hkt_lift_zpow_mod_mem φ N (a ^ j) t ha_mod_N_j
  have hmixed_normalized :
      (α * MulAut.conjNormal (H := N) ((a ^ j) ^ t)) x = x := by
    calc
      (α * MulAut.conjNormal (H := N) ((a ^ j) ^ t)) x
          = (α * (z2 : MulAut N) ^ t) x := by rw [hz2t_lift]
      _ = (γ ^ t) x := by rw [← hγt_eq]
      _ = x := hγt_fixed
  exact hkt_same_prime_product_identity_normalized_core
    (φ := φ) (p := p) (s := s) hprime hprod N hNφ hN_elem hs_ne_p
    ((a ^ j) ^ t) ha_mod_N_jt x hx_ne_one hmixed_normalized

/--
Huppert V.8.13 (3c)--(3d), isolated after the quotient prime has been forced
to equal the HKT period prime.  The remaining source step constructs the two
fixed-point-free automorphisms on the lower elementary abelian layer and then
applies the V.8.12 linear fixed-point-free contradiction.
-/
public theorem hkt_same_prime_fixedPoint_quotient_contradiction
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (_hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (_hnon_nil : ¬ Group.IsNilpotent Q)
    (_hsolv : Group.IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (_hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (_hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (_hN_nil : Group.IsNilpotent N)
    (_hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (_hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hcenter_bot : Subgroup.center Q = ⊥)
    [Fact r.Prime] [Fact s.Prime]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (_hcentralizer_N : Subgroup.centralizer (N : Set Q) = N)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hrp : r = p)
    (hquot_fixed_ne_bot :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) ≠ ⊥)
    (hquot_card_eq_p_of_same_prime :
      r = p → IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = p)
    (hlower_action_same_prime :
      fixedPointSubgroup
          (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ ∧
        orderOf (invariantSubgroupAut φ N hNφ) = p ∧
          Nat.card (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) = p ∧
            IsCyclic (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
              IsPGroup p (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
                ActsRegularly (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) N) :
    False := by
  have hquot_comm : IsMulCommutative (Q ⧸ N) :=
    (inferInstance : IsElementaryAbelian r (Q ⧸ N)).toIsMulCommutative
  have hquot_fixed_top :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊤ := by
    have : IsMulCommutative (Q ⧸ N) := hquot_comm
    exact
      hkt_quotient_fixedPointSubgroup_eq_top_of_ne_bot
        φ N hNφ hNmax ψ hψ hquot_fixed_ne_bot
  have hquot_cyclic : IsCyclic (Q ⧸ N) := by
    have : IsMulCommutative (Q ⧸ N) := hquot_comm
    exact
      hkt_quotient_isCyclic_of_fixedPointSubgroup_eq_top
        φ N hNφ hNmax ψ hψ hquot_fixed_top
  have hquot_card_p : Nat.card (Q ⧸ N) = p :=
    hquot_card_eq_p_of_same_prime hrp hquot_cyclic
  obtain ⟨a, ha_sup_top⟩ :=
    hkt_exists_zpowers_sup_top_of_cyclic_quotient N hquot_cyclic
  let α : MulAut N := invariantSubgroupAut φ N hNφ
  let β : MulAut N := MulAut.conjNormal (H := N) a
  have hβ_fix :
      fixedPointSubgroup (↥(Subgroup.zpowers β)) N = ⊥ := by
    have : IsMulCommutative N := hN_elem.toIsMulCommutative
    simpa [β] using
      hkt_conjNormal_fixedPointSubgroup_eq_bot_of_sup_zpowers_center
        N a ha_sup_top hcenter_bot
  have ha_mod_N : φ a * a⁻¹ ∈ N :=
    hkt_quotient_fixed_top_forces_lift_div_mem
      φ N hNφ ψ hψ hquot_fixed_top a
  have hαβ_comm : α * β = β * α := by
    have : IsMulCommutative N := hN_elem.toIsMulCommutative
    simpa [α, β] using
      hkt_invariantSubgroupAut_commute_conjNormal_of_lift_fixed_mod
        φ N hNφ a ha_mod_N
  rcases hlower_action_same_prime with
    ⟨hα_fix_raw, hα_order_raw, hα_card_raw, hα_cyclic_raw,
      hα_pgroup_raw, hα_regular_raw⟩
  have hα_fix :
      fixedPointSubgroup (↥(Subgroup.zpowers α)) N = ⊥ := by
    simpa [α] using hα_fix_raw
  have hα_order : orderOf α = p := by
    simpa [α] using hα_order_raw
  have hα_card : Nat.card (Subgroup.zpowers α) = p := by
    simpa [α] using hα_card_raw
  have hα_cyclic : IsCyclic (Subgroup.zpowers α) := by
    simpa [α] using hα_cyclic_raw
  have hα_pgroup : IsPGroup p (Subgroup.zpowers α) := by
    simpa [α] using hα_pgroup_raw
  have hα_regular : ActsRegularly (Subgroup.zpowers α) N := by
    simpa [α] using hα_regular_raw
  let : Fact p.Prime := ⟨hprime⟩
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN_ne_bot
  have hapN : a ^ p ∈ N := by
    have hquot_pow : (QuotientGroup.mk' N a) ^ p = 1 := by
      have hpow_card : (QuotientGroup.mk' N a) ^ Nat.card (Q ⧸ N) = 1 :=
        pow_card_eq_one' (x := QuotientGroup.mk' N a)
      simpa [hquot_card_p] using hpow_card
    have hmk_pow : QuotientGroup.mk' N (a ^ p) = 1 := by
      simpa using hquot_pow
    exact (QuotientGroup.eq_one_iff (N := N) (x := a ^ p)).1 hmk_pow
  have hβ_pow : β ^ p = 1 := by
    simpa [β] using hkt_conjNormal_pow_eq_one_of_lift_pow_mem N a hapN
  have hβ_ne_one : β ≠ 1 := by
    intro hβ_one
    have hβ_fix_top : fixedPointSubgroup (↥(Subgroup.zpowers β)) N = ⊤ := by
      rw [hβ_one]
      ext x
      simp [fixedPointSubgroup, FixedPoints.mem_subgroup]
    have htop_bot : (⊤ : Subgroup N) = ⊥ := by
      rw [← hβ_fix_top, hβ_fix]
    exact (top_ne_bot : (⊤ : Subgroup N) ≠ ⊥) htop_bot
  have hβ_order : orderOf β = p := by
    have hβ_dvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβ_pow
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf β) hβ_dvd with
      horder_one | horder_p
    · exact False.elim <| hβ_ne_one (orderOf_eq_one_iff.mp horder_one)
    · exact horder_p
  have hβ_card : Nat.card (Subgroup.zpowers β) = p :=
    natCard_zpowers_eq_prime_of_orderOf_eq β hβ_order
  have hβ_cyclic : IsCyclic (Subgroup.zpowers β) :=
    isCyclic_zpowers β
  have hβ_pgroup : IsPGroup p (Subgroup.zpowers β) :=
    isPGroup_zpowers_of_orderOf_eq_prime β hβ_order
  have hβ_regular : ActsRegularly (Subgroup.zpowers β) N :=
    hkt_actsRegularly_of_zpowers_prime_order_fixedPointSubgroup_eq_bot
      β hβ_card hβ_fix
  let A : Type u := Subgroup.zpowers α × Subgroup.zpowers β
  let ρ : A →* MulAut N := {
    toFun := fun z => (z.1 : MulAut N) * (z.2 : MulAut N)
    map_one' := by
      simp
    map_mul' x y := by
      have hαβ : Commute α β := by
        exact (commute_iff_eq α β).2 hαβ_comm
      have hyx : Commute (y.1 : MulAut N) (x.2 : MulAut N) := by
        rcases Subgroup.mem_zpowers_iff.mp y.1.2 with ⟨m, hm⟩
        rcases Subgroup.mem_zpowers_iff.mp x.2.2 with ⟨n, hn⟩
        rw [← hm, ← hn]
        exact (hαβ.zpow_left m).zpow_right n
      calc
        ((x.1 * y.1 : Subgroup.zpowers α) : MulAut N) *
            ((x.2 * y.2 : Subgroup.zpowers β) : MulAut N)
            = ((x.1 : MulAut N) * (y.1 : MulAut N)) *
                ((x.2 : MulAut N) * (y.2 : MulAut N)) := rfl
        _ = (x.1 : MulAut N) * ((y.1 : MulAut N) * (x.2 : MulAut N)) *
            (y.2 : MulAut N) := by
              simp [mul_assoc]
        _ = (x.1 : MulAut N) * ((x.2 : MulAut N) * (y.1 : MulAut N)) *
            (y.2 : MulAut N) := by
              rw [hyx.eq]
        _ = (x.1 : MulAut N) * (x.2 : MulAut N) *
            ((y.1 : MulAut N) * (y.2 : MulAut N)) := by
              simp [mul_assoc] }
  let : MulDistribMulAction A N := MulDistribMulAction.compHom N ρ
  have hs_ne_p : s ≠ p := by
    simpa [hrp] using hs_ne_r
  have hN_pgroup : IsPGroup s N := IsElementaryAbelian.isPGroup s N
  have hcop_N : Nat.Coprime p (Nat.card N) := by
    have hcop :=
      IsPGroup.coprime_card_of_ne p s (fun hps => hs_ne_p hps.symm)
        (Subgroup.zpowers α) N hα_pgroup hN_pgroup
    simpa [hα_card] using hcop
  have hA_pgroup : IsPGroup p A := by
    intro z
    rcases hα_pgroup z.1 with ⟨m, hm⟩
    rcases hβ_pgroup z.2 with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    apply Prod.ext
    · calc
        z.1 ^ p ^ (m + n) = (z.1 ^ p ^ m) ^ p ^ n := by
          rw [Nat.pow_add, pow_mul]
        _ = 1 := by simp [hm]
    · calc
        z.2 ^ p ^ (m + n) = z.2 ^ p ^ (n + m) := by rw [Nat.add_comm]
        _ = (z.2 ^ p ^ n) ^ p ^ m := by rw [Nat.pow_add, pow_mul]
        _ = 1 := by simp [hn]
  have hA_card : Nat.card A = p ^ 2 := by
    simp [A, Nat.card_prod, hα_card, hβ_card, pow_two]
  have hA_exp_dvd : Monoid.exponent A ∣ p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro z
    apply Prod.ext
    · have hz1pow_card : z.1 ^ Nat.card (Subgroup.zpowers α) = 1 :=
        pow_card_eq_one' (x := z.1)
      change z.1 ^ p = (1 : Subgroup.zpowers α)
      simpa [hα_card] using hz1pow_card
    · have hz2pow_card : z.2 ^ Nat.card (Subgroup.zpowers β) = 1 :=
        pow_card_eq_one' (x := z.2)
      change z.2 ^ p = (1 : Subgroup.zpowers β)
      simpa [hβ_card] using hz2pow_card
  have hA_noncyclic : ¬ IsCyclic A := by
    intro hA_cyclic
    have hcard_dvd_p : p ^ 2 ∣ p := by
      simpa [hA_card, hA_cyclic.exponent_eq_card] using hA_exp_dvd
    have hp_pos : 0 < p := hprime.pos
    have hp2_le_p : p ^ 2 ≤ p := Nat.le_of_dvd hp_pos hcard_dvd_p
    have hp_lt_p2 : p < p ^ 2 := by
      simpa [pow_two] using lt_mul_of_one_lt_right hp_pos hprime.one_lt
    exact (not_lt_of_ge hp2_le_p) hp_lt_p2
  have hA_not_regular : ¬ ActsRegularly A N := by
    intro hA_regular
    exact hA_noncyclic
      (proposition_3_9 (p := p) (H := N) (R := A)
        hprime (hprime.odd_of_ne_two hp2) hcop_N hA_pgroup hA_regular)
  have hA_fixed_witness :
      ∃ z : A, z ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers z)) N ≠ ⊥ := by
    classical
    simpa [ActsRegularly, not_forall] using hA_not_regular
  rcases hA_fixed_witness with ⟨z, hz_ne_one, hz_fix_ne_bot⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hz_fix_ne_bot with ⟨xFix, hxFix_ne_one⟩
  let x : N := xFix
  have hx_ne_one : x ≠ 1 := by
    intro hx
    exact hxFix_ne_one (Subtype.ext hx)
  have hx_mem_fixed :
      x ∈ fixedPointSubgroup (↥(Subgroup.zpowers z)) N := xFix.2
  have hz_smul_x : z • x = x := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx_mem_fixed
    exact hx_mem_fixed ⟨z, Subgroup.mem_zpowers z⟩
  have hz_mulAut_x : (((z.1 : Subgroup.zpowers α) : MulAut N) *
        ((z.2 : Subgroup.zpowers β) : MulAut N)) x = x := by
    change ρ z x = x at hz_smul_x
    simpa [ρ] using hz_smul_x
  have hz_fst_ne_one : z.1 ≠ 1 := by
    intro hz1
    have hz2_ne_one : z.2 ≠ 1 := by
      intro hz2
      exact hz_ne_one (Prod.ext hz1 hz2)
    have hz2_x : z.2 • x = x := by
      change (z.2 : MulAut N) x = x
      simpa [hz1] using hz_mulAut_x
    have hx_mem_z2 :
        x ∈ fixedPointSubgroup (↥(Subgroup.zpowers z.2)) N := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro b
      exact smul_eq_self_of_mem_zpowers b.2 hz2_x
    have hx_bot : x ∈ (⊥ : Subgroup N) := by
      simpa [hβ_regular z.2 hz2_ne_one] using hx_mem_z2
    exact hx_ne_one (Subgroup.mem_bot.mp hx_bot)
  have hz_snd_ne_one : z.2 ≠ 1 := by
    intro hz2
    have hz1_ne_one : z.1 ≠ 1 := by
      intro hz1
      exact hz_ne_one (Prod.ext hz1 hz2)
    have hz1_x : z.1 • x = x := by
      change (z.1 : MulAut N) x = x
      simpa [hz2] using hz_mulAut_x
    have hx_mem_z1 :
        x ∈ fixedPointSubgroup (↥(Subgroup.zpowers z.1)) N := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro b
      exact smul_eq_self_of_mem_zpowers b.2 hz1_x
    have hx_bot : x ∈ (⊥ : Subgroup N) := by
      simpa [hα_regular z.1 hz1_ne_one] using hx_mem_z1
    exact hx_ne_one (Subgroup.mem_bot.mp hx_bot)
  have hα_card_prime : Nat.Prime (Nat.card (Subgroup.zpowers α)) := by
    simpa [hα_card] using hprime
  have hβ_card_prime : Nat.Prime (Nat.card (Subgroup.zpowers β)) := by
    simpa [hβ_card] using hprime
  have hz1_zpowers_top : Subgroup.zpowers z.1 = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hα_card_prime hz_fst_ne_one
  have hz2_zpowers_top : Subgroup.zpowers z.2 = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hβ_card_prime hz_snd_ne_one
  let αgen : Subgroup.zpowers α := ⟨α, Subgroup.mem_zpowers α⟩
  let βgen : Subgroup.zpowers β := ⟨β, Subgroup.mem_zpowers β⟩
  have hαgen_mem_z1 : αgen ∈ Subgroup.zpowers z.1 := by
    simp [hz1_zpowers_top]
  have hβgen_mem_z2 : βgen ∈ Subgroup.zpowers z.2 := by
    simp [hz2_zpowers_top]
  rcases Subgroup.mem_zpowers_iff.mp hαgen_mem_z1 with ⟨m, hαgen_zpow⟩
  rcases Subgroup.mem_zpowers_iff.mp hβgen_mem_z2 with ⟨n, hβgen_zpow⟩
  have hz1_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers z.1)) N = ⊥ :=
    hα_regular z.1 hz_fst_ne_one
  have hz2_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers z.2)) N = ⊥ :=
    hβ_regular z.2 hz_snd_ne_one
  have hz12_commute :
      Commute ((z.1 : Subgroup.zpowers α) : MulAut N)
        ((z.2 : Subgroup.zpowers β) : MulAut N) := by
    have hαβ_commute : Commute α β := by
      exact (commute_iff_eq α β).2 hαβ_comm
    rcases Subgroup.mem_zpowers_iff.mp z.1.2 with ⟨i, hz1_pow⟩
    rcases Subgroup.mem_zpowers_iff.mp z.2.2 with ⟨j, hz2_pow⟩
    rw [← hz1_pow, ← hz2_pow]
    exact (hαβ_commute.zpow_left i).zpow_right j
  have hz1_order : orderOf ((z.1 : Subgroup.zpowers α) : MulAut N) = p := by
    have hz1_order_sub : orderOf z.1 = p := by
      have horder_dvd : orderOf z.1 ∣ p := by
        simpa [hα_card] using orderOf_dvd_natCard z.1
      rcases hprime.eq_one_or_self_of_dvd (orderOf z.1) horder_dvd with h1 | hp
      · exact False.elim (hz_fst_ne_one (orderOf_eq_one_iff.mp h1))
      · exact hp
    simpa [Subgroup.orderOf_coe] using hz1_order_sub
  have hz2_order : orderOf ((z.2 : Subgroup.zpowers β) : MulAut N) = p := by
    have hz2_order_sub : orderOf z.2 = p := by
      have horder_dvd : orderOf z.2 ∣ p := by
        simpa [hβ_card] using orderOf_dvd_natCard z.2
      rcases hprime.eq_one_or_self_of_dvd (orderOf z.2) horder_dvd with h1 | hp
      · exact False.elim (hz_snd_ne_one (orderOf_eq_one_iff.mp h1))
      · exact hp
    simpa [Subgroup.orderOf_coe] using hz2_order_sub
  -- Huppert V.8.13 (3c)--(3d): use the nontrivial quotient fixed-point data
  -- to choose the lift `P`, prove `H` and `P` act fixed-point-freely on `N`,
  -- and apply V.8.12 to the elementary abelian group they generate.
  exact
    hkt_same_prime_v812_product_identity_core
      φ hprime _hperiod hprod N hNφ hN_elem hs_ne_p a ha_mod_N z.1 z.2 x
      hx_ne_one hz_mulAut_x hz1_zpowers_top hz2_zpowers_top hz1_fix_bot
      hz2_fix_bot hz12_commute hz1_order hz2_order

/--
The remaining Huppert V.8.13 step (3b)--(3d) after both the upper quotient and
the lower subgroup have been proved elementary abelian.  This is the genuine
Frobenius partition / `M(Q)` double-count and V.8.12 fixed-point-free linear
group contradiction.
-/
public theorem hkt_false_of_solvable_maximal_branch_elementary_layers
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r s : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hsolv : Group.IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hN_nil : Group.IsNilpotent N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hcenter_bot : Subgroup.center Q = ⊥)
    [Fact r.Prime] [Fact s.Prime]
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hN_elem : IsElementaryAbelian s N)
    (hs_ne_r : s ≠ r)
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hquot_card_arith :
      ∃ n : ℕ,
        Nat.card (Q ⧸ N) = r ^ n ∧ n ≠ 0 ∧
          (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card (Q ⧸ N) → s = r) ∧
            (IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = r))
    (hquot_action_if_distinct :
      r ≠ p →
        fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
          orderOf ψ = p ∧
            Nat.card (Subgroup.zpowers ψ) = p ∧
              IsCyclic (Subgroup.zpowers ψ) ∧
                IsPGroup p (Subgroup.zpowers ψ) ∧
                  ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_coprime_if_distinct :
      r ≠ p → Nat.Coprime p (Nat.card (Q ⧸ N)))
    (hquot_proposition_3_9_if_distinct :
      r ≠ p → IsCyclic (Subgroup.zpowers ψ)) :
    False := by
  have hcentralizer_N : Subgroup.centralizer (N : Set Q) = N :=
    hkt_centralizer_lower_eq_self_of_maximal_elementary_branch
      φ N hNinv hN_ne_bot hN_ne_top hNmax hcenter_bot hN_elem
  let : Fact p.Prime := ⟨hprime⟩
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hN_ne_bot
  have hlower_action_if_distinct :
      s ≠ p →
        fixedPointSubgroup
            (↥(Subgroup.zpowers (invariantSubgroupAut φ N hNφ))) N = ⊥ ∧
          orderOf (invariantSubgroupAut φ N hNφ) = p ∧
            Nat.card (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) = p ∧
              IsCyclic (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
                IsPGroup p (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) ∧
                  ActsRegularly (Subgroup.zpowers (invariantSubgroupAut φ N hNφ)) N := by
    intro hsp
    exact
      huppertV813_lower_distinct_prime_regular_action
        φ N hNφ hsp hperiod hprod
  have hquot_card_eq_p_of_same_prime :
      r = p → IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = p := by
    intro hrp hquot_cyclic
    exact
      hkt_quotient_card_eq_period_prime_of_same_prime_cyclic
        N hrp hquot_card_arith hquot_cyclic
  have hrp : r = p :=
    hkt_frobenius_partition_forces_quotient_prime_eq_period
      φ hprime hp2 hperiod hprod hnon_nil hsolv N hNφ hNinv hN_ne_bot hN_ne_top
      hNmax hN_nil hquot_nil hproper_invariant_quotient_nil hcenter_bot
      hN_elem hs_ne_r hcentralizer_N ψ hψ hquot_card_arith hquot_action_if_distinct
      hquot_coprime_if_distinct hquot_proposition_3_9_if_distinct
      hlower_action_if_distinct
  have hψ_dvd_p : orderOf ψ ∣ p := by
    rw [hψ]
    exact hkt_invariant_quotient_orderOf_dvd_prime_period φ N hNφ hperiod
  have hψ_pgroup : IsPGroup p (Subgroup.zpowers ψ) :=
    hkt_zpowers_isPGroup_of_orderOf_dvd_prime ψ hψ_dvd_p
  have hquot_fixed_ne_bot :
      fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) ≠ ⊥ :=
    hkt_same_prime_quotient_fixedPointSubgroup_ne_bot
      N ψ hrp hψ_pgroup
  have hs_ne_p : s ≠ p := by
    intro hsp
    exact hs_ne_r (by simpa [hrp] using hsp)
  exact
    hkt_same_prime_fixedPoint_quotient_contradiction
      φ hprime hp2 hperiod hprod hnon_nil hsolv N hNφ hNinv hN_ne_bot hN_ne_top
      hNmax hN_nil hquot_nil hproper_invariant_quotient_nil hcenter_bot
      hN_elem hs_ne_r hcentralizer_N ψ hψ hrp hquot_fixed_ne_bot
      hquot_card_eq_p_of_same_prime (hlower_action_if_distinct hs_ne_p)

/--
The remaining Huppert V.8.13 step (3b)--(3d) endpoint after the quotient
chief layer has been identified, its elementary-cardinality arithmetic has
been recorded, and the `r ≠ p` fixed-point-free/coprime/proposition-3.9
step has been proved. The missing source work is the lower-layer module
calculation: Huppert's Frobenius partition and the two evaluations of `M(Q)`
which first force `r = p`, then rule out the elementary abelian group generated
by the two fixed-point-free automorphisms via V.8.12.
-/
public theorem huppertV813_false_of_solvable_maximal_branch_after_quotient
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hsolv : Group.IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hN_nil : Group.IsNilpotent N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hcenter_bot : Subgroup.center Q = ⊥)
    [Fact r.Prime] [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (ψ : MulAut (Q ⧸ N))
    (hψ : ψ = invariantQuotientAut φ N hNφ)
    (hquot_card_arith :
      ∃ n : ℕ,
        Nat.card (Q ⧸ N) = r ^ n ∧ n ≠ 0 ∧
          (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card (Q ⧸ N) → s = r) ∧
            (IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = r))
    (hquot_action_if_distinct :
      r ≠ p →
        fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
          orderOf ψ = p ∧
            Nat.card (Subgroup.zpowers ψ) = p ∧
              IsCyclic (Subgroup.zpowers ψ) ∧
                IsPGroup p (Subgroup.zpowers ψ) ∧
                  ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N))
    (hquot_coprime_if_distinct :
      r ≠ p → Nat.Coprime p (Nat.card (Q ⧸ N)))
    (hquot_proposition_3_9_if_distinct :
      r ≠ p → IsCyclic (Subgroup.zpowers ψ)) :
    False := by
  obtain ⟨s, hs_prime, hN_pgroup⟩ :=
    hkt_maximal_lower_nilpotent_exists_isPGroup
      φ N hNinv hN_ne_bot hN_ne_top hN_nil
      hproper_invariant_quotient_nil hnon_nil
  have hs_ne_r : s ≠ r := by
    intro hsr
    let : Fact s.Prime := ⟨hs_prime⟩
    have hN_r : IsPGroup r N := by
      simpa [hsr] using hN_pgroup
    exact hkt_false_of_same_prime_lower_and_quotient_pgroups N hnon_nil hN_r
  let : Fact s.Prime := ⟨hs_prime⟩
  obtain ⟨hΦ_normal, hΦ_invariant, hΦ_le_N, hΦ_p, hN_frattini_quot_elem,
    hΦ_ne_bot_of_ne, hΦ_ne_top⟩ :=
      huppertV813_lower_frattini_ambient_facts
        φ N hNinv hN_ne_bot hN_ne_top hN_pgroup
  have hΦamb_bot : (frattini N).map N.subtype = (⊥ : Subgroup Q) :=
    hkt_maximal_lower_frattini_ambient_eq_bot
      φ N hproper_invariant_quotient_nil hnon_nil hΦ_normal hΦ_invariant hΦ_ne_top
  have hN_elem : IsElementaryAbelian s N :=
    hkt_lower_isElementaryAbelian_of_frattini_ambient_eq_bot N hN_pgroup hΦamb_bot
  exact
    hkt_false_of_solvable_maximal_branch_elementary_layers
      φ hprime hp2 hperiod hprod hnon_nil hsolv N hNφ hNinv hN_ne_bot hN_ne_top
      hNmax hN_nil hquot_nil hproper_invariant_quotient_nil hcenter_bot
      hN_elem hs_ne_r ψ hψ hquot_card_arith hquot_action_if_distinct
      hquot_coprime_if_distinct hquot_proposition_3_9_if_distinct
/--
Huppert V.8.13 step 3(a)--(d), isolated at the source-faithful maximal
proper invariant normal subgroup.  The maximality hypothesis records that the
upper quotient is the chief-factor layer; the remaining proof must show this
layer and the lower subgroup are elementary abelian, then execute Huppert
(3b)--(3d).
-/
public theorem hkt_false_of_solvable_maximal_branch_core
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (hprime : Nat.Prime p) (hp2 : p ≠ 2)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1)
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hsolv : Group.IsSolvable Q)
    (N : Subgroup Q) [N.Normal]
    (hNinv : IsInvariant (Subgroup.zpowers φ) Q N)
    (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N)
    (hN_nil : Group.IsNilpotent N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N))
    (hproper_invariant_quotient_nil :
      ∀ K : Subgroup Q, [K.Normal] → K ≠ ⊥ → K ≠ ⊤ →
        (∀ q : Q, q ∈ K ↔ φ q ∈ K) → Group.IsNilpotent (Q ⧸ K))
    (hcenter_bot : Subgroup.center Q = ⊥) :
    False := by
  have hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N :=
    hkt_zpowers_invariant_generator φ N
  obtain ⟨r, hr_prime, hquot_elem⟩ :=
    hkt_maximal_invariant_quotient_exists_isElementaryAbelian
      φ N hNφ hN_ne_top hNmax hquot_nil
  let : Fact r.Prime := ⟨hr_prime⟩
  let : IsElementaryAbelian r (Q ⧸ N) := hquot_elem
  have : Nontrivial (Q ⧸ N) :=
    (QuotientGroup.nontrivial_iff (N := N)).2 hN_ne_top
  obtain ⟨n, hquot_card, hn_ne_zero, hquot_prime_divisor_eq_r,
    hquot_card_eq_r_of_cyclic⟩ :=
      elementaryAbelian_natCard_primePower_facts (r := r) (G := Q ⧸ N)
  have hquot_card_arith :
      ∃ n : ℕ,
        Nat.card (Q ⧸ N) = r ^ n ∧ n ≠ 0 ∧
          (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card (Q ⧸ N) → s = r) ∧
            (IsCyclic (Q ⧸ N) → Nat.card (Q ⧸ N) = r) :=
    ⟨n, hquot_card, hn_ne_zero, hquot_prime_divisor_eq_r, hquot_card_eq_r_of_cyclic⟩
  let : Fact p.Prime := ⟨hprime⟩
  let ψ : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  have hquot_action_if_distinct :
      r ≠ p →
        fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ ∧
          orderOf ψ = p ∧
            Nat.card (Subgroup.zpowers ψ) = p ∧
              IsCyclic (Subgroup.zpowers ψ) ∧
                IsPGroup p (Subgroup.zpowers ψ) ∧
                  ActsRegularly (Subgroup.zpowers ψ) (Q ⧸ N) := by
    intro hrp
    simpa [ψ] using
      huppertV813_quotient_distinct_prime_regular_action
        φ N hNφ hrp hperiod hprod
  have hquot_coprime_if_distinct :
      r ≠ p → Nat.Coprime p (Nat.card (Q ⧸ N)) := by
    intro hrp
    rw [hquot_card]
    exact ((Nat.coprime_primes hprime hr_prime).2 (fun hpr => hrp hpr.symm)).pow_right n
  have hquot_proposition_3_9_if_distinct :
      r ≠ p → IsCyclic (Subgroup.zpowers ψ) := by
    intro hrp
    obtain ⟨_hfix, _horder, _hcard, _hcyclic, hpgroup, hregular⟩ :=
      hquot_action_if_distinct hrp
    exact proposition_3_9 (p := p) (H := Q ⧸ N) (R := Subgroup.zpowers ψ)
      hprime (hprime.odd_of_ne_two hp2) (hquot_coprime_if_distinct hrp) hpgroup hregular
  exact
    huppertV813_false_of_solvable_maximal_branch_after_quotient
      φ hprime hp2 hperiod hprod hnon_nil hsolv N hNφ hNinv hN_ne_bot hN_ne_top
      hNmax hN_nil hquot_nil hproper_invariant_quotient_nil hcenter_bot
      ψ rfl hquot_card_arith hquot_action_if_distinct hquot_coprime_if_distinct
      hquot_proposition_3_9_if_distinct
end External
end CFSG.BenderSuzuki
