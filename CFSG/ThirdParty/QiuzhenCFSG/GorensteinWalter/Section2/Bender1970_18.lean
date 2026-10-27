module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Statements 1.8 and the shared F*-centralizer helpers

This module proves Statement 1.8
(`bender1970_1_8_centralizerNormalizer_pGroup`) and exposes the reusable
`F*`-of-centralizer/normalizer facts used by Statement 1.9 in
`Bender1970_19.lean`.

The route follows the source: with `K = O^p(F*(C_G(U)))` (resp.
`O^p(F*(N_G(U)))`), the Thompson lemma 1.1 forces `K` to centralize
`F*(G)`, hence `K` is a `p`-group.  Since a group whose `p`-residual is a
`p`-group is itself a `p`-group, `F*(C_G(U))` and `F*(N_G(U))` are
`p`-groups.
-/

noncomputable section

open scoped Pointwise commutatorElement BigOperators

namespace CFSG.GorensteinWalter

universe u

/-! ## Generic residual facts -/

/-- If `H / N` is a `p`-group and `N` is normal in `H`, then
`O^p(H) ≤ N`. -/
public theorem pResidualOf_le_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H N : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hNle : N ≤ H)
    (hN : (N.subgroupOf H).Normal)
    (hQ : IsPGroup p (H ⧸ N.subgroupOf H)) :
    pResidualOf H p ≤ N := by
  let : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_card.mp hQ) with ⟨n, hn⟩
  have hidx : ∃ n : ℕ, (N.subgroupOf H).index = p ^ n := ⟨n, by
    rw [← hn]
    exact (Subgroup.index_eq_card (N.subgroupOf H)).symm⟩
  have hle := pResidualOf_le_of_normal_index H p (N.subgroupOf H) hN hidx
  simpa [Subgroup.map_subgroupOf_eq_of_le hNle] using hle

/-- Every element of `H` whose order is coprime to `p` lies in
`O^p(H)`: it is killed in every normal quotient of `p`-power index. -/
public theorem mem_pResidualOf_of_order_coprime
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) {x : G} (hx : x ∈ H)
    (hcop : Nat.Coprime p (orderOf x)) : x ∈ pResidualOf H p := by
  rw [pResidualOf]
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_sInf]
  intro N hN
  rcases hN with ⟨hNnormal, n, hn⟩
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (H ⧸ N) := IsPGroup.of_card (n := n) (by
    rw [← hn]
    exact (Subgroup.index_eq_card N).symm)
  let q : H ⧸ N := QuotientGroup.mk' N ⟨x, hx⟩
  have hcopH : Nat.Coprime p (orderOf (⟨x, hx⟩ : H)) := by
    have hord : orderOf (⟨x, hx⟩ : H) = orderOf x :=
      (orderOf_injective H.subtype H.subtype_injective (⟨x, hx⟩ : H)).symm
    rwa [hord]
  have hqcop : (orderOf q).Coprime (orderOf (⟨x, hx⟩ : H)) :=
    hQ.orderOf_coprime hcopH q
  have hqdiv : orderOf q ∣ orderOf (⟨x, hx⟩ : H) :=
    orderOf_map_dvd (QuotientGroup.mk' N) (⟨x, hx⟩)
  have hq1 : q = 1 :=
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hqcop dvd_rfl hqdiv))
  exact (QuotientGroup.eq_one_iff (N := N) (x := (⟨x, hx⟩ : H))).1 hq1

/-- If the `p`-residual of `H` is a `p`-group, then so is `H`. -/
public theorem isPGroup_of_pResidualOf_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hR : IsPGroup p (pResidualOf H p)) : IsPGroup p H := by
  apply isPGroup_of_primeFactors_subset_singleton H hp
  intro q hq
  by_contra hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvd : q ∣ Nat.card (↥H) := Nat.dvd_of_mem_primeFactors hq
  let : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) q hqdvd
  have hordG : orderOf (x : G) = q := by
    calc
      orderOf (x : G) = orderOf x :=
        by simpa using (orderOf_injective H.subtype H.subtype_injective x).symm
      _ = q := hxorder
  have hcopq : Nat.Coprime p q := (Nat.coprime_primes hp hqprime).2 (by
    intro hpq
    exact hqp hpq.symm)
  have hcop : Nat.Coprime p (orderOf (x : G)) := by
    rwa [hordG]
  have hxR : (x : G) ∈ pResidualOf H p :=
    mem_pResidualOf_of_order_coprime H p hp x.2 hcop
  let r : pResidualOf H p := ⟨x, hxR⟩
  let : Fact p.Prime := ⟨hp⟩
  have hRcop : (orderOf r).Coprime q := hR.orderOf_coprime hcopq r
  have hordR : orderOf r = q := by
    calc
      orderOf r = orderOf (r : G) :=
        (orderOf_injective (pResidualOf H p).subtype
          (pResidualOf H p).subtype_injective r).symm
      _ = orderOf (x : G) := rfl
      _ = q := hordG
  have hqcop : q.Coprime q := hordR ▸ hRcop
  exact hqprime.ne_one (Nat.eq_one_of_dvd_coprimes hqcop dvd_rfl dvd_rfl)

/-- `O^p(H)` is characteristic in `H`. -/
public theorem pResidualOf_subgroupOf_characteristic
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Characteristic := by
  classical
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  have hNres : (pResidualOf H p).subgroupOf H = sInf family := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective (sInf family)
  rw [hNres]
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact pResidual_map_iso (G := H) (H := H) p e

/-- `O^p(H)` is normal in `H`. -/
public instance pResidualOf_subgroupOf_normal
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Normal := by
  have : ((pResidualOf H p).subgroupOf H).Characteristic :=
    pResidualOf_subgroupOf_characteristic H p
  infer_instance

/-- `H / O^p(H)` is a `p`-group. -/
public theorem isPGroup_quotient_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) :
    IsPGroup p (H ⧸ (pResidualOf H p).subgroupOf H) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have : ((pResidualOf H p).subgroupOf H).Normal := pResidualOf_subgroupOf_normal H p
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  let N : Subgroup H := sInf family
  have hNres : (pResidualOf H p).subgroupOf H = N := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  let ι : Type u := {M : Subgroup H // M ∈ family}
  have : Finite ι := Finite.of_injective (fun M : ι => (M : Subgroup H)) (by
    intro M N h
    exact Subtype.ext h)
  let : Fintype ι := Fintype.ofFinite ι
  have : ∀ M : ι, (M : Subgroup H).Normal := fun M => M.2.1
  have : N.Normal := by
    change (sInf family).Normal
    rw [sInf_eq_iInf']
    exact Subgroup.normal_iInf_normal (fun M : ι => M.2.1)
  let n : ι → ℕ := fun M => Classical.choose M.2.2
  have hn : ∀ M : ι, (M : Subgroup H).index = p ^ n M := fun M =>
    Classical.choose_spec M.2.2
  have hQcard : ∀ M : ι, Nat.card (H ⧸ (M : Subgroup H)) = p ^ n M := by
    intro M
    rw [← hn M, Subgroup.index_eq_card]
  let T : Type u := ∀ M : ι, H ⧸ (M : Subgroup H)
  have hTcard : Nat.card T = p ^ (∑ M, n M) := by
    rw [Nat.card_pi]
    simp_rw [hQcard]
    rw [Finset.prod_pow_eq_pow_sum]
  have hT : IsPGroup p T := IsPGroup.of_card hTcard
  let f : H →* T :=
    { toFun := fun h M => QuotientGroup.mk' (M : Subgroup H) h
      map_one' := by ext M; rfl
      map_mul' := by intro x y; ext M; rfl }
  have hfker : f.ker = N := by
    ext h
    constructor
    · intro hh
      rw [Subgroup.mem_sInf]
      intro M hM
      have : M.Normal := hM.1
      have hcomp : QuotientGroup.mk' M h = (1 : H ⧸ M) := congrFun hh ⟨M, hM⟩
      exact (QuotientGroup.eq_one_iff (N := M) h).1 hcomp
    · intro hh
      ext M
      have : (M : Subgroup H).Normal := M.2.1
      exact (QuotientGroup.eq_one_iff (N := (M : Subgroup H)) h).2
        ((Subgroup.mem_sInf.mp hh) (M : Subgroup H) M.2)
  let eN : H ⧸ N ≃* f.range :=
    (QuotientGroup.congr (G' := f.ker) (H' := N) (MulEquiv.refl H) (by simpa using hfker)).symm.trans
      (QuotientGroup.quotientKerEquivRange f)
  let eRes : H ⧸ (pResidualOf H p).subgroupOf H ≃* f.range :=
    (QuotientGroup.congr (G' := N)
      (H' := (pResidualOf H p).subgroupOf H) (MulEquiv.refl H)
        (by simpa using hNres.symm)).symm.trans eN
  have hRange : IsPGroup p (f.range : Subgroup T) :=
    hT.to_subgroup (f.range : Subgroup T)
  exact hRange.of_equiv eRes.symm

/-! ## Basic `F*` containment and `O_q` commutativity -/

/-- `F*(A) ≤ A`. -/
public theorem generalizedFittingSubgroupOf_le {G : Type u} [Group G]
    (A : Subgroup G) : generalizedFittingSubgroupOf A ≤ A := by
  rw [generalizedFittingSubgroupOf]
  refine sup_le ?_ ?_
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  · rw [componentLayerOf]
    refine sSup_le ?_
    intro E hE
    exact hE.1

/-- `O_p(A) ≤ F(A)`. -/
public theorem qCoreOf_le_fittingSubgroupOf {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) : qCoreOf A p ≤ fittingSubgroupOf A := by
  let : Fact p.Prime := ⟨hp⟩
  have hle : pCore p (↥A) ≤ fittingSubgroup (↥A) :=
    pCore_le_fitting (G := ↥A) p
  exact Subgroup.map_mono (f := A.subtype) hle

/-- For distinct primes, `O_q(A)` centralizes `O_p(A)`. -/
public theorem qCoreOf_centralizer_of_ne {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    qCoreOf A q ≤ Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (Subgroup.mem_map).1 hx with ⟨x₀, hx₀, rfl⟩
  rcases (Subgroup.mem_map).1 hy with ⟨y₀, hy₀, rfl⟩
  have hdisj : Disjoint (pCore q (↥A)) (pCore p (↥A)) :=
    IsPGroup.disjoint_of_ne q p (hne.symm)
      (pCore q (↥A)) (pCore p (↥A))
      (pCore_isPGroup (p := q) (G := ↥A)) (pCore_isPGroup (p := p) (G := ↥A))
  have hcomm₀ : ⁅x₀, y₀⁆ = (1 : ↥A) := by
    have hmem : ⁅x₀, y₀⁆ ∈ ⁅pCore q (↥A), pCore p (↥A)⁆ :=
      Subgroup.commutator_mem_commutator hx₀ hy₀
    have hle : ⁅pCore q (↥A), pCore p (↥A)⁆ ≤
        pCore q (↥A) ⊓ pCore p (↥A) :=
      Subgroup.commutator_le_inf (H₁ := pCore q (↥A)) (H₂ := pCore p (↥A))
    have hinf : (pCore q (↥A) ⊓ pCore p (↥A) : Subgroup (↥A)) = ⊥ := by
      exact hdisj.eq_bot
    have : ⁅x₀, y₀⁆ ∈ (⊥ : Subgroup (↥A)) := by
      rw [← hinf]
      exact hle hmem
    simpa using this
  exact congrArg Subtype.val ((commutatorElement_eq_one_iff_mul_comm.mp hcomm₀).symm)

/-! ## `O^p(F*(A))` centralizes `O_p(A)` -/

/-- `F(A)` is the join of its `O_q(A)` over the prime divisors of `|A|`. -/
public theorem fittingSubgroupOf_eq_iSup_qCoreOf {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) :
    fittingSubgroupOf A =
      ⨆ q : (Nat.card (↥A)).primeFactors.attach, qCoreOf A q.1.1 := by
  unfold fittingSubgroupOf qCoreOf
  rw [fitting_eq_sup_pCore, Subgroup.map_iSup]

/-- `O^p(F*(A))` centralizes `O_p(A)`. -/
public theorem pResidualOf_generalizedFitting_centralizer_qCore
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  classical
  let H : Subgroup G := generalizedFittingSubgroupOf A
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let P : Subgroup G := qCoreOf A p
  let Z : Subgroup G := Subgroup.centralizer (P : Set G)
  let K : Subgroup G := H ⊓ Z
  have hHF : F ≤ H := le_sup_left
  have hHE : E ≤ H := le_sup_right
  have hHA : H ≤ A := generalizedFittingSubgroupOf_le A
  have hFA : F ≤ A := by
    exact hHF.trans hHA
  have hPleF : P ≤ F := qCoreOf_le_fittingSubgroupOf A p hp
  have hPleH : P ≤ H := hPleF.trans hHF
  have hPleA : P ≤ A := hPleF.trans hFA
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := F)).mp (layer_centralizes_fitting A)
  have hZF : Subgroup.centralizer (F : Set G) ≤ Z :=
    Subgroup.centralizer_le (show (P : Set G) ⊆ (F : Set G) from hPleF)
  have hEcentral : E ≤ Z := hEF.trans hZF
  -- `H ≤ N_G(P)`: `O_p(A)` is normal in `A`.
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro h hh z hz
    exact (qCoreOf_normal_in A p).2 h (hHA hh) z hz
  -- `K = H ⊓ C_G(P)` is normal in `H`.
  have hKleH : K ≤ H := inf_le_left
  have hKnormal : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKleH]
    intro x h hx hh
    have hxH : x ∈ H := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxZ' : x ∈ Subgroup.centralizer (P : Set G) := hxZ
    have hmH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    have hmZ : h * x * h⁻¹ ∈ Z := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : h⁻¹ * z * h ∈ P :=
        by simpa using
          (Subgroup.le_set_normalizer_iff).1 hHnormP (h⁻¹) (H.inv_mem hh) z hz
      have hkx : x * (h⁻¹ * z * h) = (h⁻¹ * z * h) * x :=
        (Subgroup.mem_centralizer_iff.mp hxZ' (h⁻¹ * z * h) hz').symm
      have hmain : (h * x * h⁻¹) * z = z * (h * x * h⁻¹) := by
        calc
          (h * x * h⁻¹) * z = h * (x * (h⁻¹ * z * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * z * h) * x) * h⁻¹ := by rw [hkx]
          _ = z * (h * x * h⁻¹) := by group
      exact hmain.symm
    exact ⟨hmH, hmZ⟩
  let π : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hKmap : (K.subgroupOf H).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := K.subgroupOf H) (f := π)).2
    intro x hx
    simpa [π, QuotientGroup.ker_mk'] using hx
  have hPsub : IsPGroup p (P.subgroupOf H) :=
    (qCoreOf_isPGroup A p).of_equiv (Subgroup.subgroupOfEquivOfLe hPleH).symm
  have hPm : IsPGroup p ((P.subgroupOf H).map π) :=
    IsPGroup.map hPsub π
  -- Every `O_q(A)` for `q ≠ p` lies in `K`; hence `F(A)` maps into
  -- `O_p(A)` after quotienting by `K`.
  have hFleKP : F ≤ K ⊔ P := by
    change fittingSubgroupOf A ≤ K ⊔ P
    rw [fittingSubgroupOf_eq_iSup_qCoreOf A]
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact le_sup_right
    · have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hQleZ : qCoreOf A q.1.1 ≤ Z :=
        qCoreOf_centralizer_of_ne A hp hqprime (by
          intro hpq
          exact hqp hpq.symm)
      have hQleH : qCoreOf A q.1.1 ≤ H :=
        (qCoreOf_le_fittingSubgroupOf A q.1.1 hqprime).trans hHF
      exact le_trans (le_inf hQleH hQleZ) le_sup_left
  have hFm_le : (F.subgroupOf H).map π ≤ (P.subgroupOf H).map π := by
    calc
      (F.subgroupOf H).map π ≤ ((K ⊔ P).subgroupOf H).map π :=
        Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono H hFleKP)
      _ = ((K.subgroupOf H ⊔ P.subgroupOf H).map π) := by
        rw [Subgroup.subgroupOf_sup hKleH hPleH]
      _ = (P.subgroupOf H).map π := by
        rw [Subgroup.map_sup, hKmap]
        simp
  have hFm : IsPGroup p ((F.subgroupOf H).map π) :=
    IsPGroup.to_le hPm hFm_le
  have hEm : IsPGroup p ((E.subgroupOf H).map π) := by
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    rw [hEmap]
    exact IsPGroup.of_bot
  have htop_eq : (⊤ : Subgroup H) = F.subgroupOf H ⊔ E.subgroupOf H := by
    rw [← Subgroup.subgroupOf_self H]
    change (F ⊔ E).subgroupOf H = F.subgroupOf H ⊔ E.subgroupOf H
    exact Subgroup.subgroupOf_sup hHF hHE
  have hQ : IsPGroup p ((⊤ : Subgroup H).map π) := by
    rw [htop_eq, Subgroup.map_sup]
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    have : ((E.subgroupOf H).map π).Normal := by
      rw [hEmap]
      infer_instance
    exact IsPGroup.to_sup_of_normal_right hFm hEm
  have hQquot : IsPGroup p (H ⧸ K.subgroupOf H) := by
    have htopmap : (⊤ : Subgroup H).map π = ⊤ :=
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (K.subgroupOf H))
    have hQtop : IsPGroup p (⊤ : Subgroup (H ⧸ K.subgroupOf H)) := by
      rw [← htopmap]
      exact hQ
    exact hQtop.of_equiv Subgroup.topEquiv
  have hRes : pResidualOf H p ≤ K :=
    pResidualOf_le_of_quotient_isPGroup H K p hp hKleH hKnormal hQquot
  exact hRes.trans inf_le_right

/-! ## `F*` monotonicity and normal-layer infrastructure -/

/-- `L` normalizes `N` when `N` is normal in `L`. -/
public theorem le_normalizer_of_isNormalIn {G : Type u} [Group G]
    {L N : Subgroup G} (hN : IsNormalIn N L) :
    L ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hN.2 x hx y hy
  · intro hy
    have hxinv : x⁻¹ ∈ L := L.inv_mem hx
    have h := hN.2 x⁻¹ hxinv (x * y * x⁻¹) hy
    simpa [mul_assoc] using h

/-- A nilpotent subgroup which is normal in `L` lies in `F(L)`. -/
public theorem le_fittingSubgroupOf_of_isNormalIn_nilpotent
    {G : Type u} [Group G] [Finite G]
    {L N : Subgroup G} (hNL : N ≤ L) (hN : IsNormalIn N L)
    (hNil : Group.IsNilpotent N) :
    N ≤ fittingSubgroupOf L := by
  let N' : Subgroup (↥L) := N.subgroupOf L
  have hN'normal : N'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := N)
      (le_normalizer_of_isNormalIn hN)
  have hN'nil : Group.IsNilpotent N' := by
    have : Group.IsNilpotent N := hNil
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNL).symm
  have hle : N' ≤ fittingSubgroup (↥L) :=
    le_sSup ⟨hN'normal, hN'nil⟩
  have hmap : N'.map L.subtype ≤ (fittingSubgroup (↥L)).map L.subtype :=
    Subgroup.map_mono (f := L.subtype) hle
  have hmapN : N'.map L.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNL
  have hmapF : (fittingSubgroup (↥L)).map L.subtype = fittingSubgroupOf L := rfl
  simpa [hmapN, hmapF] using hmap

/-- Subnormality descends through a normal intermediate subgroup. -/
public theorem isSubnormal_of_isNormalIn_subgroup
    {G : Type u} [Group G] {L N E : Subgroup G}
    (hNL : N ≤ L) (hN : IsNormalIn N L) (hEN : E ≤ N)
    (hEsubN : (E.subgroupOf N).IsSubnormal) :
    (E.subgroupOf L).IsSubnormal := by
  let N' : Subgroup (↥L) := N.subgroupOf L
  let E' : Subgroup (↥L) := E.subgroupOf L
  let e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNL
  have hE'N' : E'.subgroupOf N' = (E.subgroupOf N).comap e.toMonoidHom := by
    rfl
  have hsubN' : (E'.subgroupOf N').IsSubnormal := by
    rw [hE'N']
    exact hEsubN.comap (f := e.toMonoidHom)
  have hN'normal : N'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := N)
      (le_normalizer_of_isNormalIn hN)
  have hEN' : E' ≤ N' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hEN hx
  have hE'sn : E'.IsSubnormal := by
    exact Subgroup.IsSubnormal.trans (H := E') (K := N') hEN' hsubN' hN'normal.isSubnormal
  simpa [E'] using hE'sn

/-- The image of the center under a group isomorphism is the center. -/
private theorem map_center_eq_center_of_mulEquiv {G H : Type u}
    [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
      map_center_eq_center_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- Conjugation by an ambient element transports quasisimplicity. -/
private theorem isQuasisimple_conjugateSubgroup
    {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : IsQuasisimple E) :
    IsQuasisimple (conjugateSubgroup E g) :=
  isQuasisimple_mulEquiv ((MulAut.conj g).subgroupMap E) hE

/-- Conjugation by an ambient element transports subnormality. -/
private theorem isSubnormal_conjugateSubgroup
    {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : E.IsSubnormal) :
    (conjugateSubgroup E g).IsSubnormal := by
  simpa [conjugateSubgroup] using hE.map (MulAut.conj g).surjective

/-- A conjugate (by an element of `A`) of a component of `A` is again a
component of `A`. -/
private theorem isComponentOf_conjugateSubgroup_of_mem
    {G : Type u} [Group G]
    {E A : Subgroup G} (hE : IsComponentOf E A) (a : G) (ha : a ∈ A) :
    IsComponentOf (conjugateSubgroup E a) A := by
  refine ⟨?_, ?_, isQuasisimple_conjugateSubgroup E a hE.2.2⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨e, he, rfl⟩
    exact A.mul_mem (A.mul_mem ha (hE.1 he)) (A.inv_mem ha)
  · have hsnA : (E.subgroupOf A).IsSubnormal := hE.2.1
    have hconjA : (conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A)).IsSubnormal :=
      isSubnormal_conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) hsnA
    have hEq : conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) =
        (conjugateSubgroup E a).subgroupOf A := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        rcases (Subgroup.mem_map).1 hx with ⟨k, hk, hkx⟩
        exact Subgroup.mem_map.mpr ⟨(k : G), (Subgroup.mem_subgroupOf).1 hk,
          by simpa [conjugateSubgroup] using congrArg Subtype.val hkx⟩
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
        let v : ↥A := ⟨y, hE.1 hy⟩
        refine Subgroup.mem_map.mpr ⟨v, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hy
        · ext
          simpa [v, conjugateSubgroup] using hxy
    simpa [hEq] using hconjA

/-- The layer `E(A)` is normal in `A`. -/
public theorem componentLayerOf_isNormalIn {G : Type u} [Group G]
    (A : Subgroup G) : IsNormalIn (componentLayerOf A) A := by
  refine ⟨?_, ?_⟩
  · rw [componentLayerOf]
    exact sSup_le (fun E hE => hE.1)
  · intro a ha e he
    rw [componentLayerOf, sSup_eq_iSup', Subgroup.iSup_eq_closure] at he
    have hgen : ∀ y : G,
        y ∈ ⋃ E : {E : Subgroup G // IsComponentOf E A}, (E.1 : Set G) →
          a * y * a⁻¹ ∈ componentLayerOf A := by
      intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨E, hyE⟩
      exact Subgroup.mem_sSup_of_mem
        (isComponentOf_conjugateSubgroup_of_mem E.2 a ha)
        (by
          exact Subgroup.mem_map.mpr ⟨y, hyE, by simp [conjugateSubgroup]⟩)
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ he
    · intro x hx
      simpa [mul_assoc] using (componentLayerOf A).inv_mem (hgen x hx)
    · simpa using (componentLayerOf A).one_mem
    · intro x y _hx _hy hx' hy'
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using
        (componentLayerOf A).mul_mem hx' hy'

/-- The generalized Fitting subgroup `F*(A)` is normal in `A`. -/
public theorem generalizedFittingSubgroupOf_isNormalIn {G : Type u} [Group G]
    (A : Subgroup G) :
    IsNormalIn (generalizedFittingSubgroupOf A) A := by
  have hF : IsNormalIn (fittingSubgroupOf A) A := fittingSubgroupOf_isNormalIn A
  have hE : IsNormalIn (componentLayerOf A) A := componentLayerOf_isNormalIn A
  refine ⟨?_, ?_⟩
  · exact sup_le hF.1 hE.1
  · intro a ha x hx
    change x ∈ fittingSubgroupOf A ⊔ componentLayerOf A at hx
    rw [Subgroup.sup_eq_closure] at hx
    have hgen : ∀ y : G,
        y ∈ ((fittingSubgroupOf A : Set G) ∪ (componentLayerOf A : Set G)) →
          a * y * a⁻¹ ∈ generalizedFittingSubgroupOf A := by
      intro y hy
      rcases hy with hyF | hyE
      · exact Subgroup.mem_sup_left (hF.2 a ha y hyF)
      · exact Subgroup.mem_sup_right (hE.2 a ha y hyE)
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
    · intro y hy
      simpa [mul_assoc] using (generalizedFittingSubgroupOf A).inv_mem (hgen y hy)
    · simpa using (generalizedFittingSubgroupOf A).one_mem
    · intro y z _ _ hy' hz'
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using
        (generalizedFittingSubgroupOf A).mul_mem hy' hz'

/-! ## Centralizer-intersection facts for `C_G(F*(G))` -/

/-- If `E` centralizes `F`, every element of `F ⊔ E` decomposes as `f · e`. -/
public theorem mem_sup_decompose_of_centralizes {G : Type u} [Group G]
    {F E : Subgroup G} {x : G} (hx : x ∈ F ⊔ E)
    (hE : E ≤ Subgroup.centralizer (F : Set G)) :
    ∃ f ∈ F, ∃ e ∈ E, x = f * e := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v, hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v, hvE, by simp⟩
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v⁻¹, F.inv_mem hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v⁻¹, E.inv_mem hvE, by simp⟩
  · exact ⟨1, F.one_mem, 1, E.one_mem, by simp⟩
  · intro a b _ha _hb hpa hpb
    rcases hpa with ⟨f, hf, e, he, rfl⟩
    rcases hpb with ⟨f', hf', e', he', rfl⟩
    have hcomm : e * f' = f' * e :=
      ((Subgroup.mem_centralizer_iff (g := e) (s := (F : Set G))).1 (hE he) f' hf').symm
    refine ⟨f * f', F.mul_mem hf hf', e * e', E.mul_mem he he', ?_⟩
    calc
      (f * e) * (f' * e') = f * ((e * f') * e') := by simp [mul_assoc]
      _ = f * ((f' * e) * e') := by rw [hcomm]
      _ = (f * f') * (e * e') := by simp [mul_assoc]

/-- The center of the layer `E(G)` lies in `F(G)`. -/
public theorem center_componentLayer_top_le_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G] :
    let E := componentLayerOf (⊤ : Subgroup G)
    (Subgroup.center (↥E)).map E.subtype ≤ fittingSubgroupOf (⊤ : Subgroup G) := by
  classical
  let E : Subgroup G := componentLayerOf (⊤ : Subgroup G)
  let ZE : Subgroup G := (Subgroup.center (↥E)).map E.subtype
  have hEtop : IsNormalIn E (⊤ : Subgroup G) := componentLayerOf_isNormalIn (⊤ : Subgroup G)
  have hEnormal : E.Normal :=
    (Subgroup.normalizer_eq_top_iff).mp
      (top_le_iff.mp (le_normalizer_of_isNormalIn hEtop))
  have : E.Normal := hEnormal
  have : ZE.Normal := by
    dsimp [ZE]
    infer_instance
  have hZEnormal : IsNormalIn ZE (⊤ : Subgroup G) := by
    refine ⟨le_top, ?_⟩
    intro g _hg z hz
    exact (inferInstance : ZE.Normal).conj_mem z hz g
  have hZEcomm : IsMulCommutative (↥ZE) := by
    dsimp [ZE]
    infer_instance
  have hZEnil : Group.IsNilpotent ZE := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    exact hZEcomm
  have hZEleF : ZE ≤ fittingSubgroupOf (⊤ : Subgroup G) :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent le_top hZEnormal hZEnil
  simpa [ZE] using hZEleF

/-- `C_G(F*(G)) ∩ F*(G) ≤ F(G)`. -/
public theorem centralizer_generalizedFitting_intersection_le_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G] :
    let X := generalizedFittingSubgroupOf (⊤ : Subgroup G)
    let C := Subgroup.centralizer (X : Set G)
    C ⊓ X ≤ fittingSubgroupOf (⊤ : Subgroup G) := by
  classical
  let F : Subgroup G := fittingSubgroupOf (⊤ : Subgroup G)
  let E : Subgroup G := componentLayerOf (⊤ : Subgroup G)
  let X : Subgroup G := generalizedFittingSubgroupOf (⊤ : Subgroup G)
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := F)).mp (layer_centralizes_fitting (⊤ : Subgroup G))
  have hFE : F ≤ Subgroup.centralizer (E : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hEF he)) f hf).symm
  have hZE : (Subgroup.center (↥E)).map E.subtype ≤ F :=
    center_componentLayer_top_le_fittingSubgroupOf (G := G)
  change ∀ x : G, x ∈ C ⊓ X → x ∈ fittingSubgroupOf (⊤ : Subgroup G)
  intro x hx
  rcases hx with ⟨hxC, hxX⟩
  have hxC' : x ∈ C := hxC
  have hxX' : x ∈ F ⊔ E := by
    simpa [X, generalizedFittingSubgroupOf] using hxX
  rcases mem_sup_decompose_of_centralizes (F := F) (E := E) hxX' hEF with
    ⟨f, hf, e, he, hxeq⟩
  rw [hxeq]
  have heZ : e ∈ (Subgroup.center (↥E)).map E.subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨e, he⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hyE : (y : G) ∈ E := y.2
    have hxE : ∀ z : G, z ∈ E → x * z = z * x :=
      fun z hz => ((Subgroup.mem_centralizer_iff.mp hxC') z
        ((show E ≤ X from le_sup_right) hz)).symm
    have hfE : ∀ z : G, z ∈ E → f * z = z * f :=
      fun z hz => ((Subgroup.mem_centralizer_iff.mp (hFE hf)) z hz).symm
    have hfE' : ∀ z : G, z ∈ E → f⁻¹ * z = z * f⁻¹ := by
      intro z hz
      have h : f * z = z * f := hfE z hz
      exact (inv_mul_eq_iff_eq_mul).2 (by
        calc
          z = (z * f) * f⁻¹ := by group
          _ = (f * z) * f⁻¹ := by rw [← h]
          _ = f * (z * f⁻¹) := by group)
    have he_eq : e = f⁻¹ * x := by
      rw [hxeq]
      group
    exact Subtype.ext (by
      change (y : G) * (e : G) = (e : G) * (y : G)
      calc
        (y : G) * (e : G) = (y : G) * (f⁻¹ * x) := by rw [he_eq]
        _ = ((y : G) * f⁻¹) * x := by group
        _ = (f⁻¹ * (y : G)) * x := by
          rw [hfE' (y : G) hyE]
        _ = f⁻¹ * ((y : G) * x) := by group
        _ = f⁻¹ * (x * (y : G)) := by rw [hxE (y : G) hyE]
        _ = (f⁻¹ * x) * (y : G) := by group
        _ = (e : G) * (y : G) := by rw [he_eq])
  exact F.mul_mem hf (hZE heZ)

/-- If `C` centralizes `X` and every component of `C` lies in `X`, then
`C` has no components. -/
public theorem componentLayerOf_centralizer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (C X : Subgroup G)
    (hCX : C ≤ Subgroup.centralizer (X : Set G))
    (hEX : componentLayerOf C ≤ X) :
    componentLayerOf C = ⊥ := by
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro L hL
  have hLleLayerC : L ≤ componentLayerOf C :=
    le_sSup (s := {E : Subgroup G | IsComponentOf E C}) hL
  have hLleX : L ≤ X := hLleLayerC.trans hEX
  have hLleCentX : L ≤ Subgroup.centralizer (X : Set G) := hL.1.trans hCX
  have hLleCentL : L ≤ Subgroup.centralizer (L : Set G) := by
    refine hLleCentX.trans ?_
    exact Subgroup.centralizer_le (show (L : Set G) ⊆ (X : Set G) from hLleX)
  have hcomm : ⁅L, L⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := L) (H₂ := L)).mpr hLleCentL
  have hLperf : Group.IsPerfect L := (Group.isPerfect_def).2 hL.2.2.2.1
  have hLperfect : ⁅L, L⁆ = L :=
    (Subgroup.isPerfect_iff (H := L)).mp hLperf
  have hLbot : L = ⊥ := by
    rw [← hLperfect, hcomm]
  exact False.elim ((Subgroup.nontrivial_iff_ne_bot L).mp hL.2.2.1 hLbot)

public theorem isSubnormal_subgroupOf_of_subnormal_of_le {A : Type u} [Group A]
    {H N : Subgroup A} (hHN : H ≤ N) (hH : H.IsSubnormal) :
    (H.subgroupOf N).IsSubnormal := by
  classical
  rcases (Subgroup.IsSubnormal.isSubnormal_iff).1 hH with ⟨n, f, hmono, hnorm, hf0, hfn⟩
  let g : ℕ → Subgroup (↥N) := fun i => ((f i) ⊓ N).subgroupOf N
  have hgmono : Monotone g := by
    intro i j hij
    exact Subgroup.subgroupOf_mono N (inf_le_inf (hmono hij) le_rfl)
  have hgnorm : ∀ i, ((g i).subgroupOf (g (i + 1))).Normal := by
    intro i
    let X : Subgroup A := f i ⊓ N
    let Y : Subgroup A := f (i + 1) ⊓ N
    have hXleY : X ≤ Y := inf_le_inf (hmono (Nat.le_succ i)) le_rfl
    have hnorm' : ((f i).subgroupOf (f (i + 1))).Normal := hnorm i
    have hfn' : f (i + 1) ≤ Subgroup.normalizer (f i : Set A) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (h := hmono (Nat.le_succ i))).1 hnorm'
    have hNself : N ≤ Subgroup.normalizer (N : Set A) := N.le_normalizer
    have hYle : Y ≤ Subgroup.normalizer (X : Set A) :=
      (inf_le_inf hfn' hNself).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := f i) (K := N))
    have hle' : g i ≤ g (i + 1) := hgmono (Nat.le_succ i)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (h := hle')]
    have hXN : X ≤ N := inf_le_right
    rw [← Subgroup.subgroupOf_normalizer_eq (h := hXN)]
    simpa [g, X, Y] using Subgroup.subgroupOf_mono N hYle
  have hg0 : g 0 = H.subgroupOf N := by
    simpa [g, hf0, inf_of_le_left hHN]
  have hgn : g n = ⊤ := by
    simp [g, hfn]
  exact (Subgroup.IsSubnormal.isSubnormal_iff).2 ⟨n, g, hgmono, hgnorm, hg0, hgn⟩

/-- A nontrivial finite group has a minimal nontrivial subnormal subgroup. -/
public theorem exists_minimal_subnormal {A : Type u} [Group A] [Finite A]
    (hA : Nontrivial A) :
    ∃ K : Subgroup A, K ≠ ⊥ ∧ K.IsSubnormal ∧
      ∀ L : Subgroup A, L ≠ ⊥ → L.IsSubnormal → L ≤ K → L = K := by
  classical
  let P : ℕ → Prop := fun n => ∃ K : Subgroup A, K ≠ ⊥ ∧ K.IsSubnormal ∧ Nat.card K = n
  have hP : ∃ n, P n := by
    refine ⟨Nat.card A, ⟨⊤, ?_, Subgroup.IsSubnormal.top, ?_⟩⟩
    · exact (Subgroup.one_lt_card_iff_ne_bot (H := (⊤ : Subgroup A))).1 (by
        simpa using (Finite.one_lt_card_iff_nontrivial (α := A)).2 hA)
    · simpa using (Nat.card_congr (Subgroup.topEquiv (G := A)).toEquiv).symm
  let n0 : ℕ := Nat.find hP
  rcases Nat.find_spec hP with ⟨K, hKne, hKsn, hKcard⟩
  refine ⟨K, hKne, hKsn, ?_⟩
  intro L hLne hLsn hLK
  have hPL : P (Nat.card L) := ⟨L, hLne, hLsn, rfl⟩
  have hmin : n0 ≤ Nat.card L := Nat.find_min' hP hPL
  have hcard : Nat.card K ≤ Nat.card L := by
    simpa [n0, hKcard] using hmin
  exact Subgroup.eq_of_le_of_card_ge hLK hcard

/-- A minimal nontrivial subnormal subgroup is either commutative or quasisimple. -/
public theorem minimal_subnormal_isMulCommutative_or_quasisimple
    {A : Type u} [Group A] [Finite A]
    {K : Subgroup A} (hKne : K ≠ ⊥) (hKsn : K.IsSubnormal)
    (hmin : ∀ L : Subgroup A, L ≠ ⊥ → L.IsSubnormal → L ≤ K → L = K) :
    IsMulCommutative (↥K) ∨ IsQuasisimple K := by
  classical
  by_cases hcomm : IsMulCommutative (↥K)
  · exact Or.inl hcomm
  · right
    have : Nontrivial (↥K) := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
    let K' : Subgroup (↥K) := commutator (↥K)
    have : K'.Characteristic := by
      dsimp [K']
      infer_instance
    have hK'norm : K'.Normal := inferInstance
    have hK'snK : K'.IsSubnormal := hK'norm.isSubnormal
    have hK'map : (K'.map K.subtype) = ⁅K, K⁆ := by
      have htop_map : (⊤ : Subgroup (↥K)).map K.subtype = K := by
        simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
      change (⁅(⊤ : Subgroup (↥K)), (⊤ : Subgroup (↥K))⁆).map K.subtype = ⁅K, K⁆
      rw [Subgroup.map_commutator, htop_map]
    have hKKsn : (⁅K, K⁆).IsSubnormal := by
      simpa [hK'map] using (Subgroup.IsSubnormal.trans' (H := K') (K := K) hK'snK hKsn)
    have hKKne : ⁅K, K⁆ ≠ ⊥ := by
      intro hbot
      have hle : K ≤ Subgroup.centralizer (K : Set A) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := K)).1 hbot
      exact hcomm ((Subgroup.le_centralizer_iff_isMulCommutative (K := K)).1 hle)
    have hKKleK : ⁅K, K⁆ ≤ K := by
      rw [← hK'map]
      exact Subgroup.map_subtype_le (H := K) K'
    have hKKeq : ⁅K, K⁆ = K :=
      hmin (⁅K, K⁆) hKKne hKKsn hKKleK
    have hPerf : Group.IsPerfect (↥K) := (Subgroup.isPerfect_iff (H := K)).2 hKKeq
    -- center is trivial
    let Z : Subgroup (↥K) := Subgroup.center (↥K)
    have hZsnK : Z.IsSubnormal := (inferInstance : Z.Normal).isSubnormal
    let ZA : Subgroup A := Z.map K.subtype
    have hZAsn : ZA.IsSubnormal := by
      simpa [ZA] using (Subgroup.IsSubnormal.trans' (H := Z) (K := K) hZsnK hKsn)
    have hZbot : Z = ⊥ := by
      by_cases hZAbot : ZA = ⊥
      · exact (Subgroup.map_eq_bot_iff_of_injective (H := Z) (f := K.subtype)
          K.subtype_injective).1 hZAbot
      · have hZAK : ZA = K := hmin ZA hZAbot hZAsn (Subgroup.map_subtype_le (H := K) Z)
        have hZtop' : Z = ⊤ := by
          have hinj : Function.Injective (Subgroup.map K.subtype) :=
            Subgroup.map_injective (f := K.subtype) K.subtype_injective
          have htop_map : (⊤ : Subgroup (↥K)).map K.subtype = K := by
            simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
          apply hinj
          simpa [ZA, htop_map] using hZAK
        have hcomm' : IsMulCommutative (↥K) := by
          apply (Subgroup.le_centralizer_iff_isMulCommutative (K := K)).1
          intro x _hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hxZ : (⟨x, _hx⟩ : ↥K) ∈ Z := by
            rw [hZtop']
            trivial
          have hxy := (Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩)
          exact congrArg Subtype.val hxy
        exact False.elim (hcomm hcomm')
    -- simple
    have hKsimple : IsSimpleGroup (↥K) := by
      refine IsSimpleGroup.mk ?_
      intro L' hL'norm
      let LA : Subgroup A := L'.map K.subtype
      have hLAsn : LA.IsSubnormal := by
        simpa [LA] using (Subgroup.IsSubnormal.trans' (H := L') (K := K)
          hL'norm.isSubnormal hKsn)
      have hLAle : LA ≤ K := Subgroup.map_subtype_le (H := K) L'
      by_cases hLAbot : LA = ⊥
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective (H := L') (f := K.subtype)
          K.subtype_injective).1 hLAbot
      · have hLAK : LA = K := hmin LA hLAbot hLAsn hLAle
        right
        have hinj : Function.Injective (Subgroup.map K.subtype) :=
          Subgroup.map_injective (f := K.subtype) K.subtype_injective
        have htop_map : (⊤ : Subgroup (↥K)).map K.subtype = K := by
          simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
        apply hinj
        simpa [LA, htop_map] using hLAK
    -- quasisimple: perfect + simple quotient by trivial center
    have hZbot' : Subgroup.center (↥K) = ⊥ := by
      simpa [Z] using hZbot
    have hsimpleQ : IsSimpleGroup ((↥K) ⧸ Subgroup.center (↥K)) := by
      have e0 : (↥K) ⧸ Subgroup.center (↥K) ≃* (↥K) ⧸ (⊥ : Subgroup (↥K)) :=
        QuotientGroup.quotientMulEquivOfEq (G := ↥K)
          (M := Subgroup.center (↥K)) (N := ⊥) hZbot'
      exact (MulEquiv.isSimpleGroup_congr (e0.trans QuotientGroup.quotientBot)).mpr hKsimple
    exact ⟨inferInstance, (Group.isPerfect_def).1 hPerf, hsimpleQ⟩

/-- Solvability is invariant under a group isomorphism. -/
public theorem isSolvable_of_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) [Group.IsSolvable G] : Group.IsSolvable H :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom) e.toEquiv.surjective

/-- Commutativity is preserved by a surjective homomorphism. -/
public theorem isMulCommutative_of_surjective {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hcomm : IsMulCommutative G) :
    IsMulCommutative H := by
  rw [isMulCommutative_iff]
  intro a b
  rcases hf a with ⟨a', rfl⟩
  rcases hf b with ⟨b', rfl⟩
  have h : a' * b' = b' * a' := (IsMulCommutative.is_comm (M := G)).comm a' b'
  simpa [map_mul] using congrArg f h

/-- Commutativity is inherited by `subgroupOf` (restriction). -/
public theorem isMulCommutative_subgroupOf {G : Type u} [Group G]
    {K N : Subgroup G} (hKN : K ≤ N) (hcomm : IsMulCommutative (↥K)) :
    IsMulCommutative (↥(K.subgroupOf N)) := by
  let e : K.subgroupOf N ≃* K := Subgroup.subgroupOfEquivOfLe hKN
  exact isMulCommutative_of_surjective e.symm.toMonoidHom e.symm.toEquiv.surjective hcomm

/-- Commutativity is inherited by the image of a commutative subgroup. -/
public theorem isMulCommutative_map_of_surjective {G H : Type u} [Group G] [Group H]
    (f : G →* H) (_hf : Function.Surjective f) (S : Subgroup G)
    (hcomm : IsMulCommutative (↥S)) : IsMulCommutative (↥(S.map f)) := by
  rw [isMulCommutative_iff]
  intro a b
  rcases (Subgroup.mem_map).1 a.2 with ⟨a₀, ha₀, ha⟩
  rcases (Subgroup.mem_map).1 b.2 with ⟨b₀, hb₀, hb⟩
  have hab : a₀ * b₀ = b₀ * a₀ := by
    have h' := (IsMulCommutative.is_comm (M := ↥S)).comm ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    exact congrArg Subtype.val h'
  have hmain : f a₀ * f b₀ = f b₀ * f a₀ := by
    simpa [map_mul] using congrArg f hab
  apply Subtype.ext
  simpa [ha, hb] using hmain

/-- The join of two normal solvable subgroups is solvable. -/
public theorem isSolvable_sup_of_normal_solvable
    {H : Type u} [Group H] [Finite H]
    (A B : Subgroup H) (hA : A.Normal) (hB : B.Normal)
    [Group.IsSolvable (↥A)] [Group.IsSolvable (↥B)] : Group.IsSolvable (↥(A ⊔ B)) := by
  classical
  let : A.Normal := hA
  let : B.Normal := hB
  let J : Subgroup H := A ⊔ B
  have : J.Normal := by
    dsimp [J]
    infer_instance
  have hBleJ : B ≤ J := le_sup_right
  have hAleJ : A ≤ J := le_sup_left
  -- `J / B` is a quotient of `A`
  let φ : (↥A) →* (↥J ⧸ B.subgroupOf J) :=
    { toFun := fun a => QuotientGroup.mk' (B.subgroupOf J) ⟨a, hAleJ a.2⟩
      map_one' := rfl
      map_mul' := fun a a' => rfl }
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases QuotientGroup.mk'_surjective (B.subgroupOf J) y with ⟨j, rfl⟩
    have hAB : (↑J : Set H) = (A : Set H) * (B : Set H) := by
      simpa [J] using Subgroup.mul_normal A B
    have hjAB : (j : H) ∈ (A : Set H) * (B : Set H) := hAB ▸ j.2
    rcases hjAB with ⟨a, ha, b, hb, hj_eq⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    have hdiv : j / ⟨a, hAleJ ha⟩ ∈ B.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      have hmap : J.subtype (j / ⟨a, hAleJ ha⟩) = ↑j / a :=
        map_div (J.subtype) j ⟨a, hAleJ ha⟩
      change J.subtype (j / ⟨a, hAleJ ha⟩) ∈ B
      rw [hmap]
      rw [div_eq_mul_inv]
      rw [← hj_eq]
      have hconj : (a * b) * a⁻¹ ∈ B := hB.conj_mem b hb a
      simpa [mul_assoc] using hconj
    exact ((QuotientGroup.eq_iff_div_mem (N := B.subgroupOf J) (x := j)
      (y := (⟨a, hAleJ ha⟩ : ↥J))).2 hdiv).symm
  have hJdivBsolv : Group.IsSolvable (↥J ⧸ B.subgroupOf J) :=
    Group.isSolvable_of_surjective (f := φ) hφsurj
  -- extension theorem
  let f : (↥B) →* (↥J) :=
    { toFun := fun b => ⟨b, hBleJ b.2⟩
      map_one' := rfl
      map_mul' := fun b b' => rfl }
  let g : (↥J) →* (↥J ⧸ B.subgroupOf J) := QuotientGroup.mk' (B.subgroupOf J)
  have hker : g.ker = f.range := by
    ext j
    constructor
    · intro hj
      have hjB : (j : H) ∈ B := by
        have hj' : j ∈ B.subgroupOf J := by
          simpa [g, QuotientGroup.ker_mk'] using hj
        exact (Subgroup.mem_subgroupOf).1 hj'
      refine ⟨⟨j, hjB⟩, ?_⟩
      rfl
    · intro hj
      rcases (MonoidHom.mem_range).1 hj with ⟨b, rfl⟩
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := B.subgroupOf J)
        (x := (⟨(b : H), hBleJ b.2⟩ : ↥J))).2 (by
          rw [Subgroup.mem_subgroupOf]
          exact b.2)
  have hJsolv : Group.IsSolvable (↥J) := by
    let : Group.IsSolvable (↥B) := inferInstance
    let : Group.IsSolvable (↥J ⧸ B.subgroupOf J) := hJdivBsolv
    exact Group.isSolvable_of_ker_le_range f g (le_of_eq hker)
  simpa [J] using hJsolv

/-- The join of a finite family of normal solvable subgroups is solvable. -/
public theorem isSolvable_iSup_of_normal_solvable
    {H : Type u} [Group H] [Finite H] {ι : Type u} [Fintype ι]
    (S : ι → Subgroup H) (hS : ∀ i, (S i).Normal)
    (hSolv : ∀ i, Group.IsSolvable (↥(S i))) : Group.IsSolvable (↥(⨆ i, S i)) := by
  classical
  have hmain : ∀ s : Finset ι, Group.IsSolvable (↥(⨆ i ∈ s, S i)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hbot : (⨆ i ∈ (∅ : Finset ι), S i) = (⊥ : Subgroup H) := by
        rw [iSup_eq_bot]
        intro i
        rw [iSup_eq_bot]
        intro hi
        exact False.elim (by simpa using hi)
      rw [hbot]
      infer_instance
    · intro a s' has' ih
      rw [Finset.iSup_insert]
      have hnorm : (⨆ i ∈ s', S i).Normal := by
        infer_instance
      exact @isSolvable_sup_of_normal_solvable H _ _ (S a) (⨆ i ∈ s', S i) (hS a) hnorm
        (hSolv a) ih
  have hEq : (⨆ i : ι, S i) = ⨆ i ∈ (Finset.univ : Finset ι), S i := by
    apply le_antisymm
    · exact iSup_le (fun i => le_iSup_of_le i
        (le_iSup (fun _ : i ∈ (Finset.univ : Finset ι) => S i) (Finset.mem_univ i)))
    · exact iSup_le (fun i => iSup_le (fun _hi => le_iSup S i))
  exact hEq ▸ hmain Finset.univ

/-- `subgroupOf` distributes over an `iSup` when all terms are contained in the
intermediate subgroup. -/
public theorem subgroupOf_iSup_of_le {G : Type u} [Group G] {ι : Type u}
    {H : ι → Subgroup G} {N : Subgroup G} (hH : ∀ i, H i ≤ N) :
    (⨆ i, H i).subgroupOf N = ⨆ i, (H i).subgroupOf N := by
  classical
  apply le_antisymm
  · have hRHS_coe : (⨆ i, (H i).subgroupOf N).map N.subtype = ⨆ i, H i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr (fun i => Subgroup.map_subgroupOf_eq_of_le (hH i))
    intro x hx
    have hxG : (x : G) ∈ (⨆ i, (H i).subgroupOf N).map N.subtype := by
      rwa [hRHS_coe]
    rcases (Subgroup.mem_map).1 hxG with ⟨y, hy, hxy⟩
    have hyx : (y : ↥N) = x := N.subtype_injective hxy
    simpa [hyx] using hy
  · exact iSup_le (fun i => Subgroup.subgroupOf_mono N (le_iSup H i))

/-- The normal closure of a subgroup is the join of its conjugates. -/
public theorem normalClosure_eq_iSup_conjugates {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) :
    Subgroup.normalClosure (K : Set G) = ⨆ g : G, K.map (MulAut.conj g).toMonoidHom := by
  classical
  let J : Subgroup G := ⨆ g : G, K.map (MulAut.conj g).toMonoidHom
  have hJnorm : J.Normal := by
    refine ⟨fun x hx b => ?_⟩
    dsimp [J] at hx ⊢
    rw [Subgroup.iSup_eq_closure] at hx
    have hgen : ∀ y : G, y ∈ ⋃ g : G, (K.map (MulAut.conj g).toMonoidHom : Set G) →
        b * y * b⁻¹ ∈ J := by
      intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨g, hyg⟩
      rcases (Subgroup.mem_map).1 hyg with ⟨k, hk, rfl⟩
      have hcalc : b * ((MulAut.conj g).toMonoidHom k) * b⁻¹ =
          (MulAut.conj (b * g)).toMonoidHom k := by
        change b * (g * k * g⁻¹) * b⁻¹ = (b * g) * k * (b * g)⁻¹
        group
      rw [hcalc]
      exact (le_iSup (fun g : G => K.map (MulAut.conj g).toMonoidHom) (b * g))
        (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
    · intro y hy'
      have hyJ : b * y * b⁻¹ ∈ J := hgen y hy'
      have h : b * y⁻¹ * b⁻¹ = (b * y * b⁻¹)⁻¹ := by group
      rw [h]
      exact J.inv_mem hyJ
    · have h : b * 1 * b⁻¹ = 1 := by group
      rw [h]
      exact J.one_mem
    · intro a c _ha _hc ha' hc'
      have h : b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) := by group
      rw [h]
      exact J.mul_mem ha' hc'
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (N := J) (by
      intro x hx
      exact (le_iSup (fun g : G => K.map (MulAut.conj g).toMonoidHom) 1)
        (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj]⟩))
  · refine iSup_le ?_
    intro g
    exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      Subgroup.le_normalClosure).trans
      (le_of_eq (Subgroup.Normal.map_conj_eq (H := Subgroup.normalClosure (K : Set G)) g))

/-- The normal closure of a subnormal commutative subgroup of a finite group is
solvable.  Classical proof by strong induction on the ambient order: intersect a
proper normal overgroup `N`, close inside `N`, then express the full closure as
an extension of the `N`-closure by a join of normal solvable subgroups of `N/L`. -/
public theorem isSolvable_normalClosure_of_subnormal_abelian
    {A : Type u} [Group A] [Finite A] {H : Subgroup A}
    (hH : H.IsSubnormal) (hcomm : IsMulCommutative (↥H)) :
    Group.IsSolvable (↥(Subgroup.normalClosure (H : Set A))) := by
  classical
  let P : ℕ → Prop := fun n => ∀ (B : Type u) [Group B] [Finite B], Nat.card B = n →
    ∀ (K : Subgroup B), K.IsSubnormal → IsMulCommutative (↥K) →
      Group.IsSolvable (↥(Subgroup.normalClosure (K : Set B)))
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih B _ _ hcard K hKsn hKcomm
    classical
    by_cases hKtop : K = ⊤
    · subst hKtop
      have hnc : Subgroup.normalClosure ((⊤ : Subgroup B) : Set B) = ⊤ := by
        apply le_antisymm
        · exact Subgroup.normalClosure_le_normal (N := ⊤) (by intro x hx; trivial)
        · exact Subgroup.le_normalClosure
      have : Group.IsSolvable (↥(⊤ : Subgroup B)) := by
        exact Group.isSolvable_of_comm (G := ↥(⊤ : Subgroup B))
          (fun a b => (IsMulCommutative.is_comm (M := ↥(⊤ : Subgroup B))).comm a b)
      rw [hnc]
      exact (inferInstance : Group.IsSolvable (↥(⊤ : Subgroup B)))
    · rcases (Subgroup.IsSubnormal.lt_normal hKsn) with htop | ⟨N, hNnorm, hKN, hNlt⟩
      · exact False.elim (hKtop htop)
      · let : N.Normal := hNnorm
        have hNcardlt : Nat.card (↥N) < Nat.card B := by
          have hle : Nat.card (↥N) ≤ Nat.card B := Subgroup.card_le_card_group N
          have hne : Nat.card (↥N) ≠ Nat.card B := by
            intro hEq
            have htopN : N = ⊤ := Subgroup.eq_top_of_card_eq N hEq
            exact (ne_of_lt hNlt) htopN
          exact lt_of_le_of_ne hle hne
        have hNcard' : Nat.card (↥N) < n := by simpa [hcard] using hNcardlt
        have hKsubN : (K.subgroupOf N).IsSubnormal :=
          isSubnormal_subgroupOf_of_subnormal_of_le hKN hKsn
        have hKcommN : IsMulCommutative (↥(K.subgroupOf N)) :=
          isMulCommutative_subgroupOf hKN hKcomm
        let L : Subgroup (↥N) := Subgroup.normalClosure
          ((K.subgroupOf N : Subgroup (↥N)) : Set (↥N))
        have hLsolv : Group.IsSolvable (↥L) :=
          ih (Nat.card (↥N)) hNcard' (↥N) rfl (K.subgroupOf N) hKsubN hKcommN
        let Q : Type u := ↥N ⧸ L
        have : L.Normal := Subgroup.normalClosure_normal
        let π : (↥N) →* Q := QuotientGroup.mk' L
        let S : B → Subgroup Q := fun g =>
          ((K.map (MulAut.conj g).toMonoidHom).subgroupOf N).map π
        have hKc_le_N : ∀ g, K.map (MulAut.conj g).toMonoidHom ≤ N := by
          intro g
          have hmap : N.map (MulAut.conj g).toMonoidHom = N :=
            (Subgroup.Normal.map_conj_eq (H := N) g)
          exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKN).trans
            (le_of_eq hmap)
        have hS_sn : ∀ g, (S g).IsSubnormal := by
          intro g
          have hKg_sn : (K.map (MulAut.conj g).toMonoidHom).IsSubnormal :=
            hKsn.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).toEquiv.surjective
          have hKg_subN : ((K.map (MulAut.conj g).toMonoidHom).subgroupOf N).IsSubnormal :=
            isSubnormal_subgroupOf_of_subnormal_of_le (hKc_le_N g) hKg_sn
          simpa [S] using hKg_subN.map (f := π) (QuotientGroup.mk'_surjective L)
        have hS_comm : ∀ g, IsMulCommutative (↥(S g)) := by
          intro g
          let Kg : Subgroup B := K.map (MulAut.conj g).toMonoidHom
          have hKg_comm : IsMulCommutative (↥Kg) := by
            let e : ↥K ≃* ↥Kg := Subgroup.equivMapOfInjective K
              (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
            exact isMulCommutative_of_surjective e.toMonoidHom e.toEquiv.surjective hKcomm
          have hKgN_comm : IsMulCommutative (↥(Kg.subgroupOf N)) :=
            isMulCommutative_subgroupOf (hKc_le_N g) hKg_comm
          simpa [S, Kg] using isMulCommutative_map_of_surjective π
            (QuotientGroup.mk'_surjective L) (Kg.subgroupOf N) hKgN_comm
        have hQle : Nat.card Q ≤ Nat.card (↥N) :=
          Finite.card_le_of_surjective' (f := π) (QuotientGroup.mk'_surjective L) (by
            intro hz
            exact False.elim ((Nat.card_pos (α := ↥N)).ne' hz))
        have hQcard' : Nat.card Q < n := lt_of_le_of_lt hQle hNcard'
        have hCg_solv : ∀ g, Group.IsSolvable (↥(Subgroup.normalClosure (S g : Set Q))) := by
          intro g
          exact ih (Nat.card Q) hQcard' Q rfl (S g) (hS_sn g) (hS_comm g)
        let J : Subgroup Q := ⨆ g : B, Subgroup.normalClosure (S g : Set Q)
        have hJsolv : Group.IsSolvable (↥J) := by
          let : Fintype B := Fintype.ofFinite B
          dsimp [J]
          exact isSolvable_iSup_of_normal_solvable
            (fun g : B => Subgroup.normalClosure (S g : Set Q))
            (fun g => Subgroup.normalClosure_normal) hCg_solv
        let C : Subgroup B := Subgroup.normalClosure (K : Set B)
        have hC_le_N : C ≤ N := by
          exact Subgroup.normalClosure_le_normal (N := N) (by
            intro x hx
            exact hKN hx)
        let C' : Subgroup (↥N) := C.subgroupOf N
        have hCeq : C = ⨆ g : B, K.map (MulAut.conj g).toMonoidHom :=
          normalClosure_eq_iSup_conjugates K
        have hC'eq : C' = ⨆ g : B, (K.map (MulAut.conj g).toMonoidHom).subgroupOf N := by
          change (C.subgroupOf N) = ⨆ g : B, (K.map (MulAut.conj g).toMonoidHom).subgroupOf N
          rw [hCeq]
          exact subgroupOf_iSup_of_le hKc_le_N
        have hC'map_eq : C'.map π = ⨆ g : B, S g := by
          rw [hC'eq, Subgroup.map_iSup]
        have hC'norm : (C'.map π).Normal := by
          have : C'.Normal := by
            dsimp [C']
            infer_instance
          exact (inferInstance : C'.Normal).map π (QuotientGroup.mk'_surjective L)
        have hS_le : ∀ g, S g ≤ C'.map π := by
          intro g x hx
          rcases (Subgroup.mem_map).1 hx with ⟨n, hn, rfl⟩
          have hnKc : (n : B) ∈ K.map (MulAut.conj g).toMonoidHom :=
            (Subgroup.mem_subgroupOf).1 hn
          have hnC : (n : B) ∈ C := by
            rw [hCeq]
            exact (le_iSup (fun g : B => K.map (MulAut.conj g).toMonoidHom) g) hnKc
          exact Subgroup.mem_map_of_mem π (by
            rw [Subgroup.mem_subgroupOf]
            exact hnC)
        have hC'map : C'.map π = J := by
          apply le_antisymm
          · rw [hC'map_eq]
            refine iSup_le ?_
            intro g
            exact Subgroup.le_normalClosure.trans
              (le_iSup (fun g' : B => Subgroup.normalClosure (S g' : Set Q)) g)
          · refine iSup_le ?_
            intro g
            refine Subgroup.normalClosure_le_normal (N := C'.map π) ?_
            intro x hx
            exact hS_le g hx
        have hC'solv : Group.IsSolvable (↥C') := by
          have hLleC' : L ≤ C' := by
            refine Subgroup.normalClosure_le_normal (N := C') ?_
            intro x hx
            change x ∈ C.subgroupOf N
            rw [Subgroup.mem_subgroupOf]
            have hxK : (x : B) ∈ K := (Subgroup.mem_subgroupOf).1 hx
            exact Subgroup.le_normalClosure hxK
          let f : (↥L) →* (↥C') :=
            { toFun := fun x => ⟨x, hLleC' x.2⟩
              map_one' := by ext; rfl
              map_mul' := by intro x y; ext; rfl }
          let g : (↥C') →* (↥(C'.map π)) :=
            { toFun := fun x => ⟨π (C'.subtype x), Subgroup.mem_map_of_mem π x.2⟩
              map_one' := by ext; rfl
              map_mul' := by intro x y; ext; rfl }
          have hfg : g.ker ≤ f.range := by
            intro x hx
            have hx1 : π (C'.subtype x) = 1 := by
              simpa [g, MonoidHom.mem_ker] using hx
            have hxL : (x : ↥N) ∈ L := (QuotientGroup.eq_one_iff (N := L) (x := (C'.subtype x))).1 hx1
            refine ⟨⟨x, hxL⟩, ?_⟩
            rfl
          have hJ' : Group.IsSolvable (↥(C'.map π)) := by
            rw [hC'map]
            exact hJsolv
          let : Group.IsSolvable (↥L) := hLsolv
          let : Group.IsSolvable (↥(C'.map π)) := hJ'
          exact Group.isSolvable_of_ker_le_range f g hfg
        let : Group.IsSolvable (↥C') := hC'solv
        exact isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC_le_N)
  exact hP (Nat.card A) A rfl H hH hcomm

/-- The normal closure of a subnormal solvable subgroup of a finite group is
solvable.  Reduce to the abelian case by induction on `|H|` using the derived
subgroup. -/
public theorem isSolvable_normalClosure_of_subnormal_solvable
    {A : Type u} [Group A] [Finite A] {H : Subgroup A}
    (hH : H.IsSubnormal) [Group.IsSolvable (↥H)] :
    Group.IsSolvable (↥(Subgroup.normalClosure (H : Set A))) := by
  classical
  -- strong induction on |H|
  let P : ℕ → Prop := fun n => ∀ (A : Type u) [Group A] [Finite A],
    ∀ (H : Subgroup A), Nat.card H = n → H.IsSubnormal → [Group.IsSolvable (↥H)] →
      Group.IsSolvable (↥(Subgroup.normalClosure (H : Set A)))
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ H hcard hH
    classical
    by_cases hHbot : H = ⊥
    · subst hHbot
      have hnc : Subgroup.normalClosure ((⊥ : Subgroup A) : Set A) = ⊥ :=
        Subgroup.normalClosure_eq_self (⊥ : Subgroup A)
      rw [hnc]
      infer_instance
    · have : Nontrivial (↥H) := (Subgroup.nontrivial_iff_ne_bot H).2 hHbot
      have hH'lt : commutator (↥H) < (⊤ : Subgroup (↥H)) :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H)
      let H' : Subgroup (↥H) := commutator (↥H)
      have hH'lt' : H' ≠ (⊤ : Subgroup (↥H)) := ne_of_lt hH'lt
      have hH'card : Nat.card H' < Nat.card H := by
        have hle : Nat.card H' ≤ Nat.card H := Subgroup.card_le_card_group H'
        have hne : Nat.card H' ≠ Nat.card H := by
          intro hEq
          have htop : H' = ⊤ := Subgroup.eq_top_of_card_eq H' hEq
          exact hH'lt' htop
        exact lt_of_le_of_ne hle hne
      have hH'card' : Nat.card H' < n := by simpa [hcard] using hH'card
      have hH'char : H'.Characteristic := by
        dsimp [H']
        infer_instance
      have : H'.Characteristic := hH'char
      have hH'sn : H'.IsSubnormal := (inferInstance : H'.Normal).isSubnormal
      have hH'snA : (H'.map H.subtype).IsSubnormal := by
        simpa using (Subgroup.IsSubnormal.trans' (H := H') (K := H) hH'sn hH)
      have : Group.IsSolvable (↥H') := by
        infer_instance
      let K : Subgroup A := Subgroup.normalClosure ((H'.map H.subtype : Subgroup A) : Set A)
      have hKsolv : Group.IsSolvable (↥K) := by
        have hcard' : Nat.card (H'.map H.subtype) = Nat.card H' := by
          exact (Nat.card_congr (Subgroup.equivMapOfInjective H' H.subtype
            H.subtype_injective).toEquiv).symm
        have hcard'' : Nat.card (H'.map H.subtype) < n := by
          rw [hcard']
          exact hH'card'
        have hH'Asolv : Group.IsSolvable (↥(H'.map H.subtype)) := by
          let : Group.IsSolvable (↥H') := inferInstance
          exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective H' H.subtype
            H.subtype_injective)
        let : Group.IsSolvable (↥(H'.map H.subtype)) := hH'Asolv
        exact ih (Nat.card (H'.map H.subtype)) hcard'' A (H'.map H.subtype) rfl hH'snA
      have : K.Normal := Subgroup.normalClosure_normal
      let Q : Type u := A ⧸ K
      let π : A →* Q := QuotientGroup.mk' K
      -- image of H in Q is abelian
      let Hbar : Subgroup Q := H.map π
      have hHbar_sn : Hbar.IsSubnormal :=
        hH.map (f := π) (QuotientGroup.mk'_surjective K)
      have hHbar_comm : IsMulCommutative (↥Hbar) := by
        rw [isMulCommutative_iff]
        intro a b
        rcases (Subgroup.mem_map).1 a.2 with ⟨a₀, ha₀, ha⟩
        rcases (Subgroup.mem_map).1 b.2 with ⟨b₀, hb₀, hb⟩
        have hKK_eq : ⁅H, H⁆ = (commutator (↥H)).map H.subtype := by
          have htop_map : (⊤ : Subgroup (↥H)).map H.subtype = H := by
            simpa [MonoidHom.range_eq_map] using (H.range_subtype : H.subtype.range = H)
          have hm : (commutator (↥H)).map H.subtype =
              ⁅(⊤ : Subgroup (↥H)).map H.subtype, (⊤ : Subgroup (↥H)).map H.subtype⁆ := by
            rw [commutator_def]
            rw [Subgroup.map_commutator (H₁ := (⊤ : Subgroup (↥H)))
              (H₂ := (⊤ : Subgroup (↥H))) (f := H.subtype)]
          conv at hm => rhs; rw [htop_map]
          exact hm.symm
        have hcommA : ⁅(a₀ : A), (b₀ : A)⁆ ∈ ⁅H, H⁆ :=
          Subgroup.commutator_mem_commutator (G := A) (H₁ := H) (H₂ := H)
            ha₀ hb₀
        have hKmem : (a₀ : A) * (b₀ : A) * (a₀ : A)⁻¹ * (b₀ : A)⁻¹ ∈ K := by
          have h' : ⁅(a₀ : A), (b₀ : A)⁆ ∈ (commutator (↥H)).map H.subtype := by
            rwa [hKK_eq] at hcommA
          have h'' : ⁅(a₀ : A), (b₀ : A)⁆ ∈ K := Subgroup.le_normalClosure h'
          convert h'' using 1
        have hπeq : π (a₀ * b₀) = π (b₀ * a₀) := by
          apply (QuotientGroup.eq_iff_div_mem (N := K)
            (x := ((a₀ : A) * (b₀ : A))) (y := ((b₀ : A) * (a₀ : A)))).2
          rw [div_eq_mul_inv]
          have hcalc : (a₀ : A) * (b₀ : A) * ((b₀ : A) * (a₀ : A))⁻¹ =
              (a₀ : A) * (b₀ : A) * (a₀ : A)⁻¹ * (b₀ : A)⁻¹ := by group
          rw [hcalc]
          exact hKmem
        have hmain : π a₀ * π b₀ = π b₀ * π a₀ := by
          simpa [map_mul] using hπeq
        apply Subtype.ext
        simpa [ha, hb] using hmain
      -- abelian case on (Q, H̄)
      have hHbarCl : Group.IsSolvable (↥(Subgroup.normalClosure (Hbar : Set Q))) := by
        exact isSolvable_normalClosure_of_subnormal_abelian hHbar_sn hHbar_comm
      -- relate to C = normalClosure H
      let C : Subgroup A := Subgroup.normalClosure (H : Set A)
      have hCmap : C.map π = Subgroup.normalClosure (Hbar : Set Q) := by
        calc
          C.map π = Subgroup.normalClosure (π '' (H : Set A)) :=
            Subgroup.map_normalClosure (H : Set A) π (QuotientGroup.mk'_surjective K)
          _ = Subgroup.normalClosure (Hbar : Set Q) := by
            rfl
      have hCsub : Group.IsSolvable (↥(C.map π)) := by
        rw [hCmap]
        exact hHbarCl
      -- C / K ≅ C.map π and K solvable
      have hKleC : K ≤ C := by
        refine Subgroup.normalClosure_mono ?_
        intro y hy
        exact Subgroup.map_subtype_le (H := H) (K := H') hy
      let f : (↥K) →* (↥C) :=
        { toFun := fun x => ⟨x, hKleC x.2⟩
          map_one' := by ext; rfl
          map_mul' := by intro x y; ext; rfl }
      let g : (↥C) →* (↥(C.map π)) :=
        { toFun := fun x => ⟨π (C.subtype x), Subgroup.mem_map_of_mem π x.2⟩
          map_one' := by ext; rfl
          map_mul' := by intro x y; ext; rfl }
      have hfg : g.ker ≤ f.range := by
        intro x hx
        have hx1 : π (C.subtype x) = 1 := by
          simpa [g, MonoidHom.mem_ker] using hx
        have hxK : (x : A) ∈ K := (QuotientGroup.eq_one_iff (N := K) (x := (C.subtype x))).1 hx1
        refine ⟨⟨x, hxK⟩, ?_⟩
        rfl
      let : Group.IsSolvable (↥K) := hKsolv
      let : Group.IsSolvable (↥(C.map π)) := hCsub
      have hCsolv : Group.IsSolvable (↥C) := Group.isSolvable_of_ker_le_range f g hfg
      simpa [C] using hCsolv
  exact hP (Nat.card H) A H rfl hH

/-- Components of a normal subgroup are components of the ambient group. -/
public theorem componentLayerOf_le_of_normal {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) :
    componentLayerOf N ≤ componentLayerOf (⊤ : Subgroup G) := by
  classical
  rw [componentLayerOf, componentLayerOf]
  refine sSup_le ?_
  intro E hE
  have hE_snG : E.IsSubnormal := by
    have hNsn : N.IsSubnormal := hN.isSubnormal
    have h' : ((E.subgroupOf N).map N.subtype).IsSubnormal :=
      (Subgroup.IsSubnormal.trans' (H := E.subgroupOf N) (K := N) hE.2.1 hNsn)
    rwa [Subgroup.map_subgroupOf_eq_of_le hE.1] at h'
  have hE_sn_top : (E.subgroupOf (⊤ : Subgroup G)).IsSubnormal := hE_snG.subgroupOf
  exact le_sSup (s := {E' : Subgroup G | IsComponentOf E' (⊤ : Subgroup G)})
    ⟨le_top, hE_sn_top, hE.2.2⟩

/-- A nonsolvable minimal normal subgroup of a finite group contains a
component of the ambient group. -/
public theorem exists_component_of_minimalNormal_nonsolvable
    {G : Type u} [Group G] [Finite G] (N : Subgroup G)
    (hN : N.Normal) (hNne : N ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K ≠ ⊥ → K = N)
    (hnsolv : ¬ Group.IsSolvable (↥N)) :
    ∃ S : Subgroup G, S ≤ N ∧ IsComponentOf S (⊤ : Subgroup G) := by
  classical
  let M : Type u := ↥N
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
  rcases exists_minimal_subnormal (A := M) inferInstance with ⟨K, hKne, hKsn, hminK⟩
  rcases minimal_subnormal_isMulCommutative_or_quasisimple (A := M) hKne hKsn hminK with
    hcomm | hq
  · -- abelian minimal subnormal subgroup: its normal closure in `N` is solvable,
    -- and the conjugates of that closure generate all of `N`
    have hKsolv : Group.IsSolvable (↥K) := by
      exact Group.isSolvable_of_comm (G := ↥K)
        (fun a b => (IsMulCommutative.is_comm (M := ↥K)).comm a b)
    let L : Subgroup M := Subgroup.normalClosure (K : Set M)
    have hLsolv : Group.IsSolvable (↥L) :=
      isSolvable_normalClosure_of_subnormal_solvable (A := M) hKsn
    let L' : Subgroup G := L.map N.subtype
    have hL'sn : L'.IsSubnormal := by
      have hLsn : L.IsSubnormal := Subgroup.normalClosure_normal.isSubnormal
      have hNsn : N.IsSubnormal := hN.isSubnormal
      simpa [L'] using (Subgroup.IsSubnormal.trans' (H := L) (K := N) hLsn hNsn)
    have hL'solv : Group.IsSolvable (↥L') := by
      let : Group.IsSolvable (↥L) := hLsolv
      exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective L N.subtype N.subtype_injective)
    let J : Subgroup G := Subgroup.normalClosure (L' : Set G)
    have hJsolv : Group.IsSolvable (↥J) :=
      isSolvable_normalClosure_of_subnormal_solvable (A := G) hL'sn
    have hJleN : J ≤ N := by
      exact Subgroup.normalClosure_le_normal (N := N) (by
        intro x hx
        exact (Subgroup.map_subtype_le (H := N) L) hx)
    have hJne : J ≠ ⊥ := by
      intro hbot
      have hL'leJ : L' ≤ J := Subgroup.le_normalClosure
      have hL'bot : L' = ⊥ := le_bot_iff.mp (hL'leJ.trans (le_of_eq hbot))
      have hLbot : L = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := L) (f := N.subtype)
          N.subtype_injective).1 hL'bot
      have hKleL : K ≤ L := Subgroup.le_normalClosure
      exact hKne (le_bot_iff.mp (hKleL.trans (le_of_eq hLbot)))
    have hJeqN : J = N := hmin J (inferInstance : J.Normal) hJleN hJne
    have hNsolv : Group.IsSolvable (↥N) := by
      let : Group.IsSolvable (↥J) := hJsolv
      exact isSolvable_of_mulEquiv (MulEquiv.subgroupCongr hJeqN)
    exact False.elim (hnsolv hNsolv)
  · let S : Subgroup G := K.map N.subtype
    have hSleN : S ≤ N := Subgroup.map_subtype_le (H := N) K
    have hSsn : (S.subgroupOf (⊤ : Subgroup G)).IsSubnormal := by
      have hNsn : N.IsSubnormal := hN.isSubnormal
      have hSsnG : S.IsSubnormal := by
        simpa [S] using (Subgroup.IsSubnormal.trans' (H := K) (K := N) hKsn hNsn)
      exact hSsnG.subgroupOf (K := (⊤ : Subgroup G))
    have hSq : IsQuasisimple S := by
      exact isQuasisimple_mulEquiv (Subgroup.equivMapOfInjective K N.subtype
        N.subtype_injective) hq
    exact ⟨S, hSleN, ⟨le_top, hSsn, hSq⟩⟩

/-- A nontrivial finite group has nontrivial Fitting subgroup or nontrivial
layer.  Equivalently, a finite group with trivial Fitting subgroup and trivial
component layer is trivial. -/
public theorem finite_group_eq_bot_of_fitting_bot_and_componentLayer_bot
    {G : Type u} [Group G] [Finite G] :
    fittingSubgroup G = ⊥ → componentLayerOf (⊤ : Subgroup G) = ⊥ →
    Subsingleton G := by
  classical
  intro hF hE
  by_contra hns
  have hnt : Nontrivial G := by
    exact not_subsingleton_iff_nontrivial.mp hns
  have hTopne : (⊤ : Subgroup G) ≠ ⊥ := by
    exact (Subgroup.one_lt_card_iff_ne_bot (H := (⊤ : Subgroup G))).1 (by
      simpa using (Finite.one_lt_card_iff_nontrivial (α := G)).2 hnt)
  rcases exists_minimal_normal_le (⊤ : Subgroup G) inferInstance hTopne with
    ⟨N, hNnorm, hNle, hNne, hNmin⟩
  have : N.Normal := hNnorm
  by_cases hNsolv : Group.IsSolvable (↥N)
  · -- solvable minimal normal subgroup lies in F(G)
    have : IsMinimalNormal N := ⟨fun K hKnorm hKle => by
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hNmin K hKnorm hKle hKbot)⟩
    have hNleF : N ≤ fittingSubgroup G := by
      have hNleZ : N ≤ centerIn (G := G) (fittingSubgroup G) :=
        minimalNormal_solvable_le_centerIn_fittingSubgroup N
      exact hNleZ.trans (by
        intro x hx
        exact hx.1)
    have hNbot : N = ⊥ := le_bot_iff.mp (hNleF.trans (le_of_eq hF))
    exact hNne hNbot
  · -- nonsolvable minimal normal subgroup contains a component of G
    rcases exists_component_of_minimalNormal_nonsolvable N hNnorm hNne hNmin hNsolv with
      ⟨S, hSN, hScomp⟩
    have hSleE : S ≤ componentLayerOf (⊤ : Subgroup G) := by
      exact le_sSup (s := {E : Subgroup G | IsComponentOf E (⊤ : Subgroup G)}) hScomp
    have hSbot : S = ⊥ := le_bot_iff.mp (hSleE.trans (le_of_eq hE))
    have hSne : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp hScomp.2.2.1
    exact hSne hSbot

/-- The Fitting subgroup of `C / K` is trivial when `K` is a central subgroup of
`C` and `F(C) ≤ K` (KS 5.2.2). -/
public theorem fittingSubgroup_quotient_eq_bot_of_central_kernel
    {G : Type u} [Group G] [Finite G]
    (C K : Subgroup G) (hKnormal : (K.subgroupOf C).Normal)
    (hKcentral : K ≤ Subgroup.centralizer (C : Set G))
    (hFCleK : fittingSubgroupOf C ≤ K) :
    fittingSubgroup (C ⧸ K.subgroupOf C) = ⊥ := by
  classical
  let Q : Type u := C ⧸ K.subgroupOf C
  let π : (↥C) →* Q := QuotientGroup.mk' (K.subgroupOf C)
  have hO : ∀ p : ℕ, p.Prime → pCore p Q = ⊥ := by
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    let Pbar : Subgroup Q := pCore p Q
    let P : Subgroup (↥C) := Pbar.comap π
    have hPnorm : P.Normal := by
      dsimp [P]
      infer_instance
    have : P.Normal := hPnorm
    have hPnil : Group.IsNilpotent P := by
      let f : (↥P) →* (↥Pbar) :=
        { toFun := fun x => ⟨π (P.subtype x), by
            exact (Subgroup.mem_comap).1 (by simpa [P] using x.2)⟩
          map_one' := by ext; rfl
          map_mul' := by intro x y; ext; rfl }
      have hker : f.ker ≤ Subgroup.center (↥P) := by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro y
        have hfx : f x = 1 := by simpa [f, MonoidHom.mem_ker] using hx
        have hx1 : π (P.subtype x) = 1 := congrArg Subtype.val hfx
        have hxK : (P.subtype x : ↥C) ∈ K.subgroupOf C :=
          (QuotientGroup.eq_one_iff (N := K.subgroupOf C) (x := (P.subtype x))).1 hx1
        have hxKG : (x : G) ∈ K := (Subgroup.mem_subgroupOf).1 hxK
        apply Subtype.ext
        apply Subtype.ext
        have hyC : ((y : ↥C) : G) ∈ C :=
          (Subgroup.map_subtype_le (H := C) P) (Subgroup.mem_map.mpr ⟨y, by simpa using y.2, rfl⟩)
        have hc : ((y : ↥C) : G) * (x : G) = (x : G) * ((y : ↥C) : G) :=
          (Subgroup.mem_centralizer_iff (g := (x : G)) (s := (C : Set G))).1
            (hKcentral hxKG) (y : ↥C) hyC
        simpa using hc
      have : Group.IsNilpotent (↥Pbar) := (pCore_isPGroup (G := Q) (p := p)).isNilpotent
      exact isNilpotent_of_ker_le_center f hker
    let Pg : Subgroup G := P.map C.subtype
    have hPleC : Pg ≤ C := Subgroup.map_subtype_le (H := C) P
    have hPleFC : Pg ≤ fittingSubgroupOf C := by
      have hPnormC : IsNormalIn Pg C := by
        refine ⟨hPleC, ?_⟩
        intro c hc p hp
        rcases (Subgroup.mem_map).1 hp with ⟨p₀, hp₀, rfl⟩
        exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * p₀ * ⟨c, hc⟩⁻¹,
          hPnorm.conj_mem p₀ hp₀ ⟨c, hc⟩, by simp⟩
      have hPnilG : Group.IsNilpotent Pg := by
        dsimp [Pg]
        let : Group.IsNilpotent (↥P) := hPnil
        exact Group.nilpotent_of_mulEquiv (G := ↥P) (G' := ↥(P.map C.subtype))
          (Subgroup.equivMapOfInjective P C.subtype C.subtype_injective)
      exact le_fittingSubgroupOf_of_isNormalIn_nilpotent (L := C) (N := Pg)
        hPleC hPnormC hPnilG
    have hPbar_bot : Pbar = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxP : x ∈ P.map π := by
        rw [Subgroup.map_comap_eq_self_of_surjective (f := π)
          (QuotientGroup.mk'_surjective (K.subgroupOf C)) Pbar]
        exact hx
      rcases (Subgroup.mem_map).1 hxP with ⟨p, hp, rfl⟩
      have hpFC : (p : G) ∈ fittingSubgroupOf C := hPleFC (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
      have hpK : (p : G) ∈ K := hFCleK hpFC
      have hpKC : p ∈ K.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        exact hpK
      have hπ : π p = 1 := (QuotientGroup.eq_one_iff (N := K.subgroupOf C) (x := p)).2 hpKC
      rw [Subgroup.mem_bot]
      exact hπ
    exact hPbar_bot
  have hF : fittingSubgroup Q = ⊥ := by
    dsimp [Q]
    rw [fitting_eq_sup_pCore]
    apply le_bot_iff.mp
    refine iSup_le ?_
    intro q
    have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hqbot : pCore q.1.1 Q = ⊥ := hO q.1.1 hqprime
    simpa [hqbot]
  simpa [Q] using hF

private theorem monoidHom_eq_one_of_perfect_abelian
    {G A : Type u} [Group G] [Group A]
    (hG : Group.IsPerfect G) (hA : IsMulCommutative A) (f : G →* A) :
    f = 1 := by
  apply MonoidHom.ext
  intro x
  have hx : x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
    have htop : Group.IsPerfect (↥(⊤ : Subgroup G)) := by
      let : Group.IsPerfect G := hG
      infer_instance
    have hcomm : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ :=
      (Subgroup.isPerfect_iff (H := (⊤ : Subgroup G))).mp htop
    rw [hcomm]
    trivial
  rw [Subgroup.commutator_def] at hx
  refine Subgroup.closure_induction (p := fun y _hy => f y = 1) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨g₁, _hg₁, g₂, _hg₂, rfl⟩
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).2
      ((IsMulCommutative.is_comm (M := A)).comm (f g₁) (f g₂))
  · simp
  · intro a b _ha _hb ha hb
    rw [map_mul, ha, hb, mul_one]
  · intro a _ha ha
    rw [map_inv, ha, inv_one]

/-- `[a, b·c] = [a,b]·[a,c]` when `b` commutes with `[a,c]`. -/
private theorem commutator_mul_central_right {A : Type u} [Group A] (a b c : A)
    (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by group
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by
      rw [h]
      group

/-- If `D` is a central subgroup of a perfect group `M`, then the center of
`M / D` is the image of the center of `M`. -/
public theorem center_quotient_center_eq_map
    {A : Type u} [Group A]
    (M D : Subgroup A) (hDleZ : D ≤ Subgroup.center A) (_hDleM : D ≤ M)
    [hDnormal : (D.subgroupOf M).Normal]
    (hMperf : Group.IsPerfect (↥M)) :
    Subgroup.center (M ⧸ D.subgroupOf M) =
      (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M)) := by
  classical
  have hDleZM : D.subgroupOf M ≤ Subgroup.center (↥M) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hDleZ (Subgroup.mem_subgroupOf.mp hx))) (y : A)
  have : IsMulCommutative (↥(D.subgroupOf M)) := by
    apply (Subgroup.le_centralizer_iff_isMulCommutative (K := D.subgroupOf M)).1
    exact hDleZM.trans (Subgroup.center_le_centralizer ((D.subgroupOf M : Set (↥M))))
  let π : (↥M) →* (M ⧸ D.subgroupOf M) := QuotientGroup.mk' (D.subgroupOf M)
  apply le_antisymm
  · -- a central coset `π m` has `m` central in `M`
    intro q hq
    rcases QuotientGroup.mk'_surjective (D.subgroupOf M) q with ⟨m, rfl⟩
    refine Subgroup.mem_map.mpr ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro n
    have hcommD : ∀ z : ↥M, ⁅m, z⁆ ∈ D.subgroupOf M := by
      intro z
      have hqcommz : π m * π z = π z * π m := by
        exact ((Subgroup.mem_center_iff.mp hq) (π z)).symm
      have hπmz : π (m * z) = π (z * m) := by
        rw [map_mul π m z, map_mul π z m]
        exact hqcommz
      have hdivz : (m * z) * (z * m)⁻¹ ∈ D.subgroupOf M := by
        simpa [div_eq_mul_inv] using
          (QuotientGroup.eq_iff_div_mem (N := D.subgroupOf M) (x := m * z) (y := z * m)).1 hπmz
      apply (Subgroup.mem_subgroupOf).2
      have hdiv' : ((m : A) * (z : A) * ((z : A) * (m : A))⁻¹) ∈ D :=
        (Subgroup.mem_subgroupOf).1 hdivz
      change ⁅(m : A), (z : A)⁆ ∈ D
      have hc : ⁅(m : A), (z : A)⁆ = (m : A) * (z : A) * ((z : A) * (m : A))⁻¹ := by
        rw [commutatorElement_def]
        group
      rwa [hc]
    let ψ : (↥M) →* (↥(D.subgroupOf M)) :=
      { toFun := fun z =>
          (⟨⟨⁅(m : A), (z : A)⁆, by
            simpa [commutatorElement_def] using
              M.mul_mem (M.mul_mem (M.mul_mem m.2 z.2) (M.inv_mem m.2)) (M.inv_mem z.2)⟩,
            hcommD z⟩ : ↥(D.subgroupOf M))
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          simp
        map_mul' := by
          intro z₁ z₂
          apply Subtype.ext
          apply Subtype.ext
          change ⁅(m : A), (z₁ : A) * (z₂ : A)⁆ = ⁅(m : A), (z₁ : A)⁆ * ⁅(m : A), (z₂ : A)⁆
          have hz₂c : (z₁ : A) * ⁅(m : A), (z₂ : A)⁆ = ⁅(m : A), (z₂ : A)⁆ * (z₁ : A) := by
            have hz : (↑(⁅m, z₂⁆ : ↥M) : A) ∈ Subgroup.center A :=
              hDleZ (Subgroup.mem_subgroupOf.mp (hcommD z₂))
            exact (Subgroup.mem_center_iff.mp hz (z₁ : A))
          exact commutator_mul_central_right (m : A) (z₁ : A) (z₂ : A) hz₂c }
    have hψ : ψ = 1 := monoidHom_eq_one_of_perfect_abelian hMperf inferInstance ψ
    have hcommA : ⁅(m : A), (n : A)⁆ = (1 : A) := by
      have hψn : ψ n = 1 := by rw [hψ]; rfl
      have hval : ((ψ n : ↥(D.subgroupOf M)) : ↥M) = 1 :=
        congrArg (fun t : ↥(D.subgroupOf M) => (t : ↥M)) hψn
      have hvalA : (((ψ n : ↥(D.subgroupOf M)) : ↥M) : A) = (1 : A) :=
        congrArg (fun t : ↥M => (t : A)) hval
      exact hvalA
    exact Subtype.ext ((commutatorElement_eq_one_iff_mul_comm.mp hcommA).symm)
  · -- the image of the center is central
    intro q hq
    rcases (Subgroup.mem_map).1 hq with ⟨m, hm, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q'
    rcases QuotientGroup.mk'_surjective (D.subgroupOf M) q' with ⟨n, rfl⟩
    have hmc : m * n = n * m := (Subgroup.mem_center_iff.mp hm n).symm
    have hπmn : π (m * n) = π (n * m) := congrArg π hmc
    rw [← map_mul π m n, ← map_mul π n m]
    exact hπmn.symm

/-- A component of `C / K` (with `K` central in `C`) lifts to a component
of `C`.  The lifted component is the commutator subgroup of the preimage of
the component. -/
public theorem isComponentOf_of_central_quotient_component
    {G : Type u} [Group G] [Finite G]
    (C K : Subgroup G) [hKnormal : (K.subgroupOf C).Normal]
    (hKcentral : K ≤ Subgroup.centralizer (C : Set G))
    (S : Subgroup (C ⧸ K.subgroupOf C))
    (hS : IsComponentOf S (⊤ : Subgroup (C ⧸ K.subgroupOf C))) :
    ∃ T : Subgroup G, IsComponentOf T C := by
  classical
  let Q : Type u := C ⧸ K.subgroupOf C
  let π : (↥C) →* Q := QuotientGroup.mk' (K.subgroupOf C)
  let K' : Subgroup (↥C) := K.subgroupOf C
  let L : Subgroup (↥C) := S.comap π
  let M : Subgroup (↥C) := ⁅L, L⁆
  -- `K'` is central in `↥C`
  have hK'leZ : K' ≤ Subgroup.center (↥C) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hKcentral (Subgroup.mem_subgroupOf.mp hx))) y y.2
  -- `K'` lies in `L`
  have hK'leL : K' ≤ L := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff (N := K') (x := x)).2 hx
    simpa [hx1] using (S.one_mem : (1 : Q) ∈ S)
  -- subnormality of `M` in `↥C`
  have hSsn : S.IsSubnormal := by
    have h' : ((S.subgroupOf (⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype).IsSubnormal :=
      hS.2.1.map (f := (⊤ : Subgroup Q).subtype)
        (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : S ≤ (⊤ : Subgroup Q))] at h'
  have hLsn : L.IsSubnormal := Subgroup.IsSubnormal.comap π hSsn
  have hMleL : M ≤ L := by
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp L.le_normalizer
  have hMLnorm : (M.subgroupOf L).Normal := by
    have hsup : L ⊔ L = L := le_antisymm (sup_le le_rfl le_rfl) le_sup_left
    have h' : (⁅L, L⁆.subgroupOf (L ⊔ L)).Normal :=
      Subgroup.normal_subgroupOf_commutator_sup (H₁ := L) (H₂ := L)
    rw [hsup] at h'
    simpa [M] using h'
  have hMsn : M.IsSubnormal :=
    Subgroup.IsSubnormal.trans hMleL hMLnorm.isSubnormal hLsn
  -- `π(M) = S`
  have hπL : L.map π = S :=
    Subgroup.map_comap_eq_self_of_surjective (f := π)
      (QuotientGroup.mk'_surjective K') S
  have hSperf : Group.IsPerfect (↥S) := (Group.isPerfect_def).2 hS.2.2.2.1
  have hSS : ⁅S, S⁆ = S := (Subgroup.isPerfect_iff (H := S)).mp hSperf
  have hπM : M.map π = S := by
    rw [show M = ⁅L, L⁆ by rfl, Subgroup.map_commutator (H₁ := L) (H₂ := L) π, hπL, hSS]
  -- `L = M ⊔ K'`
  have hMK'leL : M ⊔ K' ≤ L := sup_le hMleL hK'leL
  have hLleMK' : L ≤ M ⊔ K' := by
    intro x hx
    have hxπM : π x ∈ M.map π := by
      rw [hπM, ← hπL]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rcases (Subgroup.mem_map).1 hxπM with ⟨m, hm, hπm⟩
    have hxmk : x * m⁻¹ ∈ K' := by
      have hπ : π (x * m⁻¹) = 1 := by
        rw [map_mul, map_inv, hπm]
        simp
      exact (QuotientGroup.eq_one_iff (N := K') (x := x * m⁻¹)).1 hπ
    have hkz : x * m⁻¹ ∈ Subgroup.center (↥C) := hK'leZ hxmk
    have hEq : m * (x * m⁻¹) = x := by
      calc
        m * (x * m⁻¹) = (x * m⁻¹) * m := Subgroup.mem_center_iff.mp hkz m
        _ = x := by group
    rw [Subgroup.mem_sup_of_normal_right (s := M) (t := K')]
    exact ⟨m, hm, x * m⁻¹, hxmk, hEq⟩
  have hL_eq : L = M ⊔ K' := le_antisymm hLleMK' hMK'leL
  -- `M` is perfect
  have hMperfect : Group.IsPerfect (↥M) := by
    apply (Subgroup.isPerfect_iff (H := M)).mpr
    apply le_antisymm
    · exact (Subgroup.le_normalizer_iff_commutator_le_right).mp M.le_normalizer
    · have hLLleMM : ⁅L, L⁆ ≤ ⁅M, M⁆ := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hg₁' : g₁ ∈ M ⊔ K' := by simpa [hL_eq] using hg₁
        have hg₂' : g₂ ∈ M ⊔ K' := by simpa [hL_eq] using hg₂
        rcases (Subgroup.mem_sup_of_normal_right (s := M) (t := K') (x := g₁)).1 hg₁' with
          ⟨m₁, hm₁, k₁, hk₁, hgk₁⟩
        rcases (Subgroup.mem_sup_of_normal_right (s := M) (t := K') (x := g₂)).1 hg₂' with
          ⟨m₂, hm₂, k₂, hk₂, hgk₂⟩
        have hk₁z : k₁ ∈ Subgroup.center (↥C) := hK'leZ hk₁
        have hk₂z : k₂ ∈ Subgroup.center (↥C) := hK'leZ hk₂
        have hz₁y : Commute k₁ (m₂ * k₂) :=
          ((Subgroup.mem_center_iff.mp hk₁z) (m₂ * k₂)).symm
        have hz₂c : Commute m₁ k₂ := (Subgroup.mem_center_iff.mp hk₂z) m₁
        have hcalc : ⁅g₁, g₂⁆ = ⁅m₁, m₂⁆ := by
          calc
            ⁅g₁, g₂⁆ = ⁅m₁ * k₁, m₂ * k₂⁆ := by rw [hgk₁, hgk₂]
            _ = ⁅m₁, m₂ * k₂⁆ := by
              rw [commutatorElement_mul_left_eq_conj_mul]
              simp [Commute.commutator_eq hz₁y]
            _ = ⁅m₁, m₂⁆ := by
              rw [commutatorElement_mul_right_eq_mul_conj]
              simp [Commute.commutator_eq hz₂c]
        exact hcalc ▸ Subgroup.commutator_mem_commutator hm₁ hm₂
      simpa [M] using hLLleMM
  -- `M` is nontrivial
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hSbot : S = ⊥ := by
      calc
        S = M.map π := hπM.symm
        _ = ⊥ := by
          rw [hbot]
          exact Subgroup.map_bot (G := ↥C) (N := Q) π
    exact (Subgroup.nontrivial_iff_ne_bot S).mp hS.2.2.1 hSbot
  have : Nontrivial (↥M) := (Subgroup.nontrivial_iff_ne_bot (G := ↥C) M).2 hMne
  -- `M / Z(M)` is isomorphic to `S / Z(S)`
  let D : Subgroup (↥C) := K' ⊓ M
  have hDleM : D ≤ M := inf_le_right
  have hDleZ : D ≤ Subgroup.center (↥C) := (inf_le_left : D ≤ K').trans hK'leZ
  have hDsubZ : D.subgroupOf M ≤ Subgroup.center (↥M) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hDleZ (Subgroup.mem_subgroupOf.mp hx))) (y : ↥C)
  have hDnormal : (D.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (hHK := hDleM)]
    intro x hx y hy
    have hxZ : x ∈ Subgroup.center (↥C) := hDleZ y
    have hxy : hx * x = x * hx := (Subgroup.mem_center_iff.mp hxZ) hx
    have hEq : hx * x * hx⁻¹ = x := by
      calc
        hx * x * hx⁻¹ = x * hx * hx⁻¹ := by rw [hxy]
        _ = x := by group
    rwa [hEq]
  let f : (↥M) →* Q := π.comp M.subtype
  have hker : f.ker = D.subgroupOf M := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxK : (x : ↥C) ∈ K' :=
        (QuotientGroup.eq_one_iff (N := K') (x := (M.subtype x))).1 hx
      apply (Subgroup.mem_subgroupOf).2
      change (x : ↥C) ∈ K' ⊓ M
      exact ⟨hxK, x.2⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := K') (x := (M.subtype x))).2
        ((Subgroup.mem_subgroupOf).1 hx).1
  have hrange : f.range = S := by
    ext x
    constructor
    · intro hx
      rcases (MonoidHom.mem_range).1 hx with ⟨m, rfl⟩
      have hmem : π (M.subtype m) ∈ M.map π := Subgroup.mem_map.mpr ⟨M.subtype m, m.2, rfl⟩
      rwa [hπM] at hmem
    · intro hx
      rw [MonoidHom.mem_range]
      have hxM : x ∈ M.map π := by simpa [hπM] using hx
      rcases (Subgroup.mem_map).1 hxM with ⟨a, ha, hax⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      simpa [f] using hax
  let e₀ : (↥M) ⧸ (D.subgroupOf M) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq (G := ↥M) (M := f.ker) (N := D.subgroupOf M)
      hker).symm.trans
      ((QuotientGroup.quotientKerEquivRange (φ := f)).trans (MulEquiv.subgroupCongr hrange))
  have hcenterEq : (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M)) =
      Subgroup.center ((↥M) ⧸ (D.subgroupOf M)) :=
    (center_quotient_center_eq_map (A := ↥C) M D hDleZ hDleM hMperfect).symm
  let QM : Type u := (↥M) ⧸ (D.subgroupOf M)
  let ZM : Subgroup QM := (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M))
  have hZM : ZM = Subgroup.center QM := by
    simpa [QM, ZM] using hcenterEq
  have hZM' : ZM = (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M)) := by
    simpa [QM] using hZM.trans hcenterEq.symm
  have hZSm : ZM.map e₀.toMonoidHom = Subgroup.center S := by
    rw [hZM']
    exact hcenterEq ▸ (map_center_eq_center_of_mulEquiv e₀)
  have : (D.subgroupOf M).Normal := hDnormal
  have : ZM.Normal := by
    dsimp [ZM]
    infer_instance
  have : (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M)) |>.Normal := by
    infer_instance
  let e₁ : QM ⧸ ZM ≃* (↥M) ⧸ Subgroup.center (↥M) :=
    (QuotientGroup.quotientMulEquivOfEq (G := QM) (M := ZM)
      (N := (Subgroup.center (↥M)).map (QuotientGroup.mk' (D.subgroupOf M))) hZM').trans
      (QuotientGroup.quotientQuotientEquivQuotient (G := ↥M) (N := D.subgroupOf M)
        (M := Subgroup.center (↥M)) hDsubZ)
  let e₂ : QM ⧸ ZM ≃* S ⧸ Subgroup.center S :=
    QuotientGroup.congr (G' := ZM) (H' := Subgroup.center S) e₀ hZSm
  have hMsimple : IsSimpleGroup ((↥M) ⧸ Subgroup.center (↥M)) := by
    have hQMsimple : IsSimpleGroup (QM ⧸ ZM) :=
      (MulEquiv.isSimpleGroup_congr e₂).mpr hS.2.2.2.2
    exact (MulEquiv.isSimpleGroup_congr e₁).mp hQMsimple
  have hMq : IsQuasisimple M := ⟨inferInstance, (Group.isPerfect_def).1 hMperfect, hMsimple⟩
  -- map back to `G`
  let T : Subgroup G := M.map C.subtype
  have hTle : T ≤ C := Subgroup.map_subtype_le (H := C) M
  have hTsub : (T.subgroupOf C).IsSubnormal := by
    have hEq : T.subgroupOf C = M := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hyx⟩
        have hyx' : (y : ↥C) = x := C.subtype_injective hyx
        simpa [hyx'] using hy
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [hEq]
  have hTq : IsQuasisimple T := by
    exact isQuasisimple_mulEquiv (Subgroup.equivMapOfInjective M C.subtype
      C.subtype_injective) hMq
  exact ⟨T, ⟨hTle, hTsub, hTq⟩⟩

/-- If `K` is a central subgroup of `C` and `C` has no components, then
`C / K` has no components. -/
public theorem componentLayerOf_quotient_eq_bot_of_central_kernel
    {G : Type u} [Group G] [Finite G]
    (C K : Subgroup G) [hKnormal : (K.subgroupOf C).Normal]
    (hKcentral : K ≤ Subgroup.centralizer (C : Set G))
    (hEC : componentLayerOf C = ⊥) :
    componentLayerOf (⊤ : Subgroup (C ⧸ K.subgroupOf C)) = ⊥ := by
  classical
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro S hS
  rcases isComponentOf_of_central_quotient_component C K hKcentral S hS with
    ⟨T, hT⟩
  have hTleE : T ≤ componentLayerOf C :=
    le_sSup (s := {E : Subgroup G | IsComponentOf E C}) hT
  have hTbot : T = ⊥ := le_bot_iff.mp (hTleE.trans (le_of_eq hEC))
  have hTne : T ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot T).mp hT.2.2.1
  exact False.elim (hTne hTbot)

/-- The generalized Fitting subgroup is self-centralizing in the whole
group: `C_G(F*(G)) ≤ F*(G)` (KS 6.5.8). -/
public theorem fstar_self_centralizing
    {G : Type u} [Group G] [Finite G] :
    Subgroup.centralizer ((generalizedFittingSubgroupOf (⊤ : Subgroup G) : Set G)) ≤
      generalizedFittingSubgroupOf (⊤ : Subgroup G) := by
  classical
  let X : Subgroup G := generalizedFittingSubgroupOf (⊤ : Subgroup G)
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let K : Subgroup G := C ⊓ X
  have hXnorm : X.Normal := by
    have hXi : IsNormalIn X (⊤ : Subgroup G) := generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup G)
    exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp (le_normalizer_of_isNormalIn hXi))
  have : X.Normal := hXnorm
  have : C.Normal := by
    dsimp [C]
    infer_instance
  have : K.Normal := by
    dsimp [K]
    infer_instance
  have hKleC : K ≤ C := inf_le_left
  have hKnormalC : (K.subgroupOf C).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : K.Normal) C
  -- `K` is central in `C`
  have hKcentral : K ≤ Subgroup.centralizer (C : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcX : c ∈ Subgroup.centralizer (X : Set G) := by simpa [C] using hc
    exact ((Subgroup.mem_centralizer_iff.mp hcX) k hk.2).symm
  -- `F(C) ≤ K`
  have hFCleK : fittingSubgroupOf C ≤ K := by
    refine le_inf ?_ ?_
    · exact (Subgroup.map_subtype_le (H := C) (K := fittingSubgroup (↥C)))
    · have hFCleF : fittingSubgroupOf C ≤ fittingSubgroupOf (⊤ : Subgroup G) := by
        exact le_fittingSubgroupOf_of_normal_nilpotent (H := (⊤ : Subgroup G))
          (N := fittingSubgroupOf C) le_top (fittingSubgroupOf_normal C (inferInstance : C.Normal))
          (fittingSubgroupOf_isNilpotent C)
      exact hFCleF.trans (le_sup_left : fittingSubgroupOf (⊤ : Subgroup G) ≤ X)
  -- `E(C) = ⊥`
  have hECbot : componentLayerOf C = ⊥ := by
    have hCX : C ≤ Subgroup.centralizer (X : Set G) := by rfl
    have hEX : componentLayerOf C ≤ X := by
      exact (componentLayerOf_le_of_normal C (inferInstance : C.Normal)).trans
        (le_sup_right : componentLayerOf (⊤ : Subgroup G) ≤ X)
    exact componentLayerOf_centralizer_eq_bot C X hCX hEX
  -- the quotient `C / K` is trivial
  have hEQ : componentLayerOf (⊤ : Subgroup (C ⧸ K.subgroupOf C)) = ⊥ :=
    componentLayerOf_quotient_eq_bot_of_central_kernel C K hKcentral hECbot
  have hFQ : fittingSubgroup (C ⧸ K.subgroupOf C) = ⊥ :=
    fittingSubgroup_quotient_eq_bot_of_central_kernel C K hKnormalC hKcentral hFCleK
  let Q : Type u := C ⧸ K.subgroupOf C
  have hQsub : Subsingleton Q := by
    exact finite_group_eq_bot_of_fitting_bot_and_componentLayer_bot (G := Q)
      (by simpa [Q] using hFQ) (by simpa [Q] using hEQ)
  -- `C ≤ K ≤ X`
  have hCleK : C ≤ K := by
    intro c hc
    let c₀ : ↥C := ⟨c, hc⟩
    have hπ : QuotientGroup.mk' (K.subgroupOf C) c₀ = 1 := Subsingleton.elim _ _
    have hcK' : c₀ ∈ K.subgroupOf C :=
      (QuotientGroup.eq_one_iff (N := K.subgroupOf C) (x := c₀)).1 hπ
    exact (Subgroup.mem_subgroupOf).1 hcK'
  change C ≤ X
  exact hCleK.trans inf_le_right


/-- If `N ⊴ G`, `N` is a `p`-group and `G / N` is a `p`-group, then `G` is
a `p`-group. -/
public theorem isPGroup_of_subgroup_and_quotient
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p G := by
  rcases (IsPGroup.iff_card.mp hN) with ⟨a, ha⟩
  rcases (IsPGroup.iff_card.mp hQ) with ⟨b, hb⟩
  apply IsPGroup.of_card
  calc
    Nat.card G = Nat.card N * N.index := (Subgroup.card_mul_index N).symm
    _ = Nat.card N * Nat.card (G ⧸ N) := by rw [Subgroup.index_eq_card]
    _ = p ^ a * p ^ b := by rw [ha, hb]
    _ = p ^ (a + b) := by rw [pow_add]

/-- The image in `N` of a characteristic subgroup of a subgroup `H` that is
normal in `N` is normal in `N`. -/
public theorem map_characteristic_isNormalIn_of_isNormalIn
    {G : Type u} [Group G] {H N : Subgroup G}
    (K : Subgroup (↥H)) (hKchar : K.Characteristic) (hHnormal : IsNormalIn H N) :
    IsNormalIn (K.map H.subtype) N := by
  refine ⟨?_, ?_⟩
  · exact (Subgroup.map_subtype_le (H := H) K).trans hHnormal.1
  · intro n hn x hx
    rcases (Subgroup.mem_map).1 hx with ⟨k, hk, rfl⟩
    let α : ↥H ≃* ↥H := {
      toFun := fun y => ⟨n * y.1 * n⁻¹, hHnormal.2 n hn y.1 y.2⟩
      invFun := fun y => ⟨n⁻¹ * y.1 * n, by
        have h' : n⁻¹ * y.1 * (n⁻¹)⁻¹ ∈ H := hHnormal.2 n⁻¹ (N.inv_mem hn) y.1 y.2
        simpa using h'⟩
      left_inv := by intro y; ext; group
      right_inv := by intro y; ext; group
      map_mul' := by
        intro a b
        ext
        change n * ↑(a * b) * n⁻¹ = (n * ↑a * n⁻¹) * (n * ↑b * n⁻¹)
        rw [Subgroup.coe_mul]
        group
    }
    have hαk : α k ∈ K := by
      rw [← (Subgroup.characteristic_iff_map_eq.mp hKchar) α]
      exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    exact Subgroup.mem_map.mpr ⟨α k, hαk, rfl⟩

/-- A normal `p`-subgroup of `A` lies in `O_p(A)`. -/
public theorem le_qCoreOf_of_normal_isPGroup
    {G : Type u} [Group G] [Finite G]
    (A N : Subgroup G) (p : ℕ) (hNle : N ≤ A) (hN : (N.subgroupOf A).Normal)
    (hNp : IsPGroup p N) : N ≤ qCoreOf A p := by
  classical
  let N' : Subgroup (↥A) := N.subgroupOf A
  have hN'norm : N'.Normal := hN
  have hN'p : IsPGroup p N' := by
    exact hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNle).symm
  have hle : N' ≤ pCore p (↥A) := le_sSup ⟨hN'norm, hN'p⟩
  have hmap : N'.map A.subtype ≤ (pCore p (↥A)).map A.subtype :=
    Subgroup.map_mono (f := A.subtype) hle
  have hNmap : N'.map A.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNle
  simpa [qCoreOf, hNmap] using hmap

/-- `O_p(A) ≤ O_p(B)` when `A ⊴ B`. -/
public theorem qCoreOf_le_qCoreOf_of_isNormalIn
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hAB : IsNormalIn A B) :
    qCoreOf A p ≤ qCoreOf B p := by
  classical
  have hQnorm : IsNormalIn (qCoreOf A p) B := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := A) (N := B)
      (pCore p (↥A)) (inferInstance : (pCore p (↥A)).Characteristic) hAB
    simpa [qCoreOf] using h
  have hQleB : qCoreOf A p ≤ B := hQnorm.1
  exact le_qCoreOf_of_normal_isPGroup B (qCoreOf A p) p hQleB
    (by
      rw [Subgroup.normal_subgroupOf_iff hQleB]
      intro x hx b hb
      exact hQnorm.2 hx hb x b)
    (qCoreOf_isPGroup A p)

/-- `O^p` is idempotent. -/
public theorem pResidualOf_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (pResidualOf H p) p = pResidualOf H p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let K : Subgroup G := pResidualOf H p
  let R : Subgroup G := pResidualOf K p
  have hKleH : K ≤ H := pResidualOf_le H p
  have hRleK : R ≤ K := pResidualOf_le K p
  have hRleH : R ≤ H := hRleK.trans hKleH
  have hKchar : ((pResidualOf H p).subgroupOf H).Characteristic :=
    pResidualOf_subgroupOf_characteristic H p
  have hRchar : ((pResidualOf K p).subgroupOf K).Characteristic :=
    pResidualOf_subgroupOf_characteristic K p
  -- `K ⊴ H`
  have hKisN : IsNormalIn K H := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := H) (N := H)
      (K.subgroupOf H) hKchar ⟨le_rfl, by
        intro x hx y hy
        exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)⟩
    rw [Subgroup.map_subgroupOf_eq_of_le hKleH] at h
    exact h
  have : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKleH]
    intro x hx h hh
    exact hKisN.2 hx hh x h
  -- `R ⊴ H`
  have hRisN : IsNormalIn R H := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := K) (N := H)
      (R.subgroupOf K) hRchar hKisN
    rw [Subgroup.map_subgroupOf_eq_of_le hRleK] at h
    exact h
  have hRnormH : (R.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRleH]
    intro x hx h hh
    exact hRisN.2 hx hh x h
  -- `H / R` is a `p`-group
  let R' : Subgroup (↥H) := R.subgroupOf H
  let K' : Subgroup (↥H) := K.subgroupOf H
  have hRleK' : R' ≤ K' := Subgroup.subgroupOf_mono H hRleK
  have : R'.Normal := hRnormH
  let π : (↥H) →* (↥H ⧸ R') := QuotientGroup.mk' R'
  let Kbar : Subgroup (↥H ⧸ R') := K'.map π
  have : Kbar.Normal := (inferInstance : K'.Normal).map π (QuotientGroup.mk'_surjective R')
  have hKQ : IsPGroup p (K ⧸ (pResidualOf K p).subgroupOf K) :=
    isPGroup_quotient_pResidualOf K p hp
  have hKbar : IsPGroup p Kbar := by
    let φ : (↥K) →* (↥H ⧸ R') := π.comp (Subgroup.inclusion hKleH)
    have hkerφ : φ.ker = R.subgroupOf K := by
      ext x
      constructor
      · intro hx
        rw [MonoidHom.mem_ker] at hx
        have hxR : ((Subgroup.inclusion hKleH) x : ↥H) ∈ R' :=
          (QuotientGroup.eq_one_iff (N := R') (x := ((Subgroup.inclusion hKleH) x))).1 hx
        exact (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_subgroupOf.mp hxR)
      · intro hx
        rw [MonoidHom.mem_ker]
        exact (QuotientGroup.eq_one_iff (N := R') (x := ((Subgroup.inclusion hKleH) x))).2
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx))
    have hrangeφ : φ.range = Kbar := by
      ext y
      constructor
      · intro hy
        rcases (MonoidHom.mem_range).1 hy with ⟨x, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(Subgroup.inclusion hKleH) x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
      · intro hy
        rw [MonoidHom.mem_range]
        rcases (Subgroup.mem_map).1 hy with ⟨k, hk, rfl⟩
        refine ⟨⟨k, (Subgroup.mem_subgroupOf).1 hk⟩, ?_⟩
        rfl
    let eKbar : K ⧸ R.subgroupOf K ≃* Kbar :=
      (QuotientGroup.quotientMulEquivOfEq (G := ↥K) (M := φ.ker) (N := R.subgroupOf K)
        hkerφ).symm.trans
        ((QuotientGroup.quotientKerEquivRange (φ := φ)).trans (MulEquiv.subgroupCongr hrangeφ))
    exact (by simpa [R] using hKQ : IsPGroup p (K ⧸ R.subgroupOf K)).of_equiv eKbar
  have hQbar : IsPGroup p ((↥H ⧸ R') ⧸ Kbar) := by
    have hHQ : IsPGroup p (H ⧸ K.subgroupOf H) := isPGroup_quotient_pResidualOf H p hp
    have e' : (↥H ⧸ R') ⧸ Kbar ≃* (↥H) ⧸ K' :=
      QuotientGroup.quotientQuotientEquivQuotient (G := ↥H) (N := R') (M := K') hRleK'
    have hHQ' : IsPGroup p ((↥H) ⧸ K') := by simpa [K'] using hHQ
    exact hHQ'.of_equiv e'.symm
  have hHR : IsPGroup p (H ⧸ R.subgroupOf H) := by
    have hHR' : IsPGroup p (↥H ⧸ R') :=
      isPGroup_of_subgroup_and_quotient (G := ↥H ⧸ R') (N := Kbar) hKbar hQbar
    simpa [R'] using hHR'
  -- conclude
  have hKR : K ≤ R := by
    exact pResidualOf_le_of_quotient_isPGroup H R p hp hRleH hRnormH hHR
  exact le_antisymm hRleK hKR

/-- The core step of Statement 1.8: if `F*(G)` is a `p`-group, the
`U`-centralizer inside `F*(G)` lies in `O_p(X)`, and `U` commutes with
`O^p(F*(X))` (as is the case for `X = C_G(U)` and `X = N_G(U)`), then
`F*(X)` is a `p`-group. -/
private theorem isPGroup_generalizedFitting_of_pCore_containment
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (hF : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup G)))
    (U X : Subgroup G) (hU : IsPGroup p U)
    (hCleO : (generalizedFittingSubgroupOf (⊤ : Subgroup G)) ⊓
        Subgroup.centralizer (U : Set G) ≤ qCoreOf X p)
    (hUK : ⁅U, pResidualOf (generalizedFittingSubgroupOf X) p⁆ = ⊥) :
    IsPGroup p (generalizedFittingSubgroupOf X) := by
  classical
  let Xstar : Subgroup G := generalizedFittingSubgroupOf X
  let K : Subgroup G := pResidualOf Xstar p
  let FstarG : Subgroup G := generalizedFittingSubgroupOf (⊤ : Subgroup G)
  have hKU : ⁅U, K⁆ = ⊥ := by simpa [K] using hUK
  have hKcent : K ≤ Subgroup.centralizer ((qCoreOf X p : Subgroup G) : Set G) := by
    exact pResidualOf_generalizedFitting_centralizer_qCore X p hp
  have hCBK : ⁅FstarG ⊓ Subgroup.centralizer (U : Set G), K⁆ = ⊥ := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := FstarG ⊓ Subgroup.centralizer (U : Set G)) (H₂ := K)).mpr
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkcent : k ∈ Subgroup.centralizer ((qCoreOf X p : Subgroup G) : Set G) :=
      hKcent hk
    exact ((Subgroup.mem_centralizer_iff.mp hkcent) z (hCleO hz)).symm
  have hFnorm : FstarG.Normal := by
    have hFi : IsNormalIn FstarG (⊤ : Subgroup G) :=
      generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup G)
    exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp (le_normalizer_of_isNormalIn hFi))
  have hUnormG : U ≤ Subgroup.normalizer (FstarG : Set G) := by
    have htop : Subgroup.normalizer (FstarG : Set G) = ⊤ :=
      (Subgroup.normalizer_eq_top_iff).mpr hFnorm
    simpa [htop]
  have hKnormG : K ≤ Subgroup.normalizer (FstarG : Set G) := by
    have htop : Subgroup.normalizer (FstarG : Set G) = ⊤ :=
      (Subgroup.normalizer_eq_top_iff).mpr hFnorm
    simpa [htop]
  have hKidem : pResidualOf K p = K := by
    simpa [K] using pResidualOf_pResidualOf Xstar p hp
  have hcent : Centralizes K FstarG :=
    bender1970_1_1_thompson p hp U K FstarG hU hF hKidem hUnormG hKnormG hKU hCBK
  have hKleF : K ≤ FstarG := by
    exact hcent.trans (by simpa [FstarG] using (fstar_self_centralizing (G := G)))
  have hKp : IsPGroup p K := IsPGroup.to_le hF hKleF
  exact isPGroup_of_pResidualOf_isPGroup Xstar p hp hKp

/-- Bender (1970), Statement 1.8. -/
public theorem bender1970_1_8_centralizerNormalizer_pGroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (hF : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup G)))
    (U : Subgroup G) (hU : IsPGroup p U) :
    IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G))) ∧
      IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer (U : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (U : Set G)
  let N : Subgroup G := Subgroup.normalizer (U : Set G)
  let FstarG : Subgroup G := generalizedFittingSubgroupOf (⊤ : Subgroup G)
  -- `F*(G) ⊴ G`
  have hFnorm : FstarG.Normal := by
    have hFi : IsNormalIn FstarG (⊤ : Subgroup G) :=
      generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup G)
    exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp (le_normalizer_of_isNormalIn hFi))
  -- `C_{F*(G)}(U)` is a normal `p`-subgroup of `C_G(U)`
  have hCUleC : FstarG ⊓ C ≤ C := inf_le_right
  have hCUnormC : ((FstarG ⊓ C).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCUleC]
    intro x hx c hc
    refine ⟨hFnorm.conj_mem x c.1 hx, C.mul_mem (C.mul_mem hc c.2) (C.inv_mem hc)⟩
  have hCUp : IsPGroup p (FstarG ⊓ C : Subgroup G) :=
    IsPGroup.to_inf_left hF
  -- `U ⊴ N_G(U)`
  have hUnormN : (U.subgroupOf N).Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := U) le_rfl
  -- `C_G(U) ⊴ N_G(U)`
  have hCisN : IsNormalIn C N := by
    have hCsubN : C ≤ N := Subgroup.centralizer_le_normalizer (U : Set G)
    have hnorm : (C.subgroupOf N).Normal := inferInstance
    have h' : ∀ h k : G, h ∈ C → k ∈ N → k * h * k⁻¹ ∈ C :=
      (Subgroup.normal_subgroupOf_iff hCsubN).mp hnorm
    exact ⟨hCsubN, by intro n hn c hc; exact h' c n hc hn⟩
  -- the `O_p` containments
  have hCleOC : FstarG ⊓ C ≤ qCoreOf C p :=
    le_qCoreOf_of_normal_isPGroup C (FstarG ⊓ C) p hCUleC hCUnormC hCUp
  have hUleON : U ≤ qCoreOf N p :=
    le_qCoreOf_of_normal_isPGroup N U p (by
      intro u hu
      exact Subgroup.le_normalizer hu) hUnormN hU
  have hCleON : FstarG ⊓ C ≤ qCoreOf N p :=
    hCleOC.trans (qCoreOf_le_qCoreOf_of_isNormalIn C N p hCisN)
  -- `U` commutes with the two residuals
  have hUKC : ⁅U, pResidualOf (generalizedFittingSubgroupOf C) p⁆ = ⊥ := by
    have hKleC : pResidualOf (generalizedFittingSubgroupOf C) p ≤ C :=
      (pResidualOf_le (generalizedFittingSubgroupOf C) p).trans
        (generalizedFittingSubgroupOf_le C)
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := U) (H₂ := pResidualOf (generalizedFittingSubgroupOf C) p)).mpr
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkC : k ∈ C := hKleC hk
    exact ((Subgroup.mem_centralizer_iff.mp hkC) u hu).symm
  have hUKN : ⁅U, pResidualOf (generalizedFittingSubgroupOf N) p⁆ = ⊥ := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := U) (H₂ := pResidualOf (generalizedFittingSubgroupOf N) p)).mpr
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkcent : k ∈ Subgroup.centralizer ((qCoreOf N p : Subgroup G) : Set G) :=
      pResidualOf_generalizedFitting_centralizer_qCore N p hp hk
    exact ((Subgroup.mem_centralizer_iff.mp hkcent) u (hUleON hu)).symm
  constructor
  · exact isPGroup_generalizedFitting_of_pCore_containment p hp hF U C hU hCleOC hUKC
  · exact isPGroup_generalizedFitting_of_pCore_containment p hp hF U N hU hCleON hUKN

end CFSG.GorensteinWalter
