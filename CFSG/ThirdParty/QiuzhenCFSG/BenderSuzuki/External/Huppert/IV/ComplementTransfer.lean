module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.NoncommCoprod

namespace CFSG
end CFSG
open CFSG

/-!
# Common complement-transfer tools for Huppert IV

This file contains the normal-complement, quotient, Thompson-subgroup, and
focal-transfer utilities used by Huppert IV.6.2 and later Huppert V arguments.
It deliberately avoids importing chapter V theorem files, so chapter IV remains
in book order.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
/-- If a normal subgroup and its quotient are `p`-groups, then the ambient group is a `p`-group. -/
public theorem hkt_isPGroup_of_normal_quotient
    {p : ℕ} {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p G := fun g => by
  rcases hQ (g : G ⧸ N) with ⟨k₁, hk₁⟩
  rw [← @QuotientGroup.mk_pow G _ N _ g (p ^ k₁), QuotientGroup.eq_one_iff] at hk₁
  rcases hN ⟨g ^ (p ^ k₁), hk₁⟩ with ⟨k₂, hk₂⟩
  use k₁ + k₂
  rw [SubmonoidClass.mk_pow, Subgroup.mk_eq_one, ← pow_mul, ← pow_add] at hk₂
  exact hk₂

/--
Solvability extension bridge for the HKT minimal-counterexample argument: a
normal nilpotent subgroup with nilpotent quotient makes the ambient group
solvable.
-/
public theorem hkt_solvable_of_normal_nilpotent_and_quotient_nilpotent
    {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal]
    (hN_nil : Group.IsNilpotent N)
    (hquot_nil : Group.IsNilpotent (Q ⧸ N)) :
    Group.IsSolvable Q := by
  have : Group.IsNilpotent N := hN_nil
  have : Group.IsSolvable N := IsNilpotent.to_isSolvable
  have : Group.IsNilpotent (Q ⧸ N) := hquot_nil
  have : Group.IsSolvable (Q ⧸ N) := IsNilpotent.to_isSolvable
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- A finite nilpotent group is `p`-nilpotent for every prime `p`. -/
public theorem hkt_hasNormalPComplement_of_nilpotent
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ_nil : Group.IsNilpotent Q) : HasNormalPComplement p Q := by
  classical
  refine ⟨pPrimeCore p Q, inferInstance, pPrimeCore_coprime_card (p := p) (G := Q), ?_⟩
  have hquot_nil : Group.IsNilpotent (Q ⧸ pPrimeCore p Q) := by
    infer_instance
  have hcore_bot : pPrimeCore p (Q ⧸ pPrimeCore p Q) = ⊥ := by
    simpa using pPrimeCore_quotient_pPrimeCore_eq_bot (G := Q) (p := p)
  have htop_le :
      (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤
        pCore p (Q ⧸ pPrimeCore p Q) ⊔ pPrimeCore p (Q ⧸ pPrimeCore p Q) := by
    have : Group.IsNilpotent (Q ⧸ pPrimeCore p Q) := hquot_nil
    have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q))) := by
      exact Group.nilpotent_of_mulEquiv
        (G := Q ⧸ pPrimeCore p Q) (G' := ↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
        (Subgroup.topEquiv.symm :
          (Q ⧸ pPrimeCore p Q) ≃* ↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
    have hTop_le_iSup :
        (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤
          ⨆ q : (Nat.card (Q ⧸ pPrimeCore p Q)).primeFactors.attach,
            pCore q.1 (Q ⧸ pPrimeCore p Q) :=
      normal_nilpotent_le_sup_pCore
        (G := Q ⧸ pPrimeCore p Q)
        (N := (⊤ : Subgroup (Q ⧸ pPrimeCore p Q))) (hN := inferInstance) hnilTop
    refine hTop_le_iSup.trans ?_
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1 = p
    · simp [hqp]
    · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
      let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
      obtain ⟨n, hn⟩ :=
        (pCore_isPGroup (G := Q ⧸ pPrimeCore p Q) (p := q.1)).exists_card_eq
      have hcop : Nat.Coprime p (Nat.card (pCore q.1 (Q ⧸ pPrimeCore p Q))) := by
        rw [hn]
        have hpq : p ≠ q.1 := by
          intro hpq'
          exact hqp hpq'.symm
        exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
      exact
        (le_sSup (show pCore q.1 (Q ⧸ pPrimeCore p Q) ∈
          {K : Subgroup (Q ⧸ pPrimeCore p Q) | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
            ⟨inferInstance, hcop⟩)).trans le_sup_right
  have htop_le_pcore :
      (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤ pCore p (Q ⧸ pPrimeCore p Q) := by
    simpa [hcore_bot] using htop_le
  have htop_p : IsPGroup p (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) :=
    IsPGroup.to_le (H := (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
      (K := pCore p (Q ⧸ pPrimeCore p Q))
      (pCore_isPGroup (G := Q ⧸ pPrimeCore p Q) (p := p)) htop_le_pcore
  simpa using htop_p.of_equiv
    (Subgroup.topEquiv : (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≃* (Q ⧸ pPrimeCore p Q))


/-- Repackage the definition of a normal `p`-complement using the canonical
`p'`-core quotient. This direction is only definitional: the real work is to
prove that `Q / O_{p'}(Q)` is a `p`-group. -/
public theorem hkt_hasNormalPComplement_of_quotient_pPrimeCore_isPGroup
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hquot : IsPGroup p (Q ⧸ pPrimeCore p Q)) :
    HasNormalPComplement p Q := by
  exact ⟨pPrimeCore p Q, inferInstance, pPrimeCore_coprime_card (p := p) (G := Q), hquot⟩
public theorem hkt_isPGroup_quotient_map_subtype_of_extension
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (K : Subgroup H) [K.Characteristic]
    (hHKp : IsPGroup p (H ⧸ K)) (hGHp : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  let N : Subgroup G := K.map H.subtype
  have hN_le_H : N ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, _hk, rfl⟩
    exact k.property
  have : N.Normal := by
    dsimp [N]
    infer_instance
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (G ⧸ N) := H.map qN
  have : Hbar.Normal := by
    exact Subgroup.Normal.map (inferInstance : H.Normal) qN (QuotientGroup.mk'_surjective N)
  have hHbar_p : IsPGroup p Hbar := by
    let eHN : H ⧸ N.subgroupOf H ≃* H ⧸ K :=
      QuotientGroup.quotientMulEquivOfEq (by
        simpa [N] using (subgroupOf_map_subtype_eq (K := H) K))
    let eRange : H ⧸ N.subgroupOf H ≃* Hbar := quotientSubgroupRangeEquiv H N
    exact hHKp.of_equiv (eHN.symm.trans eRange)
  have hquot_p : IsPGroup p ((G ⧸ N) ⧸ Hbar) := by
    let e : (G ⧸ N) ⧸ Hbar ≃* G ⧸ H :=
      QuotientGroup.quotientQuotientEquivQuotient (N := N) (M := H) hN_le_H
    exact hGHp.of_equiv e.symm
  obtain ⟨a, ha⟩ := hquot_p.exists_card_eq
  obtain ⟨b, hb⟩ := hHbar_p.exists_card_eq
  have hcard :
      Nat.card (G ⧸ N) = Nat.card ((G ⧸ N) ⧸ Hbar) * Nat.card Hbar := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Hbar))
  refine IsPGroup.of_card (p := p) (G := G ⧸ N) (n := a + b) ?_
  rw [hcard, ha, hb, Nat.pow_add]

public theorem hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal]
    (hGHp : IsPGroup p (G ⧸ H))
    (hHcomp : HasNormalPComplement p H) :
    HasNormalPComplement p G := by
  classical
  let K : Subgroup H := pPrimeCore p H
  let N : Subgroup G := K.map H.subtype
  have : K.Characteristic := pPrimeCore_characteristic (p := p) (G := H)
  have hNnorm : N.Normal := by
    dsimp [N, K]
    infer_instance
  have hNcop : Nat.Coprime p (Nat.card N) := by
    have hcard : Nat.card N = Nat.card K := by
      simpa [N] using
        (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := H) (p := p)
  have hHKp : IsPGroup p (H ⧸ K) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hHcomp
  have hGNp : IsPGroup p (G ⧸ N) :=
    hkt_isPGroup_quotient_map_subtype_of_extension (G := G) (p := p)
      H K hHKp hGHp
  exact ⟨N, hNnorm, hNcop, hGNp⟩


/-- A normal `p`-complement descends to an arbitrary normal quotient.  The image
of the original `p'`-complement is still of `p'`-order, and the new quotient is a
surjective image of the old `p`-group quotient. -/
public theorem hkt_hasNormalPComplement_to_quotient
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup H) [N.Normal] :
    HasNormalPComplement p H → HasNormalPComplement p (H ⧸ N) := by
  classical
  intro hcomp
  rcases hcomp with ⟨K, hKnorm, hKcop, hquotp⟩
  let qN : H →* H ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (H ⧸ N) := K.map qN
  have hKbar_norm : Kbar.Normal :=
    Subgroup.Normal.map hKnorm qN (QuotientGroup.mk'_surjective N)
  have hKbar_cop : Nat.Coprime p (Nat.card Kbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := K) qN) hKcop
  let φ0 : H →* (H ⧸ N) ⧸ Kbar := (QuotientGroup.mk' Kbar).comp qN
  have hK_le_ker : K ≤ φ0.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := Kbar) (x := qN x)).2
      (Subgroup.mem_map_of_mem qN hx)
  let φ : H ⧸ K →* (H ⧸ N) ⧸ Kbar := QuotientGroup.lift K φ0 hK_le_ker
  have hφ_surj : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective
      (N := K) (φ := φ0) (by
        intro y
        obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective Kbar y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y0
        exact ⟨x, rfl⟩) hK_le_ker
  exact ⟨Kbar, hKbar_norm, hKbar_cop, hquotp.of_surjective φ hφ_surj⟩

/-- A normal `p`-complement for a subgroup descends to its image in a quotient by
an ambient normal subgroup contained in it. -/
public theorem hkt_hasNormalPComplement_map_quotient_of_normal_subgroup
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N K : Subgroup H) [N.Normal] (_hN_le_K : N ≤ K)
    [hN_K_normal : (N.subgroupOf K).Normal]
    (hcomp : HasNormalPComplement p K) :
    HasNormalPComplement p (K.map (QuotientGroup.mk' N)) := by
  classical
  have hquot : HasNormalPComplement p (K ⧸ N.subgroupOf K) := by
    exact hkt_hasNormalPComplement_to_quotient (H := K) (p := p)
      (N := N.subgroupOf K) hcomp
  let e : K ⧸ N.subgroupOf K ≃* K.map (QuotientGroup.mk' N) :=
    quotientSubgroupRangeEquiv K N
  exact hasNormalPComplement_of_equiv (G := K ⧸ N.subgroupOf K) (p := p) e hquot
/-- For a quotient by a normal subgroup already contained in `T`, normalizers
commute with passing to the quotient. -/
public theorem hkt_normalizer_map_quotient_eq_map_normalizer_of_le
    {G : Type u} [Group G] (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    Subgroup.normalizer (T.map q : Set (G ⧸ N)) =
      (Subgroup.normalizer (T : Set G)).map q := by
  classical
  intro q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  apply Subgroup.comap_injective hqsurj
  rw [Subgroup.comap_normalizer_eq_of_surjective (H := T.map q) hqsurj]
  rw [QuotientGroup.comap_map_mk' (N := N) (H := T)]
  rw [QuotientGroup.comap_map_mk' (N := N) (H := Subgroup.normalizer (T : Set G))]
  have hN_le_norm : N ≤ Subgroup.normalizer (T : Set G) :=
    hN_le_T.trans (Subgroup.le_normalizer (H := T))
  rw [sup_eq_right.mpr hN_le_T, sup_eq_right.mpr hN_le_norm]

/-- In the same quotient setting, the centralizer of `T/U` is contained in the
image of the ambient normalizer of `T`. -/
public theorem hkt_centralizer_map_quotient_le_map_normalizer_of_le
    {G : Type u} [Group G] (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    Subgroup.centralizer (T.map q : Set (G ⧸ N)) ≤
      (Subgroup.normalizer (T : Set G)).map q := by
  classical
  intro q
  calc
    Subgroup.centralizer (T.map q : Set (G ⧸ N)) ≤
        Subgroup.normalizer (T.map q : Set (G ⧸ N)) :=
      centralizer_le_normalizer (T.map q)
    _ = (Subgroup.normalizer (T : Set G)).map q :=
      hkt_normalizer_map_quotient_eq_map_normalizer_of_le (N := N) (T := T) hN_le_T
/-- The preimage-in-`P` description of `Z(P/U)` maps to the ambient `centerIn`
of the image of `P` in `G/U`. -/
public theorem hkt_centerIn_map_quotient_subgroup_eq
    {G : Type u} [Group G] [Finite G]
    (N P : Subgroup G) [N.Normal] (_hN_le_P : N ≤ P) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    let NP : Subgroup P := N.subgroupOf P
    let Zbar : Subgroup (P ⧸ NP) := Subgroup.center (P ⧸ NP)
    let K : Subgroup P := Zbar.comap (QuotientGroup.mk' NP)
    let K_G : Subgroup G := K.map P.subtype
    K_G.map q = centerIn (G := G ⧸ N) (P.map q) := by
  classical
  intro q NP Zbar K K_G
  let : NP.Normal := by
    simpa [NP] using (inferInstance : (N.subgroupOf P).Normal)
  let e : P ⧸ NP ≃* P.map q := quotientSubgroupRangeEquiv P N
  have htop_map : (⊤ : Subgroup (P.map q)).map (P.map q).subtype = P.map q := by
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := P.map q))
  calc
    K_G.map q = K.map (q.comp P.subtype) := by
      simp [K_G, Subgroup.map_map]
    _ = (Zbar.map e.toMonoidHom).map (P.map q).subtype := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨k, hkK, rfl⟩
        refine Subgroup.mem_map.mpr ?_
        refine ⟨e (QuotientGroup.mk' NP k), ?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' NP k,
            (by simpa [K] using hkK), rfl⟩
        · simpa [e, q] using quotientSubgroupRangeEquiv_apply_mk P N k
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzval⟩
        rcases Subgroup.mem_map.mp hz with ⟨zq, hzZ, rfl⟩
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective NP zq
        refine Subgroup.mem_map.mpr ⟨k, hzZ, ?_⟩
        calc
          q (k : G) = (e (QuotientGroup.mk' NP k) : G ⧸ N) := by
            simpa [e, q] using (quotientSubgroupRangeEquiv_apply_mk P N k).symm
          _ = x := hzval
    _ = (centerIn (G := P.map q) (⊤ : Subgroup (P.map q))).map (P.map q).subtype := by
      have hcenter_map :
          Zbar.map e.toMonoidHom =
            centerIn (G := P.map q) (⊤ : Subgroup (P.map q)) := by
        have hZbar :
            Zbar = centerIn (G := P ⧸ NP) (⊤ : Subgroup (P ⧸ NP)) := by
          simp [Zbar, centerIn, Subgroup.centralizer_univ]
        rw [hZbar]
        simpa using centerIn_map_mulEquiv e (⊤ : Subgroup (P ⧸ NP))
      rw [hcenter_map]
    _ = centerIn (G := G ⧸ N) (P.map q) := by
      simpa [htop_map] using
        (centerIn_top_map_subtype (G := G ⧸ N) (S := P.map q)
          (H := (⊤ : Subgroup (P.map q))))

/-- The preimage-in-`P` description of `J(P/U)` maps to the Thompson subgroup
of the image of `P` in `G/U`. -/
public theorem hkt_thompsonSubgroup_map_quotient_subgroup_eq
    {G : Type u} [Group G] [Finite G]
    (N P : Subgroup G) [N.Normal] (_hN_le_P : N ≤ P) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    let NP : Subgroup P := N.subgroupOf P
    let Jbar : Subgroup (P ⧸ NP) := thompsonSubgroup (G := P ⧸ NP) ⊤
    let K : Subgroup P := Jbar.comap (QuotientGroup.mk' NP)
    let K_G : Subgroup G := K.map P.subtype
    K_G.map q = thompsonSubgroup (G := G ⧸ N) (P.map q) := by
  classical
  intro q NP Jbar K K_G
  let : NP.Normal := by
    simpa [NP] using (inferInstance : (N.subgroupOf P).Normal)
  let e : P ⧸ NP ≃* P.map q := quotientSubgroupRangeEquiv P N
  calc
    K_G.map q = K.map (q.comp P.subtype) := by
      simp [K_G, Subgroup.map_map]
    _ = (Jbar.map e.toMonoidHom).map (P.map q).subtype := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨k, hkK, rfl⟩
        refine Subgroup.mem_map.mpr ?_
        refine ⟨e (QuotientGroup.mk' NP k), ?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' NP k,
            (by simpa [K] using hkK), rfl⟩
        · simpa [e, q] using quotientSubgroupRangeEquiv_apply_mk P N k
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzval⟩
        rcases Subgroup.mem_map.mp hz with ⟨zq, hzJ, rfl⟩
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective NP zq
        refine Subgroup.mem_map.mpr ⟨k, hzJ, ?_⟩
        calc
          q (k : G) = (e (QuotientGroup.mk' NP k) : G ⧸ N) := by
            simpa [e, q] using (quotientSubgroupRangeEquiv_apply_mk P N k).symm
          _ = x := hzval
    _ = (thompsonSubgroup (G := P.map q) (⊤ : Subgroup (P.map q))).map
          (P.map q).subtype := by
      have hJ_map :
          Jbar.map e.toMonoidHom =
            thompsonSubgroup (G := P.map q) (⊤ : Subgroup (P.map q)) := by
        simpa [Jbar] using thompsonSubgroup_top_map_mulEquiv e
      rw [hJ_map]
    _ = thompsonSubgroup (G := G ⧸ N) (P.map q) := by
      simpa using thompsonSubgroup_top_map_subtype (G := G ⧸ N) (P.map q)
/-- The image in the ambient group of the normalizer of an intrinsic subgroup
normalizes the ambient image of that subgroup. -/
public theorem hkt_normalizer_map_subtype_le_normalizer_map
    {G : Type u} [Group G] (N : Subgroup G) (K : Subgroup N) :
    (Subgroup.normalizer (K : Set N)).map N.subtype ≤
      Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G) := by
  classical
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨k, hk, rfl⟩
    refine Subgroup.mem_map.mpr ⟨((n : N) * k * (n : N)⁻¹), ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hn k).1 hk
    · simp
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨k, hk, hkz⟩
    refine Subgroup.mem_map.mpr ⟨((n : N)⁻¹ * k * (n : N)), ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set N)).inv_mem hn) k).1 hk
    · calc
        N.subtype ((n : N)⁻¹ * k * (n : N)) =
            (N.subtype (n : N))⁻¹ * N.subtype k * N.subtype (n : N) := by
              simp
        _ = (N.subtype (n : N))⁻¹ *
              (N.subtype (n : N) * z * (N.subtype (n : N))⁻¹) *
                N.subtype (n : N) := by
              rw [hkz]
        _ = z := by simp [mul_assoc]

/-- Pull a normal `p`-complement back from an ambient subgroup containing the
ambient image of an intrinsic subgroup. -/
public theorem hkt_hasNormalPComplement_of_map_subtype_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) (H : Subgroup G) (L : Subgroup N)
    (hLmap_le_H : L.map N.subtype ≤ H)
    (hcomp : HasNormalPComplement p H) :
    HasNormalPComplement p L := by
  classical
  have hLmap_comp : HasNormalPComplement p (L.map N.subtype) :=
    hasNormalPComplement_of_le p hLmap_le_H hcomp
  exact hasNormalPComplement_of_map_subtype (G := G) (p := p) (H := N) (K := L)
    hLmap_comp

/-- The image in the ambient group of the centralizer of an intrinsic subgroup
centralizes the ambient image of that subgroup. -/
public theorem hkt_centralizer_map_subtype_le_centralizer_map
    {G : Type u} [Group G] (N : Subgroup G) (K : Subgroup N) :
    (Subgroup.centralizer (K : Set N)).map N.subtype ≤
      Subgroup.centralizer ((K.map N.subtype : Subgroup G) : Set G) := by
  classical
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨k, hk, rfl⟩
  exact congrArg Subtype.val (hn k hk)


/-- If an ambient subgroup `T` is contained in the ambient image of an intrinsic
subgroup `K`, a normal `p`-complement for `C_G(T)` pulls back to `C_N(K)`. -/
public theorem hkt_hasNormalPComplement_centralizer_subgroupOf_of_ambient_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) (K : Subgroup N) (T : Subgroup G)
    (hT_le_Kmap : T ≤ K.map N.subtype)
    (hcomp : HasNormalPComplement p (Subgroup.centralizer (T : Set G))) :
    HasNormalPComplement p (Subgroup.centralizer (K : Set N)) := by
  classical
  exact hkt_hasNormalPComplement_of_map_subtype_le
    (G := G) (p := p) (N := N)
    (H := Subgroup.centralizer (T : Set G))
    (L := Subgroup.centralizer (K : Set N))
    ((hkt_centralizer_map_subtype_le_centralizer_map (N := N) (K := K)).trans
      (Subgroup.centralizer_le (show (T : Set G) ⊆ (K.map N.subtype : Set G) from hT_le_Kmap)))
    hcomp
/-- If the ambient normalizer of the ambient image of an intrinsic subgroup has
a normal `p`-complement, then the intrinsic normalizer has one too. -/
public theorem hkt_hasNormalPComplement_normalizer_subgroupOf_of_ambient_image
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) (K : Subgroup N)
    (hcomp : HasNormalPComplement p
      (Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G))) :
    HasNormalPComplement p (Subgroup.normalizer (K : Set N)) := by
  classical
  exact hkt_hasNormalPComplement_of_map_subtype_le
    (G := G) (p := p) (N := N)
    (H := Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G))
    (L := Subgroup.normalizer (K : Set N))
    (hkt_normalizer_map_subtype_le_normalizer_map (N := N) (K := K)) hcomp
/-- If `N ≤ T`, a normal `p`-complement for `N_G(T)` descends to the image of
`N_G(T)` in `G/N`. -/
public theorem hkt_hasNormalPComplement_normalizer_map_quotient_of_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T)
    (hcomp : HasNormalPComplement p (Subgroup.normalizer (T : Set G))) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    HasNormalPComplement p ((Subgroup.normalizer (T : Set G)).map q) := by
  classical
  intro q
  have hN_le_norm : N ≤ Subgroup.normalizer (T : Set G) :=
    hN_le_T.trans (Subgroup.le_normalizer (H := T))
  have : (N.subgroupOf (Subgroup.normalizer (T : Set G))).Normal := by
    have hnorm_top : Subgroup.normalizer (N : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := N) (K := Subgroup.normalizer (T : Set G)) hN_le_norm).2 (by
          simp [hnorm_top])
  exact hkt_hasNormalPComplement_map_quotient_of_normal_subgroup
    (H := G) (p := p) (N := N) (K := Subgroup.normalizer (T : Set G))
    hN_le_norm hcomp

/-- If `N ≤ T`, then a normal `p`-complement for the ambient normalizer of `T`
gives one for the centralizer of `T/N` in the quotient. -/
public theorem hkt_hasNormalPComplement_centralizer_map_quotient_of_normalizer
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T)
    (hcomp : HasNormalPComplement p (Subgroup.normalizer (T : Set G))) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    HasNormalPComplement p
      (Subgroup.centralizer (T.map q : Set (G ⧸ N))) := by
  classical
  intro q
  have hcomp_map : HasNormalPComplement p ((Subgroup.normalizer (T : Set G)).map q) := by
    simpa [q] using
      hkt_hasNormalPComplement_normalizer_map_quotient_of_le
        (G := G) (p := p) (N := N) (T := T) hN_le_T hcomp
  exact hasNormalPComplement_of_le p
    (hkt_centralizer_map_quotient_le_map_normalizer_of_le
      (G := G) (N := N) (T := T) hN_le_T)
    hcomp_map

/-- If `N ≤ T`, then a normal `p`-complement for the ambient normalizer of `T`
gives one for the normalizer of `T/N` in the quotient. -/
public theorem hkt_hasNormalPComplement_normalizer_map_quotient_of_normalizer
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T)
    (hcomp : HasNormalPComplement p (Subgroup.normalizer (T : Set G))) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    HasNormalPComplement p
      (Subgroup.normalizer (T.map q : Set (G ⧸ N))) := by
  classical
  intro q
  have hcomp_map : HasNormalPComplement p ((Subgroup.normalizer (T : Set G)).map q) := by
    simpa [q] using
      hkt_hasNormalPComplement_normalizer_map_quotient_of_le
        (G := G) (p := p) (N := N) (T := T) hN_le_T hcomp
  rw [hkt_normalizer_map_quotient_eq_map_normalizer_of_le
    (G := G) (N := N) (T := T) hN_le_T]
  exact hcomp_map
/-- A normal `p`-complement survives quotienting by a normal subgroup contained
in the canonical `p'`-core. -/
public theorem hkt_hasNormalPComplement_quotient_of_le_pPrimeCore
    {H : Type u} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [Fact p.Prime]
    (hN_le_core : N ≤ pPrimeCore p H) (hcomp : HasNormalPComplement p H) :
    HasNormalPComplement p (H ⧸ N) := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let C : Subgroup (H ⧸ N) := (pPrimeCore p H).map q
  have hCnormal : C.Normal :=
    Subgroup.Normal.map (inferInstance : (pPrimeCore p H).Normal) q
      (QuotientGroup.mk'_surjective N)
  have hCcop : Nat.Coprime p (Nat.card C) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_map_dvd (H := pPrimeCore p H) q)
      (pPrimeCore_coprime_card (G := H) (p := p))
  have hquot_core_p : IsPGroup p (H ⧸ pPrimeCore p H) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := H) hcomp
  have hquot_p : IsPGroup p ((H ⧸ N) ⧸ C) := by
    let e : (H ⧸ N) ⧸ C ≃* H ⧸ pPrimeCore p H :=
      QuotientGroup.quotientQuotientEquivQuotient
        (N := N) (M := pPrimeCore p H) hN_le_core
    exact hquot_core_p.of_equiv e.symm
  exact ⟨C, hCnormal, hCcop, hquot_p⟩

/-- A normal `p`-complement for a subgroup survives passage to its image modulo
an ambient `p'`-core. -/
public theorem hkt_hasNormalPComplement_map_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (H : Subgroup Q) (hcomp : HasNormalPComplement p H) :
    let M : Subgroup Q := pPrimeCore p Q
    let π : Q →* Q ⧸ M := QuotientGroup.mk' M
    HasNormalPComplement p (H.map π) := by
  classical
  intro M π
  let ψ0 : H →* H.map π :=
    (π.comp H.subtype).codRestrict (H.map π) (by
      intro x
      exact Subgroup.mem_map_of_mem π x.2)
  have hψ0_surj : Function.Surjective ψ0 := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hxH, hxy⟩
    refine ⟨⟨x, hxH⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let K : Subgroup H := ψ0.ker
  have hK_le_core : K ≤ pPrimeCore p H := by
    have hK_normal : K.Normal := inferInstance
    have hK_coprime : Nat.Coprime p (Nat.card K) := by
      let KmapQ : Subgroup Q := K.map H.subtype
      have hKmap_le_M : KmapQ ≤ M := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨k, hkK, rfl⟩
        have hkψ : ψ0 k = 1 := hkK
        have hπ_one : π ((k : H) : Q) = 1 := by
          have hval := congrArg Subtype.val hkψ
          simpa [ψ0] using hval
        exact (QuotientGroup.eq_one_iff (N := M) (x := ((k : H) : Q))).1 hπ_one
      have hcard_map : Nat.card KmapQ = Nat.card K := by
        exact Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective
      have hcard_sub : Nat.card (KmapQ.subgroupOf M) = Nat.card KmapQ := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := KmapQ) (K := M) hKmap_le_M).toEquiv
      have hcard_dvd_M : Nat.card K ∣ Nat.card M := by
        have hdvd : Nat.card (KmapQ.subgroupOf M) ∣ Nat.card M :=
          Subgroup.card_subgroup_dvd_card (KmapQ.subgroupOf M)
        simpa [hcard_sub, hcard_map] using hdvd
      exact Nat.Coprime.of_dvd_right hcard_dvd_M
        (pPrimeCore_coprime_card (G := Q) (p := p))
    exact le_sSup ⟨hK_normal, hK_coprime⟩
  have hcomp_quot : HasNormalPComplement p (H ⧸ K) :=
    hkt_hasNormalPComplement_quotient_of_le_pPrimeCore
      (H := H) (N := K) (p := p) hK_le_core hcomp
  let e : H ⧸ K ≃* H.map π :=
    QuotientGroup.quotientKerEquivOfSurjective ψ0 hψ0_surj
  exact hasNormalPComplement_of_equiv (G := H ⧸ K) (p := p) e hcomp_quot

/-- If a quotient is a `p`-group, the image of any Sylow `p`-subgroup in that
quotient is all of the quotient. -/
public theorem sylow_map_quotient_eq_top_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup p (G ⧸ N)) :
    (S : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Q := G ⧸ N
  let Tmap : Sylow p Q := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop_p : IsPGroup p (⊤ : Subgroup Q) := by
    simpa [Q] using hquot.to_subgroup (⊤ : Subgroup (G ⧸ N))
  let Ttop : Sylow p Q :=
    IsPGroup.toSylow (G := Q) (p := p) htop_p (by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one)
  have hTtop_normal : (Ttop : Subgroup Q).Normal := by
    have hTtop_eq : (Ttop : Subgroup Q) = ⊤ := by
      dsimp [Ttop]
    rw [hTtop_eq]
    infer_instance
  have : Unique (Sylow p Q) := Sylow.unique_of_normal Ttop hTtop_normal
  have hSylow_eq : Tmap = Ttop := Subsingleton.elim _ _
  change (Tmap : Subgroup Q) = ⊤
  simpa [Tmap, Ttop, IsPGroup.toSylow_coe, q, Q] using
    congrArg (fun P : Sylow p Q => (P : Subgroup Q)) hSylow_eq

/-- Element form of `sylow_map_quotient_eq_top_of_quotient_isPGroup`: every
quotient class has a representative in the fixed Sylow subgroup. -/
public theorem hkt_exists_sylow_div_mem_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup p (G ⧸ N)) (g : G) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧ g * s⁻¹ ∈ N := by
  classical
  have hmap_top :
      (S : Subgroup G).map (QuotientGroup.mk' N) = ⊤ :=
    sylow_map_quotient_eq_top_of_quotient_isPGroup
      (G := G) (p := p) S N hquot
  have hgmap : QuotientGroup.mk' N g ∈ (S : Subgroup G).map (QuotientGroup.mk' N) := by
    simp [hmap_top]
  rcases Subgroup.mem_map.mp hgmap with ⟨s, hsS, hs_eq⟩
  refine ⟨s, hsS, ?_⟩
  have hdiv : g / s ∈ N :=
    (QuotientGroup.eq_iff_div_mem (N := N)).1 hs_eq.symm
  simpa [div_eq_mul_inv] using hdiv

/-- The center of a Sylow subgroup maps to the center of the image Sylow after
quotienting by the canonical `p'`-core. -/
public theorem hkt_centerIn_sylow_map_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (S : Sylow p Q) :
    let M : Subgroup Q := pPrimeCore p Q
    let π : Q →* Q ⧸ M := QuotientGroup.mk' M
    let Sbar : Sylow p (Q ⧸ M) :=
      S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
    (centerIn (G := Q) (S : Subgroup Q)).map π =
      centerIn (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
  classical
  intro M π Sbar
  have hqinj : Function.Injective (π.comp (S : Subgroup Q).subtype) := by
    simpa [π, M] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := Q) (p := p) (H := (S : Subgroup Q)) S.isPGroup'
  let f : S →* ((S : Subgroup Q).map π) :=
    (π.comp (S : Subgroup Q).subtype).codRestrict ((S : Subgroup Q).map π) (by
      intro x
      exact Subgroup.mem_map_of_mem π x.2)
  let e : S ≃* ((S : Subgroup Q).map π) := by
    refine MulEquiv.ofBijective f ⟨?_, ?_⟩
    · intro a b hab
      exact hqinj <| by exact congrArg Subtype.val hab
    · intro x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  have hcomp :
      ((Subgroup.subtype ((S : Subgroup Q).map π)).comp e.toMonoidHom) =
        π.comp (S : Subgroup Q).subtype := by
    rfl
  calc
    (centerIn (G := Q) (S : Subgroup Q)).map π =
        ((centerIn (G := S) (⊤ : Subgroup S)).map (S : Subgroup Q).subtype).map π := by
          have hcenter_sub :
              ((centerIn (G := S) (⊤ : Subgroup S)).map (S : Subgroup Q).subtype) =
                centerIn (G := Q) (S : Subgroup Q) := by
            have htop_map :
                (⊤ : Subgroup S).map (S : Subgroup Q).subtype = (S : Subgroup Q) := by
              simpa [MonoidHom.range_eq_map] using
                (Subgroup.range_subtype (H := (S : Subgroup Q)))
            simpa [htop_map] using
              centerIn_top_map_subtype (G := Q) (S := (S : Subgroup Q))
                (H := (⊤ : Subgroup S))
          exact (congrArg (fun K : Subgroup Q => K.map π) hcenter_sub).symm
    _ = (centerIn (G := S) (⊤ : Subgroup S)).map
          (π.comp (S : Subgroup Q).subtype) := by
          rw [Subgroup.map_map]
    _ = ((centerIn (G := S) (⊤ : Subgroup S)).map e.toMonoidHom).map
          (Subgroup.subtype ((S : Subgroup Q).map π)) := by
          rw [Subgroup.map_map, hcomp]
    _ = (centerIn (G := ((S : Subgroup Q).map π))
          (⊤ : Subgroup ((S : Subgroup Q).map π))).map
          (Subgroup.subtype ((S : Subgroup Q).map π)) := by
          rw [centerIn_map_mulEquiv]
          simp
    _ = centerIn (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
          have htop_map :
              (⊤ : Subgroup ((S : Subgroup Q).map π)).map
                  (Subgroup.subtype ((S : Subgroup Q).map π)) =
                (S : Subgroup Q).map π := by
            simpa [MonoidHom.range_eq_map] using
              (Subgroup.range_subtype (H := ((S : Subgroup Q).map π)))
          simpa [Sbar, Sylow.coe_mapSurjective, htop_map] using
            centerIn_top_map_subtype (G := Q ⧸ M) ((S : Subgroup Q).map π)
              (⊤ : Subgroup ((S : Subgroup Q).map π))


/-- If the canonical `p'`-core has vanished, the canonical quotient criterion
is just `Q` itself being a `p`-group. -/
public theorem hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥)
    (hquot : IsPGroup p (Q ⧸ pPrimeCore p Q)) :
    IsPGroup p Q := by
  let e : Q ⧸ pPrimeCore p Q ≃* Q ⧸ (⊥ : Subgroup Q) :=
    QuotientGroup.quotientMulEquivOfEq hcore
  have hbot : IsPGroup p (Q ⧸ (⊥ : Subgroup Q)) := hquot.of_equiv e
  exact hbot.of_equiv (QuotientGroup.quotientBot (G := Q))

public theorem hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥) (hcomp : HasNormalPComplement p Q) :
    IsPGroup p Q :=
  hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    (Q := Q) (p := p) hcore
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := Q) hcomp)

/-- The local normal-complement hypothesis for `C_Q(Z(S))` descends to the
canonical `p'`-core quotient. -/
public theorem hkt_centralizer_center_sylow_hasNormalPComplement_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (S : Sylow p Q)
    (hcomp : HasNormalPComplement p
      (↥(Subgroup.centralizer (centerIn (G := Q) (S : Subgroup Q) : Set Q)))) :
    let M : Subgroup Q := pPrimeCore p Q
    let π : Q →* Q ⧸ M := QuotientGroup.mk' M
    let Sbar : Sylow p (Q ⧸ M) :=
      S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
    HasNormalPComplement p
      (↥(Subgroup.centralizer
        (centerIn (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) : Set (Q ⧸ M)))) := by
  classical
  intro M π Sbar
  have : Fact (IsPGroup p (↥(centerIn (G := Q) (S : Subgroup Q)))) :=
    ⟨IsPGroup.to_le S.isPGroup' (show centerIn (G := Q) (S : Subgroup Q) ≤ (S : Subgroup Q) from inf_le_left)⟩
  have hcenter_map :
      (centerIn (G := Q) (S : Subgroup Q)).map π =
        centerIn (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) := by
    simpa [M, π, Sbar] using
      hkt_centerIn_sylow_map_quotient_pPrimeCore (Q := Q) (p := p) S
  have hcent_eq :
      Subgroup.centralizer
          (centerIn (G := Q ⧸ M) (Sbar : Subgroup (Q ⧸ M)) : Set (Q ⧸ M)) =
        (Subgroup.centralizer (centerIn (G := Q) (S : Subgroup Q) : Set Q)).map π := by
    simpa [π, M, hcenter_map] using
      (centralizer_map_quotient_eq_map_centralizer
        (G := Q) (p := p) (T := centerIn (G := Q) (S : Subgroup Q)) (M := M)
        (inferInstance : M.Normal)
        (by simpa [M] using (pPrimeCore_coprime_card (G := Q) (p := p))))
  rw [hcent_eq]
  exact hkt_hasNormalPComplement_map_quotient_pPrimeCore
    (Q := Q) (p := p)
    (H := Subgroup.centralizer (centerIn (G := Q) (S : Subgroup Q) : Set Q)) hcomp


public theorem hkt_dvd_card_quotient_pPrimeCore_of_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hp_dvd : p ∣ Nat.card Q) :
    p ∣ Nat.card (Q ⧸ pPrimeCore p Q) := by
  classical
  let M : Subgroup Q := pPrimeCore p Q
  have hcard :
      Nat.card Q = Nat.card (Q ⧸ M) * Nat.card M := by
    simpa [M] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := M))
  have hp_dvd_mul :
      p ∣ Nat.card (Q ⧸ M) * Nat.card M := by
    simpa [hcard] using hp_dvd
  rcases (Fact.out : Nat.Prime p).dvd_mul.mp hp_dvd_mul with hquot | hcore
  · simpa [M] using hquot
  · have hcop : Nat.Coprime p (Nat.card M) := by
      simpa [M] using pPrimeCore_coprime_card (G := Q) (p := p)
    exact False.elim (((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop) hcore)

/-- Burnside centrality descends faithfully through the `q'`-core quotient: if
the image Sylow subgroup is central in its normalizer modulo `O_{q'}(Q)`, then
the original Sylow subgroup was already central in its normalizer. -/
public theorem sylow_le_center_normalizer_of_quotient_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hquot :
      ((S.mapSurjective
        (f := QuotientGroup.mk' (pPrimeCore q Q))
        (QuotientGroup.mk'_surjective (pPrimeCore q Q)) :
          Sylow q (Q ⧸ pPrimeCore q Q)) : Subgroup (Q ⧸ pPrimeCore q Q)) ≤
        centerIn (G := Q ⧸ pPrimeCore q Q)
          (Subgroup.normalizer
            (((S.mapSurjective
              (f := QuotientGroup.mk' (pPrimeCore q Q))
              (QuotientGroup.mk'_surjective (pPrimeCore q Q)) :
                Sylow q (Q ⧸ pPrimeCore q Q)) : Subgroup (Q ⧸ pPrimeCore q Q)) :
                  Set (Q ⧸ pPrimeCore q Q)))) :
    (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
  classical
  let M : Subgroup Q := pPrimeCore q Q
  let π : Q →* Q ⧸ M := QuotientGroup.mk' M
  let Sbar : Sylow q (Q ⧸ M) := S.mapSurjective (f := π) (QuotientGroup.mk'_surjective M)
  have hπS_inj : Function.Injective (π.comp (S : Subgroup Q).subtype) := by
    simpa [π, M] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := Q) (p := q) (H := (S : Subgroup Q)) S.isPGroup'
  intro x hxS
  refine ⟨Subgroup.le_normalizer hxS, ?_⟩
  change x ∈ Subgroup.centralizer
    ((Subgroup.normalizer ((S : Subgroup Q) : Set Q)) : Set Q)
  rw [Subgroup.mem_centralizer_iff]
  intro n hnN
  have hπx_mem : π x ∈ (Sbar : Subgroup (Q ⧸ M)) := by
    simpa [Sbar, π, M, Sylow.coe_mapSurjective] using
      (Subgroup.mem_map_of_mem π hxS)
  have hπn_norm :
      π n ∈ Subgroup.normalizer ((Sbar : Subgroup (Q ⧸ M)) : Set (Q ⧸ M)) := by
    have : Fact (IsPGroup q (↥(S : Subgroup Q))) := ⟨S.isPGroup'⟩
    have hnorm :
        Subgroup.normalizer ((Sbar : Subgroup (Q ⧸ M)) : Set (Q ⧸ M)) =
          (Subgroup.normalizer (S : Subgroup Q)).map π := by
      have hmap :
          (Sbar : Subgroup (Q ⧸ M)) = (S : Subgroup Q).map π := by
        simp [Sbar, Sylow.coe_mapSurjective]
      simpa [π, M, hmap] using
        (normalizer_map_quotient_eq_map_normalizer
          (G := Q) (p := q) (T := (S : Subgroup Q)) (M := M)
          (inferInstance : M.Normal)
          (by simpa [M] using (pPrimeCore_coprime_card (G := Q) (p := q))))
    rw [hnorm]
    exact Subgroup.mem_map_of_mem π hnN
  have hπx_center := hquot hπx_mem
  have hcommπ : π n * π x = π x * π n :=
    Subgroup.mem_centralizer_iff.mp hπx_center.2 (π n) hπn_norm
  let c : S := ⟨n * x * n⁻¹ * x⁻¹, by
    have hconj : n * x * n⁻¹ ∈ (S : Subgroup Q) :=
      (Subgroup.mem_normalizer_iff.mp hnN x).1 hxS
    exact (S : Subgroup Q).mul_mem hconj ((S : Subgroup Q).inv_mem hxS)⟩
  have hcπ : (π.comp (S : Subgroup Q).subtype) c =
      (π.comp (S : Subgroup Q).subtype) 1 := by
    change π (n * x * n⁻¹ * x⁻¹) = 1
    calc
      π (n * x * n⁻¹ * x⁻¹)
          = π n * π x * (π n)⁻¹ * (π x)⁻¹ := by simp [π, map_mul, mul_assoc]
      _ = 1 := by
        rw [hcommπ]
        simp [mul_assoc]
  have hc_one : c = 1 := hπS_inj hcπ
  have hcomm_one : n * x * n⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hc_one
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (by simpa [commutatorElement_def] using hcomm_one)

public theorem hkt_quotient_pPrimeCore_nonburnside_of_nonburnside
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hnot_burnside :
      ¬ (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    ¬
      ((S.mapSurjective
        (f := QuotientGroup.mk' (pPrimeCore q Q))
        (QuotientGroup.mk'_surjective (pPrimeCore q Q)) :
          Sylow q (Q ⧸ pPrimeCore q Q)) : Subgroup (Q ⧸ pPrimeCore q Q)) ≤
        centerIn (G := Q ⧸ pPrimeCore q Q)
          (Subgroup.normalizer
            (((S.mapSurjective
              (f := QuotientGroup.mk' (pPrimeCore q Q))
              (QuotientGroup.mk'_surjective (pPrimeCore q Q)) :
                Sylow q (Q ⧸ pPrimeCore q Q)) : Subgroup (Q ⧸ pPrimeCore q Q)) :
                  Set (Q ⧸ pPrimeCore q Q))) := by
  intro hquot
  exact hnot_burnside (sylow_le_center_normalizer_of_quotient_pPrimeCore S hquot)
/-- If `p` does not divide the group order, the whole group is a normal
`p`-complement and the quotient is trivial. -/
public theorem hkt_hasNormalPComplement_of_not_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hnot : ¬ p ∣ Nat.card Q) : HasNormalPComplement p Q := by
  classical
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · simpa using (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot
  · have : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) :=
      QuotientGroup.subsingleton_quotient_top
    refine IsPGroup.of_card (p := p) (G := Q ⧸ (⊤ : Subgroup Q)) (n := 0) ?_
    simp

/--
Burnside's normal-complement endpoint in the precise form needed as the easy
branch of Thompson IV.6.2: if the Sylow subgroup already centralizes its
normalizer, then the desired normal `q`-complement follows without using the
Thompson local hypotheses.
-/
public theorem hkt_hasNormalPComplement_of_sylow_le_center_normalizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hS : (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    HasNormalPComplement q Q := by
  exact hasNormalPComplement_of_sylow_le_center_normalizer (G := Q) q S hS

/-- If a top subgroup has a normal `p`-complement, transport it to the ambient
group. -/
public theorem hkt_hasNormalPComplement_of_subgroup_eq_top
    {Q : Type u} [Group Q] {q : ℕ} (H : Subgroup Q)
    (hHtop : H = ⊤) (hH : HasNormalPComplement q H) :
    HasNormalPComplement q Q := by
  let e : H ≃* Q :=
    (MulEquiv.subgroupCongr hHtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  exact hasNormalPComplement_of_equiv (G := H) (p := q) e hH


/-- The transfer map to the focal quotient is already onto when restricted to a
Sylow subgroup: on the focal quotient the restriction is the `index`-power map,
and the Sylow index is prime to `q`. -/
public theorem hkt_transferFocal_restrict_surjective
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    Function.Surjective
      (((S : Subgroup Q).feitThompsonTransferFocal).domRestrict (S : Subgroup Q)) := by
  classical
  let H : Subgroup Q := S
  intro y
  have hquot_p : IsPGroup q (H ⧸ H.feitThompsonFocalSubgroupOf) := by
    simpa [H] using S.2.to_quotient ((S : Subgroup Q).feitThompsonFocalSubgroupOf)
  have hindex : ¬ q ∣ H.index := by
    simpa [H] using S.not_dvd_index
  obtain ⟨z, hz⟩ := (hquot_p.powEquiv' hindex).surjective y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective H.feitThompsonFocalSubgroupOf z
  refine ⟨s, ?_⟩
  rw [MonoidHom.domRestrict_apply, Subgroup.feitThompsonTransferFocal_eq_pow]
  exact hz


end External
end CFSG.BenderSuzuki
