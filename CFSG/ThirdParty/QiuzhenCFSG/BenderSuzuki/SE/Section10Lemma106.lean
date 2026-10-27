module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma105
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.6

This file freezes the source prime set and subgroup notation for Lemma 10.6,
and supplies the group-theoretic complement-extension glue used by its final
assembly.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFchapter1section1
open scoped Pointwise commutatorElement

universe u

/-- The set of primes `pi` from source Lemma 10.6. -/
@[expose] public def lemma106Pi
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E V t) : Set Nat.Primes :=
  {r | r.val ∣ Nat.card D ∧ r.val ≠ d.choice.p ∧
    ¬ r.val ∣ Nat.card (Subgroup.closure (peterfalviKSet D t))}

/-- The source subgroup `H = K[A,P]` from Lemma 10.6. -/
@[expose] public def lemma106H
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E V t) : Subgroup X :=
  Subgroup.closure (peterfalviKSet D t) ⊔
    ⁅d.choice.initial.A1, d.choice.P⁆

/-- The conclusions of source Lemma 10.6. -/
public structure Lemma106Conclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E V : Subgroup X) (t : X)
    (d : Lemma101Conclusion M W D E V t) : Prop where
  C_hall_D :
    IsHallSubgroup (lemma106Pi d) ((lemma104C d).subgroupOf D)
  centralizer_kernel_sup_A1 :
    subgroupCentralizerIn
        (Subgroup.closure (peterfalviKSet D t) ⊔ d.choice.initial.A1)
        d.choice.P =
      lemma104C d
  normal_complement :
    IsNormalComplementIn D (lemma104C d)
      (lemma106H d ⊔ d.choice.P)
  kernel_commutator_inf_V :
    lemma106H d ⊓ V = ⁅d.choice.initial.A1, d.choice.P⁆

/-- The normalizer factorization `N_D(P)=CP`, together with `N cap P=1`,
identifies the centralizer of `P` in `N` with `C`. -/
public theorem lemma106_subgroupCentralizerIn_eq_of_normalizer_factorization
    {X : Type*} [Group X]
    {D N C P : Subgroup X}
    (hNleD : N ≤ D) (hCleN : C ≤ N)
    (hNdisjP : Disjoint N P)
    (hfactor : (normalizerIn D P : Set X) =
      (C : Set X) * (P : Set X))
    (hCcentralP : C ≤ Subgroup.centralizer (P : Set X)) :
    subgroupCentralizerIn N P = C := by
  apply le_antisymm
  · intro x hx
    have hxnorm : x ∈ normalizerIn D P :=
      ⟨hNleD hx.1, centralizer_le_normalizer P hx.2⟩
    have hxfactor : x ∈ (C : Set X) * (P : Set X) := by
      rw [← hfactor]
      exact hxnorm
    rcases Set.mem_mul.mp hxfactor with ⟨c, hc, p, hp, hcp⟩
    have hpN : p ∈ N := by
      have hpEq : p = c⁻¹ * x := by
        calc
          p = c⁻¹ * (c * p) := by simp
          _ = c⁻¹ * x := by rw [hcp]
      rw [hpEq]
      exact N.mul_mem (N.inv_mem (hCleN hc)) hx.1
    have hpone : p = 1 :=
      (Subgroup.disjoint_def.mp hNdisjP (x := p)) hpN hp
    have hcx : c = x := by simpa [hpone] using hcp
    simpa [← hcx] using hc
  · intro x hx
    exact ⟨hCleN hx, hCcentralP hx⟩

/-- A normal complement `H` to `C` in `N` extends to the normal complement
`HP` in `D=N P` when `P` normalizes `H`, centralizes `C`, and is disjoint
from `N`. -/
public theorem lemma106_extend_normal_complement
    {X : Type*} [Group X]
    {D N C P H : Subgroup X}
    (hNleD : N ≤ D) (hPleD : P ≤ D)
    (hC : C ≤ N) (hH : H ≤ N)
    (hNsupP : N ⊔ P = D)
    (hPnormH : P ≤ Subgroup.normalizer (H : Set X))
    (hHnormalN : (H.subgroupOf N).Normal)
    (hCcentralP : C ≤ Subgroup.centralizer (P : Set X))
    (hcomp : IsNormalComplementIn N C H)
    (hNdisjP : Disjoint N P) :
    IsNormalComplementIn D C (H ⊔ P) := by
  let Q : Subgroup X := H ⊔ P
  have hQleD : Q ≤ D := sup_le (hH.trans hNleD) hPleD
  have hCnormalH : C ≤ Subgroup.normalizer (H : Set X) := by
    intro c hc
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hH).mp hHnormalN
      (hC hc)
  have hCnormalQ : C ≤ Subgroup.normalizer (Q : Set X) := by
    intro c hc
    apply mem_normalizer_sup_of_mem_normalizers
    · exact hCnormalH hc
    · exact centralizer_le_normalizer P (hCcentralP hc)
  have hDsupC : Q ⊔ C = D := by
    calc
      Q ⊔ C = (H ⊔ C) ⊔ P := by
        simp [Q, sup_left_comm, sup_comm]
      _ = N ⊔ P := by rw [hcomp.sup_eq]
      _ = D := hNsupP
  have hQnormalD : (Q.subgroupOf D).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQleD).mpr
    rw [← hDsupC]
    exact sup_le Subgroup.le_normalizer hCnormalQ
  have hdisjQ : Disjoint Q C := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxC
    have hxQ' : x ∈ (H : Set X) * (P : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H P hPnormH]
      exact hxQ
    rcases Set.mem_mul.mp hxQ' with ⟨h, hh, p, hp, hhp⟩
    have hpN : p ∈ N := by
      have hpEq : p = h⁻¹ * x := by
        calc
          p = h⁻¹ * (h * p) := by simp
          _ = h⁻¹ * x := by rw [hhp]
      rw [hpEq]
      exact N.mul_mem (N.inv_mem (hH hh)) (hC hxC)
    have hpone : (p : X) = 1 :=
      Subgroup.disjoint_def.mp hNdisjP hpN hp
    have hxeq : (h : X) = x := by simpa [hpone] using hhp
    have hhC : (h : X) ∈ C := by rw [hxeq]; exact hxC
    calc
      x = h := hxeq.symm
      _ = 1 :=
        (Subgroup.disjoint_def.mp hcomp.disjoint_D (x := h)) hh hhC
  exact {
    le_M := hQleD
    normal_in_M := hQnormalD
    sup_eq := hDsupC
    disjoint_D := hdisjQ }

/-- If the fixed-point subgroup for a coprime action is a Hall `pi`-subgroup,
then the action commutator is an invariant normal Hall `pi'`-complement.
This is the checked coprime-action content of source `(10F)`. -/
public theorem lemma106_hall_complement_action
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    (pi : Set Nat.Primes) (C : Subgroup G)
    (hHallC : IsHallSubgroup pi C)
    (hCfix : fixedPointSubgroup A G = C) :
    ∃ S : Subgroup G,
      IsHallSubgroup {p | p ∉ pi} S ∧
      IsInvariant A G S ∧
      S.IsComplement' C ∧
      S.Normal ∧
      commutatorAction (A := A) (G := G) = S := by
  classical
  letI : Group.IsSolvable G := hsolv
  obtain ⟨S, hHallS, hSinv⟩ :=
    exists_isHallSubgroup_isInvariant (G := G) (A := A) hsolv hcop
      {p | p ∉ pi}
  have hcopCards : Nat.Coprime (Nat.card S) (Nat.card C) := by
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqS hqC
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hqnot : q' ∉ pi :=
      hHallS.p_in_pi_of_p_dvd_card q' hqS
    have hqyes : q' ∈ pi := hHallC.p_in_pi_of_p_dvd_card q' hqC
    exact hqnot hqyes
  have hcopIndices : Nat.Coprime S.index C.index := by
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqS hqC
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hqmem : q' ∈ pi := by
      have hqnot : q' ∉ {p : Nat.Primes | p ∉ pi} :=
        hHallS.p_in_pi_of_p_dvd_index q' hqS
      exact by_contra fun hn => hqnot hn
    have hqnotmem : q' ∉ pi :=
      hHallC.p_in_pi_of_p_dvd_index q' hqC
    exact hqnotmem hqmem
  have hcardS_dvd_Cindex : Nat.card S ∣ C.index := by
    have hdiv : Nat.card S ∣ C.index * Nat.card C := by
      simpa [Subgroup.index_mul_card] using
        (Subgroup.card_subgroup_dvd_card S)
    exact hcopCards.dvd_of_dvd_mul_right hdiv
  have hCindex_dvd_Scard : C.index ∣ Nat.card S := by
    have hdiv : C.index ∣ Nat.card S * S.index := by
      simpa [Subgroup.card_mul_index] using
        (Subgroup.index_dvd_card (H := C))
    exact hcopIndices.symm.dvd_of_dvd_mul_right hdiv
  have hcardS_eq_Cindex : Nat.card S = C.index :=
    Nat.dvd_antisymm hcardS_dvd_Cindex hCindex_dvd_Scard
  have hcard_mul : Nat.card S * Nat.card C = Nat.card G := by
    calc
      Nat.card S * Nat.card C = C.index * Nat.card C := by
        rw [hcardS_eq_Cindex]
      _ = Nat.card G := Subgroup.index_mul_card (H := C)
  have hcompSC : S.IsComplement' C :=
    Subgroup.isComplement'_of_coprime hcard_mul hcopCards
  have hCfixS : fixedPointSubgroup A S = ⊥ := by
    have hCfixSmap :
        (fixedPointSubgroup A S).map S.subtype =
          S ⊓ fixedPointSubgroup A G := by
      simpa using fixedPointSubgroup_map_subtype_eq_inf S
    have hInf : S ⊓ fixedPointSubgroup A G = ⊥ := by
      rw [hCfix, ← hcompSC.disjoint.eq_bot]
    apply (Subgroup.map_subtype_inj (H := S)).mp
    calc
      (fixedPointSubgroup A S).map S.subtype =
          S ⊓ fixedPointSubgroup A G := hCfixSmap
      _ = ⊥ := hInf
      _ = (⊥ : Subgroup S).map S.subtype := by simp
  have hcopS : Nat.Coprime (Nat.card A) (Nat.card S) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card S) hcop
  letI : IsInvariant A G S := hSinv
  have hsupS :
      fixedPointSubgroup A S ⊔ commutatorAction (A := A) (G := S) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (by infer_instance : Group.IsSolvable S) hcopS
  have hcommS : commutatorAction (A := A) (G := S) = ⊤ := by
    rw [hCfixS] at hsupS
    simpa using hsupS
  have hcomm_le_S : commutatorAction (A := A) (G := G) ≤ S := by
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    refine (Subgroup.closure_le (K := S)).2 ?_
    intro x hx
    rcases hx with ⟨a, g, rfl⟩
    rcases (hcompSC.symm.existsUnique g).exists with
      ⟨⟨⟨c, hc⟩, ⟨s, hs⟩⟩, hcs⟩
    have hcfixed : a • c = c := by
      exact (FixedPoints.mem_subgroup (M := A) (a := (c : G))).1
        (by simpa [hCfix] using hc) a
    have hscS : s⁻¹ * (a • s) ∈ S := by
      have has : a • (s : G) ∈ S := (hSinv.invariant a s).1 hs
      exact S.mul_mem (S.inv_mem hs) has
    rw [← hcs]
    simpa [smul_mul', hcfixed, mul_assoc] using hscS
  have hcomm_ge_S : S ≤ commutatorAction (A := A) (G := G) := by
    have hmap_le :
        (commutatorAction (A := A) (G := S)).map S.subtype ≤
          commutatorAction (A := A) (G := G) := by
      rw [commutatorAction_eq_closure (G := S) (A := A),
        MonoidHom.map_closure]
      refine (Subgroup.closure_le
        (K := commutatorAction (A := A) (G := G))).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with ⟨a, g, rfl⟩
      rw [commutatorAction_eq_closure (G := G) (A := A)]
      refine Subgroup.subset_closure ?_
      exact ⟨a, (g : G), by rfl⟩
    have htopmap :
        (commutatorAction (A := A) (G := S)).map S.subtype = S := by
      rw [hcommS]
      ext x
      simp
    rw [← htopmap]
    exact hmap_le
  have hcommEq : commutatorAction (A := A) (G := G) = S :=
    le_antisymm hcomm_le_S hcomm_ge_S
  have hSnormal : S.Normal := by
    rw [← hcommEq]
    exact commutatorAction_normal
  exact ⟨S, hHallS, hSinv, hcompSC, hSnormal, hcommEq⟩

/-- Map a normal complement in the subtype group `N` back to the ambient
group, retaining the `IsNormalComplementIn` packaging used in Sections
9--11. -/
public theorem lemma106_map_normal_complement
    {X : Type*} [Group X] {N C : Subgroup X}
    (hC : C ≤ N) (S : Subgroup N)
    (hSnormal : S.Normal)
    (hcomp : S.IsComplement' (C.subgroupOf N)) :
    IsNormalComplementIn N C (S.map N.subtype) := by
  let H : Subgroup X := S.map N.subtype
  have hHle : H ≤ N := Subgroup.map_subtype_le S
  have hHsub : H.subgroupOf N = S := by
    apply (Subgroup.map_subtype_inj (H := N)).mp
    calc
      (H.subgroupOf N).map N.subtype = H := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHle]
      _ = S.map N.subtype := rfl
  have hHnormal : (H.subgroupOf N).Normal := by
    rw [hHsub]
    exact hSnormal
  have hsup : H ⊔ C = N := by
    calc
      H ⊔ C = (S ⊔ C.subgroupOf N).map N.subtype := by
        rw [Subgroup.map_sup]
        simp [H, hC]
      _ = (⊤ : Subgroup N).map N.subtype := by rw [hcomp.sup_eq_top]
      _ = N := by
        ext x
        simp
  have hdisj : Disjoint H C := by
    rw [Subgroup.disjoint_def]
    intro x hxH hxC
    rcases Subgroup.mem_map.mp hxH with ⟨s, hs, rfl⟩
    have hsC : s ∈ C.subgroupOf N := hxC
    exact congrArg Subtype.val
      (Subgroup.disjoint_def.mp hcomp.disjoint hs hsC)
  exact {
    le_M := hHle
    normal_in_M := hHnormal
    sup_eq := hsup
    disjoint_D := hdisj }

/-- A Hall subgroup remains Hall after restricting the ambient group from
`D` to an intermediate subgroup `N`. -/
public theorem lemma106_hall_subgroupOf_between
    {X : Type*} [Group X]
    {C N D : Subgroup X} {pi : Set Nat.Primes}
    (hCN : C ≤ N) (hND : N ≤ D)
    (hHallD : IsHallSubgroup pi (C.subgroupOf D)) :
    IsHallSubgroup pi (C.subgroupOf N) := by
  let ND : Subgroup D := N.subgroupOf D
  have hCD : C ≤ D := hCN.trans hND
  have hCsub_le_Nsub : C.subgroupOf D ≤ ND := by
    intro x hx
    exact hCN hx
  refine isHallSubgroup_of (G := N) (π := pi) (H := C.subgroupOf N) ?_ ?_
  · intro p hp
    apply hHallD.p_in_pi_of_p_dvd_card p
    simpa [natCard_subgroupOf_eq C N hCN,
      natCard_subgroupOf_eq C D hCD] using hp
  · intro p hpπ hpidx
    have hrel_eq :
        (C.subgroupOf N).index = (C.subgroupOf D).relIndex ND := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := C) (K := N) (L := D) hND
      simpa [ND, Subgroup.relIndex] using hsub.symm
    have hidx_dvd : (C.subgroupOf N).index ∣ (C.subgroupOf D).index := by
      have hrel_dvd :
          (C.subgroupOf D).relIndex ND ∣ (C.subgroupOf D).index :=
        Subgroup.relIndex_dvd_index_of_le hCsub_le_Nsub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallD.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

/-- The source commutator calculation
`[K A, P] = K [A, P]` when `P` normalizes `K` and `[K, P] = K`. -/
public theorem lemma106_commutator_sup_eq
    {X : Type*} [Group X] {K A P : Subgroup X}
    (hAnormK : A ≤ Subgroup.normalizer (K : Set X))
    (hPnormK : P ≤ Subgroup.normalizer (K : Set X))
    (hKcomm : ⁅K, P⁆ = K) :
    ⁅K ⊔ A, P⁆ = K ⊔ ⁅A, P⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx p hp
    have hxprod : x ∈ (K : Set X) * (A : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K A hAnormK]
      exact hx
    rcases Set.mem_mul.mp hxprod with ⟨k, hk, a, ha, hka⟩
    have hAP : ⁅a, p⁆ ∈ ⁅A, P⁆ :=
      Subgroup.commutator_mem_commutator ha hp
    have hKP : ⁅k, p⁆ ∈ K := by
      have hconj : p * k⁻¹ * p⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPnormK hp) k⁻¹).1
          (K.inv_mem hk)
      simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hconj
    have hkH : k ∈ K ⊔ ⁅A, P⁆ :=
      (show K ≤ K ⊔ ⁅A, P⁆ from le_sup_left) hk
    have hAPH : ⁅a, p⁆ ∈ K ⊔ ⁅A, P⁆ :=
      (show ⁅A, P⁆ ≤ K ⊔ ⁅A, P⁆ from le_sup_right) hAP
    have hkinvH : k⁻¹ ∈ K ⊔ ⁅A, P⁆ :=
      (show K ≤ K ⊔ ⁅A, P⁆ from le_sup_left) (K.inv_mem hk)
    have hKPH : ⁅k, p⁆ ∈ K ⊔ ⁅A, P⁆ :=
      (show K ≤ K ⊔ ⁅A, P⁆ from le_sup_left) hKP
    have hfirst : k * ⁅a, p⁆ ∈ K ⊔ ⁅A, P⁆ :=
      (K ⊔ ⁅A, P⁆).mul_mem hkH hAPH
    have hsecond : k * ⁅a, p⁆ * k⁻¹ ∈ K ⊔ ⁅A, P⁆ :=
      (K ⊔ ⁅A, P⁆).mul_mem hfirst hkinvH
    rw [← hka, commutator_mul_left]
    exact (K ⊔ ⁅A, P⁆).mul_mem hsecond hKPH
  · have hKcomm_le : ⁅K, P⁆ ≤ ⁅K ⊔ A, P⁆ :=
      Subgroup.commutator_mono
        (show K ≤ K ⊔ A from le_sup_left)
        (show P ≤ P from le_rfl)
    have hKle : K ≤ ⁅K ⊔ A, P⁆ := by
      calc
        K = ⁅K, P⁆ := hKcomm.symm
        _ ≤ ⁅K ⊔ A, P⁆ := hKcomm_le
    have hAle : ⁅A, P⁆ ≤ ⁅K ⊔ A, P⁆ :=
      Subgroup.commutator_mono
        (show A ≤ K ⊔ A from le_sup_right)
        (show P ≤ P from le_rfl)
    exact sup_le hKle hAle

/-- A solvable coprime action with trivial fixed subgroup makes the whole
acted-on subgroup equal to its action commutator. -/
public theorem lemma106_eq_commutator_of_coprime_fixedPointFree
    {X : Type*} [Group X] [Finite X]
    (R P : Subgroup X)
    (hPnormR : P ≤ Subgroup.normalizer (R : Set X))
    (hsolvR : Group.IsSolvable R)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card R))
    (hcentral : subgroupCentralizerIn R P = ⊥) :
    R = ⁅R, P⁆ := by
  letI : Subgroup.Normalizes P R := ⟨hPnormR⟩
  let Cfix : Subgroup R := fixedPointSubgroup P R
  let Ccomm : Subgroup R := commutatorAction (A := P) (G := R)
  have hfix : Cfix = ⊥ := by
    simpa [Cfix, hcentral] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        R P hPnormR
  have hsup : Cfix ⊔ Ccomm = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      hsolvR hcop
  have hcomm : Ccomm = ⊤ := by
    rw [hfix] at hsup
    simpa [Ccomm] using hsup
  have hmap : Ccomm.map R.subtype = ⁅R, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator R P hPnormR
  calc
    R = (⊤ : Subgroup R).map R.subtype := by
      ext x
      simp
    _ = Ccomm.map R.subtype := by rw [hcomm]
    _ = ⁅R, P⁆ := hmap

/-- If `V = A P`, `P` normalizes `A`, and `P` is abelian, then
`[V,P]=[A,P]`. -/
public theorem lemma106_commutator_sup_right_eq
    {X : Type*} [Group X]
    {A P V : Subgroup X}
    (hVeq : V = A ⊔ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set X))
    (hPcomm : P ≤ Subgroup.centralizer (P : Set X)) :
    ⁅V, P⁆ = ⁅A, P⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx p hp
    have hxprod : x ∈ (A : Set X) * (P : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A P hPnormA]
      rw [← hVeq]
      exact hx
    rcases Set.mem_mul.mp hxprod with ⟨a, ha, s, hs, has⟩
    rw [← has, commutator_mul_left]
    have hsp : ⁅s, p⁆ = 1 := by
      have hps : p * s = s * p :=
        Subgroup.mem_centralizer_iff.mp (hPcomm hs) p hp
      exact commutatorElement_eq_one_iff_commute.mpr hps.symm
    simp [hsp]
    exact Subgroup.commutator_mem_commutator ha hp
  · exact Subgroup.commutator_mono
      (by rw [hVeq]; exact le_sup_left) le_rfl

end CFSG.BenderSuzuki
