module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
import Mathlib.GroupTheory.SchurZassenhaus

namespace CFSG
end CFSG
open CFSG

/-!
# Quotient permutation actions for Theorem SE

This file collects generic facts about quotienting a finite group by an odd
normal subgroup and about factoring a permutation action through its pointwise
kernel.
-/

namespace CFSG.BenderSuzuki

open PFchapter1section1

universe u v

/-- Quotienting a finite group of 2-rank at most one by an odd normal subgroup
preserves the 2-rank bound. -/
public theorem not_twoRankAtLeastTwo_quotient_of_odd
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (hG : ¬ TwoRankAtLeastTwo G) :
    ¬ TwoRankAtLeastTwo (G ⧸ N) := by
  classical
  intro hquot
  rcases hquot with ⟨E, hEcard, hEsq⟩
  let pi : G →* G ⧸ N := QuotientGroup.mk' N
  let M : Subgroup G := E.comap pi
  have hN_le_M : N ≤ M := by
    intro n hn
    change pi n ∈ E
    have hpi : pi n = 1 := by
      exact (QuotientGroup.eq_one_iff (N := N) n).2 hn
    simp [hpi]
  let NM : Subgroup M := N.subgroupOf M
  let phi : M →* E :=
    (pi.domRestrict M).codRestrict E (by
      intro m
      exact m.property)
  have hphi_surj : Function.Surjective phi := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : G ⧸ N)
    let m : M := ⟨g, by
      change pi g ∈ E
      rw [show pi g = e from hg]
      exact e.property⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change (pi g : G ⧸ N) = (e : G ⧸ N)
    exact hg
  have hphi_ker : phi.ker = NM := by
    ext m
    constructor
    · intro hm
      change (m : G) ∈ N
      apply (QuotientGroup.eq_one_iff (N := N) (m : G)).1
      have hm' : phi m = 1 := by
        simpa [MonoidHom.mem_ker] using hm
      exact congrArg Subtype.val hm'
    · intro hm
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change pi (m : G) = 1
      exact (QuotientGroup.eq_one_iff (N := N) (m : G)).2 hm
  haveI : NM.Normal := (inferInstance : N.Normal).subgroupOf M
  have hNMcard : Nat.card NM = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_M).toEquiv
  have hNModd : Odd (Nat.card NM) := hNMcard ▸ hNodd
  have hNMindex : NM.index = 4 := by
    calc
      NM.index = phi.ker.index := congrArg Subgroup.index hphi_ker.symm
      _ = Nat.card phi.range := Subgroup.index_ker phi
      _ = Nat.card E := by
        rw [phi.range_eq_top_of_surjective hphi_surj]
        simp
      _ = 4 := hEcard
  have hcoprime : Nat.Coprime (Nat.card NM) NM.index := by
    rw [hNMindex, show 4 = 2 ^ 2 by decide]
    exact hNModd.coprime_two_right.pow_right 2
  obtain ⟨K, hK⟩ := NM.exists_right_complement'_of_coprime hcoprime
  have hKcard : Nat.card K = 4 := by
    calc
      Nat.card K = NM.index := hK.symm.index_eq_card.symm
      _ = 4 := hNMindex
  have hKsq : ∀ x : K, (x : K) ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    let xM : M := x
    let e : E := ⟨pi (xM : G), xM.property⟩
    have he2 : e ^ 2 = 1 := hEsq e
    have hpi2 : pi ((xM : G) ^ 2) = 1 := by
      simpa [e, map_pow] using congrArg Subtype.val he2
    have hx2_NM : xM ^ 2 ∈ NM := by
      change (xM : G) ^ 2 ∈ N
      exact (QuotientGroup.eq_one_iff (N := N) ((xM : G) ^ 2)).1 hpi2
    have hx2_K : xM ^ 2 ∈ K := K.pow_mem x.property 2
    have hx2_bot : xM ^ 2 ∈ (⊥ : Subgroup M) := by
      rw [← hK.disjoint.eq_bot]
      exact ⟨hx2_NM, hx2_K⟩
    simpa [xM] using hx2_bot
  let KG : Subgroup G := K.map M.subtype
  have hKGcard : Nat.card KG = 4 := by
    calc
      Nat.card KG = Nat.card K :=
        Subgroup.card_map_of_injective (K := K) (f := M.subtype) M.subtype_injective
      _ = 4 := hKcard
  apply hG
  refine ⟨KG, hKGcard, ?_⟩
  rintro ⟨g, hg⟩
  rcases hg with ⟨m, hmK, rfl⟩
  apply Subtype.ext
  simpa using congrArg (fun z : K => ((z : M) : G)) (hKsq ⟨m, hmK⟩)

/-- The intersection of all point stabilizers is the kernel of the associated
permutation representation. -/
public theorem pointStabilizerCore_eq_ker
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] :
    pointStabilizerCore G Omega = (MulAction.toPermHom G Omega).ker := by
  ext g
  simp [pointStabilizerCore, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker,
    Equiv.Perm.ext_iff]

/-- The pointwise kernel of a group action is normal. -/
public theorem pointStabilizerCore_normal
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega] :
    (pointStabilizerCore G Omega).Normal := by
  rw [pointStabilizerCore_eq_ker]
  infer_instance

/-- The pointwise kernel lies in every point stabilizer. -/
public theorem pointStabilizerCore_le_stabilizer
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (omega : Omega) :
    pointStabilizerCore G Omega ≤ MulAction.stabilizer G omega := by
  intro g hg
  have hg_all : ∀ w : Omega, g ∈ MulAction.stabilizer G w := by
    simpa [pointStabilizerCore] using hg
  exact hg_all omega

/-- In particular, the pointwise kernel lies in the intersection of any two
point stabilizers. -/
public theorem pointStabilizerCore_le_inf_stabilizers
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (omega₁ omega₂ : Omega) :
    pointStabilizerCore G Omega ≤
      MulAction.stabilizer G omega₁ ⊓ MulAction.stabilizer G omega₂ :=
  le_inf (pointStabilizerCore_le_stabilizer omega₁)
    (pointStabilizerCore_le_stabilizer omega₂)

/-- The permutation representation induced on the quotient by the pointwise
kernel. -/
@[expose] public def pointStabilizerCoreQuotientPermHom
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [(pointStabilizerCore G Omega).Normal] :
    G ⧸ pointStabilizerCore G Omega →* Equiv.Perm Omega :=
  QuotientGroup.lift (pointStabilizerCore G Omega) (MulAction.toPermHom G Omega) (by
    intro g hg
    rw [← pointStabilizerCore_eq_ker]
    exact hg)

/-- The canonical action of the quotient by the pointwise kernel. -/
@[reducible, expose] public def pointStabilizerCoreQuotientAction
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [(pointStabilizerCore G Omega).Normal] :
    MulAction (G ⧸ pointStabilizerCore G Omega) Omega :=
  MulAction.compHom Omega pointStabilizerCoreQuotientPermHom

/-- The canonical quotient action agrees with the original action on quotient
representatives. -/
public theorem pointStabilizerCoreQuotientAction_mk_smul
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [(pointStabilizerCore G Omega).Normal] (g : G) (omega : Omega) :
    @SMul.smul (G ⧸ pointStabilizerCore G Omega) Omega
        pointStabilizerCoreQuotientAction.toSMul
        (QuotientGroup.mk g) omega =
      g • omega := by
  change pointStabilizerCoreQuotientPermHom
      (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Omega) omega = g • omega
  simp [pointStabilizerCoreQuotientPermHom, MulAction.toPermHom_apply]

/-- Double transitivity descends through the pointwise action kernel. -/
public theorem pointStabilizerCoreQuotientAction_twoPretransitive
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2) :
    letI : (pointStabilizerCore G Omega).Normal := pointStabilizerCore_normal
    letI : MulAction (G ⧸ pointStabilizerCore G Omega) Omega :=
      pointStabilizerCoreQuotientAction
    MulAction.IsMultiplyPretransitive
      (G ⧸ pointStabilizerCore G Omega) Omega 2 := by
  letI : (pointStabilizerCore G Omega).Normal := pointStabilizerCore_normal
  letI : MulAction (G ⧸ pointStabilizerCore G Omega) Omega :=
    pointStabilizerCoreQuotientAction
  rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
  intro a b c d hab hcd
  obtain ⟨g, hgac, hgbd⟩ := htwo hab hcd
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · exact (pointStabilizerCoreQuotientAction_mk_smul g a).trans hgac
  · exact (pointStabilizerCoreQuotientAction_mk_smul g b).trans hgbd

/-- Any quotient action by the pointwise kernel that agrees on representatives
is faithful. -/
public theorem faithfulSMul_quotient_pointStabilizerCore
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [(pointStabilizerCore G Omega).Normal]
    (quotientAction : MulAction (G ⧸ pointStabilizerCore G Omega) Omega)
    (hsmul : ∀ (g : G) (omega : Omega),
      @SMul.smul (G ⧸ pointStabilizerCore G Omega) Omega
        quotientAction.toSMul (QuotientGroup.mk g) omega = g • omega) :
    @FaithfulSMul (G ⧸ pointStabilizerCore G Omega) Omega
      quotientAction.toSMul := by
  letI : MulAction (G ⧸ pointStabilizerCore G Omega) Omega := quotientAction
  refine { eq_of_smul_eq_smul := ?_ }
  intro a b hab
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) a
  obtain ⟨h, rfl⟩ :=
    QuotientGroup.mk'_surjective (pointStabilizerCore G Omega) b
  apply QuotientGroup.eq_iff_div_mem.mpr
  change g / h ∈ pointStabilizerCore G Omega
  simp only [pointStabilizerCore, Subgroup.mem_iInf,
    MulAction.mem_stabilizer_iff]
  intro w
  calc
    (g / h) • w = g • (h⁻¹ • w) := by simp [div_eq_mul_inv, mul_smul]
    _ = (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Omega) •
        (h⁻¹ • w) := by exact (hsmul g (h⁻¹ • w)).symm
    _ = (QuotientGroup.mk h : G ⧸ pointStabilizerCore G Omega) •
        (h⁻¹ • w) := hab (h⁻¹ • w)
    _ = h • (h⁻¹ • w) := hsmul h (h⁻¹ • w)
    _ = w := by simp

/-- The canonical quotient action by the pointwise kernel is faithful. -/
public theorem faithfulSMul_pointStabilizerCoreQuotientAction
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [(pointStabilizerCore G Omega).Normal] :
    @FaithfulSMul (G ⧸ pointStabilizerCore G Omega) Omega
      pointStabilizerCoreQuotientAction.toSMul :=
  faithfulSMul_quotient_pointStabilizerCore
    pointStabilizerCoreQuotientAction
    pointStabilizerCoreQuotientAction_mk_smul

/-! ## Centralizers in quotients -/

/-- Orbit--stabilizer for the conjugation action, with the stabilizer written
as the ordinary element centralizer. -/
public theorem conjugacyOrbit_ncard_mul_centralizer_card
    {G : Type u} [Group G] [Finite G] (x : G) :
    (MulAction.orbit (ConjAct G) x).ncard *
        Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have h :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  rw [← Nat.card_coe_set_eq,
    Subgroup.nat_card_centralizer_nat_card_stabilizer]
  simpa only [Nat.card_eq_fintype_card, ConjAct.card] using h

/-- `[IG; 9.16]`: the centralizer of the image of an element in a quotient
has cardinality at most that of the original element centralizer. -/
public theorem ig916_quotient_centralizer_card_le
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (x : G) :
    Nat.card
        (Subgroup.centralizer
          ({QuotientGroup.mk' N x} : Set (G ⧸ N))) ≤
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let O : Set G := MulAction.orbit (ConjAct G) x
  let Obar : Set (G ⧸ N) :=
    MulAction.orbit (ConjAct (G ⧸ N)) (q x)
  have hOsubset : O ⊆ q ⁻¹' Obar := by
    intro y hy
    rw [ConjAct.mem_orbit_conjAct] at hy
    change q y ∈ MulAction.orbit (ConjAct (G ⧸ N)) (q x)
    rw [ConjAct.mem_orbit_conjAct]
    exact q.map_isConj hy
  have hOrbitLe : O.ncard ≤ Nat.card N * Obar.ncard := by
    calc
      O.ncard ≤ (q ⁻¹' Obar).ncard :=
        Set.ncard_le_ncard hOsubset
      _ = Nat.card N * Obar.ncard := by
        simpa [q] using QuotientGroup.card_preimage_mk N Obar
  have hGcard :
      O.ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) =
        Nat.card G := by
    simpa [O] using conjugacyOrbit_ncard_mul_centralizer_card x
  have hQcard :
      Obar.ncard *
          Nat.card
            (Subgroup.centralizer ({q x} : Set (G ⧸ N))) =
        Nat.card (G ⧸ N) := by
    simpa [Obar] using
      conjugacyOrbit_ncard_mul_centralizer_card (q x)
  have hCardEq :
      (Nat.card N * Obar.ncard) *
          Nat.card
            (Subgroup.centralizer ({q x} : Set (G ⧸ N))) =
        O.ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    calc
      (Nat.card N * Obar.ncard) *
          Nat.card
            (Subgroup.centralizer ({q x} : Set (G ⧸ N))) =
          Nat.card N *
            (Obar.ncard *
              Nat.card
                (Subgroup.centralizer ({q x} : Set (G ⧸ N)))) := by
            ac_rfl
      _ = Nat.card N * Nat.card (G ⧸ N) := by rw [hQcard]
      _ = Nat.card G := by
        rw [← N.index_eq_card]
        exact N.card_mul_index
      _ = O.ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) :=
        hGcard.symm
  have hMulLe :
      (Nat.card N * Obar.ncard) *
          Nat.card
            (Subgroup.centralizer ({q x} : Set (G ⧸ N))) ≤
        (Nat.card N * Obar.ncard) *
          Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    calc
      (Nat.card N * Obar.ncard) *
          Nat.card
            (Subgroup.centralizer ({q x} : Set (G ⧸ N))) =
          O.ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) :=
        hCardEq
      _ ≤ (Nat.card N * Obar.ncard) *
          Nat.card (Subgroup.centralizer ({x} : Set G)) :=
        Nat.mul_le_mul_right _ hOrbitLe
  have hObarPos : 0 < Obar.ncard := by
    rw [Set.ncard_pos]
    exact ⟨q x, MulAction.mem_orbit_self (q x)⟩
  have hFactorPos : 0 < Nat.card N * Obar.ncard :=
    Nat.mul_pos Nat.card_pos hObarPos
  simpa [q] using Nat.le_of_mul_le_mul_left hMulLe hFactorPos

end CFSG.BenderSuzuki
