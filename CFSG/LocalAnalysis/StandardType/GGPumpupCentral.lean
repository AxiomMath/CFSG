module

public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.Assembly Subgroup

namespace GGPumpup

section Abstract

variable {H : Type*} [Group H]

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {x : H} (hx : x ^ p = 1) :
    IsPGroup p (zpowers x) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
  rw [SubgroupClass.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hx, one_zpow, OneMemClass.coe_one]

theorem centralizer_zpowers_eq (x : H) :
    centralizer ((zpowers x : Subgroup H) : Set H) = centralizer ({x} : Set H) := by
  rw [zpowers_eq_closure, centralizer_closure]

variable [Finite H] {p : ℕ} [Fact p.Prime]

theorem sup_pPrimeCore_eq_of_commutator_le {x : H} (hx : x ^ p = 1) {T A : Subgroup H}
    (hTC : T ≤ centralizer ({x} : Set H))
    (hT : IsPComponent p (T.subgroupOf (centralizer ({x} : Set H))))
    (hA : IsPComponent p A) (hTA : T ≤ A) (hxA : x ∈ normalizer (A : Set H))
    (hc : ⁅A, zpowers x⁆ ≤ (pPrimeCore p A).map A.subtype) :
    T ⊔ (pPrimeCore p A).map A.subtype = A := by
  obtain ⟨hcover, -, -, -, hT', -⟩ :=
    UnbalancedGS.trivial_quotient_action_fixed_layer_is_p_component p A hA.choose_spec.2.1
      (zpowers x) (zpowers_le.mpr hxA) (isPGroup_zpowers_of_pow_eq_one hx)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple p A hA) hc _ rfl _ rfl
  rw [centralizer_zpowers_eq] at hT' hcover
  set C := A ⊓ centralizer ({x} : Set H) with hCdef
  set T' := (pLayer C p).map C.subtype with hT'def
  have hCC : C ≤ centralizer ({x} : Set H) := inf_le_right
  have hTC' : T ≤ C := le_inf hTA hTC
  obtain ⟨hTsub, hTres, hTq⟩ := (pComponent_subgroupOf_iff p T _ hTC).mp hT
  have hTsubC : (T.subgroupOf C).IsSubnormal := by
    have h := hTsub.comap (Subgroup.inclusion hCC)
    have heq : (T.subgroupOf (centralizer ({x} : Set H))).comap (Subgroup.inclusion hCC) =
        T.subgroupOf C := by
      ext z
      simp only [mem_comap, mem_subgroupOf, coe_inclusion]
    rwa [heq] at h
  have hTCp : IsPComponent p (T.subgroupOf C) :=
    (pComponent_subgroupOf_iff p T C hTC').mpr ⟨hTsubC, hTres, hTq⟩
  have hTT' : T ≤ T' := by
    have h := map_mono (f := C.subtype) (show T.subgroupOf C ≤ pLayer C p from le_sSup hTCp)
    rwa [map_subgroupOf_eq_of_le hTC'] at h
  have hT'C : T' ≤ centralizer ({x} : Set H) := (map_subtype_le _).trans hCC
  have hsub : T.subgroupOf (centralizer ({x} : Set H)) ≤
      T'.subgroupOf (centralizer ({x} : Set H)) := fun z hz => hTT' hz
  have heq := eq_of_le p _ _ hT hT' hsub
  have hTeq : T = T' := by
    have h := congrArg (Subgroup.map (centralizer ({x} : Set H)).subtype) heq
    rwa [map_subgroupOf_eq_of_le hTC, map_subgroupOf_eq_of_le hT'C] at h
  rw [hTeq]
  exact hcover

end Abstract

section Relative

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem map_map_pPrimeCore_subgroupOf {Y A : Subgroup G} (hAY : A ≤ Y) :
    ((pPrimeCore p ↥(A.subgroupOf Y)).map (A.subgroupOf Y).subtype).map Y.subtype =
      LargeEvenPPrimeCoreOf p A := by
  set e := subgroupOfEquivOfLe hAY with hedef
  have hcomp : Y.subtype.comp (A.subgroupOf Y).subtype = A.subtype.comp e.toMonoidHom := by
    ext z
    rfl
  rw [map_map, hcomp, ← map_map, pPrimeCore_map_iso]
  rfl

theorem eq_sup_largeEvenPPrimeCoreOf_of_commutator_le {Y J A : Subgroup G} {x : G}
    (hxY : x ∈ Y) (hxp : x ^ p = 1)
    (hJ : CFSG.Open.lBalanceIsPComponent p (Y ⊓ centralizer ({x} : Set G)) J)
    (hA : CFSG.Open.lBalanceIsPComponent p Y A) (hJA : J ≤ A)
    (hxA : x ∈ normalizer (A : Set G)) (hc : ⁅A, zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A) :
    A = J ⊔ LargeEvenPPrimeCoreOf p A := by
  have hAY : A ≤ Y := LBalance.subnormal_le hA.1
  have hJY : J ≤ Y := (LBalance.subnormal_le hJ.1).trans inf_le_left
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx'p : x' ^ p = 1 := Subtype.ext (by simp [x', hxp])
  obtain ⟨hTC, hT⟩ := isPComponent_subgroupOf_centralizer hxY hJ
  have hA' : IsPComponent p (A.subgroupOf Y) :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y A hAY).mpr hA
  have hTA : J.subgroupOf Y ≤ A.subgroupOf Y := fun z hz => hJA hz
  have hxA' : x' ∈ normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [mem_normalizer_iff]
    intro h
    exact (mem_normalizer_iff.mp hxA h)
  have hc' : ⁅A.subgroupOf Y, zpowers x'⁆ ≤
      (pPrimeCore p ↥(A.subgroupOf Y)).map (A.subgroupOf Y).subtype := by
    refine (map_le_map_iff_of_injective Y.subtype_injective).mp ?_
    rw [map_commutator, map_subgroupOf_eq_of_le hAY, MonoidHom.map_zpowers,
      map_map_pPrimeCore_subgroupOf hAY]
    exact hc
  have h := sup_pPrimeCore_eq_of_commutator_le hx'p hTC hT hA' hTA hxA' hc'
  have h2 := congrArg (Subgroup.map Y.subtype) h
  rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hJY, map_subgroupOf_eq_of_le hAY,
    map_map_pPrimeCore_subgroupOf hAY, eq_comm] at h2

end Relative

end GGPumpup

section StdSub

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_or_eq_sup_of_stdSub (hPU : GGPumpupInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hD : D = Subgroup.closure {x, d}) :
    GGNbr p B x D J d (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) ∨
      ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J =
        J ⊔ LargeEvenPPrimeCoreOf p (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hK, hJK, hxK, hor⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
  rcases hor with h | h
  · exact Or.inl h
  · right
    have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
    obtain ⟨-, hxd, -, -⟩ := facts_of_closure_pair hI hDJ hD
    have hxY : x ∈ Subgroup.centralizer ({d} : Set G) := mem_centralizer_singleton_iff.mpr hxd
    exact GGPumpup.eq_sup_largeEvenPPrimeCoreOf_of_commutator_le hxY (hS.1.1.2 x hS.2.1)
      (GGPumpup.lBalanceIsPComponent_inf_of_pLayer
        (lBalanceIsPComponent_pLayer_of_stdSub hI hDJ hpJ hD))
      ((largeEvenPComponent_iff_lBalance p _ _).1 hK).2 hJK hxK h

end StdSub

end CFSG.StandardType

end
