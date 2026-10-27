module

public import CFSG.LieType.SteinbergBRGL2ThreeCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkL3
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Sporadic.Co1Patterson.GenerationCount
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

section GL23

open CFSG.LieType.SteinbergBR.GL2Three

theorem gl23_exists_sylow_two_card_sixteen : ∃ S : Sylow 2 G23, Nat.card S = 16 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card G23).factorization 2 = 4 := by
    rw [card_G23, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G23))
  exact ⟨S, by rw [Sylow.card_eq_multiplicity, hfac]; norm_num⟩

theorem gl23_nonempty_bar2_top_equiv_perm :
    Nonempty (Bar2 (⊤ : Subgroup G23) ≃* Equiv.Perm (Fin 3)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS16⟩ := gl23_exists_sylow_two_card_sixteen
  have hrel : (S : Subgroup G23).relIndex ⊤ = 3 := by
    rw [Subgroup.relIndex_top_right]
    have h := Subgroup.index_mul_card (S : Subgroup G23)
    rw [hS16, card_G23] at h
    omega
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup G23) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    have h3 : ((S : Subgroup G23).subgroupOf ⊤).index = 3 := hrel
    rw [h3]
    norm_num
  have hnotnormal : ¬ (⊤ : Subgroup G23) ≤ Subgroup.normalizer (S : Set G23) := by
    intro h
    have hSnorm : (S : Subgroup G23).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_unique h
    have hle : (S : Subgroup G23) ≤ CFSG.pCore 2 G23 :=
      CFSG.LieType.BorelTits.le_pCore 2 hSnorm S.isPGroup'
    rw [pCore_two_eq] at hle
    have hdvd : Nat.card ↥(S : Subgroup G23) ∣ Nat.card ↥quatQ := Subgroup.card_dvd_of_le hle
    rw [hS16, card_quatQ] at hdvd
    norm_num at hdvd
  exact CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hsyl hrel hnotnormal

theorem gl23_map_eq_neg_one_of_central {A : Type*} [Group A] (e : A ≃* G23) (z : A)
    (hzord : orderOf z = 2) (hcen : ∀ g : A, g * z = z * g) : e z = -1 := by
  have hcen' : ∀ g : G23, g * e z = e z * g := by
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hcen x]
  have hord : orderOf (e z) = 2 :=
    (orderOf_injective (e : A →* G23) e.injective z).trans hzord
  have hcenter : e z ∈ Subgroup.center G23 := Subgroup.mem_center_iff.mpr hcen'
  have hnormal : (Subgroup.zpowers (e z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ Subgroup.center G23 := (Subgroup.zpowers_le.2 hcenter) hn
    rw [Subgroup.mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn
  have hp : IsPGroup 2 (Subgroup.zpowers (e z)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hmem : e z ∈ CFSG.pCore 2 G23 :=
    CFSG.LieType.BorelTits.le_pCore 2 hnormal hp (Subgroup.mem_zpowers _)
  have hq : e z ∈ quatQ := by
    rwa [← pCore_two_eq]
  exact (mem_quatQ_orderOf hq).mp hord

theorem gl23_map_mem_pCore_eq_neg_one {A : Type*} [Group A] (e : A ≃* G23) {x : A}
    (hx : x ∈ CFSG.pCore 2 A) (hxord : orderOf x = 2) : e x = -1 := by
  have hord : orderOf (e x) = 2 :=
    (orderOf_injective (e : A →* G23) e.injective x).trans hxord
  have hmem : e x ∈ CFSG.pCore 2 G23 := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  have hq : e x ∈ quatQ := by
    rwa [← pCore_two_eq]
  exact (mem_quatQ_orderOf hq).mp hord

end GL23

variable {Q : Type} [Group Q] [Finite Q]

theorem centralizer_bar2_three {L : Subgroup Q} (hL : LieModel ↥L .PSL 3 3 1) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) :
    Nonempty (Bar2 (L ⊓ centralizer ({z} : Set Q)) ≃* Equiv.Perm (Fin 3)) ∧
      ∀ x ∈ pCoreOf 2 (L ⊓ centralizer ({z} : Set Q)), orderOf x = 2 → x = z := by
  classical
  set Y : Subgroup ↥L := Subgroup.centralizer ({⟨z, hzL⟩} : Set ↥L) with hYdef
  set X : Subgroup Q := L ⊓ Subgroup.centralizer ({z} : Set Q) with hXdef
  have hXY : X = Y.map L.subtype := by
    rw [hXdef, hYdef]
    exact (CFSG.Sporadic.Co1Patterson.map_centralizer_subtype L ⟨z, hzL⟩).symm
  have hzY : orderOf (⟨z, hzL⟩ : ↥L) = 2 := (Subgroup.orderOf_mk z hzL).trans hz2
  obtain ⟨e₀⟩ :=
    CFSG.OddStandard.SmallF3.Omega.nonempty_centralizer_equiv_gl2_of_lieModel_psl33 hL hzY
  let ee : ↥Y ≃* ↥(Y.map L.subtype) :=
    Subgroup.equivMapOfInjective Y L.subtype L.subtype_injective
  let e : ↥X ≃* CFSG.LieType.SteinbergBR.GL2Three.G23 :=
    ((MulEquiv.subgroupCongr hXY).trans ee.symm).trans e₀
  have hzX : z ∈ X := by
    rw [hXdef]
    exact ⟨hzL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let zX : ↥X := ⟨z, hzX⟩
  have hzXord : orderOf zX = 2 := (Subgroup.orderOf_mk z hzX).trans hz2
  have hzXcen : ∀ g : ↥X, g * zX = zX * g := by
    intro g
    refine Subtype.ext ?_
    have hg : (g : Q) ∈ L ⊓ Subgroup.centralizer ({z} : Set Q) := by
      rw [← hXdef]
      exact g.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have hwneg : e zX = -1 := gl23_map_eq_neg_one_of_central e zX hzXord hzXcen
  refine ⟨?_, ?_⟩
  · obtain ⟨e3⟩ := gl23_nonempty_bar2_top_equiv_perm
    let eX : ↥X ≃* ↥(⊤ : Subgroup CFSG.LieType.SteinbergBR.GL2Three.G23) :=
      e.trans Subgroup.topEquiv.symm
    exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥X)
      (CFSG.pCore 2 ↥(⊤ : Subgroup CFSG.LieType.SteinbergBR.GL2Three.G23)) eX
      (CFSG.pCore_map_iso 2 eX)).trans e3⟩
  · intro x hx hxord
    have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hx
    have hxc : (⟨x, hxX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
      have hx' : x ∈ (CFSG.pCore 2 ↥X).map X.subtype := hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
      have hyx : y = ⟨x, hxX⟩ := Subtype.ext hxy
      rwa [← hyx]
    have hxord' : orderOf (⟨x, hxX⟩ : ↥X) = 2 := (Subgroup.orderOf_mk x hxX).trans hxord
    have hxneg : e ⟨x, hxX⟩ = -1 := gl23_map_mem_pCore_eq_neg_one e hxc hxord'
    have hxz : (⟨x, hxX⟩ : ↥X) = zX := e.injective (hxneg.trans hwneg.symm)
    exact congrArg Subtype.val hxz

end CFSG.LocalAnalysis.WeakClosure81.FourEleven

