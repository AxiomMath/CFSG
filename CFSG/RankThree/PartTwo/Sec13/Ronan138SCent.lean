module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem cent_mem_zpowers_e_of_comm {E K T : Subgroup G} {e r a : G}
    (hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hrN : r ∈ Subgroup.normalizer (E : Set G)) (hrC : r ∈ Sec4.thetaQuotCentralizer K)
    (haE : a ∈ E) (haT : a ∈ T) : r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers e := by
  have hx : r * a * r⁻¹ * a⁻¹ ∈ E :=
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hrN a).mp haE) (E.inv_mem haE)
  have h1 : a * r⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer K :=
    CFSG.RankThree.PartTwo.Sec6.conj_mem_thetaQuotCentralizer
      ((Sec4.thetaQuotCentralizer K).inv_mem hrC) (hTK haT)
  have hxC : r * a * r⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
    have e' : r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) := by group
    rw [e']
    exact (Sec4.thetaQuotCentralizer K).mul_mem hrC h1
  exact hCK _ hx hxC

private theorem cent_comm_of_normalizes {E K L T : Subgroup G} {c e r : G}
    (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L))
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hLH : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G))
    (he3 : e ^ 3 = 1) (heL : e ∉ L)
    (hce : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥)
    (hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hET : E ≤ T)
    (hrN : r ∈ Subgroup.normalizer (E : Set G)) (hrC : r ∈ Sec4.thetaQuotCentralizer K) :
    ∀ x ∈ E, r * x = x * r := by
  have hrZ : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hU hrN
  have hrL : r ∈ Subgroup.normalizer (L : Set G) := hLH hrZ
  have hcE : c ∈ E := by
    rw [hEdec]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hrc : r * c = c * r := by
    have hx1 := cent_mem_zpowers_e_of_comm hCK hTK hrN hrC hcE (hET hcE)
    have hx2 : r * c * r⁻¹ * c⁻¹ ∈ Subgroup.zpowers c := by
      have h1 : r * c * r⁻¹ ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff.mp hrZ c).mp (Subgroup.mem_zpowers c)
      exact (Subgroup.zpowers c).mul_mem h1
        ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c))
    have hmem : r * c * r⁻¹ * c⁻¹ ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers e :=
      Subgroup.mem_inf.mpr ⟨hx2, hx1⟩
    rw [hce, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)
  have hcommL : ∀ x ∈ E ⊓ L, r * x = x * r := by
    intro x hx
    obtain ⟨hxE, hxL⟩ := Subgroup.mem_inf.mp hx
    have hx1 := cent_mem_zpowers_e_of_comm hCK hTK hrN hrC hxE (hET hxE)
    have hx2 : r * x * r⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hrL x).mp hxL) (L.inv_mem hxL)
    have hmem : r * x * r⁻¹ * x⁻¹ ∈ Subgroup.zpowers e ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [CFSG.RankThree.PartTwo.Sec13.zpowers_inf_eq_bot he3 heL, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hmem)
  have hcent : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ Subgroup.centralizer ({r} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hrc.symm)) ?_
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommL x hx).symm
  rw [← hEdec] at hcent
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent hx)).symm

private theorem cent_mem_of_normalizes {E K L T : Subgroup G} {c e r : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L))
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hLH : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G))
    (he3 : e ^ 3 = 1) (heL : e ∉ L)
    (hce : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥)
    (hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e)
    (hCL : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c)
    (hLstep : ∀ r : G, r ∈ Subgroup.normalizer (L : Set G) → (∀ a ∈ E, r * a = a * r) →
      (∃ k : ℕ, r ^ 3 ^ k = 1) → ∃ β ∈ E ⊓ L, β⁻¹ * r ∈ Sec4.thetaQuotCentralizer L)
    (hT : IsPGroup 3 T) (hET : E ≤ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hrT : r ∈ T) (hrC : r ∈ Sec4.thetaQuotCentralizer K)
    (hrN : r ∈ Subgroup.normalizer (E : Set G)) : r ∈ E := by
  classical
  by_contra hrE
  have hcomm : ∀ x ∈ E, r * x = x * r :=
    cent_comm_of_normalizes hEdec hU hLH he3 heL hce hCK hTK hET hrN hrC
  have hex : ∃ k : ℕ, r ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT ⟨r, hrT⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, r ^ 3 ^ n = 1 ∧ ∀ j < n, r ^ 3 ^ j ≠ 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hrE
    have h1 : r = 1 := by simpa using hn
    rw [h1]
    exact E.one_mem
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hu1 : r ^ 3 ^ m ≠ 1 := hmin m (by omega)
  have hu3 : (r ^ 3 ^ m) ^ 3 = 1 := by
    rw [← pow_mul, ← Nat.pow_succ]
    exact hn
  have hcommu : ∀ x ∈ E, x * r ^ 3 ^ m = r ^ 3 ^ m * x := fun x hx =>
    ((show Commute r x from hcomm x hx).pow_left (3 ^ m)).symm
  have hEu : CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers (r ^ 3 ^ m)) :=
    CFSG.RankThree.PartTwo.Sec15.isElemAbelian_sup_zpowers hE hu3 hcommu
  have hsup : E ⊔ Subgroup.zpowers (r ^ 3 ^ m) = E := hEmax _ hEu le_sup_left
  have huE : r ^ 3 ^ m ∈ E := by
    have h : r ^ 3 ^ m ∈ E ⊔ Subgroup.zpowers (r ^ 3 ^ m) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [hsup] at h
  have huC : r ^ 3 ^ m ∈ Sec4.thetaQuotCentralizer K :=
    (Sec4.thetaQuotCentralizer K).pow_mem hrC _
  have huZe : r ^ 3 ^ m ∈ Subgroup.zpowers e := hCK _ huE huC
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    apply hrE
    simpa using huE
  · have hrL : r ∈ Subgroup.normalizer (L : Set G) := hLH (hU hrN)
    obtain ⟨β, hβ, hβC⟩ := hLstep r hrL hcomm hex
    obtain ⟨hβE, hβL⟩ := Subgroup.mem_inf.mp hβ
    have hβ3 : β ^ 3 = 1 := hE.2 β hβE
    have hβr : Commute β r := (hcomm β hβE).symm
    have hβr' : Commute β (β⁻¹ * r) := by
      show β * (β⁻¹ * r) = β⁻¹ * r * β
      rw [mul_inv_cancel_left, mul_assoc, ← hβr.eq, inv_mul_cancel_left]
    have hpow : β ^ 3 ^ m = 1 := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have h3 : (3 : ℕ) ^ m = 3 * 3 ^ j := by rw [hj]; ring
      rw [h3, pow_mul, hβ3, one_pow]
    have hu_eq : r ^ 3 ^ m = (β⁻¹ * r) ^ 3 ^ m := by
      calc r ^ 3 ^ m = (β * (β⁻¹ * r)) ^ 3 ^ m := by rw [mul_inv_cancel_left]
        _ = β ^ 3 ^ m * (β⁻¹ * r) ^ 3 ^ m := hβr'.mul_pow _
        _ = (β⁻¹ * r) ^ 3 ^ m := by rw [hpow, one_mul]
    have huL : r ^ 3 ^ m ∈ Sec4.thetaQuotCentralizer L := by
      rw [hu_eq]
      exact (Sec4.thetaQuotCentralizer L).pow_mem hβC _
    have huZc : r ^ 3 ^ m ∈ Subgroup.zpowers c := hCL _ huE huL
    have hmem : r ^ 3 ^ m ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers e :=
      Subgroup.mem_inf.mpr ⟨huZc, huZe⟩
    rw [hce, Subgroup.mem_bot] at hmem
    exact hu1 hmem

theorem mem_zpowers_of_mem_thetaQuotCentralizer {E K L T : Subgroup G} {c e : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L))
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hLH : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) (heL : e ∉ L)
    (hce : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥)
    (hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e)
    (hCL : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c)
    (hLstep : ∀ r : G, r ∈ Subgroup.normalizer (L : Set G) → (∀ a ∈ E, r * a = a * r) →
      (∃ k : ℕ, r ^ 3 ^ k = 1) → ∃ β ∈ E ⊓ L, β⁻¹ * r ∈ Sec4.thetaQuotCentralizer L)
    (hT : IsPGroup 3 T) (hET : E ≤ T) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e := by
  obtain ⟨R, hR⟩ : ∃ R : Subgroup G, R = T ⊓ Sec4.thetaQuotCentralizer K := ⟨_, rfl⟩
  have hRmem : ∀ x, x ∈ R ↔ x ∈ T ∧ x ∈ Sec4.thetaQuotCentralizer K := fun x => by
    rw [hR]
    exact Subgroup.mem_inf
  have hRconj : ∀ a ∈ T, ∀ x ∈ R, a * x * a⁻¹ ∈ R := by
    intro a ha x hx
    obtain ⟨hxT, hxC⟩ := (hRmem x).mp hx
    exact (hRmem _).mpr ⟨T.mul_mem (T.mul_mem ha hxT) (T.inv_mem ha),
      CFSG.RankThree.PartTwo.Sec6.conj_mem_thetaQuotCentralizer hxC (hTK ha)⟩
  have hER : E ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hRconj a (hET ha) x hx
    · intro hx
      have h1 := hRconj a⁻¹ (T.inv_mem (hET ha)) (a * x * a⁻¹) hx
      have e' : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
      rw [e'] at h1
      exact h1
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = E ⊔ R := ⟨_, rfl⟩
  have hXset : (X : Set G) = (E : Set G) * (R : Set G) := by
    rw [hX]
    exact Subgroup.coe_mul_of_left_le_normalizer_right E R hER
  have hXT : X ≤ T := by
    rw [hX]
    exact sup_le hET (fun x hx => ((hRmem x).mp hx).1)
  have hXp : IsPGroup 3 X := by
    intro g
    obtain ⟨k, hk⟩ := hT ⟨(g : G), hXT g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥X := IsPGroup.isNilpotent hXp
  have hRE : ∀ r ∈ R, r ∈ E := by
    intro r0 hr0
    by_contra hr0E
    have hr0X : r0 ∈ X := by
      rw [hX]
      exact Subgroup.mem_sup_right hr0
    have hHtop : E.subgroupOf X < ⊤ := by
      refine lt_top_iff_ne_top.mpr (fun h => hr0E ?_)
      have hmem : (⟨r0, hr0X⟩ : X) ∈ E.subgroupOf X := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hlt : E.subgroupOf X < Subgroup.normalizer ((E.subgroupOf X : Subgroup X) : Set X) :=
      Group.normalizerCondition_of_isNilpotent (G := ↥X) (E.subgroupOf X) hHtop
    obtain ⟨y, hyN, hyH⟩ :
        ∃ y ∈ Subgroup.normalizer ((E.subgroupOf X : Subgroup X) : Set X), y ∉ E.subgroupOf X :=
      SetLike.not_le_iff_exists.mp (fun h => lt_irrefl _ (lt_of_lt_of_le hlt h))
    have hyE : (y : G) ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hgX : g ∈ X := by
          rw [hX]
          exact Subgroup.mem_sup_left hg
        have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨g, hgX⟩).mp
          (Subgroup.mem_subgroupOf.mpr hg)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hg
        have hgX : g ∈ X := by
          have hc : (y : G) * g * (y : G)⁻¹ ∈ X := by
            have h' : (y : G) * g * (y : G)⁻¹ ∈ E ⊔ R := Subgroup.mem_sup_left hg
            rwa [← hX] at h'
          have h1 : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) ∈ X :=
            X.mul_mem (X.mul_mem (X.inv_mem y.2) hc) y.2
          have e' : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) = g := by group
          rw [e'] at h1
          exact h1
        have h2 := (Subgroup.mem_normalizer_iff.mp hyN ⟨g, hgX⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hg)
        exact Subgroup.mem_subgroupOf.mp h2
    have hyX : (y : G) ∈ (E : Set G) * (R : Set G) := by
      rw [← hXset]
      exact y.2
    obtain ⟨a, haE, r, hrR, hay⟩ := Set.mem_mul.mp hyX
    have haE' : a ∈ E := haE
    have hrR' : r ∈ R := hrR
    have hrN : r ∈ Subgroup.normalizer (E : Set G) := by
      have hr_eq : r = a⁻¹ * (y : G) := by
        rw [← hay, inv_mul_cancel_left]
      rw [hr_eq]
      exact (Subgroup.normalizer (E : Set G)).mul_mem
        ((Subgroup.normalizer (E : Set G)).inv_mem (Subgroup.le_normalizer haE')) hyE
    have hrE : r ∉ E := by
      intro hrE
      apply hyH
      apply Subgroup.mem_subgroupOf.mpr
      rw [← hay]
      exact E.mul_mem haE' hrE
    have hrT : r ∈ T := ((hRmem r).mp hrR').1
    have hrC : r ∈ Sec4.thetaQuotCentralizer K := ((hRmem r).mp hrR').2
    exact hrE (cent_mem_of_normalizes hE hEmax hEdec hU hLH he3 heL hce hCK hCL hLstep hT hET hTK
      hrT hrC hrN)
  intro r hrT hrC
  exact hCK r (hRE r ((hRmem r).mpr ⟨hrT, hrC⟩)) hrC

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
