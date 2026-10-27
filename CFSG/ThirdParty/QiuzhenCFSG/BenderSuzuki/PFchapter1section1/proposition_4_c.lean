module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 4(c)
-/

private theorem proposition_4_c_pointStabilizerCore_eq_ker
    {G Ω : Type*} [Group G] [MulAction G Ω] :
    pointStabilizerCore G Ω = (MulAction.toPermHom G Ω).ker := by
  ext g
  simp [pointStabilizerCore, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker,
    Equiv.Perm.ext_iff]

public theorem proposition_4_c_pointStabilizerCore_normal
    {G Ω : Type*} [Group G] [MulAction G Ω] :
    (pointStabilizerCore G Ω).Normal := by
  rw [proposition_4_c_pointStabilizerCore_eq_ker]
  infer_instance

private theorem proposition_4_c_pointStabilizerCore_le_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω ≤ H := by
  intro n hn
  rcases hA1.point_stabilizer with ⟨point, hpoint⟩
  have hn_all : ∀ ω : Ω, n ∈ MulAction.stabilizer G ω := by
    simpa [pointStabilizerCore] using hn
  simpa [hpoint] using hn_all point

private theorem proposition_4_c_pointStabilizerCore_le_rightConjugate
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω ≤ rightConjugate H t := by
  intro n hn
  rcases hA1.point_stabilizer with ⟨point, hpoint⟩
  have hn_all : ∀ ω : Ω, n ∈ MulAction.stabilizer G ω := by
    simpa [pointStabilizerCore] using hn
  have hn_fix : n • (t⁻¹ • point) = t⁻¹ • point := by
    simpa [MulAction.mem_stabilizer_iff] using hn_all (t⁻¹ • point)
  have htnH : t * n * t⁻¹ ∈ H := by
    rw [hpoint, MulAction.mem_stabilizer_iff]
    calc
      (t * n * t⁻¹) • point = t • (n • (t⁻¹ • point)) := by
        simp [mul_smul]
      _ = t • (t⁻¹ • point) := by rw [hn_fix]
      _ = point := by simp
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨t * n * t⁻¹, htnH, ?_⟩
  simp [MulAut.conj, mul_assoc]

private theorem proposition_4_c_pointStabilizerCore_le_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω ≤ D := by
  intro n hn
  rw [hA1.D_eq]
  exact
    ⟨proposition_4_c_pointStabilizerCore_le_H H D Q t hA1 hn,
      proposition_4_c_pointStabilizerCore_le_rightConjugate H D Q t hA1 hn⟩

private theorem proposition_4_c_pointStabilizerCore_le_centralizer_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω ≤ Subgroup.centralizer (Q : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hnD : n ∈ D :=
    proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hn
  have hnH : n ∈ H := hA1.D_le_H hnD
  have hn_normal : (pointStabilizerCore G Ω).Normal :=
    proposition_4_c_pointStabilizerCore_normal
  have hconjQ : n * q * n⁻¹ ∈ Q := by
    let qH : H := ⟨q, hA1.Q_le_H hq⟩
    let nH : H := ⟨n, hnH⟩
    have hqH : qH ∈ Q.subgroupOf H := by
      simpa [qH, Subgroup.mem_subgroupOf] using hq
    have hconj := hA1.Q_normal_in_H.conj_mem qH hqH nH
    simpa [qH, nH, Subgroup.mem_subgroupOf] using hconj
  have hcommQ : q⁻¹ * (n * q * n⁻¹) ∈ Q :=
    Q.mul_mem (Q.inv_mem hq) hconjQ
  have hcommN : q⁻¹ * (n * q * n⁻¹) ∈ pointStabilizerCore G Ω := by
    have hconjN : q⁻¹ * n * q ∈ pointStabilizerCore G Ω := by
      simpa using hn_normal.conj_mem n hn q⁻¹
    have hprodN : (q⁻¹ * n * q) * n⁻¹ ∈ pointStabilizerCore G Ω :=
      (pointStabilizerCore G Ω).mul_mem hconjN
        ((pointStabilizerCore G Ω).inv_mem hn)
    simpa [mul_assoc] using hprodN
  have hcommD : q⁻¹ * (n * q * n⁻¹) ∈ D :=
    proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hcommN
  have hcomm_one : q⁻¹ * (n * q * n⁻¹) = 1 := by
    have hmem : q⁻¹ * (n * q * n⁻¹) ∈ Q ⊓ D := ⟨hcommQ, hcommD⟩
    have := hA1.Q_disjoint_D.le_bot hmem
    simpa using this
  have hconj_eq : n * q * n⁻¹ = q := (inv_mul_eq_one.mp hcomm_one).symm
  calc
    q * n = (n * q * n⁻¹) * n := by rw [hconj_eq]
    _ = n * q := by group

private theorem proposition_4_c_mem_H_of_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {n t : G}
    (hn : n ∈ rightConjugate H t) :
    t * n * t⁻¹ ∈ H := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hn
  rcases hn with ⟨h, hhH, hn_eq⟩
  have htn : t * n * t⁻¹ = h := by
    rw [← hn_eq]
    simp [MulAut.conj, mul_assoc]
  simpa [htn] using hhH

private theorem proposition_4_c_D_inf_centralizer_Q_le_pointStabilizerCore
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    D ⊓ Subgroup.centralizer (Q : Set G) ≤ pointStabilizerCore G Ω := by
  classical
  intro n hn
  rcases hA1.point_stabilizer with ⟨point, hpoint⟩
  have hnD : n ∈ D := hn.1
  have hnH : n ∈ H := hA1.D_le_H hnD
  have hn_right : n ∈ rightConjugate H t := by
    rw [hA1.D_eq] at hnD
    exact hnD.2
  have htnH : t * n * t⁻¹ ∈ H :=
    proposition_4_c_mem_H_of_mem_rightConjugate hn_right
  have hn_fix_point : n • point = point := by
    simpa [hpoint, MulAction.mem_stabilizer_iff] using hnH
  have hn_fix_tinv_point : n • (t⁻¹ • point) = t⁻¹ • point := by
    have htn_fix : (t * n * t⁻¹) • point = point := by
      simpa [hpoint, MulAction.mem_stabilizer_iff] using htnH
    calc
      n • (t⁻¹ • point) = t⁻¹ • ((t * n * t⁻¹) • point) := by
        simp [mul_smul]
      _ = t⁻¹ • point := by rw [htn_fix]
  have hfix_all : ∀ ω : Ω, n ∈ MulAction.stabilizer G ω := by
    intro ω
    rw [MulAction.mem_stabilizer_iff]
    by_cases hω : ω = point
    · simpa [hω] using hn_fix_point
    · letI : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
      have hpre : MulAction.IsPretransitive G Ω :=
        MulAction.isPretransitive_of_is_two_pretransitive
      rcases hpre.exists_smul_eq ω point with ⟨g, hgω⟩
      have hg_not_H : g ∉ H := by
        intro hgH
        have hg_point : g • point = point := by
          simpa [hpoint, MulAction.mem_stabilizer_iff] using hgH
        have hω_eq : ω = point := by
          calc
            ω = g⁻¹ • (g • ω) := by simp
            _ = g⁻¹ • point := by rw [hgω]
            _ = g⁻¹ • (g • point) := by rw [hg_point]
            _ = point := by simp
        exact hω hω_eq
      rcases proposition_4_a H D Q t hA1 g hg_not_H with ⟨p, hp, _huniq⟩
      let x : H := p.1
      let q : Q := p.2
      have hx_inv_fix : ((x : G)⁻¹) • point = point := by
        have hx_fix : (x : G) • point = point := by
          simpa [hpoint, MulAction.mem_stabilizer_iff] using x.property
        calc
          (x : G)⁻¹ • point = (x : G)⁻¹ • ((x : G) • point) := by rw [hx_fix]
          _ = point := by simp
      have hω_eq : ω = (q : G)⁻¹ • (t⁻¹ • point) := by
        calc
          ω = g⁻¹ • point := by
            calc
              ω = g⁻¹ • (g • ω) := by simp
              _ = g⁻¹ • point := by rw [hgω]
          _ = (q : G)⁻¹ • (t⁻¹ • ((x : G)⁻¹ • point)) := by
            rw [hp]
            simp [x, q, mul_smul]
          _ = (q : G)⁻¹ • (t⁻¹ • point) := by rw [hx_inv_fix]
      have hqinv_comm : (q : G)⁻¹ * n = n * (q : G)⁻¹ := by
        exact (Subgroup.mem_centralizer_iff.mp hn.2) ((q : G)⁻¹) (Q.inv_mem q.property)
      rw [hω_eq]
      calc
        n • ((q : G)⁻¹ • (t⁻¹ • point)) =
            (n * (q : G)⁻¹) • (t⁻¹ • point) := by
              simp [mul_smul]
        _ = ((q : G)⁻¹ * n) • (t⁻¹ • point) := by rw [hqinv_comm]
        _ = (q : G)⁻¹ • (n • (t⁻¹ • point)) := by
              simp [mul_smul]
        _ = (q : G)⁻¹ • (t⁻¹ • point) := by rw [hn_fix_tinv_point]
  simpa [pointStabilizerCore] using hfix_all

private theorem proposition_4_c_kernel_eq
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω = D ⊓ Subgroup.centralizer (Q : Set G) := by
  apply le_antisymm
  · intro n hn
    exact
      ⟨proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hn,
        proposition_4_c_pointStabilizerCore_le_centralizer_Q H D Q t hA1 hn⟩
  · exact proposition_4_c_D_inf_centralizer_Q_le_pointStabilizerCore H D Q t hA1

private theorem proposition_4_c_exists_Q_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ u : G, u ∈ Q ∧ IsInvolution u := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hdiv : 2 ∣ Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    exact hA1.Q_even.two_dvd
  rcases exists_prime_orderOf_dvd_card (G := Q) 2 hdiv with ⟨q, hq⟩
  have hq' : (q : Q) ^ 2 = 1 ∧ (q : Q) ≠ 1 := by
    exact (orderOf_eq_prime_iff (x := q) (p := 2)).1 hq
  refine ⟨q, q.property, ?_⟩
  constructor
  · intro h
    exact hq'.2 (Subtype.ext h)
  · simpa using congrArg Subtype.val hq'.1

private theorem proposition_4_c_t_conjugate_to_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    ∃ u : G, u ∈ Q ∧ ∃ a : G, t = a * u * a⁻¹ := by
  classical
  rcases hsStructure with ⟨r, hrQ, hts⟩
  rcases proposition_4_c_exists_Q_involution H D Q t hA1 with ⟨u, huQ, huI⟩
  have hprop3 := (proposition_3 H D Q t hA1).2 s hsH hsI
  have hu_mem : u ∈ H ∧ IsInvolution u := ⟨hA1.Q_le_H huQ, huI⟩
  rcases (hprop3 u).1 hu_mem with ⟨k, hkK, hk_eq⟩
  have hs_eq : s = k * u * k⁻¹ := by
    have hk_eq' : k⁻¹ * s * k = u := by
      simpa [rightConjugateElem] using hk_eq
    calc
      s = k * (k⁻¹ * s * k) * k⁻¹ := by group
      _ = k * u * k⁻¹ := by rw [hk_eq']
  have htinv : t⁻¹ = t := by
    have ht2 : t * t = 1 := by
      simpa [pow_two] using hA1.involution_t.sq_eq_one
    exact inv_eq_of_mul_eq_one_left ht2
  refine ⟨u, huQ, ⟨r * t * k, ?_⟩⟩
  calc
    t = r * (t * s * t) * r⁻¹ := by
      rw [hts]
      group
    _ = r * (t * (k * u * k⁻¹) * t) * r⁻¹ := by rw [hs_eq]
    _ = (r * t * k) * u * (r * t * k)⁻¹ := by
      have hrtk_inv : (r * t * k)⁻¹ = k⁻¹ * t * r⁻¹ := by
        calc
          (r * t * k)⁻¹ = k⁻¹ * t⁻¹ * r⁻¹ := by group
          _ = k⁻¹ * t * r⁻¹ := by rw [htinv]
      rw [hrtk_inv]
      group

private theorem proposition_4_c_kernel_le_CDt
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    pointStabilizerCore G Ω ≤ peterfalviV D t := by
  intro n hn
  rw [peterfalviV]
  refine ⟨proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hn, ?_⟩
  change n ∈ Subgroup.centralizer ({t} : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  rcases proposition_4_c_t_conjugate_to_Q H D Q t s hA1 hsH hsI hsStructure with
    ⟨q, hqQ, a, ht_conj⟩
  have hn_normal : (pointStabilizerCore G Ω).Normal :=
    proposition_4_c_pointStabilizerCore_normal
  have hconjN : a⁻¹ * n * a ∈ pointStabilizerCore G Ω := by
    simpa using hn_normal.conj_mem n hn a⁻¹
  have hcent : a⁻¹ * n * a ∈ Subgroup.centralizer (Q : Set G) :=
    proposition_4_c_pointStabilizerCore_le_centralizer_Q H D Q t hA1 hconjN
  have hcomm : q * (a⁻¹ * n * a) = (a⁻¹ * n * a) * q :=
    (Subgroup.mem_centralizer_iff.mp hcent) q hqQ
  calc
    t * n = (a * q * a⁻¹) * n := by rw [ht_conj]
    _ = a * (q * (a⁻¹ * n * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * n * a) * q) * a⁻¹ := by rw [hcomm]
    _ = n * (a * q * a⁻¹) := by group
    _ = n * t := by rw [ht_conj]

private theorem proposition_4_c_eq_one_of_mem_D_sq_eq_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {d : G}
    (hdD : d ∈ D) (hd2 : d ^ 2 = 1) : d = 1 := by
  classical
  by_contra hdne
  let dD : D := ⟨d, hdD⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have horder : orderOf dD = 2 := by
    refine (orderOf_eq_prime_iff (x := dD) (p := 2)).2 ⟨?_, ?_⟩
    · ext
      simpa [dD] using hd2
    · intro h
      exact hdne (by simpa [dD] using congrArg Subtype.val h)
  have hdiv : 2 ∣ Nat.card D := by
    simpa [horder] using orderOf_dvd_natCard dD
  exact hA1.D_odd.not_two_dvd_nat hdiv

private theorem proposition_4_c_pow_st_mem_kernel_eq_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) {n : ℕ}
    (hn : (s * t) ^ n ∈ pointStabilizerCore G Ω) :
    (s * t) ^ n = 1 := by
  classical
  have htinv : t⁻¹ = t := by
    have ht2 : t * t = 1 := by
      simpa [pow_two] using hA1.involution_t.sq_eq_one
    exact inv_eq_of_mul_eq_one_left ht2
  have hsinv : s⁻¹ = s := by
    have hs2 : s * s = 1 := by
      simpa [pow_two] using hsI.sq_eq_one
    exact inv_eq_of_mul_eq_one_left hs2
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hconj_st : (MulAut.conj t) (s * t) = (s * t)⁻¹ := by
    calc
      (MulAut.conj t) (s * t) = t * (s * t) * t⁻¹ := rfl
      _ = t * s := by
        rw [htinv]
        simp [ht2, mul_assoc]
      _ = (s * t)⁻¹ := by
        simp [htinv, hsinv]
  have hconj_pow : (MulAut.conj t) ((s * t) ^ n) = ((s * t) ^ n)⁻¹ := by
    calc
      (MulAut.conj t) ((s * t) ^ n) = ((MulAut.conj t) (s * t)) ^ n := by
        rw [map_pow]
      _ = ((s * t)⁻¹) ^ n := by rw [hconj_st]
      _ = ((s * t) ^ n)⁻¹ := by
        exact inv_pow (s * t) n
  have hnV : (s * t) ^ n ∈ peterfalviV D t :=
    proposition_4_c_kernel_le_CDt H D Q t s hA1 hsH hsI hsStructure hn
  have hcent : (s * t) ^ n ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [peterfalviV] at hnV
    exact hnV.2
  have hcomm : t * ((s * t) ^ n) = ((s * t) ^ n) * t :=
    (Subgroup.mem_centralizer_iff.mp hcent) t (by simp)
  have hconj_fix : (MulAut.conj t) ((s * t) ^ n) = (s * t) ^ n := by
    change t * ((s * t) ^ n) * t⁻¹ = (s * t) ^ n
    calc
      t * ((s * t) ^ n) * t⁻¹ = ((s * t) ^ n) * t * t⁻¹ := by rw [hcomm]
      _ = (s * t) ^ n := by simp
  have hpow_inv : (s * t) ^ n = ((s * t) ^ n)⁻¹ :=
    hconj_fix.symm.trans hconj_pow
  have hpow_sq : ((s * t) ^ n) ^ 2 = 1 := by
    have hmul : (s * t) ^ n * (s * t) ^ n = 1 := by
      nth_rw 1 [hpow_inv]
      exact inv_mul_cancel ((s * t) ^ n)
    simpa [pow_two] using hmul
  have hnD : (s * t) ^ n ∈ D :=
    proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hn
  exact proposition_4_c_eq_one_of_mem_D_sq_eq_one H D Q t hA1 hnD hpow_sq

private theorem proposition_4_c_quotient_order_eq
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    orderOf (QuotientGroup.mk (s * t) : G ⧸ pointStabilizerCore G Ω) =
      orderOf (s * t) := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  apply Nat.dvd_antisymm
  · simpa [π, N] using orderOf_map_dvd π (s * t)
  · let m : ℕ := orderOf (π (s * t))
    change orderOf (s * t) ∣ m
    rw [orderOf_dvd_iff_pow_eq_one]
    have hmap_pow : π ((s * t) ^ m) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    have hmemN : (s * t) ^ m ∈ N := by
      have hker : (s * t) ^ m ∈ π.ker := by
        simpa [MonoidHom.mem_ker] using hmap_pow
      simpa [π, N, QuotientGroup.ker_mk'] using hker
    exact proposition_4_c_pow_st_mem_kernel_eq_one H D Q t s hA1 hsH hsI hsStructure hmemN

private theorem proposition_4_c_quotient_Q_iso
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Nonempty (Q ≃* Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω))) := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  refine ⟨MulEquiv.ofBijective (π.subgroupMap Q) ⟨?_, MonoidHom.subgroupMap_surjective π Q⟩⟩
  intro x y hxy
  apply Subtype.ext
  have hmap : π (x : G) = π (y : G) := by
    simpa [π] using congrArg Subtype.val hxy
  have hdiv_map : π ((x : G) * (y : G)⁻¹) = 1 := by
    calc
      π ((x : G) * (y : G)⁻¹) = π (x : G) * (π (y : G))⁻¹ := by simp [π]
      _ = 1 := by rw [hmap]; simp
  have hdivN : (x : G) * (y : G)⁻¹ ∈ N := by
    have hker : (x : G) * (y : G)⁻¹ ∈ π.ker := by
      simpa [MonoidHom.mem_ker] using hdiv_map
    simpa [π, N, QuotientGroup.ker_mk'] using hker
  have hdivQ : (x : G) * (y : G)⁻¹ ∈ Q :=
    Q.mul_mem x.property (Q.inv_mem y.property)
  have hdivD : (x : G) * (y : G)⁻¹ ∈ D := by
    have hker_eq := proposition_4_c_kernel_eq H D Q t hA1
    have hdivN' : (x : G) * (y : G)⁻¹ ∈ pointStabilizerCore G Ω := by
      simpa [N] using hdivN
    have hdivInf : (x : G) * (y : G)⁻¹ ∈ D ⊓ Subgroup.centralizer (Q : Set G) := by
      simpa [hker_eq] using hdivN'
    exact hdivInf.1
  have hdiv_one : (x : G) * (y : G)⁻¹ = 1 := by
    have hmem : (x : G) * (y : G)⁻¹ ∈ Q ⊓ D := ⟨hdivQ, hdivD⟩
    have := hA1.Q_disjoint_D.le_bot hmem
    simpa using this
  exact mul_inv_eq_one.mp hdiv_one

private theorem proposition_4_c_quotient_Q_even
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Even (Nat.card (↥(Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω))))) := by
  rcases proposition_4_c_quotient_Q_iso H D Q t hA1 with ⟨e⟩
  rw [← Nat.card_congr e.toEquiv]
  exact hA1.Q_even

private theorem proposition_4_c_quotient_D_odd
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Odd (Nat.card (↥(D.map (QuotientGroup.mk' (pointStabilizerCore G Ω))))) :=
  Odd.of_dvd_nat hA1.D_odd (Subgroup.card_map_dvd (H := D)
    (QuotientGroup.mk' (pointStabilizerCore G Ω)))

private theorem proposition_4_c_quotient_Q_disjoint_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Disjoint (Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
      (D.map (QuotientGroup.mk' (pointStabilizerCore G Ω))) := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  rw [disjoint_iff_inf_le]
  intro x hx
  rcases hx.1 with ⟨q, hqQ, hq_eq⟩
  rcases hx.2 with ⟨d, hdD, hd_eq⟩
  have hqd_eq : (q : G ⧸ N) = d := by
    exact hq_eq.trans hd_eq.symm
  have hqdivN : q / d ∈ N :=
    (QuotientGroup.eq_iff_div_mem (N := N)).mp hqd_eq
  have hqdivD : q / d ∈ D :=
    proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hqdivN
  have hqD : q ∈ D := by
    have hmul : (q / d) * d ∈ D := D.mul_mem hqdivD hdD
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hq_one : q = 1 := by
    have hmem : q ∈ Q ⊓ D := ⟨hqQ, hqD⟩
    have := hA1.Q_disjoint_D.le_bot hmem
    simpa using this
  have hx_one : x = 1 := by
    rw [← hq_eq, hq_one]
    simp
  simpa using hx_one

private theorem proposition_4_c_quotient_Q_sup_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω)) ⊔
        D.map (QuotientGroup.mk' (pointStabilizerCore G Ω)) =
      H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)) := by
  rw [← Subgroup.map_sup Q D (QuotientGroup.mk' (pointStabilizerCore G Ω)),
    hA1.Q_sup_D]

private theorem proposition_4_c_quotient_Q_normal_in_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ((Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω))).subgroupOf
      (H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))).Normal := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  constructor
  intro qbar hqbar hbar
  rw [Subgroup.mem_subgroupOf] at hqbar ⊢
  rcases hqbar with ⟨q, hqQ, hq_eq⟩
  rcases hbar.property with ⟨h, hhH, hh_eq⟩
  have hconjQ : h * q * h⁻¹ ∈ Q := by
    let qH : H := ⟨q, hA1.Q_le_H hqQ⟩
    let hH : H := ⟨h, hhH⟩
    have hqH : qH ∈ Q.subgroupOf H := by
      simpa [qH, Subgroup.mem_subgroupOf] using hqQ
    have hconj := hA1.Q_normal_in_H.conj_mem qH hqH hH
    simpa [qH, hH, Subgroup.mem_subgroupOf] using hconj
  refine ⟨h * q * h⁻¹, hconjQ, ?_⟩
  change π (h * q * h⁻¹) =
    (((hbar * qbar * hbar⁻¹ : H.map π) : G ⧸ N))
  calc
    π (h * q * h⁻¹) = π h * π q * (π h)⁻¹ := by simp [π]
    _ = (hbar : G ⧸ N) * (qbar : G ⧸ N) * (hbar : G ⧸ N)⁻¹ := by
      rw [hh_eq, hq_eq]
    _ = (((hbar * qbar * hbar⁻¹ : H.map π) : G ⧸ N)) := rfl

private theorem proposition_4_c_quotient_D_eq
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    D.map (QuotientGroup.mk' (pointStabilizerCore G Ω)) =
      H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)) ⊓
        rightConjugate (H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
          (QuotientGroup.mk t) := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  apply le_antisymm
  · intro x hxD
    rcases hxD with ⟨d, hdD, hd_eq⟩
    constructor
    · exact ⟨d, hA1.D_le_H hdD, hd_eq⟩
    · have hd_right : d ∈ rightConjugate H t := by
        rw [hA1.D_eq] at hdD
        exact hdD.2
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hd_right
      rcases hd_right with ⟨h, hhH, hd_conj_eq⟩
      change x ∈ Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj (QuotientGroup.mk t : G ⧸ N)⁻¹))
        (H.map π)
      rw [Subgroup.mem_map]
      refine ⟨π h, ⟨h, hhH, rfl⟩, ?_⟩
      calc
        (MulAut.conj (QuotientGroup.mk t : G ⧸ N)⁻¹) (π h) =
            π ((MulAut.conj t⁻¹) h) := by
              change (QuotientGroup.mk t : G ⧸ N)⁻¹ * π h * ((QuotientGroup.mk t : G ⧸ N)⁻¹)⁻¹ =
                π (t⁻¹ * h * (t⁻¹)⁻¹)
              rw [inv_inv]
              simp [π, mul_assoc]
        _ = π d := by
          simpa [π] using congrArg π hd_conj_eq
        _ = x := hd_eq
  · intro x hx
    rcases hx.1 with ⟨h, hhH, hx_eq⟩
    have hx_right :
        x ∈ Subgroup.map
          (MulEquiv.toMonoidHom (MulAut.conj (QuotientGroup.mk t : G ⧸ N)⁻¹))
          (H.map π) := by
      simpa [rightConjugate, Subgroup.conjBy, π] using hx.2
    rw [Subgroup.mem_map] at hx_right
    rcases hx_right with ⟨hbar, hhbarH, hright_eq⟩
    rcases hhbarH with ⟨h', hh'H, hhbar_eq⟩
    have hquot_eq : (h : G ⧸ N) = t⁻¹ * h' * t := by
      calc
        (h : G ⧸ N) = x := by simpa [π] using hx_eq
        _ = (MulAut.conj (QuotientGroup.mk t : G ⧸ N)⁻¹) hbar := hright_eq.symm
        _ = t⁻¹ * h' * t := by
          rw [← hhbar_eq]
          change (QuotientGroup.mk t : G ⧸ N)⁻¹ * π h' * ((QuotientGroup.mk t : G ⧸ N)⁻¹)⁻¹ =
            (QuotientGroup.mk t : G ⧸ N)⁻¹ * π h' * QuotientGroup.mk t
          rw [inv_inv]
    have hdivN : h / (t⁻¹ * h' * t) ∈ N :=
      (QuotientGroup.eq_iff_div_mem (N := N)).mp hquot_eq
    have hdivD : h / (t⁻¹ * h' * t) ∈ D :=
      proposition_4_c_pointStabilizerCore_le_D H D Q t hA1 hdivN
    have hdiv_right : h / (t⁻¹ * h' * t) ∈ rightConjugate H t := by
      rw [hA1.D_eq] at hdivD
      exact hdivD.2
    have htconjH : t⁻¹ * h' * t ∈ rightConjugate H t := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨h', hh'H, ?_⟩
      simp [MulAut.conj, mul_assoc]
    have hh_right : h ∈ rightConjugate H t := by
      have hprod := (rightConjugate H t).mul_mem hdiv_right htconjH
      simpa [div_eq_mul_inv, mul_assoc] using hprod
    have hhD : h ∈ D := by
      rw [hA1.D_eq]
      exact ⟨hhH, hh_right⟩
    exact ⟨h, hhD, hx_eq⟩

private theorem proposition_4_c_quotient_A1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [hN : (pointStabilizerCore G Ω).Normal]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ quotientAction : MulAction (G ⧸ pointStabilizerCore G Ω) Ω,
      letI : MulAction (G ⧸ pointStabilizerCore G Ω) Ω := quotientAction
      (∀ (g : G) (ω : Ω),
          (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Ω) • ω = g • ω) ∧
        HypothesisA1 (G ⧸ pointStabilizerCore G Ω) Ω
          (H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
          (D.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
          (Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
          (QuotientGroup.mk t) := by
  classical
  let N : Subgroup G := pointStabilizerCore G Ω
  let quotientPermHom : G ⧸ N →* Equiv.Perm Ω := by
    letI : N.Normal := hN
    have hNker : N ≤ (MulAction.toPermHom G Ω).ker := by
      intro n hn
      rw [← proposition_4_c_pointStabilizerCore_eq_ker]
      exact hn
    exact QuotientGroup.lift N (MulAction.toPermHom G Ω) hNker
  let quotientAction : MulAction (G ⧸ N) Ω := MulAction.compHom Ω quotientPermHom
  refine ⟨quotientAction, ?_⟩
  letI : MulAction (G ⧸ N) Ω := quotientAction
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hbar_smul : ∀ (g : G) (ω : Ω), (QuotientGroup.mk g : G ⧸ N) • ω = g • ω := by
    intro g ω
    change quotientPermHom (QuotientGroup.mk g : G ⧸ N) ω = g • ω
    simp [quotientPermHom, MulAction.toPermHom_apply]
  refine ⟨by simpa [N] using hbar_smul, ?_⟩
  refine
    { two_transitive := ?_
      point_stabilizer := ?_
      involution_t := ?_
      t_not_mem_H := ?_
      D_eq := proposition_4_c_quotient_D_eq H D Q t hA1
      Q_le_H := Subgroup.map_mono hA1.Q_le_H
      D_le_H := Subgroup.map_mono hA1.D_le_H
      Q_normal_in_H := proposition_4_c_quotient_Q_normal_in_H H D Q t hA1
      Q_disjoint_D := proposition_4_c_quotient_Q_disjoint_D H D Q t hA1
      Q_sup_D := proposition_4_c_quotient_Q_sup_D H D Q t hA1
      Q_even := proposition_4_c_quotient_Q_even H D Q t hA1
      D_odd := proposition_4_c_quotient_D_odd H D Q t hA1 }
  · rw [MulAction.isMultiplyPretransitive_iff]
    intro x y
    have htwoG :=
      (MulAction.isMultiplyPretransitive_iff (G := G) (α := Ω) (n := 2)).1
        hA1.two_transitive
    rcases htwoG x y with ⟨g, hg⟩
    refine ⟨QuotientGroup.mk g, ?_⟩
    ext i
    simpa [hbar_smul] using congrArg (fun f : Fin 2 ↪ Ω => f i) hg
  · rcases hA1.point_stabilizer with ⟨point, hpoint⟩
    refine ⟨point, ?_⟩
    ext x
    constructor
    · intro hx
      rcases hx with ⟨h, hhH, hx_eq⟩
      rw [MulAction.mem_stabilizer_iff]
      rw [← hx_eq]
      change (QuotientGroup.mk h : G ⧸ N) • point = point
      rw [hbar_smul]
      simpa [hpoint, MulAction.mem_stabilizer_iff] using hhH
    · intro hx
      revert hx
      refine QuotientGroup.induction_on x ?_
      intro g hxg
      have hgfix : g • point = point := by
        simpa [hbar_smul] using (MulAction.mem_stabilizer_iff.mp hxg)
      have hgH : g ∈ H := by
        simpa [hpoint, MulAction.mem_stabilizer_iff] using hgfix
      refine ⟨g, hgH, ?_⟩
      rfl
  · constructor
    · intro ht_one
      have htN : t ∈ N := (QuotientGroup.eq_one_iff (N := N) t).mp ht_one
      exact hA1.t_not_mem_H (proposition_4_c_pointStabilizerCore_le_H H D Q t hA1 htN)
    · simpa using congrArg (fun g : G => (QuotientGroup.mk g : G ⧸ N))
        hA1.involution_t.sq_eq_one
  · intro htH
    rcases htH with ⟨h, hhH, hh_eq⟩
    have hhtN : h / t ∈ N := by
      have hquot : (h : G ⧸ N) = t := by
        simpa [π] using hh_eq
      exact (QuotientGroup.eq_iff_div_mem (N := N)).mp hquot
    have hhtH : h / t ∈ H :=
      proposition_4_c_pointStabilizerCore_le_H H D Q t hA1 hhtN
    have htH' : t ∈ H := by
      have hinv : (h / t)⁻¹ ∈ H := H.inv_mem hhtH
      have hthinvinv : t * h⁻¹ ∈ H := by
        simpa [div_eq_mul_inv] using hinv
      have hprod : (t * h⁻¹) * h ∈ H := H.mul_mem hthinvinv hhH
      simpa [mul_assoc] using hprod
    exact hA1.t_not_mem_H htH'

/--
Peterfalvi: Proposition 4(c). With `N = ⋂ X, H^X`, the regular action of `Q` on
`Ω - {H}` identifies `N` with `C_D(Q)`, the distinguished structure equation
makes `t` centralize `N`, and the quotient action of `G/N` on `Ω` again
satisfies `(A1)` with `Qbar ≃ Q`. The last Peterfalvi paragraph proves that the
image of `st` has the same order as `st`.
-/
public theorem proposition_4_c
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    pointStabilizerCore G Ω = D ⊓ Subgroup.centralizer (Q : Set G) ∧
      pointStabilizerCore G Ω ≤ peterfalviV D t ∧
        letI : (pointStabilizerCore G Ω).Normal :=
          proposition_4_c_pointStabilizerCore_normal
        (∃ quotientAction : MulAction (G ⧸ pointStabilizerCore G Ω) Ω,
          letI : MulAction (G ⧸ pointStabilizerCore G Ω) Ω := quotientAction
          (∀ (g : G) (ω : Ω),
              (QuotientGroup.mk g : G ⧸ pointStabilizerCore G Ω) • ω = g • ω) ∧
            HypothesisA1 (G ⧸ pointStabilizerCore G Ω) Ω
              (H.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
              (D.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
              (Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω)))
              (QuotientGroup.mk t)) ∧
          Nonempty (Q ≃* Q.map (QuotientGroup.mk' (pointStabilizerCore G Ω))) ∧
            orderOf (QuotientGroup.mk (s * t) : G ⧸ pointStabilizerCore G Ω) =
              orderOf (s * t) := by
  letI : (pointStabilizerCore G Ω).Normal := proposition_4_c_pointStabilizerCore_normal
  exact
    ⟨proposition_4_c_kernel_eq H D Q t hA1,
      proposition_4_c_kernel_le_CDt H D Q t s hA1 hsH hsI hsStructure,
      proposition_4_c_quotient_A1 H D Q t hA1,
      proposition_4_c_quotient_Q_iso H D Q t hA1,
      proposition_4_c_quotient_order_eq H D Q t s hA1 hsH hsI hsStructure⟩

end PFchapter1section1
end CFSG.BenderSuzuki


