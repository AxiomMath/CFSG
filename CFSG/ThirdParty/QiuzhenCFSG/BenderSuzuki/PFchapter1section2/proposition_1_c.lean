module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Proposition 1(c)
-/

private theorem proposition_1_c_isMulCommutative_of_forall_sq_one
    {A : Type*} [Group A] (hA : ∀ x : A, x ^ 2 = 1) :
    IsMulCommutative A := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  have hinv : ∀ x : A, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by
      simpa [pow_two] using hA x
    calc
      x⁻¹ = x⁻¹ * 1 := by simp
      _ = x⁻¹ * (x * x) := by rw [hx]
      _ = x := by simp
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [hinv a, hinv b]

private theorem proposition_1_c_Q_conj_mem_of_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d q : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hqQ : q ∈ Q) (hdD : d ∈ D) :
    d * q * d⁻¹ ∈ Q := by
  let qH : H := ⟨q, hA1.Q_le_H hqQ⟩
  let dH : H := ⟨d, hA1.D_le_H hdD⟩
  have hqSub : qH ∈ Q.subgroupOf H := by
    simpa [qH, Subgroup.mem_subgroupOf] using hqQ
  have hconj := hA1.Q_normal_in_H.conj_mem qH hqSub dH
  simpa [qH, dH, Subgroup.mem_subgroupOf] using hconj

private theorem proposition_1_c_center_of_eq_D_conjugate_center
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d z y : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hzQ : z ∈ Q) (hyQ : y ∈ Q)
    (hzC : (⟨z, hzQ⟩ : Q) ∈ Subgroup.center Q)
    (hdD : d ∈ D) (hy_eq : y = d * z * d⁻¹) :
    (⟨y, hyQ⟩ : Q) ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  change (q : G) * y = y * (q : G)
  rw [hy_eq]
  have hq'Q : d⁻¹ * (q : G) * d ∈ Q := by
    simpa using
      proposition_1_c_Q_conj_mem_of_mem_D
        (G := G) (Ω := Ω) (H := H) (D := D) (Q := Q) (t := t)
        hA1 q.property (D.inv_mem hdD)
  have hcommQ :=
    (Subgroup.mem_center_iff.mp hzC) (⟨d⁻¹ * (q : G) * d, hq'Q⟩ : Q)
  have hcomm : (d⁻¹ * (q : G) * d) * z =
      z * (d⁻¹ * (q : G) * d) := by
    exact congrArg Subtype.val hcommQ
  calc
    (q : G) * (d * z * d⁻¹) =
        d * ((d⁻¹ * (q : G) * d) * z) * d⁻¹ := by group
    _ = d * (z * (d⁻¹ * (q : G) * d)) * d⁻¹ := by rw [hcomm]
    _ = (d * z * d⁻¹) * (q : G) := by group

private theorem proposition_1_c_exists_center_involution_of_even_nilpotent
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hQ_even : Even (Nat.card Q)) (hnil : Group.IsNilpotent Q) :
    ∃ z : Q, z ∈ Subgroup.center Q ∧ IsInvolution (z : G) := by
  classical
  have : Group.IsNilpotent Q := by
    simpa using hnil
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have htop : twoPrime ∈ subgroupPrimeSet (⊤ : Subgroup Q) := by
    change twoPrime.val ∣ Nat.card (⊤ : Subgroup Q)
    simpa [twoPrime] using hQ_even.two_dvd
  have hcenterPrime : twoPrime ∈ subgroupPrimeSet (Subgroup.center Q) := by
    rw [section8_subgroupPrimeSet_center_eq_top_of_nilpotent (H := Q)]
    exact htop
  have htwo_dvd_center : 2 ∣ Nat.card (Subgroup.center Q) := by
    exact hcenterPrime
  obtain ⟨zC, hzC_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 htwo_dvd_center
  let z : Q := (zC : Q)
  have hz_order : orderOf z = 2 := by
    simpa [z, hzC_order] using (Subgroup.orderOf_coe zC)
  have hz_pow_ne :=
    (orderOf_eq_prime_iff (x := z) (p := 2)).mp hz_order
  refine ⟨z, zC.property, ?_⟩
  constructor
  · intro hz_one
    exact hz_pow_ne.2 (Subtype.ext hz_one)
  · exact congrArg Subtype.val hz_pow_ne.1


private theorem proposition_1_c_involutions_center_of_Q_nilpotent_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    Group.IsNilpotent Q →
      ∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
        x ∈ Subgroup.center Q := by
  classical
  intro hnil x hxH hxI
  obtain ⟨z, hzC, hzI⟩ :=
    proposition_1_c_exists_center_involution_of_even_nilpotent
      Q hA1.Q_even hnil
  obtain ⟨p, hp, _hpuniq⟩ := proposition_4_b H D Q t hA1
  let s : G := p.1
  have hzH : (z : G) ∈ H := hA1.Q_le_H z.property
  obtain ⟨dz, hz_eq⟩ :=
    proposition_5_involution_mem_D_conjugacy_orbit
      H D Q t s (z : G) hA1
      hp.1 hp.2.1 ⟨p.2, hp.2.2.1, hp.2.2.2⟩ hzH hzI
  have hs_eq : s = (dz : G)⁻¹ * (z : G) * (dz : G) := by
    calc
      s = (dz : G)⁻¹ * ((dz : G) * s * (dz : G)⁻¹) * (dz : G) := by group
      _ = (dz : G)⁻¹ * (z : G) * (dz : G) := by rw [← hz_eq]
  have hsQ : s ∈ Q := by
    rw [hs_eq]
    simpa using
      proposition_1_c_Q_conj_mem_of_mem_D
        (G := G) (Ω := Ω) (H := H) (D := D) (Q := Q) (t := t)
        hA1 z.property (D.inv_mem dz.property)
  have hsC : (⟨s, hsQ⟩ : Q) ∈ Subgroup.center Q := by
    apply
      proposition_1_c_center_of_eq_D_conjugate_center
        (G := G) (Ω := Ω) (H := H) (D := D) (Q := Q) (t := t)
        (d := (dz : G)⁻¹) (z := (z : G)) (y := s)
        hA1 z.property hsQ hzC (D.inv_mem dz.property)
    simpa using hs_eq
  obtain ⟨dx, hx_eq⟩ :=
    proposition_5_involution_mem_D_conjugacy_orbit
      H D Q t s (x : G) hA1
      hp.1 hp.2.1 ⟨p.2, hp.2.2.1, hp.2.2.2⟩ hxH hxI
  exact
    proposition_1_c_center_of_eq_D_conjugate_center
      (G := G) (Ω := Ω) (H := H) (D := D) (Q := Q) (t := t)
      hA1 hsQ x.property hsC dx.property hx_eq

/-- Under Hypothesis (A1), nilpotence of `Q` forces every involution of `H`
lying in `Q` to be central in `Q`. -/
public theorem proposition_1_c_involutions_center_of_hypothesisA1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (hnil : Group.IsNilpotent Q) :
    ∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
      x ∈ Subgroup.center Q := by
  exact proposition_1_c_involutions_center_of_Q_nilpotent_obligation
    H D Q t hA1 hnil

public theorem proposition_1_c_exists_Q0_of_hypothesisA1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (hnil : Group.IsNilpotent Q) :
    ∃ Q0 : Subgroup G,
      Q0 ≤ Q ∧
        (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
          IsMulCommutative Q0 ∧ ∀ x : Q0, x ^ 2 = 1 := by
  let hcenter :=
    proposition_1_c_involutions_center_of_hypothesisA1 H D Q t hA1 hnil
  let Q0 : Subgroup G := {
    carrier := {x : G | x = 1 ∨ (x ∈ H ∧ IsInvolution x)}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro x y hx hy
      rcases hx with rfl | ⟨hxH, hxI⟩
      · simpa using hy
      rcases hy with rfl | ⟨hyH, hyI⟩
      · simpa using Or.inr ⟨hxH, hxI⟩
      by_cases hxy : x * y = 1
      · exact Or.inl hxy
      · refine Or.inr ⟨H.mul_mem hxH hyH, ⟨hxy, ?_⟩⟩
        have hxQ := involution_mem_Q_of_mem_H H D Q t hA1 x hxH hxI
        have hyQ := involution_mem_Q_of_mem_H H D Q t hA1 y hyH hyI
        have hxC : (⟨x, hxQ⟩ : Q) ∈ Subgroup.center Q :=
          hcenter ⟨x, hxQ⟩ hxH hxI
        have hcomm : x * y = y * x := by
          exact (congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hxC ⟨y, hyQ⟩)).symm
        calc
          (x * y) ^ 2 = x * (y * x) * y := by simp [pow_two, mul_assoc]
          _ = x * (x * y) * y := by rw [hcomm]
          _ = (x * x) * (y * y) := by simp [mul_assoc]
          _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
          _ = 1 := by rw [hxI.sq_eq_one, hyI.sq_eq_one, one_mul]
    inv_mem' := by
      intro x hx
      rcases hx with rfl | ⟨hxH, hxI⟩
      · exact Or.inl (inv_one)
      · rw [hxI.inv_eq_self]
        exact Or.inr ⟨hxH, hxI⟩
  }
  have hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x) :=
    fun _ => Iff.rfl
  have hQ0_le_Q : Q0 ≤ Q := by
    intro x hx
    rcases (hQ0_def x).mp hx with rfl | ⟨hxH, hxI⟩
    · exact Q.one_mem
    · exact involution_mem_Q_of_mem_H H D Q t hA1 x hxH hxI
  have hsq : ∀ x : Q0, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    rcases (hQ0_def (x : G)).mp x.property with hx | ⟨_hxH, hxI⟩
    · simp [hx]
    · exact hxI.sq_eq_one
  exact ⟨Q0, hQ0_le_Q, hQ0_def,
    proposition_1_c_isMulCommutative_of_forall_sq_one hsq, hsq⟩

public theorem proposition_1_c_involutions_center_of_hA
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    ∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
      x ∈ Subgroup.center Q := by
  exact proposition_1_c_involutions_center_of_Q_nilpotent_obligation
    H D Q t hA.A1 (proposition_1_b_of_hA H D Q t hA)

public theorem proposition_1_c_exists_Q0
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    ∃ Q0 : Subgroup G,
      Q0 ≤ Q ∧
        (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
          IsMulCommutative Q0 ∧ ∀ x : Q0, x ^ 2 = 1 := by
  let hcenter := proposition_1_c_involutions_center_of_hA H D Q t hA
  let Q0 : Subgroup G := {
    carrier := {x : G | x = 1 ∨ (x ∈ H ∧ IsInvolution x)}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro x y hx hy
      rcases hx with rfl | ⟨hxH, hxI⟩
      · simpa using hy
      rcases hy with rfl | ⟨hyH, hyI⟩
      · simpa using Or.inr ⟨hxH, hxI⟩
      by_cases hxy : x * y = 1
      · exact Or.inl hxy
      · refine Or.inr ⟨H.mul_mem hxH hyH, ⟨hxy, ?_⟩⟩
        have hxQ := involution_mem_Q_of_mem_H H D Q t hA.A1 x hxH hxI
        have hyQ := involution_mem_Q_of_mem_H H D Q t hA.A1 y hyH hyI
        have hxC : (⟨x, hxQ⟩ : Q) ∈ Subgroup.center Q :=
          hcenter ⟨x, hxQ⟩ hxH hxI
        have hcomm : x * y = y * x := by
          exact (congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hxC ⟨y, hyQ⟩)).symm
        calc
          (x * y) ^ 2 = x * (y * x) * y := by simp [pow_two, mul_assoc]
          _ = x * (x * y) * y := by rw [hcomm]
          _ = (x * x) * (y * y) := by simp [mul_assoc]
          _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
          _ = 1 := by rw [hxI.sq_eq_one, hyI.sq_eq_one, one_mul]
    inv_mem' := by
      intro x hx
      rcases hx with rfl | ⟨hxH, hxI⟩
      · exact Or.inl (inv_one)
      · rw [hxI.inv_eq_self]
        exact Or.inr ⟨hxH, hxI⟩
  }
  have hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x) :=
    fun _ => Iff.rfl
  have hQ0_le_Q : Q0 ≤ Q := by
    intro x hx
    rcases (hQ0_def x).mp hx with rfl | ⟨hxH, hxI⟩
    · exact Q.one_mem
    · exact involution_mem_Q_of_mem_H H D Q t hA.A1 x hxH hxI
  have hsq : ∀ x : Q0, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    rcases (hQ0_def (x : G)).mp x.property with hx | ⟨_hxH, hxI⟩
    · simp [hx]
    · exact hxI.sq_eq_one
  exact ⟨Q0, hQ0_le_Q, hQ0_def,
    proposition_1_c_isMulCommutative_of_forall_sq_one hsq, hsq⟩

/-- The Sylow `2`-factor and the commuting odd-order factor in the
decomposition of the nilpotent group `Q`. -/
public theorem proposition_1_c_exists_S_Q1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    ∃ S Q1 : Subgroup G,
      S ≤ Q ∧
        Q1 ≤ Q ∧
          (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
            Odd (Nat.card Q1) ∧
              Disjoint S Q1 ∧
                (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                  s * q1 = q1 * s) ∧
                  S ⊔ Q1 = Q := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 Q := default
  let SQ : Subgroup Q := P
  let Q1Q : Subgroup Q := pPrimeCore 2 Q
  let S : Subgroup G := SQ.map Q.subtype
  let Q1 : Subgroup G := Q1Q.map Q.subtype
  have hnil : Group.IsNilpotent Q := proposition_1_b_of_hA H D Q t hA
  have hPnormal : SQ.Normal := by
    dsimp [SQ]
    exact Group.IsNilpotent.sylow_normal hnil 2 P
  have hP_le_core : SQ ≤ pCore 2 Q := by
    exact le_sSup (show SQ ∈
      {K : Subgroup Q | K.Normal ∧ IsPGroup 2 K} from
        ⟨hPnormal, P.isPGroup'⟩)
  have hcore_le_P : pCore 2 Q ≤ SQ := by
    have hsup_p : IsPGroup 2 ((SQ ⊔ pCore 2 Q : Subgroup Q)) :=
      IsPGroup.to_sup_of_normal_right P.isPGroup'
        (pCore_isPGroup (G := Q) (p := 2))
    exact sup_eq_left.mp (P.is_maximal' hsup_p le_sup_left)
  have hP_eq_core : SQ = pCore 2 Q :=
    le_antisymm hP_le_core hcore_le_P
  have hsup_top : SQ ⊔ Q1Q = (⊤ : Subgroup Q) := by
    rw [hP_eq_core]
    exact top_unique (nilpotent_top_le_pCore_sup_pPrimeCore hnil)
  have hodd_Q1Q : Odd (Nat.card Q1Q) := by
    exact Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (G := Q) (p := 2))
  have hdisj_Q : Disjoint SQ Q1Q := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := Q) (p := 2)).pow_left n
  have hcomm_Q :
      ∀ s : Q, s ∈ SQ → ∀ q1 : Q, q1 ∈ Q1Q → s * q1 = q1 * s := by
    intro s hs q1 hq1
    exact (Subgroup.commute_of_normal_of_disjoint SQ Q1Q hPnormal
      (pPrimeCore_normal (G := Q) (p := 2)) hdisj_Q s q1 hs hq1).eq
  refine ⟨S, Q1, Subgroup.map_subtype_le SQ, Subgroup.map_subtype_le Q1Q,
    ⟨P, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [show Nat.card Q1 = Nat.card Q1Q from
      Subgroup.card_map_of_injective (K := Q1Q) (f := Q.subtype)
        Q.subtype_injective]
    exact hodd_Q1Q
  · exact Subgroup.disjoint_map Q.subtype_injective hdisj_Q
  · intro s hs q1 hq1
    rcases Subgroup.mem_map.mp hs with ⟨sQ, hsQ, rfl⟩
    rcases Subgroup.mem_map.mp hq1 with ⟨q1Q, hq1Q, rfl⟩
    exact congrArg Subtype.val (hcomm_Q sQ hsQ q1Q hq1Q)
  · calc
      S ⊔ Q1 = (SQ ⊔ Q1Q).map Q.subtype := by
        exact (Subgroup.map_sup SQ Q1Q Q.subtype).symm
      _ = (⊤ : Subgroup Q).map Q.subtype := by rw [hsup_top]
      _ = Q := by
        simpa [MonoidHom.range_eq_map] using
          (Q.range_subtype : Q.subtype.range = Q)

private theorem proposition_1_c_Q0_elementary_of_centered_involutions_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    (∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
      x ∈ Subgroup.center Q) →
        (IsMulCommutative Q0 ∧ ∀ x : Q0, x ^ 2 = 1) := by
  intro _hcenter
  have hsq : ∀ x : Q0, x ^ 2 = 1 := by
    intro x
    ext
    have hxQ0 : (x : G) ∈ Q0 := x.property
    rcases (hsec.Q0_def (x : G)).mp hxQ0 with hx_one | hx_inv
    · simp [hx_one]
    · simpa using hx_inv.2.sq_eq_one
  exact ⟨proposition_1_c_isMulCommutative_of_forall_sq_one hsq, hsq⟩

-- See PFchapter1section1/proposition_2_a.lean for why x : G can be converted to x : Q in the statement of this theorem.
public theorem proposition_1_c
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    (∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
        x ∈ Subgroup.center Q) ∧
      (IsMulCommutative Q0 ∧ ∀ x : Q0, x ^ 2 = 1) := by
  have hnil : Group.IsNilpotent Q :=
    proposition_1_b H D Q K V W Q0 S Q1 t hsec
  have hcenter :
      ∀ x : Q, (x : G) ∈ H → IsInvolution (x : G) →
        x ∈ Subgroup.center Q :=
    proposition_1_c_involutions_center_of_Q_nilpotent_obligation
      H D Q t hsec.hA.A1 hnil
  exact ⟨hcenter,
    proposition_1_c_Q0_elementary_of_centered_involutions_obligation
      H D Q K V W Q0 S Q1 t hsec hcenter⟩

end PFchapter1section2
end CFSG.BenderSuzuki
