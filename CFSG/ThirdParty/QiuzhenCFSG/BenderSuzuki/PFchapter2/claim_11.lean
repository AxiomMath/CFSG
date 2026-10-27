module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_10
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_9

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

universe u v

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open scoped Pointwise commutatorElement

/-!
# Peterfalvi, Part II, Chapter II, Claim (11)
-/

private lemma claim_11_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (K.map H.subtype : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

/-- A local Sylow subgroup is already ambient Sylow when every ambient
normalizer element remains in the local group. -/
public theorem claim_11_sylow_of_subgroupOf_sylow_of_normalizer_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    (P H : Subgroup G) (hPp : IsPGroup p P)
    (PH : Sylow p H) (hPH : (PH : Subgroup H) = P.subgroupOf H)
    (hnorm : Subgroup.normalizer (P : Set G) ≤ H) :
    ∃ PG : Sylow p G, (PG : Subgroup G) = P := by
  classical
  let PG : Sylow p G :=
    { toSubgroup := P
      isPGroup' := hPp
      is_maximal' := by
        intro Q hQ hPQ
        by_contra hQP
        have hnot_le : ¬ Q ≤ P := by
          intro hle
          exact hQP (le_antisymm hle hPQ)
        have hP_lt_Q : P < Q := ⟨hPQ, hnot_le⟩
        let PQ : Subgroup Q := P.subgroupOf Q
        have hPQ_lt_top : PQ < ⊤ := by
          refine ⟨le_top, ?_⟩
          intro htop
          apply hP_lt_Q.ne
          apply le_antisymm hPQ
          intro x hxQ
          let xQ : Q := ⟨x, hxQ⟩
          have hxPQ : xQ ∈ PQ := htop (by simp)
          simpa [PQ, Subgroup.mem_subgroupOf, xQ] using hxPQ
        have : Group.IsNilpotent Q :=
          IsPGroup.isNilpotent (p := p) (G := Q) hQ
        have hnc : NormalizerCondition Q :=
          Group.normalizerCondition_of_isNilpotent (G := Q)
        have hlt : PQ < Subgroup.normalizer (PQ : Set Q) :=
          hnc PQ hPQ_lt_top
        obtain ⟨xQ, hxNorm, hxNotPQ⟩ := SetLike.exists_of_lt hlt
        have hxNormG : (xQ : G) ∈ Subgroup.normalizer (P : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hyP
            let yQ : Q := ⟨y, hPQ hyP⟩
            have hyPQ : yQ ∈ PQ := hyP
            have hxy :=
              (Subgroup.mem_normalizer_iff.mp hxNorm yQ).1 hyPQ
            simpa [PQ, Subgroup.mem_subgroupOf, yQ, mul_assoc] using hxy
          · intro hconjP
            have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ Q := hPQ hconjP
            have hyQ : y ∈ Q := by
              have hmem := Q.mul_mem
                (Q.mul_mem (Q.inv_mem xQ.property) hconjQ) xQ.property
              simpa [mul_assoc] using hmem
            let yQ : Q := ⟨y, hyQ⟩
            have hconjPQ : xQ * yQ * xQ⁻¹ ∈ PQ := by
              simpa [PQ, Subgroup.mem_subgroupOf, yQ] using hconjP
            have hxy :=
              (Subgroup.mem_normalizer_iff.mp hxNorm yQ).2 hconjPQ
            simpa [PQ, Subgroup.mem_subgroupOf, yQ] using hxy
        have hxH : (xQ : G) ∈ H := hnorm hxNormG
        let QH : Subgroup H := Q.comap H.subtype
        have hQHp : IsPGroup p QH := IsPGroup.comap_subtype hQ
        have hPsub_le_QH : P.subgroupOf H ≤ QH := by
          intro x hxP
          exact hPQ hxP
        have hQH_eq : QH = P.subgroupOf H := by
          calc
            QH = (PH : Subgroup H) := PH.is_maximal' hQHp
              (by simpa [hPH] using hPsub_le_QH)
            _ = P.subgroupOf H := hPH
        have hxQH : (⟨(xQ : G), hxH⟩ : H) ∈ QH := xQ.property
        have hxP : (xQ : G) ∈ P := by
          rw [hQH_eq] at hxQH
          exact hxQH
        exact hxNotPQ hxP }
  exact ⟨PG, rfl⟩

private theorem claim_11_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnorm : B ≤ Subgroup.normalizer (A : Set G)) (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm]
      exact x.property
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem claim_11_rightConjugateElem_mul
    {G : Type*} [Group G] (x y c : G) :
    rightConjugateElem (x * y) c =
      rightConjugateElem x c * rightConjugateElem y c := by
  simp [rightConjugateElem, mul_assoc]

private theorem claim_11_rightConjugateElem_mem_T_of_CQ
    {G : Type*} [Group G] (Q T P : Subgroup G)
    (hCQnorm :
      (Q ⊓ Subgroup.centralizer (P : Set G)) ≤ Subgroup.normalizer (T : Set G))
    {x c : G} (hxT : x ∈ T)
    (hcCQ : c ∈ Q ⊓ Subgroup.centralizer (P : Set G)) :
    rightConjugateElem x c ∈ T := by
  have hcNorm : c ∈ Subgroup.normalizer (T : Set G) := hCQnorm hcCQ
  have hcInvNorm : c⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem hcNorm
  have hx : c⁻¹ * x * (c⁻¹)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hcInvNorm x).1 hxT
  simpa [rightConjugateElem, mul_assoc] using hx

private theorem claim_11_rightConjugateElem_of_mem_P_of_CQ
    {G : Type*} [Group G] (Q P : Subgroup G)
    {x c : G} (hxP : x ∈ P)
    (hcCQ : c ∈ Q ⊓ Subgroup.centralizer (P : Set G)) :
    rightConjugateElem x c = x := by
  have hcC : c ∈ Subgroup.centralizer (P : Set G) := hcCQ.2
  have hcomm : x * c = c * x :=
    (Subgroup.mem_centralizer_iff.mp hcC) x hxP
  calc
    rightConjugateElem x c = c⁻¹ * x * c := rfl
    _ = c⁻¹ * (x * c) := by simp [mul_assoc]
    _ = c⁻¹ * (c * x) := by rw [hcomm]
    _ = x := by simp

private theorem claim_11_rightConjugateElem_mul_T_P_of_CQ
    {G : Type*} [Group G] (Q T P : Subgroup G)
    {x y c : G} (_hxT : x ∈ T) (hyP : y ∈ P)
    (hcCQ : c ∈ Q ⊓ Subgroup.centralizer (P : Set G)) :
    rightConjugateElem (x * y) c =
      rightConjugateElem x c * y := by
  rw [claim_11_rightConjugateElem_mul]
  rw [claim_11_rightConjugateElem_of_mem_P_of_CQ Q P hyP hcCQ]

private theorem claim_11_rightConjugate_closure_singleton
    {G : Type*} [Group G] (x c : G) :
    rightConjugate (Subgroup.closure ({x} : Set G)) c =
      Subgroup.closure ({rightConjugateElem x c} : Set G) := by
  rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_closure]
  congr 1
  ext y
  simp [rightConjugateElem]

private theorem claim_11_rightConjugate_closure_mul_T_P_of_CQ
    {G : Type*} [Group G] (Q T P : Subgroup G)
    {x y c : G} (hxT : x ∈ T) (hyP : y ∈ P)
    (hcCQ : c ∈ Q ⊓ Subgroup.centralizer (P : Set G)) :
    rightConjugate (Subgroup.closure ({x * y} : Set G)) c =
      Subgroup.closure ({rightConjugateElem x c * y} : Set G) := by
  rw [claim_11_rightConjugate_closure_singleton]
  rw [claim_11_rightConjugateElem_mul_T_P_of_CQ Q T P hxT hyP hcCQ]


private theorem claim_11_rightConjugateElem_eq_one_iff
    {G : Type*} [Group G] (x c : G) :
    rightConjugateElem x c = 1 ↔ x = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun y : G => c * y * c⁻¹) h
    simpa [rightConjugateElem, mul_assoc] using h'
  · intro h
    simp [rightConjugateElem, h]

private theorem claim_11_exists_nontrivial_mem_of_subgroup_ne_bot
    {G : Type*} [Group G] (A : Subgroup G) (hA : A ≠ ⊥) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 := by
  by_contra hnone
  apply hA
  apply le_antisymm
  · intro x hxA
    have hx1 : x = 1 := by
      by_contra hxne
      exact hnone ⟨x, hxA, hxne⟩
    simp [hx1]
  · exact bot_le

private theorem claim_11_subgroup_ne_bot_of_prime_card
    {G : Type*} [Group G] (A : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p) :
    A ≠ ⊥ := by
  intro hA
  have hcard : Nat.card A = 1 := by
    simp [hA, Nat.card]
  exact hp.ne_one (hAcard ▸ hcard)

private theorem claim_11_exists_nontrivial_mem_of_prime_card
    {G : Type*} [Group G] (A : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 := by
  exact
    claim_11_exists_nontrivial_mem_of_subgroup_ne_bot A
      (claim_11_subgroup_ne_bot_of_prime_card A hp hAcard)

private theorem claim_11_P_le_normalizer_T_of_central
    {G : Type*} [Group G] (T P : Subgroup G)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G)) :
    P ≤ Subgroup.normalizer (T : Set G) := by
  intro y hyP
  have hyC : y ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxT
    exact ((Subgroup.mem_centralizer_iff.mp (hTcentral hxT)) y hyP).symm
  exact centralizer_le_normalizer T hyC

private theorem claim_11_mem_R_decompose_TP
    {G : Type*} [Group G] (P R T : Subgroup G)
    (hR : R = T ⊔ P)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    {x : G} (hxR : x ∈ R) :
    ∃ t : G, t ∈ T ∧ ∃ u : G, u ∈ P ∧ t * u = x := by
  have hPnormT : P ≤ Subgroup.normalizer (T : Set G) :=
    claim_11_P_le_normalizer_T_of_central T P hTcentral
  have hsupNormT : T ⊔ P ≤ Subgroup.normalizer (T : Set G) :=
    sup_le Subgroup.le_normalizer hPnormT
  let : (T.subgroupOf (T ⊔ P : Subgroup G)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := T ⊔ P) (N := T) hsupNormT
  let xTP : ↥(T ⊔ P : Subgroup G) := ⟨x, by simpa [hR] using hxR⟩
  have hsub_sup :
      T.subgroupOf (T ⊔ P : Subgroup G) ⊔
          P.subgroupOf (T ⊔ P : Subgroup G) = ⊤ := by
    have hsub :
        (T ⊔ P : Subgroup G).subgroupOf (T ⊔ P : Subgroup G) =
          T.subgroupOf (T ⊔ P : Subgroup G) ⊔
            P.subgroupOf (T ⊔ P : Subgroup G) :=
      Subgroup.subgroupOf_sup (A := T) (A' := P) (B := T ⊔ P)
        le_sup_left le_sup_right
    rw [← hsub]
    simp
  have hx_sup :
      xTP ∈ T.subgroupOf (T ⊔ P : Subgroup G) ⊔
        P.subgroupOf (T ⊔ P : Subgroup G) := by
    rw [hsub_sup]
    exact (show xTP ∈ (⊤ : Subgroup ↥(T ⊔ P : Subgroup G)) from by simp)
  rcases
      (Subgroup.mem_sup_of_normal_left
        (s := T.subgroupOf (T ⊔ P : Subgroup G))
        (t := P.subgroupOf (T ⊔ P : Subgroup G)) (x := xTP)).1 hx_sup with
    ⟨tTP, htT, uTP, huP, htu⟩
  exact
    ⟨(tTP : G), htT, (uTP : G), huP,
      by simpa [xTP] using congrArg Subtype.val htu⟩

private theorem claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p)
    {x : G} (hxA : x ∈ A) (hxne : x ≠ 1) :
    A = Subgroup.closure ({x} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hAcard' : Nat.card A = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hAcard
  apply le_antisymm
  · intro y hyA
    let xA : A := ⟨x, hxA⟩
    let yA : A := ⟨y, hyA⟩
    have hxA_ne : xA ≠ 1 := by
      intro h
      exact hxne (congrArg Subtype.val h)
    have hy_zpow : yA ∈ Subgroup.zpowers xA :=
      mem_zpowers_of_prime_card (G := A) hAcard' hxA_ne
    rcases Subgroup.mem_zpowers_iff.mp hy_zpow with ⟨n, hn⟩
    have hy_eq : x ^ n = y := by
      simpa [xA, yA] using congrArg Subtype.val hn
    have hx_closure : x ∈ Subgroup.closure ({x} : Set G) :=
      Subgroup.subset_closure (by simp)
    simpa [← hy_eq] using
      (Subgroup.closure ({x} : Set G)).zpow_mem hx_closure n
  · rw [← Subgroup.zpowers_eq_closure]
    exact Subgroup.zpowers_le.mpr hxA

private theorem claim_11_prime_card_subgroups_eq_of_common_nontrivial
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p)
    (hBcard : Nat.card B = p)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hxne : x ≠ 1) :
    A = B := by
  calc
    A = Subgroup.closure ({x} : Set G) :=
      claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one A hp hAcard hxA hxne
    _ = B :=
      (claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one B hp hBcard hxB hxne).symm

private theorem claim_11_T_factor_ne_one
    {G : Type*} [Group G] [Finite G] (P T A : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hAcard : Nat.card A = p) (hAneP : A ≠ P)
    {a x y : G} (haA : a ∈ A) (haT : a ∉ T)
    (_hxT : x ∈ T) (hyP : y ∈ P) (hxy : x * y = a) :
    x ≠ 1 := by
  intro hx1
  have haP : a ∈ P := by
    have hy_eq : y = a := by
      simpa [hx1] using hxy
    simpa [← hy_eq] using hyP
  have hane : a ≠ 1 := by
    intro ha1
    exact haT (by simp [ha1])
  exact
    hAneP
      (claim_11_prime_card_subgroups_eq_of_common_nontrivial
        A P hp hAcard hPcard haA haP hane)

private theorem claim_11_order_p_subgroup_graph_generator_exists
    {G : Type*} [Group G] [Finite G]
    (P R T A : Subgroup G) (p : ℕ)
    (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hR : R = T ⊔ P)
    (hdisj : Disjoint T P)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (hA : A ≤ R) (hAcard : Nat.card A = p)
    (hAnotT : ¬ A ≤ T) (hAneP : A ≠ P) :
    ∀ y : G, y ∈ P → y ≠ 1 →
      ∃ x : G,
        x ∈ T ∧ x ≠ 1 ∧
          A = Subgroup.closure ({x * y} : Set G) := by
  intro y hyP hyne
  have hnot : ∃ a : G, a ∈ A ∧ a ∉ T := by
    by_contra hnone
    apply hAnotT
    intro a haA
    by_contra haT
    exact hnone ⟨a, haA, haT⟩
  rcases hnot with ⟨a, haA, haT⟩
  rcases claim_11_mem_R_decompose_TP P R T hR hTcentral (hA haA) with
    ⟨t, htT, u, huP, htu⟩
  have htne : t ≠ 1 :=
    claim_11_T_factor_ne_one P T A hp hPcard hAcard hAneP haA haT htT huP htu
  have hune : u ≠ 1 := by
    intro hu1
    have ha_eq_t : a = t := by
      simpa [hu1] using htu.symm
    exact haT (by simpa [ha_eq_t] using htT)
  have hPcard' : Nat.card P = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hPcard
  let uP : P := ⟨u, huP⟩
  let yP : P := ⟨y, hyP⟩
  have huP_ne : uP ≠ 1 := by
    intro h
    exact hune (congrArg Subtype.val h)
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hy_zpow : yP ∈ Subgroup.zpowers uP :=
    mem_zpowers_of_prime_card (G := P) hPcard' huP_ne
  rcases Subgroup.mem_zpowers_iff.mp hy_zpow with ⟨n, hn⟩
  have hy_eq : u ^ n = y := by
    simpa [uP, yP] using congrArg Subtype.val hn
  let x : G := t ^ n
  have hxT : x ∈ T := T.zpow_mem htT n
  have htu_comm : Commute t u := by
    have hcomm : u * t = t * u :=
      (Subgroup.mem_centralizer_iff.mp (hTcentral htT)) u huP
    exact hcomm.symm
  have hxy_eq : x * y = a ^ n := by
    calc
      x * y = t ^ n * y := rfl
      _ = t ^ n * u ^ n := by rw [hy_eq]
      _ = (t * u) ^ n := (htu_comm.mul_zpow n).symm
      _ = a ^ n := by rw [htu]
  have hxyA : x * y ∈ A := by
    rw [hxy_eq]
    exact A.zpow_mem haA n
  have hxne : x ≠ 1 := by
    intro hx1
    have hyA : y ∈ A := by
      have hxy_y : x * y = y := by simp [hx1]
      simpa [hxy_y] using hxyA
    exact
      hAneP
        (claim_11_prime_card_subgroups_eq_of_common_nontrivial
          A P hp hAcard hPcard hyA hyP hyne)
  have hxyne : x * y ≠ 1 := by
    intro hxy1
    have hx_eq_yinv : x = y⁻¹ := by
      calc
        x = x * 1 := by simp
        _ = x * (y * y⁻¹) := by simp
        _ = (x * y) * y⁻¹ := by simp [mul_assoc]
        _ = y⁻¹ := by rw [hxy1]; simp
    have hxP : x ∈ P := by
      rw [hx_eq_yinv]
      exact P.inv_mem hyP
    have hx_one : x = 1 := by
      simpa using hdisj.le_bot ⟨hxT, hxP⟩
    exact hxne hx_one
  exact
    ⟨x, hxT, hxne,
      claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one A hp hAcard hxyA hxyne⟩

private theorem claim_11_order_p_subgroup_graph_generator_unique
    {G : Type*} [Group G] [Finite G]
    (P R T A : Subgroup G) (p : ℕ)
    (hp : Nat.Prime p) (_hPcard : Nat.card P = p)
    (_hR : R = T ⊔ P)
    (_hdisj : Disjoint T P)
    (_hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (_hA : A ≤ R) (hAcard : Nat.card A = p)
    (hAnotT : ¬ A ≤ T) (_hAneP : A ≠ P) :
    ∀ y : G, y ∈ P → y ≠ 1 →
      ∀ x z : G,
        x ∈ T ∧ x ≠ 1 ∧ A = Subgroup.closure ({x * y} : Set G) →
          z ∈ T ∧ z ≠ 1 ∧ A = Subgroup.closure ({z * y} : Set G) →
            x = z := by
  intro y _hyP _hyne x z hx hz
  rcases hx with ⟨hxT, _hxne, hA_x⟩
  rcases hz with ⟨hzT, _hzne, hA_z⟩
  have hA_inf_T_le_bot : A ⊓ T ≤ ⊥ := by
    intro a ha
    by_cases ha_one : a = 1
    · simp [ha_one]
    · have hA_eq :
          A = Subgroup.closure ({a} : Set G) :=
        claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one
          A hp hAcard ha.1 ha_one
      have hclosure_le_T : Subgroup.closure ({a} : Set G) ≤ T := by
        refine (Subgroup.closure_le (K := T)).2 ?_
        intro b hb
        simp at hb
        simpa [hb] using ha.2
      exact False.elim (hAnotT (by rw [hA_eq]; exact hclosure_le_T))
  have hxA : x * y ∈ A := by
    rw [hA_x]
    exact Subgroup.subset_closure (by simp)
  have hzA : z * y ∈ A := by
    rw [hA_z]
    exact Subgroup.subset_closure (by simp)
  have hquotA : (x * y) * (z * y)⁻¹ ∈ A :=
    A.mul_mem hxA (A.inv_mem hzA)
  have hquot_eq : (x * y) * (z * y)⁻¹ = x * z⁻¹ := by
    simp [mul_assoc]
  have hxzA : x * z⁻¹ ∈ A := by
    simpa [hquot_eq] using hquotA
  have hxzT : x * z⁻¹ ∈ T := T.mul_mem hxT (T.inv_mem hzT)
  have hxz_one : x * z⁻¹ = 1 := by
    have hbot : x * z⁻¹ ∈ (⊥ : Subgroup G) :=
      hA_inf_T_le_bot ⟨hxzA, hxzT⟩
    simpa using hbot
  calc
    x = (x * z⁻¹) * z := by simp [mul_assoc]
    _ = z := by simp [hxz_one]

private theorem claim_11_order_p_subgroup_graph_generator
    {G : Type*} [Group G] [Finite G]
    (P R T A : Subgroup G) (p : ℕ)
    (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hR : R = T ⊔ P)
    (hdisj : Disjoint T P)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (hA : A ≤ R) (hAcard : Nat.card A = p)
    (hAnotT : ¬ A ≤ T) (hAneP : A ≠ P) :
    ∀ y : G, y ∈ P → y ≠ 1 →
      ∃! x : G,
        x ∈ T ∧ x ≠ 1 ∧
          A = Subgroup.closure ({x * y} : Set G) := by
  intro y hyP hyne
  rcases
      claim_11_order_p_subgroup_graph_generator_exists
        P R T A p hp hPcard hR hdisj hTcentral hA hAcard hAnotT hAneP
        y hyP hyne with
    ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact
    (claim_11_order_p_subgroup_graph_generator_unique
      P R T A p hp hPcard hR hdisj hTcentral hA hAcard hAnotT hAneP
      y hyP hyne z x hz hx)

theorem claim_11_order_p_subgroups_regular
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P R T : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hR : R = T ⊔ P)
    (hdisj : Disjoint T P)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (_hNorm :
      (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
        W ⊓ Subgroup.centralizer (P : Set G)) ≤
          Subgroup.normalizer (T : Set G))
    (_hDisjCQ : Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)))
    (hCQnorm :
      (Q ⊓ Subgroup.centralizer (P : Set G)) ≤ Subgroup.normalizer (T : Set G))
    (hTregular :
      ∀ x y : G, x ∈ T → y ∈ T → x ≠ 1 → y ≠ 1 →
        ∃! c : G,
          c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
            rightConjugateElem x c = y) :
    ∀ A B : Subgroup G,
      A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
        ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
          ∃! c : G,
            c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
              B = rightConjugate A c := by
  intro A B hA hB hAcard hBcard hAnotT hBnotT hAneP hBneP
  rcases
      claim_11_exists_nontrivial_mem_of_prime_card P hch.B1.p_prime hch.B1.P_card with
    ⟨y, hyP, hyne⟩
  rcases
      claim_11_order_p_subgroup_graph_generator
        P R T A p hch.B1.p_prime hch.B1.P_card hR hdisj hTcentral
        hA hAcard hAnotT hAneP y hyP hyne with
    ⟨x, hx_graph, hx_unique⟩
  rcases hx_graph with ⟨hxT, hxne, hAgraph⟩
  rcases
      claim_11_order_p_subgroup_graph_generator
        P R T B p hch.B1.p_prime hch.B1.P_card hR hdisj hTcentral
        hB hBcard hBnotT hBneP y hyP hyne with
    ⟨z, hz_graph, hz_unique⟩
  rcases hz_graph with ⟨hzT, hzne, hBgraph⟩
  rcases hTregular x z hxT hzT hxne hzne with
    ⟨c, hc, hc_unique⟩
  rcases hc with ⟨hcCQ, hcx⟩
  refine ⟨c, ?_, ?_⟩
  · refine ⟨hcCQ, ?_⟩
    have hconj :
        rightConjugate A c =
          Subgroup.closure ({z * y} : Set G) := by
      calc
        rightConjugate A c =
            rightConjugate (Subgroup.closure ({x * y} : Set G)) c := by
              rw [hAgraph]
        _ = Subgroup.closure ({rightConjugateElem x c * y} : Set G) :=
              claim_11_rightConjugate_closure_mul_T_P_of_CQ
                Q T P hxT hyP hcCQ
        _ = Subgroup.closure ({z * y} : Set G) := by
              rw [hcx]
    exact hBgraph.trans hconj.symm
  · intro d hd
    rcases hd with ⟨hdCQ, hdB⟩
    have hdxT : rightConjugateElem x d ∈ T :=
      claim_11_rightConjugateElem_mem_T_of_CQ Q T P hCQnorm hxT hdCQ
    have hdxne : rightConjugateElem x d ≠ 1 := by
      intro hdx
      exact hxne ((claim_11_rightConjugateElem_eq_one_iff x d).mp hdx)
    have hd_graph :
        B = Subgroup.closure ({rightConjugateElem x d * y} : Set G) := by
      calc
        B = rightConjugate A d := hdB
        _ = rightConjugate (Subgroup.closure ({x * y} : Set G)) d := by
              rw [hAgraph]
        _ = Subgroup.closure ({rightConjugateElem x d * y} : Set G) :=
              claim_11_rightConjugate_closure_mul_T_P_of_CQ
                Q T P hxT hyP hdCQ
    have hdx_eq_z : rightConjugateElem x d = z :=
      hz_unique (rightConjugateElem x d) ⟨hdxT, hdxne, hd_graph⟩
    exact hc_unique d ⟨hdCQ, hdx_eq_z⟩
/-- The explicit near-field coordinates make the unit factor act regularly on
nonidentity elements of the additive factor. -/
private theorem claim_11_T_regular_nonzero_of_nearField_coordinates
    {G : Type*} {F : Type v} [Group G] [PFAppendixII.RightNearField F]
    (Q P T : Subgroup G)
    (addEquiv : Multiplicative F ≃* T)
    (unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinate : ∀ a : F, ∀ b : Fˣ,
      rightConjugateElem
          (((addEquiv (Multiplicative.ofAdd a) : T) : G))
          (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) =
        (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G))) :
    ∀ x y : G, x ∈ T → y ∈ T → x ≠ 1 → y ≠ 1 →
      ∃! c : G,
        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          rightConjugateElem x c = y := by
  intro x y hxT hyT hxne hyne
  let xT : T := ⟨x, hxT⟩
  let yT : T := ⟨y, hyT⟩
  let a : F := Multiplicative.toAdd (addEquiv.symm xT)
  let z : F := Multiplicative.toAdd (addEquiv.symm yT)
  have haCoord :
      (((addEquiv (Multiplicative.ofAdd a) : T) : G)) = x := by
    simp [a, xT]
  have hzCoord :
      (((addEquiv (Multiplicative.ofAdd z) : T) : G)) = y := by
    simp [z, yT]
  have ha : a ≠ 0 := by
    intro ha0
    apply hxne
    rw [← haCoord, ha0]
    simp
  have hz : z ≠ 0 := by
    intro hz0
    apply hyne
    rw [← hzCoord, hz0]
    simp
  let b : Fˣ := Units.mk0 (a⁻¹ * z) (mul_ne_zero (inv_ne_zero ha) hz)
  let c : G := ((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)
  have hcCQ : c ∈ Q ⊓ Subgroup.centralizer (P : Set G) :=
    (unitEquiv b).property
  have hab : a * (b : F) = z := by
    simp [b, ha]
  have hcValue : rightConjugateElem x c = y := by
    calc
      rightConjugateElem x c =
          rightConjugateElem
            (((addEquiv (Multiplicative.ofAdd a) : T) : G))
            (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := by
              rw [haCoord]
      _ = (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G)) :=
        hcoordinate a b
      _ = (((addEquiv (Multiplicative.ofAdd z) : T) : G)) := by rw [hab]
      _ = y := hzCoord
  refine ⟨c, ⟨hcCQ, hcValue⟩, ?_⟩
  intro d hd
  rcases hd with ⟨hdCQ, hdValue⟩
  let dCQ : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := ⟨d, hdCQ⟩
  let bd : Fˣ := unitEquiv.symm dCQ
  have hbdCoord :
      (((unitEquiv bd : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) = d := by
    simp [bd, dCQ]
  have haddEq :
      (((addEquiv (Multiplicative.ofAdd (a * (bd : F))) : T) : G)) =
        (((addEquiv (Multiplicative.ofAdd z) : T) : G)) := by
    calc
      (((addEquiv (Multiplicative.ofAdd (a * (bd : F))) : T) : G)) =
          rightConjugateElem
            (((addEquiv (Multiplicative.ofAdd a) : T) : G))
            (((unitEquiv bd : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) :=
        (hcoordinate a bd).symm
      _ = rightConjugateElem x d := by rw [haCoord, hbdCoord]
      _ = y := hdValue
      _ = (((addEquiv (Multiplicative.ofAdd z) : T) : G)) := hzCoord.symm
  have hmul : a * (bd : F) = z := by
    have hsubtype :
        addEquiv (Multiplicative.ofAdd (a * (bd : F))) =
          addEquiv (Multiplicative.ofAdd z) := by
      apply Subtype.ext
      exact haddEq
    have hmultiplicative :
        Multiplicative.ofAdd (a * (bd : F)) = Multiplicative.ofAdd z :=
      addEquiv.injective hsubtype
    exact congrArg Multiplicative.toAdd hmultiplicative
  have hbd : bd = b := by
    apply Units.ext
    change (bd : F) = a⁻¹ * z
    calc
      (bd : F) = a⁻¹ * (a * (bd : F)) := by simp [ha]
      _ = a⁻¹ * z := by rw [hmul]
  calc
    d = (((unitEquiv bd : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) :=
      hbdCoord.symm
    _ = (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := by
      rw [hbd]
    _ = c := rfl
private theorem claim_11_mem_T_of_mem_R_of_inverted
    {G : Type*} [Group G] [Finite G]
    (R P T : Subgroup G) (s : G)
    (hRcomm : IsMulCommutative R)
    (hRodd : Odd (Nat.card R))
    (hsI : IsInvolution s)
    (hR : R = T ⊔ P)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (hfixed : subgroupCentralizerIn R (Subgroup.zpowers s) = P)
    (hTinverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    {x : G} (hxR : x ∈ R)
    (hxinv : rightConjugateElem x s = x⁻¹) :
    x ∈ T := by
  rcases claim_11_mem_R_decompose_TP P R T hR hTcentral hxR with
    ⟨a, haT, u, huP, hau⟩
  have hP_le_R : P ≤ R := by
    rw [hR]
    exact le_sup_right
  have huR : u ∈ R := hP_le_R huP
  have huCent : u ∈ subgroupCentralizerIn R (Subgroup.zpowers s) := by
    rw [hfixed]
    exact huP
  have hsu : s * u = u * s :=
    (Subgroup.mem_centralizer_iff.mp huCent.2) s (Subgroup.mem_zpowers s)
  have hsInv : s⁻¹ = s := by
    have hsMul : s * s = 1 := by
      simpa only [pow_two] using hsI.sq_eq_one
    exact (eq_inv_of_mul_eq_one_right hsMul).symm
  have huFixed : rightConjugateElem u s = u := by
    calc
      rightConjugateElem u s = s⁻¹ * u * s := rfl
      _ = s * u * s := by rw [hsInv]
      _ = u * s * s := by rw [hsu]
      _ = u := by simp [mul_assoc, ← pow_two, hsI.sq_eq_one]
  have hxCoord : rightConjugateElem x s = a⁻¹ * u := by
    calc
      rightConjugateElem x s = rightConjugateElem (a * u) s := by rw [hau]
      _ = rightConjugateElem a s * rightConjugateElem u s := by
        simp [rightConjugateElem, mul_assoc]
      _ = a⁻¹ * u := by rw [hTinverted a haT, huFixed]
  have haR : a ∈ R := by
    rw [hR]
    exact Subgroup.mem_sup_left haT
  let aR : R := ⟨a, haR⟩
  let uR : R := ⟨u, huR⟩
  have hauComm : a * u = u * a := by
    simpa [aR, uR] using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := R)).comm aR uR)
  have huuInv : u = u⁻¹ := by
    apply mul_left_cancel (a := a⁻¹)
    calc
      a⁻¹ * u = rightConjugateElem x s := hxCoord.symm
      _ = x⁻¹ := hxinv
      _ = (a * u)⁻¹ := by rw [hau]
      _ = u⁻¹ * a⁻¹ := mul_inv_rev a u
      _ = a⁻¹ * u⁻¹ := by
        simpa using congrArg Inv.inv hauComm
  have huOne : u = 1 := by
    by_contra huNe
    have huI : IsInvolution u := by
      refine ⟨huNe, ?_⟩
      calc
        u ^ 2 = u * u := pow_two u
        _ = u * u⁻¹ := congrArg (fun z : G => u * z) huuInv
        _ = 1 := mul_inv_cancel u
    exact (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup R hRodd huR) huI
  have ha_eq : a = x := by
    simpa [huOne] using hau
  simpa [← ha_eq] using haT

private theorem claim_11_disjoint_T_CQ_of_coordinates
    {G F : Type*} [Group G]
    [PFAppendixII.RightNearField F]
    (Q P R T : Subgroup G)
    (hT_le_R : T ≤ R)
    (hRcomm : IsMulCommutative R)
    (addEquiv : Multiplicative F ≃* ↥T)
    (unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinate :
      ∀ a : F, ∀ b : Fˣ,
        rightConjugateElem
            (((addEquiv (Multiplicative.ofAdd a) : T) : G))
            (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) =
          (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G))) :
    Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) := by
  rw [Subgroup.disjoint_def]
  intro x hxT hxCQ
  let b : Fˣ := unitEquiv.symm ⟨x, hxCQ⟩
  have hxb :
      (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) = x := by
    simp [b]
  let y : G := ((addEquiv (Multiplicative.ofAdd (1 : F)) : T) : G)
  have hyT : y ∈ T := (addEquiv (Multiplicative.ofAdd (1 : F))).property
  let xR : R := ⟨x, hT_le_R hxT⟩
  let yR : R := ⟨y, hT_le_R hyT⟩
  have hcommR : xR * yR = yR * xR :=
    (IsMulCommutative.is_comm (M := R)).comm xR yR
  have hcomm : x * y = y * x := by
    simpa [xR, yR] using congrArg Subtype.val hcommR
  have hfixed : rightConjugateElem y x = y := by
    calc
      rightConjugateElem y x = x⁻¹ * y * x := rfl
      _ = x⁻¹ * (y * x) := by simp [mul_assoc]
      _ = x⁻¹ * (x * y) := by rw [← hcomm]
      _ = y := by simp
  have haddEq :
      (((addEquiv (Multiplicative.ofAdd (1 : F)) : T) : G)) =
        (((addEquiv (Multiplicative.ofAdd (b : F)) : T) : G)) := by
    calc
      (((addEquiv (Multiplicative.ofAdd (1 : F)) : T) : G)) = y := rfl
      _ = rightConjugateElem y x := hfixed.symm
      _ = rightConjugateElem y
          (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := by rw [hxb]
      _ = (((addEquiv (Multiplicative.ofAdd ((1 : F) * (b : F))) : T) : G)) :=
        hcoordinate 1 b
      _ = (((addEquiv (Multiplicative.ofAdd (b : F)) : T) : G)) := by simp
  have hsubtype :
      addEquiv (Multiplicative.ofAdd (1 : F)) =
        addEquiv (Multiplicative.ofAdd (b : F)) := by
    apply Subtype.ext
    exact haddEq
  have hmultiplicative :
      Multiplicative.ofAdd (1 : F) = Multiplicative.ofAdd (b : F) :=
    addEquiv.injective hsubtype
  have hbval : (b : F) = 1 := by
    simpa using (congrArg Multiplicative.toAdd hmultiplicative).symm
  have hb : b = 1 := Units.ext hbval
  calc
    x = (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := hxb.symm
    _ = (((unitEquiv 1 : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := by rw [hb]
    _ = 1 := by simp
private theorem claim_11_coprime_involution_decomposition
    {G : Type*} [Group G] [Finite G]
    (R P : Subgroup G) (s : G)
    (hRcomm : IsMulCommutative R)
    (hRodd : Odd (Nat.card R))
    (hsI : IsInvolution s)
    (hs_norm_R : s ∈ Subgroup.normalizer (R : Set G))
    (hP_le_R : P ≤ R)
    (hfixed : subgroupCentralizerIn R (Subgroup.zpowers s) = P) :
    let T : Subgroup G := ⁅R, Subgroup.zpowers s⁆
    R = T ⊔ P ∧ Disjoint T P ∧
      ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹ := by
  classical
  dsimp only
  let A : Subgroup G := Subgroup.zpowers s
  have hA_norm_R : A ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hs_norm_R
  let : Subgroup.Normalizes A R := ⟨hA_norm_R⟩
  let Cfix : Subgroup R := fixedPointSubgroup (↥A) (↥R)
  let Ccomm : Subgroup R := commutatorAction (A := ↥A) (G := ↥R)
  let T : Subgroup G := ⁅R, A⁆
  have hcomm_map : Ccomm.map R.subtype = T := by
    simpa [Ccomm, T] using
      commutatorAction_subgroup_conj_map_eq_commutator R A hA_norm_R
  have hfixed_eq :
      Cfix = P.subgroupOf R := by
    calc
      Cfix = (subgroupCentralizerIn R A).subgroupOf R := by
        simpa [Cfix] using
          fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R A hA_norm_R
      _ = P.subgroupOf R := by rw [hfixed]
  have hs_order : orderOf s = 2 :=
    (orderOf_eq_prime_iff.mpr ⟨hsI.sq_eq_one, hsI.ne_one⟩)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    rw [Nat.card_zpowers, hs_order]
    exact hRodd.coprime_two_left
  have hsolvR : Group.IsSolvable R := by
    let : IsMulCommutative R := hRcomm
    exact Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  have hcompl : IsCompl Cfix Ccomm := by
    simpa [Cfix, Ccomm] using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := R) (A := A) hsolvR hcop hRcomm)
  have hmap_top : (⊤ : Subgroup R).map R.subtype = R := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := R))
  have hR_decomp : R = T ⊔ P := by
    calc
      R = (⊤ : Subgroup R).map R.subtype := hmap_top.symm
      _ = (Cfix ⊔ Ccomm).map R.subtype := by rw [hcompl.codisjoint.eq_top]
      _ = Cfix.map R.subtype ⊔ T := by rw [Subgroup.map_sup, hcomm_map]
      _ = P ⊔ T := by
        rw [hfixed_eq, Subgroup.map_subgroupOf_eq_of_le hP_le_R]
      _ = T ⊔ P := sup_comm P T
  have hdisj : Disjoint T P := by
    have hmapped : Disjoint (Cfix.map R.subtype) (Ccomm.map R.subtype) :=
      Subgroup.disjoint_map R.subtype_injective hcompl.disjoint
    have hPT : Disjoint P T := by
      simpa [hfixed_eq, Subgroup.map_subgroupOf_eq_of_le hP_le_R, hcomm_map] using hmapped
    exact hPT.symm
  refine ⟨hR_decomp, hdisj, ?_⟩
  intro x hxT
  change x ∈ T at hxT
  rw [← hcomm_map] at hxT
  rcases Subgroup.mem_map.mp hxT with ⟨xR, hxComm, hxval⟩
  let sA : A := ⟨s, Subgroup.mem_zpowers s⟩
  have hsA_sq : sA * sA = 1 := by
    apply Subtype.ext
    change s * s = 1
    simpa only [pow_two] using hsI.sq_eq_one
  let : IsMulCommutative R := hRcomm
  have : IsInvariant A R Ccomm := commutatorAction_isInvariant
  let y : R := xR * (sA • xR)
  have hyComm : y ∈ Ccomm := by
    exact Ccomm.mul_mem hxComm ((IsInvariant.invariant sA xR).mp hxComm)
  have hyGen : sA • y = y := by
    simp only [y, smul_mul', smul_smul, hsA_sq, one_smul]
    exact mul_comm' _ _
  have hyFix : y ∈ Cfix := by
    change ∀ a : A, a • y = y
    intro a
    apply smul_eq_self_of_mem_zpowers (y := sA) _ hyGen
    rcases Subgroup.mem_zpowers_iff.mp a.property with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
  have hyBot : y ∈ (⊥ : Subgroup R) :=
    (Subgroup.disjoint_def.mp hcompl.disjoint) hyFix hyComm
  have hyOne : y = 1 := Subgroup.mem_bot.mp hyBot
  have hsAction : sA • xR = xR⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hyOne
  have hsInv : s⁻¹ = s := by
    have hsMul : s * s = 1 := by
      simpa only [pow_two] using hsI.sq_eq_one
    exact (eq_inv_of_mul_eq_one_right hsMul).symm
  have hsActionG := congrArg Subtype.val hsAction
  change s * (xR : G) * s⁻¹ = (xR : G)⁻¹ at hsActionG
  subst x
  simpa [rightConjugateElem, hsInv] using hsActionG

private def claim_11_additiveHom
    {X F : Type*} [Group X] [PFAppendixII.RightNearField F]
    (addLift : F → X)
    (haddZero : addLift 0 = 1)
    (hadd : ∀ a b : F, addLift (a + b) = addLift a * addLift b) :
    Multiplicative F →* X where
  toFun a := addLift (Multiplicative.toAdd a)
  map_one' := by simpa using haddZero
  map_mul' a b := by
    simpa using hadd (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- Checked quotient-map equivalence on a subgroup disjoint from the quotient
kernel, retaining its pointwise quotient computation. -/
private theorem claim_11_quotientMap_subgroup_equiv_of_disjoint
    {X : Type*} [Group X] (N Q : Subgroup X) [N.Normal]
    (hdis : Disjoint Q N) :
    ∃ e : Q ≃* Q.map (QuotientGroup.mk' N),
      ∀ q : Q, (e q : X ⧸ N) = QuotientGroup.mk' N q := by
  let pi : X →* X ⧸ N := QuotientGroup.mk' N
  let f : Q →* Q.map pi :=
    (pi.domRestrict Q).codRestrict (Q.map pi) (fun q => ⟨q, q.2, rfl⟩)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hpi : pi (x : X) = pi (y : X) := by
      have hxy' := congrArg Subtype.val hxy
      change pi (x : X) = pi (y : X) at hxy'
      exact hxy'
    have hdivN : (x : X) / (y : X) ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp hpi
    have hdivQ : (x : X) / (y : X) ∈ Q := Q.div_mem x.2 y.2
    have hdivBot : (x : X) / (y : X) ∈ (⊥ : Subgroup X) :=
      (Subgroup.disjoint_def.mp hdis) hdivQ hdivN
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hf_surjective : Function.Surjective f := by
    intro z
    rcases z.2 with ⟨g, hgQ, hg⟩
    refine ⟨⟨g, hgQ⟩, ?_⟩
    apply Subtype.ext
    change pi g = (z : X ⧸ N)
    exact hg
  let e : Q ≃* Q.map pi := MulEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨e, ?_⟩
  intro q
  change pi (q : X) = (QuotientGroup.mk' N) (q : X)
  rfl

/-- Checked Proposition-One unit-coordinate equivalence, retaining the exact
underlying quotient coordinate. -/
private theorem claim_11_proposition_one_units_equiv
    {X F : Type*} [Group X] [PFAppendixII.RightNearField F]
    (D Q : Subgroup X)
    (addLift : F → X) (unitLift : Fˣ → X)
    (hcoordinates : Function.Bijective
      (fun z : F × Fˣ × D => addLift z.1 * unitLift z.2.1 * (z.2.2 : X)))
    (haddZero : addLift 0 = 1)
    (hunitOne : unitLift 1 = 1)
    (hunitMul : ∀ x y : Fˣ, unitLift (x * y) = unitLift x * unitLift y)
    (hunitRange : ∀ q : X, q ∈ Q ↔ ∃ x : Fˣ, unitLift x = q) :
    ∃ e : Fˣ ≃* Q, ∀ x : Fˣ, (e x : X) = unitLift x := by
  let unitHom : Fˣ →* X :=
    { toFun := unitLift
      map_one' := hunitOne
      map_mul' := hunitMul }
  have hunit_mem (x : Fˣ) : unitHom x ∈ Q :=
    (hunitRange (unitHom x)).2 ⟨x, rfl⟩
  let unitHomQ : Fˣ →* Q := unitHom.codRestrict Q hunit_mem
  have hunit_injective : Function.Injective unitHomQ := by
    intro x y hxy
    have hxyX : unitLift x = unitLift y := by
      simpa [unitHomQ, unitHom] using congrArg Subtype.val hxy
    let tx : F × Fˣ × D := (0, x, 1)
    let ty : F × Fˣ × D := (0, y, 1)
    have htriple : tx = ty := hcoordinates.1 (by
      simpa [tx, ty, haddZero] using hxyX)
    exact congrArg (fun z : F × Fˣ × D => z.2.1) htriple
  have hunit_surjective : Function.Surjective unitHomQ := by
    intro q
    rcases (hunitRange (q : X)).1 q.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa [unitHomQ, unitHom] using hx
  let e : Fˣ ≃* Q :=
    MulEquiv.ofBijective unitHomQ ⟨hunit_injective, hunit_surjective⟩
  refine ⟨e, ?_⟩
  intro x
  rfl

/-- Coordinate uniqueness forces an additive coordinate to vanish when the
same element has no additive factor. -/
private theorem claim_11_additive_coordinate_eq_zero_of_eq_unit_mul
    {X F : Type*} [Group X] [PFAppendixII.RightNearField F]
    (D : Subgroup X) (addLift : F → X) (unitLift : Fˣ → X)
    (hcoordinates : Function.Injective
      (fun z : F × Fˣ × D => addLift z.1 * unitLift z.2.1 * (z.2.2 : X)))
    (haddZero : addLift 0 = 1) (hunitOne : unitLift 1 = 1)
    {a : F} {u : Fˣ} {d : D}
    (h : addLift a = unitLift u * (d : X)) :
    a = 0 := by
  let zA : F × Fˣ × D := (a, 1, 1)
  let zH : F × Fˣ × D := (0, u, d)
  have htriple : zA = zH := hcoordinates (by
    dsimp [zA, zH]
    rw [haddZero, hunitOne, one_mul, mul_one]
    simp [h])
  exact congrArg (fun z : F × Fˣ × D => z.1) htriple

/-- The exact transfer conclusion needed for the characteristic computation. -/
private theorem chapter2_claim11_p_dvd_Q_card_succ
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    p ∣ Nat.card Q + 1 := by
  exact chapter2_transfer_p_dvd_Q_card_succ
    H D Q K V W Q0 S Q1 P t s p hch

/-- The additive quotient coordinate restricts to the coprime-action complement. -/
private theorem claim_11_additive_equiv_of_decomposition
    {G F : Type*} [Group G] [PFAppendixII.RightNearField F]
    (C : Subgroup G) (core : Subgroup C) [core.Normal]
    (P R T : Subgroup G)
    (addLift : F → C ⧸ core)
    (haddZero : addLift 0 = 1)
    (hadd : ∀ a b : F, addLift (a + b) = addLift a * addLift b)
    (hRdef :
      R = ((claim_11_additiveHom addLift haddZero hadd).range.comap
        (QuotientGroup.mk' core)).map C.subtype)
    (hcore : core = P.subgroupOf C)
    (hR : R = T ⊔ P)
    (hdisj : Disjoint T P)
    (hT_le_C : T ≤ C)
    (hP_le_C : P ≤ C)
    (hTcentral : T ≤ Subgroup.centralizer (P : Set G))
    (haddHom_injective : Function.Injective
      (claim_11_additiveHom addLift haddZero hadd)) :
    ∃ addEquiv : Multiplicative F ≃* T,
      ∀ a : F, ∃ c : C,
        (c : G) = ((addEquiv (Multiplicative.ofAdd a) : T) : G) ∧
        QuotientGroup.mk' core c = addLift a := by
  let addHom : Multiplicative F →* C ⧸ core :=
    claim_11_additiveHom addLift haddZero hadd
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  have hT_mem_preimage (x : T) :
      pi ⟨(x : G), hT_le_C x.property⟩ ∈ addHom.range := by
    have hxR : (x : G) ∈ R := by
      rw [hR]
      exact Subgroup.mem_sup_left x.property
    rw [hRdef] at hxR
    rcases hxR with ⟨c, hc, hcval⟩
    have hcEq : c = (⟨(x : G), hT_le_C x.property⟩ : C) := by
      apply Subtype.ext
      exact hcval
    change pi c ∈ addHom.range at hc
    simpa [hcEq] using hc
  let qT : T →* addHom.range :=
    { toFun := fun x => ⟨pi ⟨(x : G), hT_le_C x.property⟩, hT_mem_preimage x⟩
      map_one' := by
        apply Subtype.ext
        change pi (1 : C) = 1
        exact map_one pi
      map_mul' := by
        intro x y
        apply Subtype.ext
        change pi
            ((⟨(x : G), hT_le_C x.property⟩ : C) *
              ⟨(y : G), hT_le_C y.property⟩) =
          pi ⟨(x : G), hT_le_C x.property⟩ *
            pi ⟨(y : G), hT_le_C y.property⟩
        exact map_mul pi _ _ }
  have hqT_injective : Function.Injective qT := by
    intro x y hxy
    have hquot :
        pi ⟨(x : G), hT_le_C x.property⟩ =
          pi ⟨(y : G), hT_le_C y.property⟩ :=
      congrArg Subtype.val hxy
    have hdivCore :
        (⟨(x : G), hT_le_C x.property⟩ : C) /
            ⟨(y : G), hT_le_C y.property⟩ ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hquot
    have hdivP : (x : G) / (y : G) ∈ P := by
      rw [hcore] at hdivCore
      simpa [Subgroup.mem_subgroupOf] using hdivCore
    have hdivT : (x : G) / (y : G) ∈ T := by
      exact T.div_mem x.property y.property
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdisj) hdivT hdivP
    apply Subtype.ext
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hqT_surjective : Function.Surjective qT := by
    intro z
    rcases z.property with ⟨a, ha⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective core (addHom a)
    have hcPre : c ∈ addHom.range.comap pi := by
      change pi c ∈ addHom.range
      exact ⟨a, hc.symm⟩
    have hcR : (c : G) ∈ R := by
      rw [hRdef]
      exact ⟨c, hcPre, rfl⟩
    rcases claim_11_mem_R_decompose_TP P R T hR hTcentral hcR with
      ⟨t, htT, u, huP, htu⟩
    let tT : T := ⟨t, htT⟩
    let tC : C := ⟨t, hT_le_C htT⟩
    let uC : C := ⟨u, hP_le_C huP⟩
    have huCore : uC ∈ core := by
      rw [hcore]
      exact huP
    have huPi : pi uC = 1 :=
      (QuotientGroup.eq_one_iff uC).2 huCore
    have htc : tC * uC = c := by
      apply Subtype.ext
      exact htu
    refine ⟨tT, ?_⟩
    apply Subtype.ext
    change pi tC = (z : C ⧸ core)
    calc
      pi tC = pi tC * 1 := (mul_one _).symm
      _ = pi tC * pi uC := by rw [huPi]
      _ = pi (tC * uC) := (map_mul pi tC uC).symm
      _ = pi c := by rw [htc]
      _ = addHom a := hc
      _ = z := ha
  let eF : Multiplicative F ≃* addHom.range :=
    MulEquiv.ofBijective addHom.rangeRestrict
      ⟨(fun _ _ h => haddHom_injective (congrArg Subtype.val h)),
        addHom.rangeRestrict_surjective⟩
  let eT : T ≃* addHom.range :=
    MulEquiv.ofBijective qT ⟨hqT_injective, hqT_surjective⟩
  let addEquiv : Multiplicative F ≃* T := eF.trans eT.symm
  have hcompatible (a : F) :
      QuotientGroup.mk' core
          (⟨((addEquiv (Multiplicative.ofAdd a) : T) : G),
            hT_le_C (addEquiv (Multiplicative.ofAdd a)).property⟩ : C) =
        addLift a := by
    have hq :
        qT (addEquiv (Multiplicative.ofAdd a)) =
          eF (Multiplicative.ofAdd a) := by
      change qT ((MulEquiv.ofBijective qT ⟨hqT_injective, hqT_surjective⟩).symm
          (eF (Multiplicative.ofAdd a))) = eF (Multiplicative.ofAdd a)
      exact MulEquiv.ofBijective_apply_symm_apply qT
        ⟨hqT_injective, hqT_surjective⟩
    exact congrArg Subtype.val hq
  have hcompatible_additive_coordinates :
      ∃ addEquiv : Multiplicative F ≃* T,
        ∀ a : F,
          QuotientGroup.mk' core
              (⟨((addEquiv (Multiplicative.ofAdd a) : T) : G),
                hT_le_C (addEquiv (Multiplicative.ofAdd a)).property⟩ : C) =
            addLift a :=
    ⟨addEquiv, hcompatible⟩
  obtain ⟨addEquiv, hcompatible⟩ := hcompatible_additive_coordinates
  refine ⟨addEquiv, ?_⟩
  intro a
  let c : C :=
    ⟨((addEquiv (Multiplicative.ofAdd a) : T) : G),
      hT_le_C (addEquiv (Multiplicative.ofAdd a)).property⟩
  refine ⟨c, rfl, ?_⟩
  simpa [c] using hcompatible a

set_option maxHeartbeats 800000 in
public theorem claim_11
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL) :
    ∃ R T : Subgroup G,
      (R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c) ∧
        ∃ (N : Subgroup G) (F : Type v) (_ : PFAppendixII.RightNearField F)
            (_ : Finite F) (_ : Nontrivial F)
            (addEquiv : Multiplicative F ≃* ↥T)
            (unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G))),
          N = D ⊓
              Subgroup.centralizer
                ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
              Subgroup.centralizer (P : Set G) ∧
            R ≤ Subgroup.centralizer (P : Set G) ∧
              (∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
                (g ∈ R ↔ ∃ x : F,
                  g * (((addEquiv (Multiplicative.ofAdd x) : T) : G))⁻¹ ∈ N)) ∧
                (∀ x : G, x ∈ T →
                  rightConjugateElem x s = x⁻¹) ∧
                  s * t ∈ T ∧
                  (∀ a : F, ∀ b : Fˣ,
                    rightConjugateElem
                        (((addEquiv (Multiplicative.ofAdd a) : T) : G))
                      (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) =
                      (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G))) ∧
                    addOrderOf (1 : F) = orderOf (s * t) ∧
        (p = 3 →
          Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 3 →
          Nat.card (nearFieldStar Q P) = 8 →
          let Sigma : Subgroup G := W ⊓ Subgroup.centralizer (P : Set G)
          Disjoint R Sigma ∧ Nat.card (R ⊔ Sigma : Subgroup G) = 3 ^ 4 ∧
            ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) ∧
              (∃ XC : Sylow 3 (Subgroup.centralizer (P : Set G)),
                (XC : Subgroup (Subgroup.centralizer (P : Set G))) =
                  (R ⊔ Sigma).subgroupOf
                    (Subgroup.centralizer (P : Set G))) ∧
                ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
                  ∃ r q w : G, r ∈ R ∧
                    q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                      w ∈ Sigma ∧ g = r * q * w) ∧
        (∀ m' : ℕ,
          Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
          ¬ p ∣ Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
          Subgroup.centralizer (P : Set G) ≤
              Subgroup.normalizer (R : Set G) ∧
            Nat.card R = p ^ (m' + 1) ∧
              Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
                p ^ m' ∧
              ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
                (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
                  R.subgroupOf (Subgroup.centralizer (P : Set G))) ∧
        (∀ m' : ℕ,
          Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
          ¬ p ∣ Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
          m' = 1 →
          s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
            (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
              q * s = s * q) ∧
            (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
            ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
              ∃ r q : G, r ∈ R ∧
                q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type v := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
  let : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  let N : Subgroup G :=
    D ⊓
      Subgroup.centralizer
        ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
      Subgroup.centralizer (P : Set G)
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨hNcore, hnormal, quotientAction, hsmul, hAbar,
      F, hFnear, hFfinite, hFnontrivial, unitEquivNear, hPO, hchar⟩
  let : core.Normal := by
    simpa [core, OmegaP, C] using hnormal
  have hNcoreLocal : N.subgroupOf C = core := by
    simpa [N, C, OmegaP, HP, DP, QP, core] using hNcore
  let : PFAppendixII.RightNearField F := hFnear
  let : Finite F := hFfinite
  let : Nontrivial F := hFnontrivial
  let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
  have hQcard :
      Nat.card Q = Nat.card (nearFieldStar Q P) ^ p := by
    simpa [nearFieldStar] using
      claim_4 H D Q K V W Q0 S Q1 P t s p hch
  have hpQ : p ∣ Nat.card Q + 1 :=
    chapter2_claim11_p_dvd_Q_card_succ
      H D Q K V W Q0 S Q1 P t s p hch
  have hpStar : p ∣ Nat.card (nearFieldStar Q P) + 1 := by
    have hcast :
        ((Nat.card (nearFieldStar Q P) + 1 : ℕ) : ZMod p) = 0 := by
      calc
        ((Nat.card (nearFieldStar Q P) + 1 : ℕ) : ZMod p) =
            (Nat.card (nearFieldStar Q P) : ZMod p) ^ p + 1 := by
              simp [ZMod.pow_card]
        _ = ((Nat.card (nearFieldStar Q P) ^ p + 1 : ℕ) : ZMod p) := by
              simp
        _ = ((Nat.card Q + 1 : ℕ) : ZMod p) := by rw [hQcard]
        _ = 0 := (ZMod.natCast_eq_zero_iff (Nat.card Q + 1) p).2 hpQ
    exact
      (ZMod.natCast_eq_zero_iff
        (Nat.card (nearFieldStar Q P) + 1) p).1 hcast
  have horderPrime : Nat.Prime (orderOf (s * t)) := by
    rw [← hchar]
    exact PFAppendixII.rightNearField_addOrderOf_one_prime
  obtain ⟨a, hFcardForOrder⟩ :=
    PFAppendixII.rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  have hUnitsCardForOrder :
      Nat.card (nearFieldStar Q P) = Nat.card Fˣ := by
    simpa [nearFieldStar] using Nat.card_congr unitEquivNear.toEquiv
  have hStarOrderPow :
      Nat.card (nearFieldStar Q P) + 1 = orderOf (s * t) ^ a := by
    calc
      Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by
        rw [hUnitsCardForOrder]
      _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
      _ = addOrderOf (1 : F) ^ a := hFcardForOrder
      _ = orderOf (s * t) ^ a := by rw [hchar]
  have hpOrderPow : p ∣ orderOf (s * t) ^ a := by
    rw [← hStarOrderPow]
    exact hpStar
  have horderP : orderOf (s * t) = p :=
    (Nat.prime_eq_prime_of_dvd_pow
      hch.B1.p_prime horderPrime hpOrderPow).symm
  have hcharP : addOrderOf (1 : F) = p := hchar.trans horderP
  obtain ⟨m, hFcard⟩ :=
    PFAppendixII.rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  have hUnitsCard : Nat.card (nearFieldStar Q P) = Nat.card Fˣ := by
    simpa [nearFieldStar] using Nat.card_congr unitEquivNear.toEquiv
  have hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m := by
    calc
      Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by rw [hUnitsCard]
      _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
      _ = addOrderOf (1 : F) ^ m := hFcard
      _ = p ^ m := by rw [hcharP]
  have h10 :=
    claim_10 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P
      (W ⊓ Subgroup.centralizer (P : Set G)) t s p m hch hind rfl hStarComm_order
  have hcase10 :
      (¬ p ∣ Nat.card ((W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) ∧
          ∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧
            Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u) ∨
        p = 3 ∧
          Nat.card ((W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) = 3 ∧
            Nat.card (nearFieldStar Q P) = 8 ∧
              (Nat.card W = 3 ∨ Nat.card W = 9) ∧
                ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
                  Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u := by
    rcases h10 with h10_1 | h10_2
    · exact Or.inl h10_1
    · rcases h10_2 with
        ⟨hp3, hSigma3, hStar8, _hWcyclic, hWcards, hpPart, _hmodel⟩
      exact Or.inr ⟨hp3, hSigma3, hStar8, hWcards, hpPart⟩
  have hN :
      N = D ⊓
        Subgroup.centralizer
          ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
        Subgroup.centralizer (P : Set G) := rfl
  have h7 := claim_7 H D Q K V W Q0 S Q1 P N t s p hch hind hN
  dsimp only at h7
  rcases h7 with ⟨_hnormal7, hNP, eSigmaData⟩
  rcases eSigmaData with ⟨eSigmaRaw, heSigmaRaw⟩
  let eSigma : DP.map (QuotientGroup.mk' core) ≃*
      ↥(W ⊓ Subgroup.centralizer (P : Set G)) := by
    simpa [DP, core, OmegaP, C] using eSigmaRaw
  have heSigma (a : DP.map (QuotientGroup.mk' core)) :
      QuotientGroup.mk' core
          ⟨(eSigma a : G), (eSigma a).property.2⟩ =
        (a : C ⧸ core) := by
    simpa [DP, core, OmegaP, C, eSigma] using heSigmaRaw a
  have hPOcopy := hPO
  rcases hPOcopy with
    ⟨addLift, unitLift, sigmaAct, hcoordinates, haddZero, hadd,
      hunitOne, hunitMul, hunitRange, hrightQ, hsigmaMaps,
      hsigmaOne, hsigmaMul, hsigmaInjective, hrightSigma,
      hinvolutionUnique, hinvolutionOrder⟩
  let addHom : Multiplicative F →* C ⧸ core :=
    claim_11_additiveHom addLift haddZero hadd
  let R : Subgroup G :=
    (addHom.range.comap (QuotientGroup.mk' core)).map C.subtype
  have hN_le_R : N ≤ R := by
    intro n hnN
    have hnC : n ∈ C := hnN.2
    let nC : C := ⟨n, hnC⟩
    have hnCore : nC ∈ core := by
      rw [← hNcoreLocal]
      exact hnN
    have hpi : QuotientGroup.mk' core nC = 1 :=
      (QuotientGroup.eq_one_iff (N := core) nC).2 hnCore
    have hnPre : nC ∈ addHom.range.comap (QuotientGroup.mk' core) := by
      change QuotientGroup.mk' core nC ∈ addHom.range
      rw [hpi]
      exact addHom.range.one_mem
    exact ⟨nC, hnPre, rfl⟩
  have hP_le_R : P ≤ R := by
    rw [← hNP]
    exact hN_le_R
  have hR_le_C : R ≤ C := by
    intro r hrR
    rcases hrR with ⟨rC, _hrPre, rfl⟩
    exact rC.property
  have hV_le_D : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hP_le_D : P ≤ D := hch.B1.P_le_V.trans hV_le_D
  have hQP_core_disjoint : Disjoint QP core := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxcore
    have hxPsub := hxcore
    rw [← hNcoreLocal, hNP] at hxPsub
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hxPsub
    have hxQG : (x : G) ∈ Q := by
      change (x : G) ∈ Q at hxQ
      exact hxQ
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      hch.section3.section2.hA.A1.Q_disjoint_D.le_bot
        ⟨hxQG, hP_le_D hxP⟩
    simpa using hxBot
  obtain ⟨qpToQbar, hqpToQbar⟩ :=
    claim_11_quotientMap_subgroup_equiv_of_disjoint
      core QP hQP_core_disjoint
  obtain ⟨unitToQbar, hunitToQbar⟩ :=
    claim_11_proposition_one_units_equiv
      (DP.map (QuotientGroup.mk' core))
      (QP.map (QuotientGroup.mk' core)) addLift unitLift
        hcoordinates haddZero hunitOne hunitMul hunitRange
  let starToQP : nearFieldStar Q P ≃* QP :=
    { toFun := fun x => ⟨⟨x, x.2.2⟩, x.2.1⟩
      invFun := fun x => ⟨x, x.2, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let unitEquivCoord : nearFieldStar Q P ≃* Fˣ :=
    (starToQP.trans qpToQbar).trans unitToQbar.symm
  let unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G)) :=
    { unitEquivCoord.symm with }
  have hunitCoordinate (b : Fˣ) :
      QuotientGroup.mk' core
          ⟨((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G),
            (unitEquiv b).property.2⟩ =
        unitLift b := by
    let qC : C :=
      ⟨((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G),
        (unitEquiv b).property.2⟩
    let qP : QP := starToQP (unitEquivCoord.symm b)
    have hqP_C : (qP : C) = qC := by
      apply Subtype.ext
      rfl
    change QuotientGroup.mk' core qC = unitLift b
    calc
      QuotientGroup.mk' core qC = (qpToQbar qP : C ⧸ core) := by
        rw [← hqP_C]
        exact (hqpToQbar qP).symm
      _ = (unitToQbar b : C ⧸ core) := by
        have hq : qpToQbar qP = unitToQbar b := by
          simp [qP, unitEquivCoord]
        exact congrArg Subtype.val hq
      _ = unitLift b := hunitToQbar b
  have haddHom_injective : Function.Injective addHom := by
    intro a b hab
    change addLift (Multiplicative.toAdd a) =
      addLift (Multiplicative.toAdd b) at hab
    let xa : F × Fˣ × (DP.map (QuotientGroup.mk' core)) :=
      (Multiplicative.toAdd a, 1, 1)
    let xb : F × Fˣ × (DP.map (QuotientGroup.mk' core)) :=
      (Multiplicative.toAdd b, 1, 1)
    have hxab : xa = xb := hcoordinates.1 (by
      dsimp [xa, xb]
      rw [hunitOne]
      exact congrArg (fun z : C ⧸ core => z * 1 * 1) hab)
    exact Multiplicative.toAdd.injective
      (congrArg (fun z : F × Fˣ × (DP.map (QuotientGroup.mk' core)) => z.1) hxab)
  have hAddRangeCard : Nat.card addHom.range = Nat.card F := by
    calc
      Nat.card addHom.range = Nat.card (Multiplicative F) :=
        Nat.card_congr (Equiv.ofInjective addHom haddHom_injective).symm
      _ = Nat.card F := by rfl
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  let M : Subgroup C := addHom.range.comap pi
  have hQuotCard :
      Nat.card (M ⧸ pi.ker.subgroupOf M) = Nat.card addHom.range := by
    simpa [M] using
      (card_quotient_subgroupOf_comap_eq
        (f := pi) (hf := QuotientGroup.mk'_surjective core)
        (H := addHom.range))
  have hKerLe : pi.ker ≤ M := Subgroup.ker_le_comap pi addHom.range
  have hKerCard : Nat.card (pi.ker.subgroupOf M) = Nat.card core := by
    calc
      Nat.card (pi.ker.subgroupOf M) = Nat.card pi.ker :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKerLe).toEquiv
      _ = Nat.card core := by simp [pi, QuotientGroup.ker_mk']
  have hMcard : Nat.card M = Nat.card addHom.range * Nat.card core := by
    calc
      Nat.card M =
          Nat.card (M ⧸ pi.ker.subgroupOf M) *
            Nat.card (pi.ker.subgroupOf M) := by
        simpa using
          (Subgroup.card_eq_card_quotient_mul_card_subgroup
            (s := pi.ker.subgroupOf M))
      _ = Nat.card addHom.range * Nat.card core := by
        rw [hQuotCard, hKerCard]
  have hRcard : Nat.card R = Nat.card M := by
    simpa [R, M, pi] using
      (Subgroup.card_map_of_injective
        (K := M) (f := C.subtype) C.subtype_injective)
  have hP_le_C : P ≤ C := hP_le_R.trans hR_le_C
  have hCoreCard : Nat.card core = Nat.card P := by
    calc
      Nat.card core = Nat.card (P.subgroupOf C) := by
        rw [← hNcoreLocal, hNP]
      _ = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_C).toEquiv
  have hPodd : Odd (Nat.card P) :=
    hch.section3.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hP_le_D)
  have hpOdd : Odd p := by simpa [hch.B1.P_card] using hPodd
  have hFOdd : Odd (Nat.card F) := by
    rw [hFcard, hcharP]
    exact hpOdd.pow
  have hRodd : Odd (Nat.card R) := by
    rw [hRcard, hMcard, hAddRangeCard, hCoreCard]
    exact hFOdd.mul hPodd
  have hAddRangeNormal : addHom.range.Normal := by
    refine ⟨?_⟩
    intro n hn g
    rcases hn with ⟨a, rfl⟩
    let aF : F := Multiplicative.toAdd a
    rcases hcoordinates.2 g⁻¹ with ⟨⟨b, u, d⟩, hcoord⟩
    change addLift b * unitLift u * (d : C ⧸ core) = g⁻¹ at hcoord
    have hrightAdd :
        rightConjugateElem (addLift aF) (addLift b) = addLift aF := by
      have hcommAdd : addLift aF * addLift b = addLift b * addLift aF := by
        calc
          addLift aF * addLift b = addLift (aF + b) := (hadd aF b).symm
          _ = addLift (b + aF) := by rw [add_comm]
          _ = addLift b * addLift aF := hadd b aF
      calc
        rightConjugateElem (addLift aF) (addLift b) =
            (addLift b)⁻¹ * addLift aF * addLift b := rfl
        _ = (addLift b)⁻¹ * (addLift aF * addLift b) := by rw [mul_assoc]
        _ = (addLift b)⁻¹ * (addLift b * addLift aF) := by rw [hcommAdd]
        _ = addLift aF := by exact inv_mul_cancel_left (addLift b) (addLift aF)
    refine ⟨Multiplicative.ofAdd (sigmaAct d (aF * (u : F))), ?_⟩
    change addLift (sigmaAct d (aF * (u : F))) =
      g * addLift aF * g⁻¹
    symm
    calc
      g * addLift aF * g⁻¹ =
          rightConjugateElem (addLift aF) g⁻¹ := by
            simp only [rightConjugateElem, inv_inv]
      _ = rightConjugateElem (addLift aF)
            (addLift b * unitLift u * (d : C ⧸ core)) := by
              rw [hcoord]
      _ = rightConjugateElem
            (rightConjugateElem
              (rightConjugateElem (addLift aF) (addLift b))
              (unitLift u))
            (d : C ⧸ core) := by
              simp only [rightConjugateElem]
              group
      _ = rightConjugateElem
            (rightConjugateElem (addLift aF) (unitLift u))
            (d : C ⧸ core) := by rw [hrightAdd]
      _ = rightConjugateElem (addLift (aF * (u : F)))
            (d : C ⧸ core) := by rw [hrightQ]
      _ = addLift (sigmaAct d (aF * (u : F))) :=
        hrightSigma d (aF * (u : F))
  have hMNormal : M.Normal := hAddRangeNormal.comap pi
  have hVeqCs :
      V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hch.section3.section2.V_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (proposition_5 H D Q t s hch.section3.section2.hA.A1
          hch.section3.s_mem_H hch.section3.s_involution
          hch.section3.s_conjugate).1
  have hsC : s ∈ C := by
    change s ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxP
    have hxV := hch.B1.P_le_V hxP
    rw [hVeqCs] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp hxV.2
  let sC : C := ⟨s, hsC⟩
  have hsNormalizerM : sC ∈ Subgroup.normalizer (M : Set C) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hMNormal]
    simp
  have hsNormalizerMap :
      s ∈ (Subgroup.normalizer (M : Set C)).map C.subtype :=
    ⟨sC, hsNormalizerM, rfl⟩
  have hs_norm_R : s ∈ Subgroup.normalizer (R : Set G) := by
    simpa [R, M, pi] using
      (Subgroup.le_normalizer_map (H := M) C.subtype hsNormalizerMap)
  have hsQ : s ∈ Q :=
    hch.section3.section2.Q0_le_Q
      ((hch.section3.section2.Q0_def s).2
        (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩))
  have hsQP : sC ∈ QP := by
    change s ∈ Q
    exact hsQ
  let sBar : C ⧸ core := pi sC
  have hsBarQ : sBar ∈ QP.map pi := ⟨sC, hsQP, rfl⟩
  have hsBarSq : sBar ^ 2 = 1 := by
    calc
      sBar ^ 2 = pi (sC ^ 2) := (map_pow pi sC 2).symm
      _ = pi 1 := by
        congr 1
        apply Subtype.ext
        exact hch.section3.s_involution.sq_eq_one
      _ = 1 := map_one pi
  have hsBarNe : sBar ≠ 1 := by
    intro hsOne
    have hsCore : sC ∈ core :=
      (QuotientGroup.eq_one_iff sC).1 (by simpa [sBar, pi] using hsOne)
    have hsPsub : sC ∈ P.subgroupOf C := by
      rw [← hNP, hNcoreLocal]
      exact hsCore
    have hsP : s ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hsPsub
    exact
      (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        D hch.section3.section2.hA.A1.D_odd (hP_le_D hsP))
        hch.section3.s_involution
  let sBarQ : QP.map pi := ⟨sBar, hsBarQ⟩
  let u : Fˣ := unitToQbar.symm sBarQ
  have huToQ : unitToQbar u = sBarQ := unitToQbar.apply_symm_apply sBarQ
  have huCoord : unitLift u = sBar := by
    calc
      unitLift u = (unitToQbar u : C ⧸ core) := (hunitToQbar u).symm
      _ = (sBarQ : C ⧸ core) := congrArg Subtype.val huToQ
      _ = sBar := rfl
  have huSq : u ^ 2 = 1 := by
    apply unitToQbar.injective
    calc
      unitToQbar (u ^ 2) = (unitToQbar u) ^ 2 := map_pow unitToQbar u 2
      _ = sBarQ ^ 2 := by rw [huToQ]
      _ = 1 := by
        apply Subtype.ext
        exact hsBarSq
      _ = unitToQbar 1 := (map_one unitToQbar).symm
  have huNe : u ≠ 1 := by
    intro huOne
    apply hsBarNe
    calc
      sBar = (sBarQ : C ⧸ core) := rfl
      _ = (unitToQbar u : C ⧸ core) :=
        (congrArg Subtype.val huToQ).symm
      _ = (unitToQbar 1 : C ⧸ core) := by rw [huOne]
      _ = 1 := by exact congrArg Subtype.val (map_one unitToQbar)
  have huValSq : (u : F) ^ 2 = 1 := by
    simpa using congrArg (fun z : Fˣ => (z : F)) huSq
  have huVal : (u : F) = -1 := by
    rcases
        PFAppendixII.rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one huValSq with
      huOne | huNeg
    · exact (huNe (Units.ext huOne)).elim
    · exact huNeg
  have hnegOneNe : (-1 : F) ≠ 1 := by
    intro hneg
    apply huNe
    apply Units.ext
    calc
      (u : F) = -1 := huVal
      _ = 1 := hneg
      _ = ((1 : Fˣ) : F) := rfl
  have haddLift_injective : Function.Injective addLift := by
    intro a b hab
    have habHom :
        addHom (Multiplicative.ofAdd a) =
          addHom (Multiplicative.ofAdd b) := by
      exact hab
    have habMult := haddHom_injective habHom
    simpa using congrArg Multiplicative.toAdd habMult
  have hfixed : subgroupCentralizerIn R (Subgroup.zpowers s) = P := by
    apply le_antisymm
    · intro x hx
      have hxR : x ∈ R := hx.1
      have hxs : s * x = x * s :=
        (Subgroup.mem_centralizer_iff.mp hx.2) s (Subgroup.mem_zpowers s)
      have hxRight : rightConjugateElem x s = x := by
        calc
          rightConjugateElem x s = s⁻¹ * x * s := rfl
          _ = s * x * s := by rw [hch.section3.s_involution.inv_eq_self]
          _ = x * s * s := by rw [hxs]
          _ = x * (s * s) := by rw [mul_assoc]
          _ = x := by
            rw [← pow_two, hch.section3.s_involution.sq_eq_one, mul_one]
      let xC : C := ⟨x, hR_le_C hxR⟩
      have hxM : xC ∈ M := by
        change x ∈ M.map C.subtype at hxR
        rcases hxR with ⟨y, hyM, hyx⟩
        have hyEq : y = xC := by
          apply Subtype.ext
          exact hyx
        simpa [hyEq] using hyM
      change pi xC ∈ addHom.range at hxM
      rcases hxM with ⟨a, ha⟩
      let aF : F := Multiplicative.toAdd a
      have haLift : addLift aF = pi xC := by
        change addLift aF = pi xC at ha
        exact ha
      have hxBarFixed :
          rightConjugateElem (pi xC) sBar = pi xC := by
        calc
          rightConjugateElem (pi xC) sBar =
              pi (rightConjugateElem xC sC) := by
                simp [rightConjugateElem, sBar, pi]
          _ = pi xC := by
            apply congrArg pi
            apply Subtype.ext
            exact hxRight
      have haFixed :
          rightConjugateElem (addLift aF) (unitLift u) = addLift aF := by
        rw [huCoord, haLift]
        exact hxBarFixed
      rw [hrightQ] at haFixed
      have haMul : aF * (u : F) = aF := haddLift_injective haFixed
      rw [huVal] at haMul
      have haZero : aF = 0 := by
        by_contra haNe
        apply hnegOneNe
        apply mul_left_cancel₀ haNe
        calc
          aF * (-1 : F) = aF := haMul
          _ = aF * 1 := (mul_one aF).symm
      have hxPiOne : pi xC = 1 := by
        calc
          pi xC = addLift aF := haLift.symm
          _ = addLift 0 := by rw [haZero]
          _ = 1 := haddZero
      have hxCore : xC ∈ core :=
        (QuotientGroup.eq_one_iff xC).1 (by simpa [pi] using hxPiOne)
      have hxPsub : xC ∈ P.subgroupOf C := by
        rw [← hNP, hNcoreLocal]
        exact hxCore
      simpa [Subgroup.mem_subgroupOf] using hxPsub
    · intro x hxP
      refine ⟨hP_le_R hxP, ?_⟩
      change x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set G)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hsC) x hxP
  let : core.Normal := by
    simpa [core, C, OmegaP] using hnormal
  let Hbar : Subgroup (C ⧸ core) := HP.map pi
  let Qbar : Subgroup (C ⧸ core) := QP.map pi
  let Dbar : Subgroup (C ⧸ core) := DP.map pi
  have hQbar_le_Hbar : Qbar ≤ Hbar := by
    simpa [Qbar, Hbar, pi, QP, HP, core, OmegaP, C] using hAbar.Q_le_H
  have hDbar_le_Hbar : Dbar ≤ Hbar := by
    simpa [Dbar, Hbar, pi, DP, HP, core, OmegaP, C] using hAbar.D_le_H
  have hQbar_normal_in_Hbar : (Qbar.subgroupOf Hbar).Normal := by
    simpa [Qbar, Hbar, pi, QP, HP, core, OmegaP, C] using hAbar.Q_normal_in_H
  have hQbar_sup_Dbar : Qbar ⊔ Dbar = Hbar := by
    simpa [Qbar, Dbar, Hbar, pi, QP, DP, HP, core, OmegaP, C] using hAbar.Q_sup_D
  have hAddRangeDisjointHbar : Disjoint addHom.range Hbar := by
    rw [Subgroup.disjoint_def]
    intro x hxAdd hxH
    rcases hxAdd with ⟨a, ha⟩
    have haLift : addLift (Multiplicative.toAdd a) = x := by
      change addLift (Multiplicative.toAdd a) = x at ha
      exact ha
    let xH : Hbar := ⟨x, hxH⟩
    let QH : Subgroup Hbar := Qbar.subgroupOf Hbar
    let DH : Subgroup Hbar := Dbar.subgroupOf Hbar
    let : QH.Normal := hQbar_normal_in_Hbar
    have hQHDH : QH ⊔ DH = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQbar_le_Hbar hDbar_le_Hbar,
        hQbar_sup_Dbar]
      exact Subgroup.subgroupOf_self Hbar
    have hxSup : xH ∈ QH ⊔ DH := by
      rw [hQHDH]
      simp
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨q, hqQ, d, hdD, hqd⟩
    have hqQbarRaw : (q : C ⧸ core) ∈ Qbar := hqQ
    have hqQbar : (q : C ⧸ core) ∈ QP.map (QuotientGroup.mk' core) := by
      simpa [Qbar, pi] using hqQbarRaw
    have hdDbar : (d : C ⧸ core) ∈ Dbar := hdD
    have hdDraw : (d : C ⧸ core) ∈ DP.map (QuotientGroup.mk' core) := by
      simpa [Dbar, pi] using hdDbar
    let dD0 : DP.map (QuotientGroup.mk' core) := ⟨(d : C ⧸ core), hdDraw⟩
    rcases (hunitRange (q : C ⧸ core)).1 hqQbar with ⟨u, hu⟩
    have hqdVal : (q : C ⧸ core) * (d : C ⧸ core) = x :=
      congrArg Subtype.val hqd
    have haUnitD :
        addLift (Multiplicative.toAdd a) = unitLift u * (dD0 : C ⧸ core) := by
      calc
        addLift (Multiplicative.toAdd a) = x := haLift
        _ = (q : C ⧸ core) * (d : C ⧸ core) := hqdVal.symm
        _ = unitLift u * (dD0 : C ⧸ core) := by
          rw [hu]
    have haZero : Multiplicative.toAdd a = 0 :=
      claim_11_additive_coordinate_eq_zero_of_eq_unit_mul
        (DP.map (QuotientGroup.mk' core)) addLift unitLift hcoordinates.1
          haddZero hunitOne haUnitD
    have hxOne : x = 1 := by
      calc
        x = addLift (Multiplicative.toAdd a) := haLift.symm
        _ = addLift 0 := by rw [haZero]
        _ = 1 := haddZero
    exact Subgroup.mem_bot.mpr hxOne
  have hAddRangeSupHbar : addHom.range ⊔ Hbar = ⊤ := by
    rw [eq_top_iff]
    intro x _hx
    rcases hcoordinates.2 x with ⟨⟨a, u, d⟩, hcoord⟩
    have hcoord' : addLift a * unitLift u * (d : C ⧸ core) = x := by
      simpa [Dbar, pi, DP, core, OmegaP, C] using hcoord
    have hdDbar : (d : C ⧸ core) ∈ Dbar := by
      simpa [Dbar, pi, DP, core, OmegaP, C] using d.property
    apply Subgroup.mem_sup_of_normal_left.mpr
    rw [mul_assoc] at hcoord'
    refine ⟨addLift a, ?_, unitLift u * (d : C ⧸ core), ?_, hcoord'⟩
    · exact ⟨Multiplicative.ofAdd a, rfl⟩
    · exact Hbar.mul_mem
        (hQbar_le_Hbar ((hunitRange (unitLift u)).2 ⟨u, rfl⟩))
        (hDbar_le_Hbar hdDbar)
  have hAddRangeComplHbar : addHom.range.IsComplement' Hbar :=
    isComplement'_of_disjoint_sup_eq_top_of_normal
      addHom.range Hbar hAddRangeDisjointHbar hAddRangeSupHbar
  let hHbarComplAdd : Hbar.IsComplement' addHom.range :=
    hAddRangeComplHbar.symm
  let proj : (C ⧸ core) →* Hbar :=
    hHbarComplAdd.QuotientMulEquiv.toMonoidHom.comp
      (QuotientGroup.mk' addHom.range)
  have hAddRangeOdd : Odd (Nat.card addHom.range) := by
    rw [hAddRangeCard]
    exact hFOdd
  have hproj_ne_one (x : C ⧸ core) (hx : IsInvolution x) : proj x ≠ 1 := by
    intro hprojOne
    have hquotOne : QuotientGroup.mk' addHom.range x = 1 := by
      apply (MulEquiv.map_eq_one_iff hHbarComplAdd.QuotientMulEquiv).mp
      exact hprojOne
    have hxAdd : x ∈ addHom.range :=
      (QuotientGroup.eq_one_iff x).1 hquotOne
    exact
      (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        addHom.range hAddRangeOdd hxAdd) hx
  have hproj_involution (x : C ⧸ core) (hx : IsInvolution x) :
      IsInvolution ((proj x : Hbar) : C ⧸ core) := by
    constructor
    · intro hcoe
      apply hproj_ne_one x hx
      apply Subtype.ext
      exact hcoe
    · suffices h : x ^ 2 = 1 by
        simpa using congrArg (fun y : ↥C ⧸ core => (proj y : ↥C ⧸ core)) h
      exact hx.2
  let tC : C :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t
      hch.B1.P_le_V hch.section3.section2.V_eq⟩
  let tBar : C ⧸ core := pi tC
  have htBarSq : tBar ^ 2 = 1 := by
    calc
      tBar ^ 2 = pi (tC ^ 2) := (map_pow pi tC 2).symm
      _ = pi 1 := by
        congr 1
        apply Subtype.ext
        exact hch.section3.section2.hA.A1.involution_t.sq_eq_one
      _ = 1 := map_one pi
  have htBarNe : tBar ≠ 1 := by
    intro htOne
    have htCore : tC ∈ core :=
      (QuotientGroup.eq_one_iff tC).1 (by simpa [tBar, pi] using htOne)
    have htPsub : tC ∈ P.subgroupOf C := by
      rw [← hNP, hNcoreLocal]
      exact htCore
    have htP : t ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using htPsub
    exact
      (PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        D hch.section3.section2.hA.A1.D_odd (hP_le_D htP))
        hch.section3.section2.hA.A1.involution_t
  have hsProjI : IsInvolution ((proj sBar : Hbar) : C ⧸ core) :=
    hproj_involution sBar ⟨hsBarNe, hsBarSq⟩
  have htProjI : IsInvolution ((proj tBar : Hbar) : C ⧸ core) :=
    hproj_involution tBar ⟨htBarNe, htBarSq⟩
  have hprojEq : proj sBar = proj tBar :=
    hinvolutionUnique.unique hsProjI htProjI
  have hprojMul : proj (sBar * tBar) = 1 := by
    rw [map_mul, hprojEq]
    have htProjSq : (proj tBar) ^ 2 = 1 := by
      apply Subtype.ext
      exact htProjI.sq_eq_one
    simpa [pow_two] using htProjSq
  have hquotMul : QuotientGroup.mk' addHom.range (sBar * tBar) = 1 := by
    apply (MulEquiv.map_eq_one_iff hHbarComplAdd.QuotientMulEquiv).mp
    exact hprojMul
  have hstAdd : sBar * tBar ∈ addHom.range :=
    (QuotientGroup.eq_one_iff (sBar * tBar)).1 hquotMul
  let stC : C := sC * tC
  have hstM : stC ∈ M := by
    change pi stC ∈ addHom.range
    have hpiSt : pi stC = sBar * tBar := by
      simp [stC, sBar, tBar]
    rw [hpiSt]
    exact hstAdd
  have hst_mem_R : s * t ∈ R := by
    exact ⟨stC, hstM, rfl⟩
  have hSigmaBarCard :
      Nat.card (DP.map (QuotientGroup.mk' core)) =
        Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    Nat.card_congr eSigma.toEquiv
  have hQuotientCard :
      Nat.card (C ⧸ core) =
        Nat.card F * Nat.card Fˣ *
          Nat.card (DP.map (QuotientGroup.mk' core)) := by
    calc
      Nat.card (C ⧸ core) =
          Nat.card (F × Fˣ × (DP.map (QuotientGroup.mk' core))) :=
        Nat.card_congr (Equiv.ofBijective _ hcoordinates).symm
      _ = Nat.card F * Nat.card Fˣ *
          Nat.card (DP.map (QuotientGroup.mk' core)) := by
        simp [Nat.mul_assoc]
  have hCcard : Nat.card C = Nat.card (C ⧸ core) * Nat.card core := by
    simpa using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := core))
  have hUnitsCard : Nat.card Fˣ = p ^ m - 1 := by
    have h := Nat.card_eq_card_units_add_one F
    rw [hFcard] at h
    omega
  have hRcardPow : Nat.card R = p ^ (m + 1) := by
    rw [hRcard, hMcard, hAddRangeCard, hCoreCard, hFcard, hcharP,
      hch.B1.P_card, pow_succ]
  have hCcardFactor :
      Nat.card C = p ^ (m + 1) *
        (Nat.card Fˣ *
          Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) := by
    rw [hCcard, hQuotientCard, hSigmaBarCard, hCoreCard, hch.B1.P_card,
      hFcard, hcharP, pow_succ]
    ring
  let RC : Subgroup C := R.subgroupOf C
  have hRCcard : Nat.card RC = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_C).toEquiv
  have hRCindex :
      RC.index =
        Nat.card Fˣ *
          Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hch.B1.p_prime.pos (m + 1))
    calc
      p ^ (m + 1) * RC.index = Nat.card RC * RC.index := by rw [hRCcard, hRcardPow]
      _ = Nat.card C := RC.card_mul_index
      _ = p ^ (m + 1) *
          (Nat.card Fˣ *
            Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) :=
        hCcardFactor
  have hC_le_norm_R : C ≤ Subgroup.normalizer (R : Set G) := by
    intro c hcC
    let cC : C := ⟨c, hcC⟩
    have hcNormalizerM : cC ∈ Subgroup.normalizer (M : Set C) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hMNormal]
      simp
    have hcNormalizerMap :
        c ∈ (Subgroup.normalizer (M : Set C)).map C.subtype :=
      ⟨cC, hcNormalizerM, rfl⟩
    simpa [R, M, pi] using
      (Subgroup.le_normalizer_map (H := M) C.subtype hcNormalizerMap)
  have hRcomm : IsMulCommutative R := by
    by_contra hRnoncomm
    have hcomm_le_P : ⁅R, R⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro x hxR y hyR
      let xC : C := ⟨x, hR_le_C hxR⟩
      let yC : C := ⟨y, hR_le_C hyR⟩
      have hxM : xC ∈ M := by
        change x ∈ M.map C.subtype at hxR
        rcases hxR with ⟨z, hzM, hzx⟩
        have hz : z = xC := by
          apply Subtype.ext
          exact hzx
        simpa [hz] using hzM
      have hyM : yC ∈ M := by
        change y ∈ M.map C.subtype at hyR
        rcases hyR with ⟨z, hzM, hzy⟩
        have hz : z = yC := by
          apply Subtype.ext
          exact hzy
        simpa [hz] using hzM
      change pi xC ∈ addHom.range at hxM
      change pi yC ∈ addHom.range at hyM
      rcases hxM with ⟨a, ha⟩
      rcases hyM with ⟨b, hb⟩
      have habEq : pi xC * pi yC = pi yC * pi xC := by
        rw [← ha, ← hb]
        change addLift (Multiplicative.toAdd a) * addLift (Multiplicative.toAdd b) =
          addLift (Multiplicative.toAdd b) * addLift (Multiplicative.toAdd a)
        calc
          addLift (Multiplicative.toAdd a) * addLift (Multiplicative.toAdd b) =
              addLift (Multiplicative.toAdd a + Multiplicative.toAdd b) :=
            (hadd _ _).symm
          _ = addLift (Multiplicative.toAdd b + Multiplicative.toAdd a) := by
            rw [add_comm]
          _ = addLift (Multiplicative.toAdd b) * addLift (Multiplicative.toAdd a) :=
            hadd _ _
      have habComm : Commute (pi xC) (pi yC) := habEq
      have hpiComm : pi ⁅xC, yC⁆ = 1 := by
        rw [map_commutatorElement]
        exact habComm.commutator_eq
      have hcommCore : ⁅xC, yC⁆ ∈ core :=
        (QuotientGroup.eq_one_iff ⁅xC, yC⁆).1 hpiComm
      have hcorePNow : core = P.subgroupOf C := by
        rw [← hNcoreLocal, hNP]
      rw [hcorePNow] at hcommCore
      change C.subtype ⁅xC, yC⁆ ∈ P at hcommCore
      rw [map_commutatorElement] at hcommCore
      change ⁅x, y⁆ ∈ P at hcommCore
      exact hcommCore
    have hcomm_ne_bot : ⁅R, R⁆ ≠ ⊥ := by
      intro hbot
      apply hRnoncomm
      refine ⟨⟨fun x y => ?_⟩⟩
      have hmem : ⁅(x : G), (y : G)⁆ ∈ ⁅R, R⁆ :=
        Subgroup.commutator_mem_commutator x.property y.property
      rw [hbot] at hmem
      have hone : ⁅(x : G), (y : G)⁆ = 1 := Subgroup.mem_bot.mp hmem
      apply Subtype.ext
      exact (commutatorElement_eq_one_iff_commute.mp hone).eq
    have hcomm_eq_P : ⁅R, R⁆ = P := by
      obtain ⟨z, hzComm, hzNe⟩ :=
        claim_11_exists_nontrivial_mem_of_subgroup_ne_bot ⁅R, R⁆ hcomm_ne_bot
      have hzP : z ∈ P := hcomm_le_P hzComm
      have hPclosure : P = Subgroup.closure ({z} : Set G) :=
        claim_11_prime_card_subgroup_eq_closure_of_mem_ne_one
          P hch.B1.p_prime hch.B1.P_card hzP hzNe
      apply le_antisymm hcomm_le_P
      rw [hPclosure]
      rw [Subgroup.closure_le]
      intro x hx
      simpa using hx ▸ hzComm
    have hnormR_le_normP :
        Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      have hnorm :=
        claim_11_normalizer_le_normalizer_map_subtype_of_characteristic
          R (_root_.commutator R)
      rw [Subgroup.map_subtype_commutator, hcomm_eq_P] at hnorm
      exact hnorm
    have hnormP_eq_C :
        Subgroup.normalizer (P : Set G) = C := by
      simpa [C] using
        (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.2.1
    have hnormR_le_C : Subgroup.normalizer (R : Set G) ≤ C := by
      rw [← hnormP_eq_C]
      exact hnormR_le_normP
    have hcorePNow : core = P.subgroupOf C := by
      rw [← hNcoreLocal, hNP]
    have hR_coordinate (x : G) (hxR : x ∈ R) :
        ∃ a : F, ∃ xC : C, (xC : G) = x ∧ pi xC = addLift a := by
      let xC : C := ⟨x, hR_le_C hxR⟩
      have hxM : xC ∈ M := by
        change x ∈ M.map C.subtype at hxR
        rcases hxR with ⟨z, hzM, hzx⟩
        have hz : z = xC := by
          apply Subtype.ext
          exact hzx
        simpa [hz] using hzM
      change pi xC ∈ addHom.range at hxM
      rcases hxM with ⟨a, ha⟩
      exact ⟨Multiplicative.toAdd a, xC, rfl, ha.symm⟩
    let ZR : Subgroup G := (Subgroup.center R).map R.subtype
    have hP_le_ZR : P ≤ ZR := by
      intro z hzP
      let zR : R := ⟨z, hP_le_R hzP⟩
      have hzCenter : zR ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro yR
        apply Subtype.ext
        exact ((Subgroup.mem_centralizer_iff.mp (hR_le_C yR.property)) z hzP).symm
      exact ⟨zR, hzCenter, rfl⟩
    have hZR_le_P : ZR ≤ P := by
      intro x hxZR
      by_contra hxNotP
      obtain ⟨a, xC, hxCval, hxCpi⟩ := hR_coordinate x
        (by
          rcases hxZR with ⟨xR, _hxCenter, rfl⟩
          exact xR.property)
      have ha : a ≠ 0 := by
        intro ha0
        have hxPiOne : pi xC = 1 := by rw [hxCpi, ha0, haddZero]
        have hxCore : xC ∈ core := (QuotientGroup.eq_one_iff xC).1 hxPiOne
        rw [hcorePNow] at hxCore
        apply hxNotP
        simpa [Subgroup.mem_subgroupOf, hxCval] using hxCore
      have hnormZR :
          Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (ZR : Set G) := by
        simpa [ZR] using
          (claim_11_normalizer_le_normalizer_map_subtype_of_characteristic
            R (Subgroup.center R))
      have hR_le_ZR : R ≤ ZR := by
        intro y hyR
        obtain ⟨b, yC, hyCval, hyCpi⟩ := hR_coordinate y hyR
        by_cases hb : b = 0
        · apply hP_le_ZR
          have hyPiOne : pi yC = 1 := by rw [hyCpi, hb, haddZero]
          have hyCore : yC ∈ core := (QuotientGroup.eq_one_iff yC).1 hyPiOne
          rw [hcorePNow] at hyCore
          simpa [Subgroup.mem_subgroupOf, hyCval] using hyCore
        · let d : Fˣ := Units.mk0 (a⁻¹ * b) (mul_ne_zero (inv_ne_zero ha) hb)
          have had : a * (d : F) = b := by
            change a * (a⁻¹ * b) = b
            rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
          let c : G :=
            ((unitEquiv d : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)
          have hcC : c ∈ C := by
            exact (unitEquiv d).property.2
          let cC : C := ⟨c, hcC⟩
          have hcNormR : c ∈ Subgroup.normalizer (R : Set G) :=
            hC_le_norm_R hcC
          have hcInvNormZR : c⁻¹ ∈ Subgroup.normalizer (ZR : Set G) :=
            (Subgroup.normalizer (ZR : Set G)).inv_mem (hnormZR hcNormR)
          have hxConjZR : rightConjugateElem x c ∈ ZR := by
            have hmem :=
              (Subgroup.mem_normalizer_iff.mp hcInvNormZR x).1 hxZR
            simpa [rightConjugateElem, mul_assoc] using hmem
          let zC : C := rightConjugateElem xC cC
          have hcPi : pi cC = unitLift d := by
            change QuotientGroup.mk' core cC = unitLift d
            exact hunitCoordinate d
          have hzCpi : pi zC = addLift b := by
            calc
              pi zC = rightConjugateElem (pi xC) (pi cC) := by
                simp [zC, rightConjugateElem]
              _ = rightConjugateElem (addLift a) (unitLift d) := by
                rw [hxCpi, hcPi]
              _ = addLift (a * (d : F)) := hrightQ a d
              _ = addLift b := by rw [had]
          have hyzQuot : pi yC = pi zC := hyCpi.trans hzCpi.symm
          have hyzCore : yC / zC ∈ core :=
            QuotientGroup.eq_iff_div_mem.mp hyzQuot
          have hzCval : (zC : G) = rightConjugateElem x c := by
            change rightConjugateElem (xC : G) (cC : G) =
              rightConjugateElem x c
            rw [hxCval]
          have hyzP : y / rightConjugateElem x c ∈ P := by
            rw [hcorePNow] at hyzCore
            simpa [Subgroup.mem_subgroupOf, hyCval, hzCval] using hyzCore
          have hyzZR : y / rightConjugateElem x c ∈ ZR := hP_le_ZR hyzP
          have hprod := ZR.mul_mem hyzZR hxConjZR
          have hyEq :
              (y / rightConjugateElem x c) * rightConjugateElem x c = y := by
            simp [div_eq_mul_inv]
          rw [hyEq] at hprod
          exact hprod
      have hR_le_centR : R ≤ Subgroup.centralizer (R : Set G) := by
        intro x hxR
        rcases hR_le_ZR hxR with ⟨xR, hxCenter, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hyR
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hxCenter ⟨y, hyR⟩)
      apply hRnoncomm
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hR_le_centR y.property))
        (x : G) x.property
    have hcenter_eq_P : ZR = P := le_antisymm hZR_le_P hP_le_ZR
    have hRp : IsPGroup p R := IsPGroup.of_card hRcardPow
    have hRCp : IsPGroup p RC := by
      apply IsPGroup.of_card (n := m + 1)
      rw [hRCcard, hRcardPow]
    have hFcardPow : Nat.card F = p ^ m := by
      calc
        Nat.card F = addOrderOf (1 : F) ^ m := hFcard
        _ = p ^ m := by rw [hcharP]
    have hmpos : 0 < m := by
      let : Fintype F := Fintype.ofFinite F
      have hFgt : 1 < Nat.card F := by
        simpa [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      rw [hm0, pow_zero] at hFcardPow
      omega
    have hp_not_units : ¬ p ∣ Nat.card Fˣ := by
      rw [hUnitsCard]
      intro hd
      have hpPow : p ∣ p ^ m := dvd_pow_self p hmpos.ne'
      have hone_le : 1 ≤ p ^ m := by
        have hpowpos : 0 < p ^ m := pow_pos hch.B1.p_prime.pos m
        omega
      have hsum : p ∣ (p ^ m - 1) + 1 := by
        rw [Nat.sub_add_cancel hone_le]
        exact hpPow
      have hsum' : p ∣ 1 + (p ^ m - 1) := by
        simpa [Nat.add_comm] using hsum
      have hpOne : p ∣ 1 := (Nat.dvd_add_iff_left hd).mpr hsum'
      exact hch.B1.p_prime.not_dvd_one hpOne
    rcases hcase10 with h10_1 | h10_2
    · have hindex_not : ¬ p ∣ RC.index := by
        rw [hRCindex]
        exact hch.B1.p_prime.not_dvd_mul hp_not_units h10_1.1
      let PRC : Sylow p C := hRCp.toSylow hindex_not
      obtain ⟨RG, hRG⟩ :=
        claim_11_sylow_of_subgroupOf_sylow_of_normalizer_le
          R C hRp PRC rfl hnormR_le_C
      rcases h10_1.2 with ⟨_k, uG, _hpPart, hGcard, _huG⟩
      have hRindex : R.index = p * uG := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hch.B1.p_prime.pos (m + 1))
        calc
          p ^ (m + 1) * R.index = Nat.card R * R.index := by rw [hRcardPow]
          _ = Nat.card G := R.card_mul_index
          _ = p ^ (m + 2) * uG := hGcard
          _ = p ^ (m + 1) * (p * uG) := by
            rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
            ring
      have hpIndex : p ∣ R.index := by
        rw [hRindex]
        exact dvd_mul_right p uG
      have hnot := RG.not_dvd_index
      rw [hRG] at hnot
      exact hnot hpIndex
    · rcases h10_2 with
        ⟨hp3, hSigma3, hStar8, hWcards, hGpart⟩
      have hm2 : m = 2 := by
        apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        calc
          3 ^ m = p ^ m := by rw [hp3]
          _ = Nat.card (nearFieldStar Q P) + 1 := hStarComm_order.symm
          _ = 8 + 1 := by rw [hStar8]
          _ = 3 ^ 2 := by norm_num
      let Sigma : Subgroup G := W ⊓ Subgroup.centralizer (P : Set G)
      have hSigmap : IsPGroup p Sigma := by
        rw [hp3]
        apply IsPGroup.of_card (n := 1)
        simpa [Sigma] using hSigma3
      have hSigma_norm_R : Sigma ≤ Subgroup.normalizer (R : Set G) := by
        intro x hx
        exact hC_le_norm_R hx.2
      have hR_disj_Sigma : Disjoint R Sigma := by
        rw [Subgroup.disjoint_def]
        intro x hxR hxSigma
        obtain ⟨a, xC, hxCval, hxCpi⟩ := hR_coordinate x hxR
        have hxAdd : pi xC ∈ addHom.range :=
          ⟨Multiplicative.ofAdd a, hxCpi.symm⟩
        have hxDP : xC ∈ DP := by
          change (xC : G) ∈ D
          rw [hxCval]
          exact PFchapter1section2.proposition_3_W_le_D
            H D Q K V W Q0 S Q1 t hch.section3.section2 hxSigma.1
        have hxDbar : pi xC ∈ Dbar := ⟨xC, hxDP, rfl⟩
        have hxHbar : pi xC ∈ Hbar := hDbar_le_Hbar hxDbar
        have hxBot : pi xC ∈ (⊥ : Subgroup (C ⧸ core)) :=
          (Subgroup.disjoint_def.mp hAddRangeDisjointHbar) hxAdd hxHbar
        have hxPiOne : pi xC = 1 := Subgroup.mem_bot.mp hxBot
        have hxCore : xC ∈ core := (QuotientGroup.eq_one_iff xC).1 hxPiOne
        rw [hcorePNow] at hxCore
        have hxP : x ∈ P := by
          simpa [Subgroup.mem_subgroupOf, hxCval] using hxCore
        have hWPdisj : Disjoint W P :=
          (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1.2.2.2.1
        have hxOne : x = 1 := Subgroup.mem_bot.mp
          ((Subgroup.disjoint_def.mp hWPdisj) hxSigma.1 hxP)
        exact hxOne
      let X : Subgroup G := R ⊔ Sigma
      have hXp : IsPGroup p X := by
        exact hRp.to_sup_of_normal_left' hSigmap hSigma_norm_R
      have hXcard : Nat.card X = 3 ^ 4 := by
        calc
          Nat.card X = Nat.card R * Nat.card Sigma :=
            claim_11_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
              R Sigma hSigma_norm_R hR_disj_Sigma
          _ = 3 ^ (m + 1) * 3 := by
            rw [hRcardPow, hp3]
            simpa [Sigma] using hSigma3
          _ = 3 ^ 4 := by rw [hm2]; norm_num
      have hX_le_C : X ≤ C := by
        exact sup_le hR_le_C (by intro x hx; exact hx.2)
      let XC : Subgroup C := X.subgroupOf C
      have hXCcard : Nat.card XC = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_C).toEquiv
      have hCcardFactor3 := hCcardFactor
      rw [hp3] at hCcardFactor3
      have hSigmaCard : Nat.card Sigma = 3 := by
        simpa [Sigma] using hSigma3
      have hXCindex : XC.index = 8 := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 4)
        calc
          3 ^ 4 * XC.index = Nat.card XC * XC.index := by rw [hXCcard, hXcard]
          _ = Nat.card C := XC.card_mul_index
          _ = 3 ^ (m + 1) * (Nat.card Fˣ * Nat.card Sigma) := by
            simpa [Sigma] using hCcardFactor3
          _ = 3 ^ 4 * 8 := by
            rw [hUnitsCard, hp3, hm2, hSigmaCard]
            norm_num
      have hXCp : IsPGroup p XC := by
        apply IsPGroup.of_card (n := 4)
        rw [hXCcard, hXcard, hp3]
      have hindex_not : ¬ p ∣ XC.index := by
        rw [hXCindex, hp3]
        norm_num
      let PXC : Sylow p C := hXCp.toSylow hindex_not
      let ZX : Subgroup G := (Subgroup.center X).map X.subtype
      have hP_le_ZX : P ≤ ZX := by
        intro z hzP
        let zX : X := ⟨z, Subgroup.mem_sup_left (hP_le_R hzP)⟩
        have hzCenter : zX ∈ Subgroup.center X := by
          rw [Subgroup.mem_center_iff]
          intro yX
          apply Subtype.ext
          exact ((Subgroup.mem_centralizer_iff.mp (hX_le_C yX.property)) z hzP).symm
        exact ⟨zX, hzCenter, rfl⟩
      have hZX_le_P : ZX ≤ P := by
        intro x hxZX
        rcases hxZX with ⟨xX, hxCenter, rfl⟩
        have hxSet : (xX : G) ∈ (R : Set G) * (Sigma : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left R Sigma hSigma_norm_R]
          exact xX.property
        rcases hxSet with ⟨r, hrR, w, hwSigma, hrw⟩
        change r * w = (xX : G) at hrw
        obtain ⟨b, rC, hrCval, hrCpi⟩ := hR_coordinate r hrR
        let wSigma : Sigma := ⟨w, hwSigma⟩
        let dBar : DP.map (QuotientGroup.mk' core) := eSigma.symm wSigma
        have heSigmaW : eSigma dBar = wSigma := eSigma.apply_symm_apply wSigma
        let wC : C := ⟨w, hwSigma.2⟩
        have hwCpi : pi wC = (dBar : C ⧸ core) := by
          let ewC : C :=
            ⟨((eSigma dBar : ↥(W ⊓ Subgroup.centralizer (P : Set G))) : G),
              (eSigma dBar).property.2⟩
          have hwCEq : wC = ewC := by
            apply Subtype.ext
            exact congrArg (fun z : Sigma => (z : G)) heSigmaW.symm
          calc
            pi wC = pi ewC := congrArg pi hwCEq
            _ = (dBar : C ⧸ core) := heSigma dBar
        let xC : C := ⟨(xX : G), hX_le_C xX.property⟩
        have hxCprod : xC = rC * wC := by
          apply Subtype.ext
          calc
            (xC : G) = (xX : G) := rfl
            _ = r * w := hrw.symm
            _ = (rC : G) * (wC : G) := by rw [hrCval]
        have hsigmaFixed (a : F) : sigmaAct dBar a = a := by
          obtain ⟨aC, haCpi⟩ := QuotientGroup.mk'_surjective core (addLift a)
          have haPre : aC ∈ M := by
            change pi aC ∈ addHom.range
            exact ⟨Multiplicative.ofAdd a, haCpi.symm⟩
          have haR : (aC : G) ∈ R := ⟨aC, haPre, rfl⟩
          let aX : X := ⟨(aC : G), Subgroup.mem_sup_left haR⟩
          have hcommX : (aX : G) * (xX : G) = (xX : G) * (aX : G) :=
            congrArg Subtype.val (Subgroup.mem_center_iff.mp hxCenter aX)
          have hrightFixed : rightConjugateElem (aC : G) (xC : G) = (aC : G) := by
            change (xC : G)⁻¹ * (aC : G) * (xC : G) = (aC : G)
            have hcommX' : (aC : G) * (xC : G) = (xC : G) * (aC : G) := by
              simpa [aX, xC] using hcommX
            calc
              (xC : G)⁻¹ * (aC : G) * (xC : G) =
                  (xC : G)⁻¹ * ((aC : G) * (xC : G)) := by rw [mul_assoc]
              _ = (xC : G)⁻¹ * ((xC : G) * (aC : G)) := by rw [hcommX']
              _ = (aC : G) := by simp
          have haddComm :
              rightConjugateElem (addLift a) (addLift b) = addLift a := by
            have hab : addLift a * addLift b = addLift b * addLift a := by
              calc
                addLift a * addLift b = addLift (a + b) := (hadd a b).symm
                _ = addLift (b + a) := by rw [add_comm]
                _ = addLift b * addLift a := hadd b a
            calc
              rightConjugateElem (addLift a) (addLift b) =
                  (addLift b)⁻¹ * addLift a * addLift b := rfl
              _ = (addLift b)⁻¹ * (addLift a * addLift b) := by rw [mul_assoc]
              _ = (addLift b)⁻¹ * (addLift b * addLift a) := by rw [hab]
              _ = addLift a := by
                exact inv_mul_cancel_left (addLift b) (addLift a)
          apply haddLift_injective
          calc
            addLift (sigmaAct dBar a) =
                rightConjugateElem (addLift a) (dBar : C ⧸ core) :=
              (hrightSigma dBar a).symm
            _ = rightConjugateElem (addLift a) (pi wC) := by rw [hwCpi]
            _ = rightConjugateElem
                (rightConjugateElem (addLift a) (pi rC)) (pi wC) := by
              rw [hrCpi, haddComm]
            _ = rightConjugateElem (addLift a) (pi (rC * wC)) := by
              simp only [rightConjugateElem, map_mul, mul_inv_rev]
              group
            _ = rightConjugateElem (pi aC) (pi xC) := by
              rw [haCpi, hxCprod]
            _ = pi (rightConjugateElem aC xC) := by
              simp [rightConjugateElem]
            _ = pi aC := by
              congr 1
              apply Subtype.ext
              exact hrightFixed
            _ = addLift a := haCpi
        have hdBarOne : dBar = 1 := by
          apply hsigmaInjective
          funext a
          calc
            sigmaAct dBar a = a := hsigmaFixed a
            _ = sigmaAct 1 a := (hsigmaOne a).symm
        have hwPiOne : pi wC = 1 := by rw [hwCpi, hdBarOne]; rfl
        have hwCore : wC ∈ core := (QuotientGroup.eq_one_iff wC).1 hwPiOne
        rw [hcorePNow] at hwCore
        have hwP : w ∈ P := by
          simpa [Subgroup.mem_subgroupOf] using hwCore
        have hWPdisj : Disjoint W P :=
          (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1.2.2.2.1
        have hwOne : w = 1 := Subgroup.mem_bot.mp
          ((Subgroup.disjoint_def.mp hWPdisj) hwSigma.1 hwP)
        have hxR : (xX : G) ∈ R := by
          have hrw' := hrw
          rw [hwOne, mul_one] at hrw'
          rw [← hrw']
          exact hrR
        let xR : R := ⟨(xX : G), hxR⟩
        have hxCenterR : xR ∈ Subgroup.center R := by
          rw [Subgroup.mem_center_iff]
          intro yR
          apply Subtype.ext
          change (yR : G) * (xX : G) = (xX : G) * (yR : G)
          exact congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hxCenter
              ⟨(yR : G), Subgroup.mem_sup_left yR.property⟩)
        have hxZR : (xX : G) ∈ ZR := ⟨xR, hxCenterR, rfl⟩
        rw [hcenter_eq_P] at hxZR
        exact hxZR
      have hcenterX_eq_P : ZX = P := le_antisymm hZX_le_P hP_le_ZX
      have hnormX_le_normP :
          Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (P : Set G) := by
        have hnorm :=
          claim_11_normalizer_le_normalizer_map_subtype_of_characteristic
            X (Subgroup.center X)
        simpa [ZX, hcenterX_eq_P] using hnorm
      have hnormX_le_C : Subgroup.normalizer (X : Set G) ≤ C := by
        rw [← hnormP_eq_C]
        exact hnormX_le_normP
      obtain ⟨XG, hXG⟩ :=
        claim_11_sylow_of_subgroupOf_sylow_of_normalizer_le
          X C hXp PXC rfl hnormX_le_C
      rcases hGpart with ⟨_k, uG, _hpPart, hGcard, _huG⟩
      have hXindex : X.index = Nat.card W * uG := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 4)
        calc
          3 ^ 4 * X.index = Nat.card X * X.index := by rw [hXcard]
          _ = Nat.card G := X.card_mul_index
          _ = (3 ^ 4 * Nat.card W) * uG := hGcard
          _ = 3 ^ 4 * (Nat.card W * uG) := by ring
      have hThreeDvdW : 3 ∣ Nat.card W := by
        rcases hWcards with hW3 | hW9
        · rw [hW3]
        · rw [hW9]
          norm_num
      have hThreeDvdIndex : 3 ∣ X.index := by
        rw [hXindex]
        exact dvd_mul_of_dvd_left hThreeDvdW uG
      have hnot := XG.not_dvd_index
      rw [hXG, hp3] at hnot
      exact hnot hThreeDvdIndex
  let T : Subgroup G := ⁅R, Subgroup.zpowers s⁆
  have hDecomp :
      R = T ⊔ P ∧ Disjoint T P ∧
        ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹ := by
    simpa [T] using
      (claim_11_coprime_involution_decomposition R P s
        hRcomm hRodd hch.section3.2.2.1 hs_norm_R hP_le_R hfixed)
  rcases hDecomp with ⟨hR, hdisj, hTinverted⟩
  have hT_le_R : T ≤ R := by
    rw [hR]
    exact le_sup_left
  have hRcentral : R ≤ Subgroup.centralizer (P : Set G) := by
    simpa [C] using hR_le_C
  have hTcentral : T ≤ Subgroup.centralizer (P : Set G) :=
    hT_le_R.trans hRcentral
  have hWCnorm :
      (W ⊓ Subgroup.centralizer (P : Set G)) ≤
        Subgroup.normalizer (T : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem T
      (W ⊓ Subgroup.centralizer (P : Set G)) ?_
    intro w x hxT
    have hwC : (w : G) ∈ C := by
      simpa [C] using w.property.2
    have hwNormR : (w : G) ∈ Subgroup.normalizer (R : Set G) :=
      hC_le_norm_R hwC
    have hxConjR : (w : G) * x * (w : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hwNormR x).1 (hT_le_R hxT)
    have hwV : (w : G) ∈ V :=
      hch.section3.section2.W_le_V w.property.1
    rw [hVeqCs] at hwV
    have hws : Commute (w : G) s :=
      Subgroup.mem_centralizer_singleton_iff.mp hwV.2
    have hxConjInv :
        rightConjugateElem ((w : G) * x * (w : G)⁻¹) s =
          ((w : G) * x * (w : G)⁻¹)⁻¹ := by
      calc
        rightConjugateElem ((w : G) * x * (w : G)⁻¹) s =
            s⁻¹ * ((w : G) * x * (w : G)⁻¹) * s := rfl
        _ = (s⁻¹ * (w : G)) * x * ((w : G)⁻¹ * s) := by group
        _ = ((w : G) * s⁻¹) * x * (s * (w : G)⁻¹) := by
          rw [hws.symm.inv_left.eq, hws.symm.inv_right.eq]
        _ = (w : G) * (s⁻¹ * x * s) * (w : G)⁻¹ := by group
        _ = (w : G) * x⁻¹ * (w : G)⁻¹ := by
          have hxInv := hTinverted x hxT
          change s⁻¹ * x * s = x⁻¹ at hxInv
          rw [hxInv]
        _ = ((w : G) * x * (w : G)⁻¹)⁻¹ := by group
    exact claim_11_mem_T_of_mem_R_of_inverted
      R P T s hRcomm hRodd hch.section3.2.2.1 hR hTcentral
        hfixed hTinverted hxConjR hxConjInv
  have hT_le_C : T ≤ C := hT_le_R.trans hR_le_C
  have hcoreP : core = P.subgroupOf C := by
    rw [← hNcoreLocal, hNP]
  have hCQnorm :
      (Q ⊓ Subgroup.centralizer (P : Set G)) ≤
        Subgroup.normalizer (T : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem T
      (Q ⊓ Subgroup.centralizer (P : Set G)) ?_
    intro q x hxT
    let b : Fˣ := unitEquiv.symm q
    have hbu : b * u = u * b := by
      let z : Fˣ := b * u * b⁻¹
      have hzSq : z ^ 2 = 1 := by
        calc
          z ^ 2 = b * (u ^ 2) * b⁻¹ := by simp [z, pow_two]
          _ = 1 := by rw [huSq]; simp
      have hzNe : z ≠ 1 := by
        intro hzOne
        apply huNe
        calc
          u = b⁻¹ * z * b := by dsimp [z]; group
          _ = b⁻¹ * 1 * b := by rw [hzOne]
          _ = 1 := by simp
      have hzValSq : (z : F) ^ 2 = 1 := by
        simpa using congrArg (fun y : Fˣ => (y : F)) hzSq
      have hzVal : (z : F) = -1 := by
        rcases
            PFAppendixII.rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one
              hzValSq with hzOne | hzNeg
        · exact (hzNe (Units.ext hzOne)).elim
        · exact hzNeg
      have hzu : z = u := Units.ext (hzVal.trans huVal.symm)
      calc
        b * u = z * b := by simp [z]
        _ = u * b := by rw [hzu]
    have hunitComm : unitLift b * unitLift u = unitLift u * unitLift b := by
      calc
        unitLift b * unitLift u = unitLift (b * u) := (hunitMul b u).symm
        _ = unitLift (u * b) := by rw [hbu]
        _ = unitLift u * unitLift b := hunitMul u b
    let qC : C := ⟨(q : G), q.property.2⟩
    have hqCoordinate : QuotientGroup.mk' core qC = unitLift b := by
      have hb := unitEquiv.apply_symm_apply q
      simpa [qC, b, hb] using hunitCoordinate b
    have hqsQuotient :
        QuotientGroup.mk' core (qC * sC) =
          QuotientGroup.mk' core (sC * qC) := by
      calc
        QuotientGroup.mk' core (qC * sC) =
            QuotientGroup.mk' core qC * QuotientGroup.mk' core sC := map_mul _ _ _
        _ = unitLift b * unitLift u := by rw [hqCoordinate, huCoord]
        _ = unitLift u * unitLift b := hunitComm
        _ = QuotientGroup.mk' core sC * QuotientGroup.mk' core qC := by
          rw [hqCoordinate, huCoord]
        _ = QuotientGroup.mk' core (sC * qC) := (map_mul _ _ _).symm
    have hkCore : (qC * sC) / (sC * qC) ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hqsQuotient
    have hkPsub : (qC * sC) / (sC * qC) ∈ P.subgroupOf C := by
      rw [← hcoreP]
      exact hkCore
    let k : G := (q : G) * s * (s * (q : G))⁻¹
    have hkP : k ∈ P := by
      change (((qC * sC) / (sC * qC) : C) : G) ∈ P at hkPsub
      simpa [k, div_eq_mul_inv, qC, sC] using hkPsub
    have hqNormR : (q : G) ∈ Subgroup.normalizer (R : Set G) :=
      hC_le_norm_R (by simpa [C] using q.property.2)
    have hsqNormR :
        s * (q : G) ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).mul_mem hs_norm_R hqNormR
    let y : G := (s * (q : G)) * x * (s * (q : G))⁻¹
    have hyR : y ∈ R := by
      exact (Subgroup.mem_normalizer_iff.mp hsqNormR x).1 (hT_le_R hxT)
    have hky : k * y = y * k :=
      (Subgroup.mem_centralizer_iff.mp (hRcentral hyR)) k hkP
    have hfactor : (q : G) * s = k * (s * (q : G)) := by
      simp [k]
      group
    have hactions :
        ((q : G) * s) * x * ((q : G) * s)⁻¹ =
          (s * (q : G)) * x * (s * (q : G))⁻¹ := by
      calc
        ((q : G) * s) * x * ((q : G) * s)⁻¹ =
            (k * (s * (q : G))) * x * (k * (s * (q : G)))⁻¹ := by
              rw [hfactor]
        _ = k * y * k⁻¹ := by simp [y]; group
        _ = y := by rw [hky]; simp
        _ = (s * (q : G)) * x * (s * (q : G))⁻¹ := rfl
    have hsInv : s⁻¹ = s := hch.section3.2.2.1.inv_eq_self
    have hxConjR : (q : G) * x * (q : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hqNormR x).1 (hT_le_R hxT)
    have hxConjInv :
        rightConjugateElem ((q : G) * x * (q : G)⁻¹) s =
          ((q : G) * x * (q : G)⁻¹)⁻¹ := by
      have hxInv := hTinverted x hxT
      change s⁻¹ * x * s = x⁻¹ at hxInv
      have hxInv' : s * x * s = x⁻¹ := by
        calc
          s * x * s = s⁻¹ * x * s := by rw [hsInv]
          _ = x⁻¹ := hxInv
      calc
        rightConjugateElem ((q : G) * x * (q : G)⁻¹) s =
            s * ((q : G) * x * (q : G)⁻¹) * s⁻¹ := by
              simp only [rightConjugateElem, hsInv]
        _ = (s * (q : G)) * x * (s * (q : G))⁻¹ := by group
        _ = ((q : G) * s) * x * ((q : G) * s)⁻¹ := hactions.symm
        _ = (q : G) * (s * x * s⁻¹) * (q : G)⁻¹ := by group
        _ = (q : G) * x⁻¹ * (q : G)⁻¹ := by
          rw [hsInv, hxInv']
        _ = ((q : G) * x * (q : G)⁻¹)⁻¹ := by group
    exact claim_11_mem_T_of_mem_R_of_inverted
      R P T s hRcomm hRodd hch.section3.2.2.1 hR hTcentral
        hfixed hTinverted hxConjR hxConjInv
  obtain ⟨addEquiv, haddQuotient⟩ :=
    claim_11_additive_equiv_of_decomposition C core P R T
      addLift haddZero hadd (by rfl) hcoreP hR hdisj hT_le_C hP_le_C hTcentral
        haddHom_injective
  have hinverseN :
      ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
        (g ∈ R ↔ ∃ x : F,
          g * (((addEquiv (Multiplicative.ofAdd x) : T) : G))⁻¹ ∈ N) := by
    intro g hgC
    let gC : C := ⟨g, by simpa [C] using hgC⟩
    constructor
    · intro hgR
      have hgPre : gC ∈ addHom.range.comap (QuotientGroup.mk' core) := by
        change g ∈ (addHom.range.comap (QuotientGroup.mk' core)).map C.subtype at hgR
        rcases hgR with ⟨y, hyPre, hyg⟩
        have hy : y = gC := by
          apply Subtype.ext
          exact hyg
        simpa [hy] using hyPre
      change QuotientGroup.mk' core gC ∈ addHom.range at hgPre
      rcases hgPre with ⟨a, ha⟩
      let x : F := Multiplicative.toAdd a
      rcases haddQuotient x with ⟨c, hcval, hcpi⟩
      refine ⟨x, ?_⟩
      have hquot : QuotientGroup.mk' core gC = QuotientGroup.mk' core c := by
        calc
          QuotientGroup.mk' core gC = addHom a := ha.symm
          _ = addLift x := by rfl
          _ = QuotientGroup.mk' core c := hcpi.symm
      have hdivCore : gC / c ∈ core :=
        QuotientGroup.eq_iff_div_mem.mp hquot
      have hdivNsub : gC / c ∈ N.subgroupOf C := by
        rw [hNcoreLocal]
        exact hdivCore
      change (((gC / c : C) : G) ∈ N) at hdivNsub
      simpa [gC, hcval, div_eq_mul_inv] using hdivNsub
    · rintro ⟨x, hxN⟩
      rcases haddQuotient x with ⟨c, hcval, hcpi⟩
      have hdivNsub : gC / c ∈ N.subgroupOf C := by
        change (((gC / c : C) : G) ∈ N)
        simpa [gC, hcval, div_eq_mul_inv] using hxN
      have hdivCore : gC / c ∈ core := by
        rw [← hNcoreLocal]
        exact hdivNsub
      have hquot : QuotientGroup.mk' core gC = QuotientGroup.mk' core c :=
        QuotientGroup.eq_iff_div_mem.mpr hdivCore
      have hgPre : gC ∈ addHom.range.comap (QuotientGroup.mk' core) := by
        change QuotientGroup.mk' core gC ∈ addHom.range
        refine ⟨Multiplicative.ofAdd x, ?_⟩
        change addLift x = QuotientGroup.mk' core gC
        exact hcpi.symm.trans hquot.symm
      exact ⟨gC, hgPre, rfl⟩
  have hcoordinate : ∀ a : F, ∀ b : Fˣ,
      rightConjugateElem
          (((addEquiv (Multiplicative.ofAdd a) : T) : G))
          (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) =
        (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G)) := by
    intro a b
    have haT :
        (((addEquiv (Multiplicative.ofAdd a) : T) : G)) ∈ T :=
      (addEquiv (Multiplicative.ofAdd a)).property
    have hleftT :
        rightConjugateElem
            (((addEquiv (Multiplicative.ofAdd a) : T) : G))
            (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) ∈ T :=
      claim_11_rightConjugateElem_mem_T_of_CQ
        Q T P hCQnorm haT (unitEquiv b).property
    have habT :
        (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G)) ∈ T :=
      (addEquiv (Multiplicative.ofAdd (a * (b : F)))).property
    rcases haddQuotient a with ⟨ca, hcaval, hcapi⟩
    rcases haddQuotient (a * (b : F)) with ⟨cab, hcabval, hcabpi⟩
    let bC : C :=
      ⟨((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G),
        (unitEquiv b).property.2⟩
    have hbpi : QuotientGroup.mk' core bC = unitLift b := by
      simpa [bC] using hunitCoordinate b
    have hquot :
        QuotientGroup.mk' core (rightConjugateElem ca bC) =
          QuotientGroup.mk' core cab := by
      calc
        QuotientGroup.mk' core (rightConjugateElem ca bC) =
            rightConjugateElem
              (QuotientGroup.mk' core ca) (QuotientGroup.mk' core bC) := by
                simp [rightConjugateElem]
        _ = rightConjugateElem (addLift a) (unitLift b) := by
              rw [hcapi, hbpi]
        _ = addLift (a * (b : F)) := hrightQ a b
        _ = QuotientGroup.mk' core cab := hcabpi.symm
    have hdivCore : rightConjugateElem ca bC / cab ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hquot
    have hdivNsub : rightConjugateElem ca bC / cab ∈ N.subgroupOf C := by
      rw [hNcoreLocal]
      exact hdivCore
    have hleftVal : ((rightConjugateElem ca bC : C) : G) =
        rightConjugateElem
          (((addEquiv (Multiplicative.ofAdd a) : T) : G))
          (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) := by
      change rightConjugateElem (ca : G) (bC : G) = _
      rw [hcaval]
    have hleftTC : ((rightConjugateElem ca bC : C) : G) ∈ T := by
      rw [hleftVal]
      exact hleftT
    have habTC : (cab : G) ∈ T := by
      rw [hcabval]
      exact habT
    have hdivT : (((rightConjugateElem ca bC / cab : C) : G)) ∈ T := by
      change ((rightConjugateElem ca bC : C) : G) / (cab : G) ∈ T
      exact T.div_mem hleftTC habTC
    have hdivP : (((rightConjugateElem ca bC / cab : C) : G)) ∈ P := by
      change (((rightConjugateElem ca bC / cab : C) : G)) ∈ N at hdivNsub
      rw [hNP] at hdivNsub
      exact hdivNsub
    have hdivBot : (((rightConjugateElem ca bC / cab : C) : G)) ∈
        (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdisj) hdivT hdivP
    have hdivOneG : (((rightConjugateElem ca bC / cab : C) : G)) = 1 :=
      Subgroup.mem_bot.mp hdivBot
    have hdivOneC : rightConjugateElem ca bC / cab = 1 := by
      apply Subtype.ext
      simpa using hdivOneG
    have hEqC : rightConjugateElem ca bC = cab := div_eq_one.mp hdivOneC
    have hEqG := congrArg Subtype.val hEqC
    calc
      rightConjugateElem
          (((addEquiv (Multiplicative.ofAdd a) : T) : G))
          (((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G)) =
          ((rightConjugateElem ca bC : C) : G) := hleftVal.symm
      _ = (cab : G) := hEqG
      _ = (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G)) := hcabval
  have hst_inverted :
      rightConjugateElem (s * t) s = (s * t)⁻¹ := by
    have hsInv : s⁻¹ = s := by
      have hsMul : s * s = 1 := by
        simpa only [pow_two] using hch.section3.2.2.1.sq_eq_one
      exact (eq_inv_of_mul_eq_one_right hsMul).symm
    have htInv : t⁻¹ = t := by
      have htMul : t * t = 1 := by
        simpa only [pow_two] using hch.section3.section2.hA.A1.involution_t.sq_eq_one
      exact (eq_inv_of_mul_eq_one_right htMul).symm
    calc
      rightConjugateElem (s * t) s = s * (s * t) * s := by
        rw [rightConjugateElem, hsInv]
      _ = (s * s) * t * s := by group
      _ = t * s := by
        simp [← pow_two, hch.section3.2.2.1.sq_eq_one]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hsInv, htInv]
  have hst_mem_T : s * t ∈ T :=
    claim_11_mem_T_of_mem_R_of_inverted
      R P T s hRcomm hRodd hch.section3.2.2.1 hR hTcentral
        hfixed hTinverted hst_mem_R hst_inverted
  have hDisjCQ : Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) :=
    claim_11_disjoint_T_CQ_of_coordinates
      Q P R T hT_le_R hRcomm addEquiv unitEquiv hcoordinate
  have hNorm :
      (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
        W ⊓ Subgroup.centralizer (P : Set G)) ≤
          Subgroup.normalizer (T : Set G) :=
    sup_le hCQnorm hWCnorm
  have hTregular :=
    claim_11_T_regular_nonzero_of_nearField_coordinates
      Q P T addEquiv unitEquiv hcoordinate
  have hSubgroups :=
    claim_11_order_p_subgroups_regular
      H D Q K V W Q0 S Q1 P R T t s p hch
        hR hdisj hTcentral hNorm hDisjCQ hCQnorm hTregular
  have hCdecompAll :
      ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
        ∃ r q w : G, r ∈ R ∧
          q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
            w ∈ W ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q * w := by
    intro g hgC
    let gC : C := ⟨g, hgC⟩
    rcases hcoordinates.2 (pi gC) with ⟨⟨a, u, d⟩, hcoord⟩
    rcases haddQuotient a with ⟨aC, haCval, haCpi⟩
    let q : ↥(Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := unitEquiv u
    let qC : C := ⟨(q : G), q.property.2⟩
    have hqCpi : pi qC = unitLift u := by
      change QuotientGroup.mk' core qC = unitLift u
      exact hunitCoordinate u
    let w : ↥(W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := eSigma d
    let wC : C := ⟨(w : G), w.property.2⟩
    have hwCpi : pi wC = (d : C ⧸ core) := by
      change QuotientGroup.mk' core wC = (d : C ⧸ core)
      exact heSigma d
    have hprodPi : pi (aC * qC * wC) = pi gC := by
      calc
        pi (aC * qC * wC) =
            addLift a * unitLift u * (d : C ⧸ core) := by
          rw [map_mul, map_mul, haCpi, hqCpi, hwCpi]
        _ = pi gC := hcoord
    have hdivCore : gC / (aC * qC * wC) ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hprodPi.symm
    have hdivP : ((gC / (aC * qC * wC) : C) : G) ∈ P := by
      rw [hcoreP] at hdivCore
      exact hdivCore
    let k : G := ((gC / (aC * qC * wC) : C) : G)
    let r : G := k * (aC : G)
    have haR : (aC : G) ∈ R := by
      rw [haCval]
      exact hT_le_R (addEquiv (Multiplicative.ofAdd a)).property
    have hkR : k ∈ R := by
      simpa [k] using hP_le_R hdivP
    have hrR : r ∈ R := R.mul_mem hkR haR
    refine ⟨r, (q : G), (w : G), hrR, q.property, w.property, ?_⟩
    dsimp [r, k]
    change (gC : G) =
      ((gC / (aC * qC * wC) : C) : G) * (aC : G) * (qC : G) * (wC : G)
    simp [div_eq_mul_inv]
    group
  have hSigmaBotOfMOne :
      m = 1 → (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ := by
    intro hm1
    have hFcardPrime : Nat.card F = p := by
      calc
        Nat.card F = addOrderOf (1 : F) ^ m := hFcard
        _ = p ^ m := by rw [hcharP]
        _ = p := by rw [hm1, pow_one]
    have hZtop : AddSubgroup.zmultiples (1 : F) = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      calc
        Nat.card (AddSubgroup.zmultiples (1 : F)) = addOrderOf (1 : F) :=
          Nat.card_zmultiples (1 : F)
        _ = p := hcharP
        _ = Nat.card F := hFcardPrime.symm
    have hsigmaEq (d : DP.map pi) (a : F) : sigmaAct d a = a := by
      have hsigmaZero : sigmaAct d 0 = 0 := by
        have h := (hsigmaMaps d 0 0).1
        simp only [zero_add] at h
        have h' : sigmaAct d 0 + 0 = sigmaAct d 0 + sigmaAct d 0 := by
          simpa using h
        exact (add_left_cancel h').symm
      let sigmaHom : F →+ F :=
        { toFun := sigmaAct d
          map_zero' := hsigmaZero
          map_add' := fun x y => (hsigmaMaps d x y).1 }
      have haZ : a ∈ AddSubgroup.zmultiples (1 : F) := by rw [hZtop]; trivial
      rcases AddSubgroup.mem_zmultiples_iff.mp haZ with ⟨k, rfl⟩
      calc
        sigmaAct d (k • (1 : F)) = sigmaHom (k • (1 : F)) := rfl
        _ = k • sigmaHom (1 : F) := sigmaHom.map_zsmul k (1 : F)
        _ = k • (1 : F) := by
          change k • sigmaAct d 1 = k • (1 : F)
          rw [(hsigmaMaps d 0 0).2.2]
    have hSigmaOne :
        ∀ w : ↥(W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G), w = 1 := by
      intro w
      let d : DP.map pi := eSigma.symm w
      have hdOne : d = 1 := by
        apply hsigmaInjective
        funext a
        exact (hsigmaEq d a).trans (hsigmaOne a).symm
      calc
        w = eSigma d := (eSigma.apply_symm_apply w).symm
        _ = eSigma 1 := by rw [hdOne]
        _ = 1 := map_one eSigma
    apply le_antisymm
    · intro w hw
      exact congrArg Subtype.val (hSigmaOne ⟨w, hw⟩)
    · exact bot_le
  have hCQCommS :
      ∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) → q * s = s * q := by
    intro q hq
    let qSub : ↥(Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := ⟨q, hq⟩
    let b : Fˣ := unitEquiv.symm qSub
    have hbu : b * u = u * b := by
      let z : Fˣ := b * u * b⁻¹
      have hzSq : z ^ 2 = 1 := by
        calc
          z ^ 2 = b * (u ^ 2) * b⁻¹ := by simp [z, pow_two]
          _ = 1 := by rw [huSq]; simp
      have hzNe : z ≠ 1 := by
        intro hzOne
        apply huNe
        calc
          u = b⁻¹ * z * b := by dsimp [z]; group
          _ = b⁻¹ * 1 * b := by rw [hzOne]
          _ = 1 := by simp
      have hzValSq : (z : F) ^ 2 = 1 := by
        simpa using congrArg (fun y : Fˣ => (y : F)) hzSq
      have hzVal : (z : F) = -1 := by
        rcases PFAppendixII.rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one
            hzValSq with hzOne | hzNeg
        · exact (hzNe (Units.ext hzOne)).elim
        · exact hzNeg
      have hzu : z = u := Units.ext (hzVal.trans huVal.symm)
      calc
        b * u = z * b := by simp [z]
        _ = u * b := by rw [hzu]
    have hunitComm : unitLift b * unitLift u = unitLift u * unitLift b := by
      calc
        unitLift b * unitLift u = unitLift (b * u) := (hunitMul b u).symm
        _ = unitLift (u * b) := by rw [hbu]
        _ = unitLift u * unitLift b := hunitMul u b
    let qC : C := ⟨q, hq.2⟩
    have hqCoordinate : pi qC = unitLift b := by
      have hb := unitEquiv.apply_symm_apply qSub
      change QuotientGroup.mk' core qC = unitLift b
      have hqC_eq :
          qC =
            ⟨((unitEquiv b : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G),
              (unitEquiv b).property.2⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val hb).symm
      rw [hqC_eq]
      exact hunitCoordinate b
    have hqsQuotient : pi (qC * sC) = pi (sC * qC) := by
      calc
        pi (qC * sC) = pi qC * pi sC := map_mul _ _ _
        _ = unitLift b * unitLift u := by rw [hqCoordinate, huCoord]
        _ = unitLift u * unitLift b := hunitComm
        _ = pi sC * pi qC := by rw [hqCoordinate, huCoord]
        _ = pi (sC * qC) := (map_mul _ _ _).symm
    have hkCore : (qC * sC) / (sC * qC) ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hqsQuotient
    have hkPsub : (qC * sC) / (sC * qC) ∈ P.subgroupOf C := by
      rw [← hcoreP]
      exact hkCore
    let k : G := q * s * (s * q)⁻¹
    have hkP : k ∈ P := by
      change (((qC * sC) / (sC * qC) : C) : G) ∈ P at hkPsub
      simpa [k, div_eq_mul_inv, qC, sC] using hkPsub
    have hkQ : k ∈ Q := by
      exact Q.mul_mem (Q.mul_mem hq.1 hsQ) (Q.inv_mem (Q.mul_mem hsQ hq.1))
    have hkBot : k ∈ (⊥ : Subgroup G) :=
      hch.section3.section2.hA.A1.Q_disjoint_D.le_bot ⟨hkQ, hP_le_D hkP⟩
    have hkOne : k = 1 := Subgroup.mem_bot.mp hkBot
    exact div_eq_one.mp (by simpa [k, div_eq_mul_inv] using hkOne)
  have hExceptionalLocal :
      p = 3 →
        Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 3 →
          Nat.card (nearFieldStar Q P) = 8 →
            let Sigma : Subgroup G := W ⊓ Subgroup.centralizer (P : Set G)
            Disjoint R Sigma ∧ Nat.card (R ⊔ Sigma : Subgroup G) = 3 ^ 4 ∧
              ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) ∧
                (∃ XC : Sylow 3 (Subgroup.centralizer (P : Set G)),
                  (XC : Subgroup (Subgroup.centralizer (P : Set G))) =
                    (R ⊔ Sigma).subgroupOf
                      (Subgroup.centralizer (P : Set G))) ∧
                  ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
                    ∃ r q w : G, r ∈ R ∧
                      q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                        w ∈ Sigma ∧ g = r * q * w := by
    intro hp3 hSigma3 hStar8
    have hm2 : m = 2 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      calc
        3 ^ m = p ^ m := by rw [hp3]
        _ = Nat.card (nearFieldStar Q P) + 1 := hStarComm_order.symm
        _ = 8 + 1 := by rw [hStar8]
        _ = 3 ^ 2 := by norm_num
    let Sigma : Subgroup G := W ⊓ Subgroup.centralizer (P : Set G)
    have hSigma_norm_R : Sigma ≤ Subgroup.normalizer (R : Set G) := by
      intro x hx
      exact hC_le_norm_R hx.2
    have hR_coordinate_local (x : G) (hxR : x ∈ R) :
        ∃ a : F, ∃ xC : C, (xC : G) = x ∧ pi xC = addLift a := by
      let xC : C := ⟨x, hR_le_C hxR⟩
      have hxM : xC ∈ M := by
        change x ∈ M.map C.subtype at hxR
        rcases hxR with ⟨z, hzM, hzx⟩
        have hz : z = xC := by
          apply Subtype.ext
          exact hzx
        simpa [hz] using hzM
      change pi xC ∈ addHom.range at hxM
      rcases hxM with ⟨a, ha⟩
      exact ⟨Multiplicative.toAdd a, xC, rfl, ha.symm⟩
    have hR_disj_Sigma : Disjoint R Sigma := by
      rw [Subgroup.disjoint_def]
      intro x hxR hxSigma
      obtain ⟨a, xC, hxCval, hxCpi⟩ := hR_coordinate_local x hxR
      have hxAdd : pi xC ∈ addHom.range :=
        ⟨Multiplicative.ofAdd a, hxCpi.symm⟩
      have hxDP : xC ∈ DP := by
        change (xC : G) ∈ D
        rw [hxCval]
        exact PFchapter1section2.proposition_3_W_le_D
          H D Q K V W Q0 S Q1 t hch.section3.section2 hxSigma.1
      have hxDbar : pi xC ∈ Dbar := ⟨xC, hxDP, rfl⟩
      have hxHbar : pi xC ∈ Hbar := hDbar_le_Hbar hxDbar
      have hxBot : pi xC ∈ (⊥ : Subgroup (C ⧸ core)) :=
        (Subgroup.disjoint_def.mp hAddRangeDisjointHbar) hxAdd hxHbar
      have hxPiOne : pi xC = 1 := Subgroup.mem_bot.mp hxBot
      have hxCore : xC ∈ core := (QuotientGroup.eq_one_iff xC).1 hxPiOne
      rw [hcoreP] at hxCore
      have hxP : x ∈ P := by
        simpa [Subgroup.mem_subgroupOf, hxCval] using hxCore
      have hWPdisj : Disjoint W P :=
        (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1.2.2.2.1
      have hxOne : x = 1 := Subgroup.mem_bot.mp
        ((Subgroup.disjoint_def.mp hWPdisj) hxSigma.1 hxP)
      exact hxOne
    have hXcard : Nat.card (R ⊔ Sigma : Subgroup G) = 3 ^ 4 := by
      calc
        Nat.card (R ⊔ Sigma : Subgroup G) = Nat.card R * Nat.card Sigma :=
          claim_11_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
            R Sigma hSigma_norm_R hR_disj_Sigma
        _ = 3 ^ (m + 1) * 3 := by
          rw [hRcardPow, hp3]
          simpa [Sigma] using hSigma3
        _ = 3 ^ 4 := by rw [hm2]; norm_num
    have hXnoncomm : ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) := by
      intro hXcomm
      let : IsMulCommutative (R ⊔ Sigma : Subgroup G) := hXcomm
      have hSigma_one : ∀ w : Sigma, w = 1 := by
        intro w
        let dBar : DP.map (QuotientGroup.mk' core) := eSigma.symm w
        have hdBarOne : dBar = 1 := by
          apply hsigmaInjective
          funext a
          rcases haddQuotient a with ⟨aC, haCval, haCpi⟩
          let wC : C := ⟨(w : G), w.property.2⟩
          have hwCpi : pi wC = (dBar : C ⧸ core) := by
            let ewC : C :=
              ⟨((eSigma dBar : ↥(W ⊓ Subgroup.centralizer (P : Set G))) : G),
                (eSigma dBar).property.2⟩
            have hwCEq : wC = ewC := by
              apply Subtype.ext
              exact congrArg (fun z : Sigma => (z : G))
                (eSigma.apply_symm_apply w).symm
            calc
              pi wC = pi ewC := congrArg pi hwCEq
              _ = (dBar : C ⧸ core) := heSigma dBar
          have haR : (aC : G) ∈ R := by
            rw [haCval]
            exact hT_le_R (addEquiv (Multiplicative.ofAdd a)).property
          let aX : ↥(R ⊔ Sigma : Subgroup G) :=
            ⟨(aC : G), Subgroup.mem_sup_left haR⟩
          let wX : ↥(R ⊔ Sigma : Subgroup G) :=
            ⟨(w : G), Subgroup.mem_sup_right w.property⟩
          have hcommX : (aC : G) * (w : G) = (w : G) * (aC : G) :=
            congrArg Subtype.val
              ((IsMulCommutative.is_comm
                (M := ↥(R ⊔ Sigma : Subgroup G))).comm aX wX)
          have hrightFixed : rightConjugateElem aC wC = aC := by
            apply Subtype.ext
            change (w : G)⁻¹ * (aC : G) * (w : G) = (aC : G)
            calc
              (w : G)⁻¹ * (aC : G) * (w : G) =
                  (w : G)⁻¹ * ((aC : G) * (w : G)) := by rw [mul_assoc]
              _ = (w : G)⁻¹ * ((w : G) * (aC : G)) := by rw [hcommX]
              _ = (aC : G) := by simp
          apply haddLift_injective
          calc
            addLift (sigmaAct dBar a) =
                rightConjugateElem (addLift a) (dBar : C ⧸ core) :=
              (hrightSigma dBar a).symm
            _ = rightConjugateElem (pi aC) (pi wC) := by
              rw [haCpi, hwCpi]
            _ = pi (rightConjugateElem aC wC) := by
              simp [rightConjugateElem]
            _ = pi aC := by rw [hrightFixed]
            _ = addLift a := haCpi
            _ = addLift (sigmaAct 1 a) := by rw [hsigmaOne]
        calc
          w = eSigma dBar := (eSigma.apply_symm_apply w).symm
          _ = eSigma 1 := by rw [hdBarOne]
          _ = 1 := map_one eSigma
      have hSigmaBot : Sigma = ⊥ := by
        apply le_antisymm
        · intro w hw
          have hwOne : (⟨w, hw⟩ : Sigma) = 1 := hSigma_one ⟨w, hw⟩
          exact congrArg Subtype.val hwOne
        · exact bot_le
      have hSigmaCardOne : Nat.card Sigma = 1 := by simp [hSigmaBot]
      have hSigmaCardThree : Nat.card Sigma = 3 := by
        simpa [Sigma] using hSigma3
      omega
    have hX_le_C : R ⊔ Sigma ≤ C := by
      exact sup_le hR_le_C (by intro x hx; exact hx.2)
    let XC : Subgroup C := (R ⊔ Sigma).subgroupOf C
    have hXCcard : Nat.card XC = 3 ^ 4 := by
      calc
        Nat.card XC = Nat.card (R ⊔ Sigma : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_C).toEquiv
        _ = 3 ^ 4 := hXcard
    have hCcardExceptional : Nat.card C = 3 ^ 4 * 8 := by
      calc
        Nat.card C = p ^ (m + 1) *
            (Nat.card Fˣ *
              Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) :=
          hCcardFactor
        _ = 3 ^ 4 * 8 := by
          rw [hp3, hm2, hSigma3]
          have hUnits8 : Nat.card Fˣ = 8 := by
            rw [hUnitsCard, hp3, hm2]
            norm_num
          rw [hUnits8]
          norm_num
    have hXCindex : XC.index = 8 := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 4)
      calc
        3 ^ 4 * XC.index = Nat.card XC * XC.index := by rw [hXCcard]
        _ = Nat.card C := XC.card_mul_index
        _ = 3 ^ 4 * 8 := hCcardExceptional
    have hXCp : IsPGroup 3 XC := IsPGroup.of_card hXCcard
    let XCsylow : Sylow 3 C := hXCp.toSylow (by
      rw [hXCindex]
      norm_num)
    have hXCsylow :
        (XCsylow : Subgroup C) =
          (R ⊔ Sigma).subgroupOf C := by rfl
    have hCdecomp :
        ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
          ∃ r q w : G, r ∈ R ∧
            q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
              w ∈ Sigma ∧ g = r * q * w := by
      intro g hgC
      let gC : C := ⟨g, hgC⟩
      rcases hcoordinates.2 (pi gC) with ⟨⟨a, u, d⟩, hcoord⟩
      rcases haddQuotient a with ⟨aC, haCval, haCpi⟩
      let q : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := unitEquiv u
      let qC : C := ⟨(q : G), q.property.2⟩
      have hqCpi : pi qC = unitLift u := by
        change QuotientGroup.mk' core qC = unitLift u
        exact hunitCoordinate u
      let w : Sigma := eSigma d
      let wC : C := ⟨(w : G), w.property.2⟩
      have hwCpi : pi wC = (d : C ⧸ core) := by
        change QuotientGroup.mk' core wC = (d : C ⧸ core)
        exact heSigma d
      have hprodPi : pi (aC * qC * wC) = pi gC := by
        calc
          pi (aC * qC * wC) =
              addLift a * unitLift u * (d : C ⧸ core) := by
            rw [map_mul, map_mul, haCpi, hqCpi, hwCpi]
          _ = pi gC := hcoord
      have hdivCore : gC / (aC * qC * wC) ∈ core :=
        QuotientGroup.eq_iff_div_mem.mp hprodPi.symm
      have hdivP : ((gC / (aC * qC * wC) : C) : G) ∈ P := by
        rw [hcoreP] at hdivCore
        exact hdivCore
      let k : G := ((gC / (aC * qC * wC) : C) : G)
      let r : G := k * (aC : G)
      have haR : (aC : G) ∈ R := by
        rw [haCval]
        exact hT_le_R (addEquiv (Multiplicative.ofAdd a)).property
      have hkR : k ∈ R := by
        simpa [k] using hP_le_R hdivP
      have hrR : r ∈ R := R.mul_mem hkR haR
      refine ⟨r, (q : G), (w : G), hrR, q.property, w.property, ?_⟩
      dsimp [r, k]
      change (gC : G) =
        ((gC / (aC * qC * wC) : C) : G) * (aC : G) * (qC : G) * (wC : G)
      simp [div_eq_mul_inv]
      group
    exact ⟨hR_disj_Sigma, hXcard, hXnoncomm,
      ⟨XCsylow, hXCsylow⟩, hCdecomp⟩
  have hCaseOneLocal :
      ∀ m' : ℕ,
        Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
        ¬ p ∣ Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
        Subgroup.centralizer (P : Set G) ≤
            Subgroup.normalizer (R : Set G) ∧
          Nat.card R = p ^ (m' + 1) ∧
            Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
              p ^ m' ∧
            ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
              (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
                R.subgroupOf (Subgroup.centralizer (P : Set G)) := by
    intro m' hStar' hpSigma
    have hm' : m' = m := by
      apply Nat.pow_right_injective hch.B1.p_prime.one_lt
      calc
        p ^ m' = Nat.card (nearFieldStar Q P) + 1 := hStar'.symm
        _ = p ^ m := hStarComm_order
    have hRcard' : Nat.card R = p ^ (m' + 1) := by
      rw [hm']
      exact hRcardPow
    have hRCp : IsPGroup p RC := by
      apply IsPGroup.of_card (n := m' + 1)
      rw [hRCcard, hRcard']
    have hp_not_units : ¬ p ∣ Nat.card Fˣ := by
      rw [hUnitsCard]
      intro hd
      have hmpos : 0 < m := by
        let : Fintype F := Fintype.ofFinite F
        have hFgt : 1 < Nat.card F := by
          simpa [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
        have hFcardPow : Nat.card F = p ^ m := by
          calc
            Nat.card F = addOrderOf (1 : F) ^ m := hFcard
            _ = p ^ m := by rw [hcharP]
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        rw [hm0, pow_zero] at hFcardPow
        omega
      have hpPow : p ∣ p ^ m := dvd_pow_self p hmpos.ne'
      have hone_le : 1 ≤ p ^ m := by
        exact (pow_pos hch.B1.p_prime.pos m)
      have hsum : p ∣ (p ^ m - 1) + 1 := by
        rw [Nat.sub_add_cancel hone_le]
        exact hpPow
      have hpOne : p ∣ 1 := (Nat.dvd_add_iff_left hd).mpr (by
        simpa [Nat.add_comm] using hsum)
      exact hch.B1.p_prime.not_dvd_one hpOne
    have hindex_not : ¬ p ∣ RC.index := by
      rw [hRCindex]
      exact hch.B1.p_prime.not_dvd_mul hp_not_units hpSigma
    let RCSylow : Sylow p C := hRCp.toSylow hindex_not
    have hCQcard :
        Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
          p ^ m' := by
      calc
        Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
            Nat.card Fˣ + 1 := by
          rw [Nat.card_congr unitEquiv.toEquiv]
        _ = (p ^ m - 1) + 1 := by rw [hUnitsCard]
        _ = p ^ m := by
          have hpos : 0 < p ^ m := pow_pos hch.B1.p_prime.pos m
          omega
        _ = p ^ m' := by rw [hm']
    refine ⟨?_, hRcard', hCQcard, ?_⟩
    · simpa [C] using hC_le_norm_R
    · exact ⟨RCSylow, by simp [RCSylow, RC, C]⟩
  have hCaseOneMOne :
      ∀ m' : ℕ,
        Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
        ¬ p ∣ Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
        m' = 1 →
        s ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
          (∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (P : Set G) →
            q * s = s * q) ∧
          (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = ⊥ ∧
          ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
            ∃ r q : G, r ∈ R ∧
              q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ g = r * q := by
    intro m' hStar' _hpSigma hmOne
    have hm' : m' = m := by
      apply Nat.pow_right_injective hch.B1.p_prime.one_lt
      calc
        p ^ m' = Nat.card (nearFieldStar Q P) + 1 := hStar'.symm
        _ = p ^ m := hStarComm_order
    have hm1 : m = 1 := hm'.symm.trans hmOne
    have hSigmaBot := hSigmaBotOfMOne hm1
    refine ⟨⟨hsQ, hsC⟩, hCQCommS, hSigmaBot, ?_⟩
    intro g hgC
    rcases hCdecompAll g hgC with ⟨r, q, w, hrR, hqCQ, hwSigma, hg⟩
    have hwBot : w ∈ (⊥ : Subgroup G) := by
      rw [← hSigmaBot]
      exact hwSigma
    have hwOne : w = 1 := Subgroup.mem_bot.mp hwBot
    exact ⟨r, q, hrR, hqCQ, by simpa [hwOne] using hg⟩
  exact
    ⟨R, T,
      ⟨hR, hdisj, hTcentral, hNorm, hDisjCQ, hSubgroups⟩,
      N, F, hFnear, hFfinite, hFnontrivial, addEquiv, unitEquiv,
        hN, hRcentral, hinverseN, hTinverted, hst_mem_T, hcoordinate, hchar,
        hExceptionalLocal, hCaseOneLocal, hCaseOneMOne⟩

end PFchapter2
end CFSG.BenderSuzuki
