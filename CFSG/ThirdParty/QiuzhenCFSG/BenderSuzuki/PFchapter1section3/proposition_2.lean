module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_e
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization

universe u v

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Proposition 2
-/

private theorem proposition_2_induction_context_obligation
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hnonsimple : ∃ L : Subgroup G, L.Normal ∧ L ≠ ⊥ ∧ L ≠ ⊤) :
    ∃ (L : Type u) (_ : Group L) (_ : Finite L)
        (ΩL : Type v) (_ : MulAction L ΩL) (_ : Finite ΩL)
        (HL DL QL : Subgroup L) (tL : L),
      Nat.card L < Nat.card G ∧
        HypothesisA L ΩL HL DL QL tL ∧
          ((∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
            Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
              ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)))) →
            ∃ (N : Subgroup G) (_ : N.Normal) (q : ℕ),
              Odd (Nat.card (G ⧸ N)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
                ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : N ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : Ω ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : N, ∀ ω : Ω,
      eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : N ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : Ω ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : N, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : N ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : Ω ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : N, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)))) := by
  classical
  rcases hnonsimple with ⟨L, hLnormal, hL_ne_bot, hL_ne_top⟩
  letI : L.Normal := hLnormal
  have hcore_bot : pPrimeCore 2 G = ⊥ := by
    rw [PFchapter1section1.proposition_1_e H D Q t
      hsec.section2.hA.A1 hsec.section2.hA.A3]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      letI : FaithfulSMul G Ω := hsec.section2.hA.A2
      apply eq_of_smul_eq_smul (α := Ω)
      intro ω
      have hxall : ∀ ω : Ω, x • ω = ω := by
        simpa [pointStabilizerCore, MulAction.mem_stabilizer_iff] using hx
      simpa using hxall ω
    · exact bot_le
  have hL_even : Even (Nat.card L) := by
    by_contra hnot_even
    have hL_odd : Odd (Nat.card L) :=
      Nat.not_even_iff_odd.mp hnot_even
    have hL_coprime : Nat.Coprime 2 (Nat.card L) :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hL_odd.not_two_dvd_nat
    have hL_le_core : L ≤ pPrimeCore 2 G :=
      le_sSup ⟨hLnormal, hL_coprime⟩
    have hL_bot : L = ⊥ := by
      rw [hcore_bot] at hL_le_core
      exact le_antisymm hL_le_core bot_le
    exact hL_ne_bot hL_bot
  have exists_involution_mem_L : ∃ u : G, u ∈ L ∧ IsInvolution u := by
    have htwo_dvd : 2 ∣ Nat.card L := hL_even.two_dvd
    obtain ⟨u, hu_order⟩ :=
      exists_prime_orderOf_dvd_card' (G := L) 2 htwo_dvd
    refine ⟨u, u.property, ?_⟩
    have hu_order_G : orderOf (u : G) = 2 := by
      rw [Subgroup.orderOf_coe, hu_order]
    exact (orderOf_eq_prime_iff (x := (u : G)) (p := 2)).mp hu_order_G |>.symm
  rcases exists_involution_mem_L with ⟨u, huL, huI⟩
  have involution_mem_L : ∀ x : G, IsInvolution x → x ∈ L := by
    intro x hx
    rcases PFchapter1section1.proposition_2_b H D Q t
        hsec.section2.hA.A1 u x huI hx with ⟨g, hg⟩
    rw [hg]
    simpa [rightConjugateElem] using
      hLnormal.conj_mem u huL g⁻¹
  have htL : t ∈ L :=
    involution_mem_L t hsec.section2.hA.A1.involution_t
  have hK_le_L : K ≤ L := by
    intro k hkK
    have hkSet : k ∈ peterfalviKSet D t :=
      (hsec.section2.K_def k).mp hkK
    have hktI : IsInvolution (k * t) := by
      have htinv : t⁻¹ = t :=
        hsec.section2.hA.A1.involution_t.inv_eq_self
      have htk : t * k * t = k⁻¹ := by
        simpa [peterfalviKSet, rightConjugateElem, htinv, mul_assoc]
          using hkSet.2
      constructor
      · intro hkt
        have hkH : k ∈ H :=
          hsec.section2.hA.A1.D_le_H hkSet.1
        have hk_eq_tinv : k = t⁻¹ := by
          calc
            k = k * 1 := by simp
            _ = k * (t * t⁻¹) := by simp
            _ = (k * t) * t⁻¹ := by rw [mul_assoc]
            _ = t⁻¹ := by rw [hkt]; simp
        exact hsec.section2.hA.A1.t_not_mem_H
          ((by simpa [htinv] using hk_eq_tinv) ▸ hkH)
      · calc
          (k * t) ^ 2 = k * (t * k * t) := by simp [pow_two, mul_assoc]
          _ = k * k⁻¹ := by rw [htk]
          _ = 1 := by simp
    have hktL : k * t ∈ L := involution_mem_L (k * t) hktI
    have htt : t * t = 1 := by
      simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
    have hk_eq : k = (k * t) * t := by simp [mul_assoc, htt]
    rw [hk_eq]
    exact L.mul_mem hktL htL
  obtain ⟨k, hkSet, hk_ne⟩ :=
    PFchapter1section2.proposition_1_b_peterfalviKSet_nontrivial
      H D Q t hsec.section2.hA
  have hkK : k ∈ K := (hsec.section2.K_def k).mpr hkSet
  have hkL : k ∈ L := hK_le_L hkK
  have hQ_le_L : Q ≤ L := by
    have hkH : k ∈ H :=
      hsec.section2.hA.A1.D_le_H
        (hsec.section2.K_le_D hkK)
    let kH : H := ⟨k, hkH⟩
    let f : Q → Q := fun x =>
      ⟨(x : G)⁻¹ * rightConjugateElem (x : G) k, by
        have hxConj : rightConjugateElem (x : G) k ∈ Q := by
          have hxQH : (⟨(x : G), hsec.section2.hA.A1.Q_le_H x.property⟩ : H) ∈ Q.subgroupOf H :=
            (Subgroup.mem_subgroupOf (h := (⟨(x : G), hsec.section2.hA.A1.Q_le_H x.property⟩ : H))).mpr x.property
          have hxNormal := hsec.section2.hA.A1.Q_normal_in_H.conj_mem
            (⟨(x : G), hsec.section2.hA.A1.Q_le_H x.property⟩ : H)
            hxQH kH⁻¹
          have hmemQ : (k⁻¹ * (x : G) * k) ∈ Q := by
            simpa [kH, mul_assoc] using
              (Subgroup.mem_subgroupOf (h := (kH⁻¹ : H) * (⟨(x : G), hsec.section2.hA.A1.Q_le_H x.property⟩ : H) * ((kH⁻¹ : H)⁻¹ : H))).mp hxNormal
          simpa [rightConjugateElem, mul_assoc] using hmemQ
        exact Q.mul_mem (Q.inv_mem x.property) hxConj⟩
    have hf_injective : Function.Injective f := by
      intro x y hxy
      have hxyG := congrArg (fun z : Q => (z : G)) hxy
      have hfixed :
          rightConjugateElem ((y : G) * (x : G)⁻¹) k =
            (y : G) * (x : G)⁻¹ := by
        calc
          rightConjugateElem ((y : G) * (x : G)⁻¹) k =
              y * (y⁻¹ * k⁻¹ * y * k) * (k⁻¹ * x⁻¹ * k) := by
                simp [rightConjugateElem]
                group
          _ = y * (x⁻¹ * k⁻¹ * x * k) * (k⁻¹ * x⁻¹ * k) := by
                rw [show y⁻¹ * k⁻¹ * y * k = x⁻¹ * k⁻¹ * x * k by
                  simpa [f, rightConjugateElem, mul_assoc] using hxyG.symm]
          _ = (y : G) * (x : G)⁻¹ := by
                simp only [Subgroup.coe_inv]
                group
      have hcomm : k * ((y : G) * (x : G)⁻¹) =
          ((y : G) * (x : G)⁻¹) * k := by
        have h := congrArg (fun z : G => k * z) hfixed
        simpa [rightConjugateElem, mul_assoc] using h.symm
      have hcentral : (y : G) * (x : G)⁻¹ ∈
          Subgroup.centralizer ({k} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        simp only [Set.mem_singleton_iff] at ha
        subst a
        exact hcomm
      have hqmem : (y : G) * (x : G)⁻¹ ∈ Q :=
        Q.mul_mem y.property (Q.inv_mem x.property)
      have hbot : (y : G) * (x : G)⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← PFchapter1section2.proposition_1_a_of_mem_peterfalviKSet
          H D Q t hsec.section2.hA.A1 k hkSet hk_ne]
        exact ⟨hcentral, hqmem⟩
      apply Subtype.ext
      exact (mul_inv_eq_one.mp (by simpa using hbot)).symm
    have hf_surjective : Function.Surjective f :=
      Finite.injective_iff_surjective.mp hf_injective
    intro q hqQ
    rcases hf_surjective ⟨q, hqQ⟩ with ⟨x, hx⟩
    have hconjL : (x : G)⁻¹ * k⁻¹ * (x : G) ∈ L := by
      simpa using hLnormal.conj_mem k⁻¹ (L.inv_mem hkL) (x : G)⁻¹
    have hfL : (f x : G) ∈ L := by
      simpa [f, rightConjugateElem, mul_assoc] using
        L.mul_mem hconjL hkL
    simpa [show (f x : G) = q from congrArg Subtype.val hx] using hfL
  let HL : Subgroup L := H.comap L.subtype
  let DL : Subgroup L := D.comap L.subtype
  let QL : Subgroup L := Q.comap L.subtype
  let tL : L := ⟨t, htL⟩
  obtain ⟨α, hHα⟩ := hsec.section2.hA.A1.point_stabilizer
  let β : Ω := t⁻¹ • α
  have hβ_ne : β ≠ α := by
    intro hβ
    apply hsec.section2.hA.A1.t_not_mem_H
    rw [hHα, MulAction.mem_stabilizer_iff]
    have htinv := hsec.section2.hA.A1.involution_t.inv_eq_self
    simpa [β, htinv] using hβ
  have hD_stab :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    simpa [β, hHα, rightConjugate_stabilizer] using
      hsec.section2.hA.A1.D_eq
  have hA1stab : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t := by
    simpa only [hHα] using hsec.section2.hA.A1
  have hQregular := hypothesisA1_Q_regular_on_complement
    hA1stab hβ_ne hD_stab
  have hL_from_base : ∀ ω : Ω, ∃ l : L, l • α = ω := by
    intro ω
    by_cases hω : ω = α
    · exact ⟨1, by simp [hω]⟩
    · rcases hQregular.2.2 hω with ⟨q, _hq, hq⟩
      let qL : L := ⟨q, hQ_le_L q.property⟩
      refine ⟨qL * tL⁻¹, ?_⟩
      calc
        (qL * tL⁻¹) • α = (q : G) • β := by
          change ((q : G) * t⁻¹) • α = (q : G) • β
          rw [mul_smul]
        _ = ω := hq
  have hL_transitive : MulAction.IsPretransitive L Ω := by
    constructor
    intro a b
    rcases hL_from_base a with ⟨la, hla⟩
    rcases hL_from_base b with ⟨lb, hlb⟩
    refine ⟨lb * la⁻¹, ?_⟩
    calc
      (lb * la⁻¹) • a = lb • (la⁻¹ • (la • α)) := by rw [hla]; simp [smul_smul]
      _ = b := by simp [smul_smul, hlb]
  have hL_two : MulAction.IsMultiplyPretransitive L Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    rcases hL_transitive.exists_smul_eq a α with ⟨la, hla⟩
    rcases hL_transitive.exists_smul_eq c α with ⟨lc, hlc⟩
    have hla_b : la • b ≠ α := by
      intro h
      exact hab (smul_left_cancel la (hla.trans h.symm))
    have hlc_d : lc • d ≠ α := by
      intro h
      exact hcd (smul_left_cancel lc (hlc.trans h.symm))
    rcases hQregular.2.2 hla_b with ⟨q₁, _hq₁, hq₁⟩
    rcases hQregular.2.2 hlc_d with ⟨q₂, _hq₂, hq₂⟩
    let qL : L :=
      ⟨(q₂ : G) * (q₁ : G)⁻¹,
        hQ_le_L (Q.mul_mem q₂.property (Q.inv_mem q₁.property))⟩
    have hq₁_fix : (q₁ : G) • α = α := by
      rw [← MulAction.mem_stabilizer_iff, ← hHα]
      exact hsec.section2.hA.A1.Q_le_H q₁.property
    have hq₂_fix : (q₂ : G) • α = α := by
      rw [← MulAction.mem_stabilizer_iff, ← hHα]
      exact hsec.section2.hA.A1.Q_le_H q₂.property
    have hq₁_inv_fix : (q₁ : G)⁻¹ • α = α := by
      calc
        (q₁ : G)⁻¹ • α = (q₁ : G)⁻¹ • ((q₁ : G) • α) := by rw [hq₁_fix]
        _ = α := by simp [smul_smul]
    have hqL_fix : (qL : G) • α = α := by
      change ((q₂ : G) * (q₁ : G)⁻¹) • α = α
      rw [mul_smul, hq₁_inv_fix, hq₂_fix]
    have hlaG : (la : G) • a = α := hla
    have hlcG : (lc : G) • c = α := hlc
    have hq₁G : (q₁ : G) • β = (la : G) • b := hq₁
    have hq₂G : (q₂ : G) • β = (lc : G) • d := hq₂
    refine ⟨lc⁻¹ * qL * la, ?_, ?_⟩
    · change (((lc : G)⁻¹ * (qL : G) * (la : G)) • a) = c
      calc
        _ = (lc : G)⁻¹ • ((qL : G) • ((la : G) • a)) := by
          rw [mul_smul, mul_smul]
        _ = (lc : G)⁻¹ • α := by rw [hlaG, hqL_fix]
        _ = c := by
          simpa [smul_smul] using
            (congrArg (fun z => (lc : G)⁻¹ • z) hlcG).symm
    · change (((lc : G)⁻¹ * (qL : G) * (la : G)) • b) = d
      calc
        _ = (lc : G)⁻¹ •
            (((q₂ : G) * (q₁ : G)⁻¹) • ((la : G) • b)) := by
          rw [mul_smul, mul_smul]
        _ = (lc : G)⁻¹ • ((lc : G) • d) := by
          rw [← hq₁G, ← hq₂G]
          simp [smul_smul]
        _ = d := by simp [smul_smul]
  have hHL_stab : HL = MulAction.stabilizer L α := by
    ext x
    change (x : G) ∈ H ↔ x • α = α
    rw [hHα]
    rfl
  have hDL_eq : DL = HL ⊓ rightConjugate HL tL := by
    ext x
    change (x : G) ∈ D ↔ x ∈ HL ∧ x ∈ rightConjugate HL tL
    rw [hsec.section2.hA.A1.D_eq]
    change ((x : G) ∈ H ∧ (x : G) ∈ rightConjugate H t) ↔ _
    constructor
    · rintro ⟨hxH, hxright⟩
      refine ⟨hxH, ?_⟩
      rcases hxright with ⟨y, hyH, hyx⟩
      have hyL : y ∈ L := by
        have hyx' : t⁻¹ * y * t = (x : G) := by
          simpa [MulAut.conj_apply] using hyx
        have hxy : y = t * (x : G) * t⁻¹ := by
          calc
            y = t * (t⁻¹ * y * t) * t⁻¹ := by group
            _ = t * (x : G) * t⁻¹ := by rw [hyx']
        rw [hxy]
        exact L.mul_mem (L.mul_mem htL x.property) (L.inv_mem htL)
      exact ⟨⟨y, hyL⟩, hyH, Subtype.ext hyx⟩
    · rintro ⟨hxH, hxright⟩
      refine ⟨hxH, ?_⟩
      rcases hxright with ⟨y, hyHL, hyx⟩
      exact ⟨(y : G), hyHL, congrArg Subtype.val hyx⟩
  have hQL_le_HL : QL ≤ HL := by
    intro x hx
    exact hsec.section2.hA.A1.Q_le_H hx
  have hDL_le_HL : DL ≤ HL := by
    intro x hx
    exact hsec.section2.hA.A1.D_le_H hx
  have hQL_normal : (QL.subgroupOf HL).Normal := by
    let f : HL →* H :=
      { toFun := λ x => ⟨(x : G), x.2⟩
        map_one' := by
          ext; simp
        map_mul' := λ x y => by
          ext; simp }
    have h_eq : (Q.subgroupOf H).comap f = QL.subgroupOf HL := by
      ext x
      have h1 : x ∈ (Q.subgroupOf H).comap f ↔ (x : G) ∈ Q := by
        simp [Subgroup.mem_comap, f, Subgroup.mem_subgroupOf]
      have h2 : x ∈ QL.subgroupOf HL ↔ (x : G) ∈ Q := by
        rfl
      rw [h1, h2]
    haveI : (Q.subgroupOf H).Normal := hsec.section2.hA.A1.Q_normal_in_H
    have h_norm_comap : ((Q.subgroupOf H).comap f).Normal :=
      Subgroup.normal_comap (f := f)
    rw [h_eq] at h_norm_comap
    exact h_norm_comap
  have hQL_disjoint_DL : Disjoint QL DL := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      hsec.section2.hA.A1.Q_disjoint_D.le_bot ⟨hx.1, hx.2⟩
    simpa using hxbot
  have hQL_sup_DL : QL ⊔ DL = HL := by
    apply le_antisymm
    · exact sup_le hQL_le_HL hDL_le_HL
    · intro x hxHL
      let QH : Subgroup H := Q.subgroupOf H
      let DH : Subgroup H := D.subgroupOf H
      letI : QH.Normal := hsec.section2.hA.A1.Q_normal_in_H
      have hsupH : QH ⊔ DH = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hsec.section2.hA.A1.Q_le_H
          hsec.section2.hA.A1.D_le_H, hsec.section2.hA.A1.Q_sup_D]
        exact Subgroup.subgroupOf_eq_top.mpr le_rfl
      let xH : H := ⟨(x : G), hxHL⟩
      have hxTop : xH ∈ QH ⊔ DH := by rw [hsupH]; trivial
      rcases Subgroup.mem_sup_of_normal_left.mp hxTop with
        ⟨q, hqQ, d, hdD, hqd⟩
      have hqL : (q : G) ∈ L := hQ_le_L hqQ
      have hdL : (d : G) ∈ L := by
        have hdEq : (d : G) = (q : G)⁻¹ * (x : G) := by
          have hqdG : (q : G) * (d : G) = (x : G) :=
            congrArg Subtype.val hqd
          rw [← hqdG]
          simp
        rw [hdEq]
        exact L.mul_mem (L.inv_mem hqL) x.property
      have hqdL : (⟨q, hqL⟩ : L) * (⟨d, hdL⟩ : L) = x := by
        apply Subtype.ext
        exact congrArg (fun z : H => (z : G)) hqd
      rw [← hqdL]
      exact Subgroup.mul_mem_sup
        (S := QL) (T := DL)
        (show (⟨q, hqL⟩ : L) ∈ QL from hqQ)
        (show (⟨d, hdL⟩ : L) ∈ DL from hdD)
  have hDL_odd : Odd (Nat.card DL) := by
    have hmap_le : DL.map L.subtype ≤ D := by
      rintro x ⟨d, hd, rfl⟩
      exact hd
    have hcard_map : Nat.card (DL.map L.subtype) = Nat.card DL :=
      Subgroup.card_map_of_injective L.subtype_injective
    exact hsec.section2.hA.A1.D_odd.of_dvd_nat
      (by rw [← hcard_map]; exact Subgroup.card_dvd_of_le hmap_le)
  have hAL1 : HypothesisA1 L Ω HL DL QL tL :=
    { two_transitive := hL_two
      point_stabilizer := ⟨α, hHL_stab⟩
      involution_t := by
        exact ⟨fun h => hsec.section2.hA.A1.involution_t.ne_one
            (congrArg Subtype.val h),
          Subtype.ext hsec.section2.hA.A1.involution_t.sq_eq_one⟩
      t_not_mem_H := hsec.section2.hA.A1.t_not_mem_H
      D_eq := hDL_eq
      Q_le_H := hQL_le_HL
      D_le_H := hDL_le_HL
      Q_normal_in_H := hQL_normal
      Q_disjoint_D := hQL_disjoint_DL
      Q_sup_D := hQL_sup_DL
      Q_even := by
        have hcard : Nat.card QL = Nat.card Q := by
          let e : Q ≃* QL :=
            { toFun := fun q =>
                ⟨(⟨(q : G), hQ_le_L q.property⟩ : L), q.property⟩
              invFun := fun q => ⟨((q : L) : G), q.property⟩
              left_inv := fun q => Subtype.ext rfl
              right_inv := fun q => Subtype.ext rfl
              map_mul' := fun _ _ => Subtype.ext rfl }
          exact (Nat.card_congr e.toEquiv).symm
        simpa [hcard] using hsec.section2.hA.A1.Q_even
      D_odd := hDL_odd }
  have hAL2 : FaithfulSMul L Ω := by
    rw [faithfulSMul_iff]
    intro a ha
    apply Subtype.ext
    exact (faithfulSMul_iff.mp hsec.section2.hA.A2) (a : G) ha
  have hAL3 : TwoRankAtLeastTwo L := by
    rcases hsec.section2.hA.A3 with ⟨E, hEcard, hEsq⟩
    have hEp : IsPGroup 2 E := by
      exact IsPGroup.of_card (n := 2) (by norm_num [hEcard])
    obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
    obtain ⟨T, hTQ⟩ := PFchapter1section1.proposition_1_c
      H D Q t hsec.section2.hA.A1
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
    let E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom
    have hE'_le_Q : E' ≤ Q := by
      intro x hx
      rcases hx with ⟨y, hyE, rfl⟩
      have hyP : y ∈ (P : Subgroup G) := hEP hyE
      apply hTQ
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g)
        (P : Subgroup G) hyP
    let EL : Subgroup L := E'.subgroupOf L
    have hE'_le_L : E' ≤ L := hE'_le_Q.trans hQ_le_L
    refine ⟨EL, ?_, ?_⟩
    · calc
        Nat.card EL = Nat.card E' :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hE'_le_L).toEquiv
        _ = Nat.card E := by
          symm
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective E
              (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
        _ = 4 := hEcard
    · intro x
      let e : EL ≃* E' := Subgroup.subgroupOfEquivOfLe hE'_le_L
      let m : E ≃* E' :=
        Subgroup.equivMapOfInjective E
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      rcases m.surjective (e x) with ⟨y, hy⟩
      apply e.injective
      calc
        e (x ^ 2) = (e x) ^ 2 := map_pow e x 2
        _ = (m y) ^ 2 := by rw [hy]
        _ = m (y ^ 2) := (map_pow m y 2).symm
        _ = m 1 := by rw [hEsq y]
        _ = 1 := map_one m
        _ = e 1 := (map_one e).symm
  have hAL : HypothesisA L Ω HL DL QL tL := ⟨hAL1, hAL2, hAL3⟩
  have hlt : Nat.card L < Nat.card G := by
    simpa using natCard_lt_of_subgroup_lt
      (lt_of_le_of_ne le_top hL_ne_top)
  have hL_sup_D : L ⊔ D = ⊤ := by
    apply top_unique
    intro g _
    have hpair_ne : g • α ≠ g • β := fun h =>
      hβ_ne (smul_left_cancel g h).symm
    rcases (MulAction.is_two_pretransitive_iff (G := L) (α := Ω)).mp hL_two
        hβ_ne.symm hpair_ne with ⟨l, hlα, hlβ⟩
    let d : G := (l : G)⁻¹ * g
    have hlαG : (l : G) • α = g • α := hlα
    have hlβG : (l : G) • β = g • β := hlβ
    have hdα : d • α = α := by
      calc
        d • α = (l : G)⁻¹ • (g • α) := by rw [mul_smul]
        _ = (l : G)⁻¹ • ((l : G) • α) := by rw [← hlαG]
        _ = α := by simp [smul_smul]
    have hdβ : d • β = β := by
      calc
        d • β = (l : G)⁻¹ • (g • β) := by rw [mul_smul]
        _ = (l : G)⁻¹ • ((l : G) • β) := by rw [← hlβG]
        _ = β := by simp [smul_smul]
    have hdD : d ∈ D := by
      rw [hD_stab]
      exact ⟨hdα, hdβ⟩
    have hld : (l : G) * d = g := by simp [d]
    rw [← hld]
    exact Subgroup.mul_mem_sup l.property hdD
  have hL_index_odd : Odd L.index := by
    let π : G →* G ⧸ L := QuotientGroup.mk' L
    let φ : D →* G ⧸ L := π.comp D.subtype
    have hφ_surjective : Function.Surjective φ := by
      intro z
      refine QuotientGroup.induction_on z ?_
      intro g
      have hgSup : g ∈ L ⊔ D := by rw [hL_sup_D]; trivial
      rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
        ⟨l, hlL, d, hdD, hld⟩
      refine ⟨⟨d, hdD⟩, ?_⟩
      apply QuotientGroup.eq_iff_div_mem.mpr
      change d / g ∈ L
      rw [← hld]
      simpa [div_eq_mul_inv] using L.inv_mem hlL
    have hcard_dvd : Nat.card (G ⧸ L) ∣ Nat.card D := by
      have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ_surjective
      simpa [hrange] using Subgroup.card_range_dvd φ
    rw [Subgroup.index_eq_card]
    exact hsec.section2.hA.A1.D_odd.of_dvd_nat hcard_dvd
  refine ⟨L, inferInstance, inferInstance, Ω, inferInstance, inferInstance,
    HL, DL, QL, tL, hlt, hAL, ?_⟩
  rintro ⟨M, hMnormal, q, hoddM, hq, hq_gt, hmodel⟩
  letI : M.Normal := hMnormal
  have hres_eq : twoPrimeResidual L = M :=
    (hypothesisA_model_subgroup_eq_twoPrimeResidual
      HL DL QL tL hAL M hMnormal q hoddM hq hq_gt hmodel).2
  subst M
  let R : Subgroup L := twoPrimeResidual L
  have hRchar : R.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ
    dsimp [R]
    rw [twoPrimeResidual, Subgroup.map_iSup]
    refine iSup_le ?_
    intro P
    let Pφ : Sylow 2 L :=
      Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective P
    change (Pφ : Subgroup L) ≤
      ⨆ S : Sylow 2 L, (S : Subgroup L)
    exact le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) Pφ
  letI : R.Characteristic := hRchar
  let N : Subgroup G := R.map L.subtype
  have hNnormal : N.Normal := by
    dsimp [N]
    exact External.hkt_map_characteristic_of_normal_normal L R
  letI : N.Normal := hNnormal
  have hoddN : Odd (Nat.card (G ⧸ N)) := by
    have hRindex : Odd R.index := by
      rw [Subgroup.index_eq_card]
      exact hoddM
    rw [← Subgroup.index_eq_card]
    change Odd (R.map L.subtype).index
    rw [Subgroup.index_map_subtype]
    exact hRindex.mul hL_index_odd
  let eRN : R ≃* N :=
    Subgroup.equivMapOfInjective R L.subtype L.subtype_injective
  refine ⟨N, hNnormal, q, hoddN, hq, hq_gt, ?_⟩
  rcases hmodel with hpsl | hsuzuki | hunitary
  · rcases hpsl with ⟨k, hk, hqk, eR, rho, eΩ, hrho, haction⟩
    let eN : N ≃* PSL2BinaryMatrixGroup k := eRN.symm.trans eR
    refine Or.inl ⟨k, hk, hqk, eN, rho, eΩ, hrho, ?_⟩
    intro n ω
    let r : R := eRN.symm n
    have hcoe : ((r : L) : G) = (n : G) := by
      calc
        ((r : L) : G) = (eRN r : G) :=
          (Subgroup.coe_equivMapOfInjective_apply
            R L.subtype L.subtype_injective r).symm
        _ = (n : G) := congrArg Subtype.val (eRN.apply_symm_apply n)
    calc
      eΩ ((n : G) • ω) = eΩ (((r : L) : G) • ω) := by rw [hcoe]
      _ = rho (eR r) (eΩ ω) := haction r ω
      _ = rho (eN n) (eΩ ω) := by rfl
  · rcases hsuzuki with ⟨k, hk, hqk, eR, rho, eΩ, hrho, haction⟩
    let eN : N ≃* SuzukiMatrixGroup k := eRN.symm.trans eR
    refine Or.inr <| Or.inl ⟨k, hk, hqk, eN, rho, eΩ, hrho, ?_⟩
    intro n ω
    let r : R := eRN.symm n
    have hcoe : ((r : L) : G) = (n : G) := by
      calc
        ((r : L) : G) = (eRN r : G) :=
          (Subgroup.coe_equivMapOfInjective_apply
            R L.subtype L.subtype_injective r).symm
        _ = (n : G) := congrArg Subtype.val (eRN.apply_symm_apply n)
    calc
      eΩ ((n : G) • ω) = eΩ (((r : L) : G) • ω) := by rw [hcoe]
      _ = rho (eR r) (eΩ ω) := haction r ω
      _ = rho (eN n) (eΩ ω) := by rfl
  · rcases hunitary with
      ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
        eR, rho, eΩ, hrho, haction⟩
    letI : Field E := hEfield
    letI : Finite E := hEfinite
    let eN : N ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
      eRN.symm.trans eR
    refine Or.inr <| Or.inr
      ⟨E, inferInstance, inferInstance, J, hJstandard, hEcard, hfixedCard,
        eN, rho, eΩ, hrho, ?_⟩
    intro n ω
    let r : R := eRN.symm n
    have hcoe : ((r : L) : G) = (n : G) := by
      calc
        ((r : L) : G) = (eRN r : G) :=
          (Subgroup.coe_equivMapOfInjective_apply
            R L.subtype L.subtype_injective r).symm
        _ = (n : G) := congrArg Subtype.val (eRN.apply_symm_apply n)
    calc
      eΩ ((n : G) • ω) = eΩ (((r : L) : G) • ω) := by rw [hcoe]
      _ = rho (eR r) (eΩ ω) := haction r ω
      _ = rho (eN n) (eΩ ω) := by rfl

public theorem proposition_2
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
                Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
                  ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω))))
    (hnonsimple : ∃ L : Subgroup G, L.Normal ∧ L ≠ ⊥ ∧ L ≠ ⊤) :
    ∃ (N : Subgroup G) (_ : N.Normal) (q : ℕ),
      Odd (Nat.card (G ⧸ N)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
        ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : N ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : Ω ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : N, ∀ ω : Ω,
      eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : N ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : Ω ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : N, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : N ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : Ω ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : N, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω))) := by
  rcases
    proposition_2_induction_context_obligation
      H D Q K V W Q0 S Q1 t s hsec hnonsimple with
    ⟨L, hLgroup, hLfinite, ΩL, hLaction, hΩLfinite, HL, DL, QL, tL,
      hlt, hA, htransport⟩
  letI : Group L := hLgroup
  letI : Finite L := hLfinite
  letI : MulAction L ΩL := hLaction
  letI : Finite ΩL := hΩLfinite
  exact htransport (hind L ΩL HL DL QL tL hlt hA)

end PFchapter1section3
end CFSG.BenderSuzuki
