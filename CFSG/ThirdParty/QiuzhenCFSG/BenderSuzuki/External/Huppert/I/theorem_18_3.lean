module

public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.Solvable

import Mathlib.GroupTheory.GroupAction.OfQuotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert I.18.3

The Zassenhaus conjugacy theorem for complements of a normal Hall subgroup.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped Pointwise

universe u v

/-- Huppert I.2.12(c), Dedekind's identity in the form used in I.18.2. -/
public theorem huppert_I_2_12_c_dedekind_identity
    {G : Type*} [Group G] (A B C : Subgroup G) (hAC : A ≤ C) :
    (A : Set G) * (B ⊓ C : Subgroup G) = (A : Set G) * (B : Set G) ∩ C := by
  exact Subgroup.mul_inf_assoc A B C hAC

/-- Huppert I.7.5, conjugacy of Sylow subgroups. -/
public theorem huppert_I_7_5_sylow_subgroups_conjugate
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  calc
    (Q : Subgroup G) = (g • P : Sylow p G) := congrArg Sylow.toSubgroup hg.symm
    _ = MulAut.conj g • (P : Subgroup G) := Sylow.coe_subgroup_smul
    _ = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := rfl

/-- Huppert I.17.5, the abelian-normal-subgroup case of complement conjugacy. -/
public theorem huppert_I_17_5_abelian_normal_complements_conjugate
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  apply Subgroup.exists_conj_eq_of_isComplement' (H := N) (K₁ := H) (K₂ := K)
  · simpa [Subgroup.index_eq_card] using hcoprime
  · exact hH
  · exact hK

/-- The solvable-normal-subgroup branch of Huppert I.18.2. -/
public theorem huppert_I_18_2_a_complements_conjugate_of_solvable_normal
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable N)
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  have hH_normalizes_N : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal (H := N)
  letI : MulDistribMulAction H N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) H N hH_normalizes_N
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let eK : G ⧸ N ≃* K := hK.symm.QuotientMulEquiv
  let sectionK : H → K := fun h => eK (q (h : G))
  have hsectionK_q : ∀ h : H, q (sectionK h : G) = q (h : G) := by
    intro h
    dsimp [sectionK, eK, q]
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hK.symm
      (QuotientGroup.mk' N (h : G))
  let cocycle : H → N := fun h =>
    ⟨(sectionK h : G) * (h : G)⁻¹, by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q ((sectionK h : G) * (h : G)⁻¹) = 1
      rw [map_mul, map_inv, hsectionK_q h]
      simp⟩
  have hsectionK_mul : ∀ a b : H, sectionK (a * b) = sectionK a * sectionK b := by
    intro a b
    dsimp [sectionK]
    exact eK.map_mul (q (a : G)) (q (b : G))
  have hsectionK_eq : ∀ h : H, (sectionK h : G) = (cocycle h : G) * (h : G) := by
    intro h
    dsimp [cocycle]
    simp [mul_assoc]
  have hcocycle : ∀ a b : H, cocycle (a * b) = cocycle a * (a • cocycle b) := by
    intro a b
    ext
    have hsG : (sectionK (a * b) : G) = (sectionK a : G) * (sectionK b : G) :=
      congrArg Subtype.val (hsectionK_mul a b)
    dsimp [cocycle]
    rw [hsG]
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  have hcardH : Nat.card H = Nat.card (G ⧸ N) := by
    calc
      Nat.card H = N.index := hH.symm.index_eq_card.symm
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have hcoprimeHN : Nat.Coprime (Nat.card H) (Nat.card N) := by
    simpa [hcardH] using hcoprime.symm
  obtain ⟨n, hn⟩ :=
    exists_principal_cocycle_of_solvable_coprime
      (A := H) (N := N) hsolvable hcoprimeHN cocycle hcocycle
  have hHn_le_K : H.map (MulAut.conj (n : G)).toMonoidHom ≤ K := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hhH, rfl⟩
    let hH' : H := ⟨h, hhH⟩
    have hnG :
        (cocycle hH' : G) = (n : G) * (((hH' : H) • n : N) : G)⁻¹ := by
      simpa using congrArg Subtype.val (hn hH')
    have hsection_eq : (sectionK hH' : G) = (n : G) * h * (n : G)⁻¹ := by
      calc
        (sectionK hH' : G) = (cocycle hH' : G) * (hH' : G) := hsectionK_eq hH'
        _ = ((n : G) * (((hH' : H) • n : N) : G)⁻¹) * (hH' : G) := by rw [hnG]
        _ = (n : G) * h * (n : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH', mul_assoc]
    simpa [MulAut.conj_apply, hH', hsection_eq] using (sectionK hH').property
  have hcardK : Nat.card K = Nat.card H :=
    hK.symm.index_eq_card.symm.trans hH.symm.index_eq_card
  have hcardHn : Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card H := by
    exact Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj (n : G)).toMonoidHom) (MulAut.conj (n : G)).injective
  have hcard_le : Nat.card K ≤ Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) := by
    rw [hcardK, hcardHn]
  exact ⟨n, (Subgroup.eq_of_le_of_card_ge hHn_le_K hcard_le).symm⟩

/-- The prime-power operator base case in the second induction of Huppert I.18.2. -/
public theorem huppert_I_18_2_b_principal_cocycle_of_pgroup_operator
    {X : Type u} {A : Type v}
    [Group X] [Finite X] [Group A] [Finite A]
    [MulDistribMulAction A X] {r : ℕ} [Fact r.Prime] [Fact (IsPGroup r A)]
    (hcoprime : Nat.Coprime r (Nat.card X))
    (c : A → X) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : X, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let originalSmul : A → X → X := fun a x => a • x
  have hc_one : c 1 = 1 := by
    have h : c 1 = c 1 * c 1 := by simpa using hc 1 1
    calc
      c 1 = (c 1)⁻¹ * (c 1 * c 1) := by simp
      _ = (c 1)⁻¹ * c 1 := by rw [← h]
      _ = 1 := by simp
  letI : MulAction A X :=
    { smul := fun a x => c a * originalSmul a x
      one_smul := by
        intro x
        change c 1 * originalSmul 1 x = x
        dsimp [originalSmul]
        simp [hc_one]
      mul_smul := by
        intro a b x
        change c (a * b) * originalSmul (a * b) x =
          c a * originalSmul a (c b * originalSmul b x)
        dsimp [originalSmul]
        rw [hc a b]
        simp [smul_mul', smul_smul, mul_assoc] }
  have hr_not_dvd : ¬ r ∣ Nat.card X :=
    ((Fact.out : Nat.Prime r).coprime_iff_not_dvd).1 hcoprime
  rcases (Fact.out : IsPGroup r A).nonempty_fixed_point_of_prime_not_dvd_card
      X hr_not_dvd with
    ⟨x, hxfix⟩
  refine ⟨x, ?_⟩
  intro a
  have hx : c a * originalSmul a x = x := by
    have hfix := (MulAction.mem_fixedPoints.mp hxfix) a
    change c a * originalSmul a x = x at hfix
    exact hfix
  show c a = x * (originalSmul a x)⁻¹
  calc
    c a = (c a * originalSmul a x) * (originalSmul a x)⁻¹ := by simp
    _ = x * (originalSmul a x)⁻¹ := by rw [hx]

/-- The minimal-normal-subgroup induction in the solvable-quotient branch of I.18.2. -/
public theorem huppert_I_18_2_b_principal_cocycle_of_solvable_operator
    {X : Type u} {A : Type v}
    [Group X] [Finite X] [Group A] [Finite A] [Group.IsSolvable A]
    [MulDistribMulAction A X] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card X))
    (c : A → X) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : X, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (A' : Type v) (X' : Type u) [Group A'] [Finite A'] [Group.IsSolvable A']
      [Group X'] [Finite X'] [MulDistribMulAction A' X'],
      Nat.card A' = n →
      Nat.Coprime (Nat.card A') (Nat.card X') →
      ∀ c' : A' → X', (∀ a b : A', c' (a * b) = c' a * (a • c' b)) →
        ∃ x : X', ∀ a : A', c' a = x * (a • x)⁻¹
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A' X' _ _ _ _ _ _ hcardA hcop c' hc'
    by_cases hA_one : Nat.card A' = 1
    · letI : Subsingleton A' := (Nat.card_eq_one_iff_unique.mp hA_one).1
      have hc_one : c' 1 = 1 := by
        have h : c' 1 = c' 1 * c' 1 := by simpa using hc' 1 1
        calc
          c' 1 = (c' 1)⁻¹ * (c' 1 * c' 1) := by simp
          _ = (c' 1)⁻¹ * c' 1 := by rw [← h]
          _ = 1 := by simp
      refine ⟨1, ?_⟩
      intro a
      have ha : a = 1 := Subsingleton.elim a 1
      simp [ha, hc_one]
    · have hA_nontrivial : Nontrivial A' := by
        exact not_subsingleton_iff_nontrivial.mp fun hsub => by
          have hcard_one : Nat.card A' = 1 :=
            Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
          exact hA_one hcard_one
      letI : Nontrivial A' := hA_nontrivial
      obtain ⟨B, hBnormal, hBne, hBminimal⟩ :=
        exists_minimal_normal (G := A') (inferInstance : Group.IsSolvable A') hA_nontrivial
      letI : B.Normal := hBnormal
      letI : IsMinimalNormal B := by
        refine ⟨?_⟩
        intro K hKnormal hKle
        by_cases hKbot : K = ⊥
        · exact Or.inl hKbot
        · exact Or.inr (hBminimal K hKnormal hKle hKbot)
      have hBsolvable : Group.IsSolvable B := inferInstance
      letI : Group.IsSolvable B := hBsolvable
      obtain ⟨r, hrprime, hBelementary⟩ :=
        minimalNormal_solvable_exists_isElementaryAbelian (G := A') B
      letI : Fact r.Prime := ⟨hrprime⟩
      letI : IsElementaryAbelian r B := hBelementary
      letI : Fact (IsPGroup r B) := ⟨IsElementaryAbelian.isPGroup r B⟩
      have hr_dvd_A : r ∣ Nat.card A' := by
        have hBp : IsPGroup r B := IsElementaryAbelian.isPGroup r B
        rcases hBp.exists_card_eq with ⟨k, hk⟩
        have hBcard_ne_one : Nat.card B ≠ 1 := by
          intro hcard
          exact hBne ((Subgroup.eq_bot_iff_card (H := B)).2 hcard)
        have hk_ne_zero : k ≠ 0 := by
          intro hk0
          apply hBcard_ne_one
          simp [hk, hk0]
        have hr_dvd_B : r ∣ Nat.card B := by
          rw [hk]
          exact dvd_pow_self r hk_ne_zero
        exact hr_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)
      have hcop_r_X : Nat.Coprime r (Nat.card X') :=
        Nat.Coprime.of_dvd_left hr_dvd_A hcop
      let cB : B → X' := fun b => c' b
      have hcB : ∀ a b : B, cB (a * b) = cB a * (a • cB b) := by
        intro a b
        change c' ((a : A') * (b : A')) = c' a * ((a : A') • c' b)
        exact hc' (a : A') (b : A')
      obtain ⟨x0, hx0⟩ :=
        huppert_I_18_2_b_principal_cocycle_of_pgroup_operator
          (X := X') (A := B) hcop_r_X cB hcB
      let c1 : A' → X' := fun a => x0⁻¹ * c' a * (a • x0)
      have hc1_def : ∀ a : A', c1 a = x0⁻¹ * c' a * (a • x0) := fun _ => rfl
      have hc1 : ∀ a b : A', c1 (a * b) = c1 a * (a • c1 b) := by
        intro a b
        dsimp [c1]
        rw [hc' a b]
        simp [smul_mul', smul_smul, mul_assoc]
      have hc1B : ∀ b : B, c1 b = 1 := by
        intro b
        dsimp [c1]
        change x0⁻¹ * cB b * (b • x0) = 1
        rw [hx0 b]
        simp
      have hc1_fixed : ∀ a : A', c1 a ∈ fixedPointSubgroup B X' := by
        intro a
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro b
        have hconj_mem : a⁻¹ * (b : A') * a ∈ B := by
          simpa using (inferInstance : B.Normal).conj_mem (b : A') b.property a⁻¹
        let b' : B := ⟨a⁻¹ * (b : A') * a, hconj_mem⟩
        have hba : (b : A') * a = a * (b' : A') := by
          simp [b', mul_assoc]
        have h1 : c1 ((b : A') * a) = (b : A') • c1 a := by
          simpa [hc1B b] using hc1 (b : A') a
        have h2 : c1 (a * (b' : A')) = c1 a := by
          simpa [hc1B b'] using hc1 a (b' : A')
        have hfixed : (b : A') • c1 a = c1 a := by
          calc
            (b : A') • c1 a = c1 ((b : A') * a) := h1.symm
            _ = c1 (a * (b' : A')) := by rw [hba]
            _ = c1 a := h2
        change (b : A') • c1 a = c1 a
        exact hfixed
      let F : Subgroup X' := fixedPointSubgroup B X'
      have hcop_Q_F : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card F) := by
        have hquot_dvd : Nat.card (A' ⧸ B) ∣ Nat.card A' :=
          Subgroup.card_quotient_dvd_card (s := B)
        have hcop_Q_X : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card X') :=
          Nat.Coprime.of_dvd_left hquot_dvd hcop
        exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card F) hcop_Q_X
      have hquot_lt : Nat.card (A' ⧸ B) < n := by
        simpa [hcardA] using card_quotient_lt_of_ne_bot (G := A') B hBne
      have hsolvable_quotient : Group.IsSolvable (A' ⧸ B) := by infer_instance
      letI : Group.IsSolvable (A' ⧸ B) := hsolvable_quotient
      letI : MulDistribMulAction (A' ⧸ B) F := by
        dsimp [F]
        infer_instance
      have hc1_eq_of_mk_eq {a b : A'} (h : (a : A' ⧸ B) = b) : c1 a = c1 b := by
        rcases (QuotientGroup.mk'_eq_mk' (N := B)).mp h with ⟨z, hzB, haz⟩
        have hz : c1 z = 1 := hc1B ⟨z, hzB⟩
        calc
          c1 a = c1 (a * z) := by simpa [hz] using (hc1 a z).symm
          _ = c1 b := by rw [haz]
      let cQ : A' ⧸ B → F := fun q => ⟨c1 q.out, hc1_fixed q.out⟩
      have hcQ_mk : ∀ a : A', cQ (a : A' ⧸ B) = ⟨c1 a, hc1_fixed a⟩ := by
        intro a
        ext
        dsimp [cQ]
        exact hc1_eq_of_mk_eq
          (by exact Quotient.out_eq (s := QuotientGroup.leftRel B) (a : A' ⧸ B))
      have hcQ : ∀ q s : A' ⧸ B, cQ (q * s) = cQ q * (q • cQ s) := by
        intro q s
        refine Quotient.inductionOn₂' q s ?_
        intro a b
        ext
        rw [← QuotientGroup.mk_mul (N := B) a b]
        simp only [hcQ_mk, Subgroup.coe_mul]
        have hsmul :
            ↑(((a : A' ⧸ B) • (⟨c1 b, hc1_fixed b⟩ : F)) : F) = a • c1 b := by
          rfl
        rw [hsmul]
        exact hc1 a b
      obtain ⟨y, hy⟩ :=
        ih (Nat.card (A' ⧸ B)) hquot_lt (A' ⧸ B) F rfl hcop_Q_F cQ hcQ
      refine ⟨x0 * (y : X'), ?_⟩
      intro a
      have hy_a : c1 a = (y : X') * (a • (y : X'))⁻¹ := by
        have h := congrArg Subtype.val (hy (a : A' ⧸ B))
        have hsmul :
            (((a : A' ⧸ B) • y : F) : X') = a • (y : X') := by
          rfl
        simpa [hcQ_mk, hsmul] using h
      have hc_rearrange : c' a = x0 * c1 a * (a • x0)⁻¹ := by
        have hdef := hc1_def a
        calc
          c' a = x0 * (x0⁻¹ * c' a * (a • x0)) * (a • x0)⁻¹ := by
            simp [mul_assoc]
          _ = x0 * c1 a * (a • x0)⁻¹ := by rw [← hdef]
      rw [hc_rearrange, hy_a]
      simp [smul_mul', mul_assoc]
  exact hP (Nat.card A) A X rfl hcoprime c hc

/-- The solvable-quotient branch of Huppert I.18.2. -/
public theorem huppert_I_18_2_b_complements_conjugate_of_solvable_quotient
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable (G ⧸ N))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  have hHsolvable : Group.IsSolvable H := by
    letI : Group.IsSolvable (G ⧸ N) := hsolvable
    exact Group.isSolvable_of_surjective
      (f := hH.symm.QuotientMulEquiv.toMonoidHom) hH.symm.QuotientMulEquiv.surjective
  letI : Group.IsSolvable H := hHsolvable
  have hH_normalizes_N : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal (H := N)
  letI : MulDistribMulAction H N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) H N hH_normalizes_N
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let eK : G ⧸ N ≃* K := hK.symm.QuotientMulEquiv
  let sectionK : H → K := fun h => eK (q (h : G))
  have hsectionK_q : ∀ h : H, q (sectionK h : G) = q (h : G) := by
    intro h
    dsimp [sectionK, eK, q]
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hK.symm
      (QuotientGroup.mk' N (h : G))
  let cocycle : H → N := fun h =>
    ⟨(sectionK h : G) * (h : G)⁻¹, by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q ((sectionK h : G) * (h : G)⁻¹) = 1
      rw [map_mul, map_inv, hsectionK_q h]
      simp⟩
  have hsectionK_mul : ∀ a b : H, sectionK (a * b) = sectionK a * sectionK b := by
    intro a b
    dsimp [sectionK]
    exact eK.map_mul (q (a : G)) (q (b : G))
  have hsectionK_eq : ∀ h : H, (sectionK h : G) = (cocycle h : G) * (h : G) := by
    intro h
    dsimp [cocycle]
    simp [mul_assoc]
  have hcocycle : ∀ a b : H, cocycle (a * b) = cocycle a * (a • cocycle b) := by
    intro a b
    ext
    have hsG : (sectionK (a * b) : G) = (sectionK a : G) * (sectionK b : G) :=
      congrArg Subtype.val (hsectionK_mul a b)
    dsimp [cocycle]
    rw [hsG]
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  have hcardH : Nat.card H = Nat.card (G ⧸ N) := by
    calc
      Nat.card H = N.index := hH.symm.index_eq_card.symm
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have hcoprimeHN : Nat.Coprime (Nat.card H) (Nat.card N) := by
    simpa [hcardH] using hcoprime.symm
  obtain ⟨n, hn⟩ :=
    huppert_I_18_2_b_principal_cocycle_of_solvable_operator
      (A := H) (X := N) hcoprimeHN cocycle hcocycle
  have hHn_le_K : H.map (MulAut.conj (n : G)).toMonoidHom ≤ K := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hhH, rfl⟩
    let hH' : H := ⟨h, hhH⟩
    have hnG :
        (cocycle hH' : G) = (n : G) * (((hH' : H) • n : N) : G)⁻¹ := by
      simpa using congrArg Subtype.val (hn hH')
    have hsection_eq : (sectionK hH' : G) = (n : G) * h * (n : G)⁻¹ := by
      calc
        (sectionK hH' : G) = (cocycle hH' : G) * (hH' : G) := hsectionK_eq hH'
        _ = ((n : G) * (((hH' : H) • n : N) : G)⁻¹) * (hH' : G) := by rw [hnG]
        _ = (n : G) * h * (n : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH', mul_assoc]
    simpa [MulAut.conj_apply, hH', hsection_eq] using (sectionK hH').property
  have hcardK : Nat.card K = Nat.card H :=
    hK.symm.index_eq_card.symm.trans hH.symm.index_eq_card
  have hcardHn : Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card H := by
    exact Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj (n : G)).toMonoidHom) (MulAut.conj (n : G)).injective
  have hcard_le : Nat.card K ≤ Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) := by
    rw [hcardK, hcardHn]
  exact ⟨n, (Subgroup.eq_of_le_of_card_ge hHn_le_K hcard_le).symm⟩

/--
Huppert I, Main Theorem 18.2. Complements of a normal Hall subgroup are
conjugate when either the normal subgroup or the quotient is solvable.
-/
public theorem huppert_I_18_2_complements_conjugate_of_solvable_normal_or_quotient
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  have hsolvable_normal :
      Group.IsSolvable N →
        ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
    intro hsolvableN
    obtain ⟨n, hn⟩ :=
      huppert_I_18_2_a_complements_conjugate_of_solvable_normal
        N H K hcoprime hsolvableN hH hK
    exact ⟨n, hn⟩
  have hsolvable_quotient :
      Group.IsSolvable (G ⧸ N) →
        ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
    intro hsolvableQ
    obtain ⟨n, hn⟩ :=
      huppert_I_18_2_b_complements_conjugate_of_solvable_quotient
        N H K hcoprime hsolvableQ hH hK
    exact ⟨n, hn⟩
  exact hsolvable.elim hsolvable_normal hsolvable_quotient

/--
Huppert I, Main Theorem 18.3. If the orders of a normal subgroup `N` and the
quotient `G / N` are coprime, then all complements of `N` in `G` are conjugate.
-/
public theorem huppert_I_18_3_complements_conjugate
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  have hodd_side : Odd (Nat.card N) ∨ Odd (Nat.card (G ⧸ N)) := by
    by_contra hnot
    rw [not_or] at hnot
    have hN_even : Even (Nat.card N) := Nat.not_odd_iff_even.mp hnot.1
    have hQ_even : Even (Nat.card (G ⧸ N)) := Nat.not_odd_iff_even.mp hnot.2
    exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two
      (even_iff_two_dvd.mp hN_even) (even_iff_two_dvd.mp hQ_even)) hcoprime
  have hsolvable_side : Group.IsSolvable N ∨ Group.IsSolvable (G ⧸ N) := by
    exact hodd_side.imp (_root_.CFSG.odd_order_theorem N) (_root_.CFSG.odd_order_theorem (G ⧸ N))
  have h18_2 :=
    huppert_I_18_2_complements_conjugate_of_solvable_normal_or_quotient
      N H K hcoprime hsolvable_side hH hK
  exact h18_2

end External
end CFSG.BenderSuzuki
