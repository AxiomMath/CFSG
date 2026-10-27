module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.RepresentationTheory.QuaternionKernelOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

@[expose] def U3ZFree {Y : Type*} [Group Y] (A E : Subgroup Y) : Prop :=
  ∀ x : ↥A, (x : Y) ∈ E →
    (QuotientGroup.mk x : ↥A ⧸ CFSG.pCore 2 ↥A) ∈ center (↥A ⧸ CFSG.pCore 2 ↥A) → (x : Y) = 1

theorem U3ZFree.of_mulEquiv {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] {A₁ E₁ : Subgroup Y₁}
    {A₂ E₂ : Subgroup Y₂} (e : ↥A₁ ≃* ↥A₂)
    (hE : ∀ x : ↥A₁, (x : Y₁) ∈ E₁ ↔ ((e x : ↥A₂) : Y₂) ∈ E₂) (h : U3ZFree A₁ E₁) :
    U3ZFree A₂ E₂ := by
  intro x hx hc
  obtain ⟨x₁, rfl⟩ := e.surjective x
  have hc' : (QuotientGroup.mk x₁ : ↥A₁ ⧸ CFSG.pCore 2 ↥A₁) ∈
      center (↥A₁ ⧸ CFSG.pCore 2 ↥A₁) := by
    let ε := QuotientGroup.congr (CFSG.pCore 2 ↥A₁) (CFSG.pCore 2 ↥A₂) e (CFSG.pCore_map_iso 2 e)
    have h1 := MulEquivClass.apply_mem_center ε.symm hc
    rwa [show ε.symm (QuotientGroup.mk (e x₁)) = QuotientGroup.mk x₁ from
      ε.symm_apply_apply (QuotientGroup.mk x₁)] at h1
  have h2 : x₁ = 1 := Subtype.ext (h x₁ ((hE x₁).2 hx) hc')
  rw [h2, map_one]
  rfl

theorem uc22ine229u3orb_rank_sum {Y : Type*} [Group Y] [Finite Y] {ι : Type*} [DecidableEq ι]
    {A E : ι → Subgroup Y} {q : ℕ} {a : ι → ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsn : ∀ i, CFSG.Open.IsSubnormal (A i) ⊤) (hp : ∀ i, ⁅A i, A i⁆ = A i)
    (hqs : ∀ i, CFSG.Open.IsQuasisimple (↥(A i) ⧸ CFSG.pCore 2 ↥(A i)))
    (hinj : Function.Injective A) (hZ : ∀ i, U3ZFree (A i) (E i)) (hEA : ∀ i, E i ≤ A i)
    (hEel : ∀ i, IsElemAbelian q (E i)) (hEc : ∀ i, Nat.card (E i) = q ^ a i) (S : Finset ι) :
    ∃ W : Subgroup Y, IsElemAbelian q W ∧ Nat.card W = q ^ (∑ i ∈ S, a i) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : Y →* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hdisj : ∀ {F : Subgroup Y}, IsElemAbelian q F → Disjoint F π.ker := by
    intro F hF
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hF.isPGroup hker hx hxk
  have hcommA : ∀ i j, i ≠ j → ⁅(A i).map π, (A j).map π⁆ = ⊥ := by
    intro i j hij
    have hne : (A i).map π ≠ (A j).map π := fun h =>
      hij (hinj (UC6S846.image_injective (hsn i) (hp i) (hsn j) (hp j) h))
    exact (CFSG.LocalCores.distinct_components_commute (UC6S846.isComponent_image (hsn i) (hqs i))
      (UC6S846.isComponent_image (hsn j) (hqs j))).resolve_left hne
  have hEcard : ∀ i, Nat.card ((E i).map π) = q ^ a i := fun i => by
    rw [UC6S846.card_map_of_disjoint_ker π (E i) (hdisj (hEel i)), hEc i]
  have hcenI : ∀ i, ∀ e ∈ E i, (∀ b ∈ (A i).map π, b * π e = π e * b) → π e = 1 := by
    intro i e he hc
    have hx : (QuotientGroup.mk (⟨e, hEA i he⟩ : ↥(A i)) : ↥(A i) ⧸ CFSG.pCore 2 ↥(A i)) ∈
        center (↥(A i) ⧸ CFSG.pCore 2 ↥(A i)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H x =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          UC6S846.pCore_eq_subgroupOf (hsn i), Subgroup.mem_subgroupOf]
        have h1 := hc _ (Subgroup.mem_map_of_mem π x.2)
        have h2 : π (((x : Y) * e)⁻¹ * (e * (x : Y))) = 1 := by
          rw [map_mul, map_inv, map_mul, map_mul, h1, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).1 h2
    have h3 : e = 1 := hZ i ⟨e, hEA i he⟩ he hx
    rw [h3, map_one]
  have key : ∀ S : Finset ι, ∃ W : Subgroup (Y ⧸ CFSG.pCore 2 Y), IsElemAbelian q W ∧
      Nat.card W = q ^ (∑ i ∈ S, a i) ∧ W ≤ ⨆ i ∈ S, (A i).map π := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨⊥, isElemAbelian_bot q, ?_, by simp⟩
      simp
    | insert j S hjS ih =>
      obtain ⟨W, hWel, hWcard, hWle⟩ := ih
      have hcentr : (⨆ i ∈ S, (A i).map π) ≤
          Subgroup.centralizer (((A j).map π : Subgroup _) : Set _) := by
        refine iSup₂_le fun i hi => ?_
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (hcommA i j (fun h => hjS (h ▸ hi)))
      have hcommWE : ∀ x ∈ W, ∀ y ∈ (E j).map π, x * y = y * x := by
        intro x hx y hy
        exact (Subgroup.mem_centralizer_iff.1 (hcentr (hWle hx)) y
          (Subgroup.map_mono (hEA j) hy)).symm
      have hint : W ⊓ (E j).map π = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨hzW, e, he, rfl⟩
        rw [hcenI j e he fun b hb => Subgroup.mem_centralizer_iff.1 (hcentr (hWle hzW)) b hb]
        exact Subgroup.one_mem _
      obtain ⟨W', hW'le, hW'el, hW'card⟩ := UC6S898.exists_elemAbelian_le_sup_of_commute hq hWel
        ((hEel j).map π) hWcard (hEcard j) hcommWE hint
      refine ⟨W', hW'el, ?_, ?_⟩
      · rw [hW'card, Finset.sum_insert hjS, add_comm]
      · refine hW'le.trans (sup_le ?_ ?_)
        · exact hWle.trans (iSup₂_le fun i hi =>
            le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl)
        · exact (Subgroup.map_mono (hEA j)).trans
            (le_iSup₂_of_le j (Finset.mem_insert_self j S) le_rfl)
  obtain ⟨W, hWel, hWcard, -⟩ := key S
  obtain ⟨Q₁, -, hQ₁map, hQ₁disj⟩ :=
    UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 W hWel.isPGroup
  refine ⟨Q₁, UC6S846.isElemAbelian_of_disjoint_ker π Q₁ hQ₁disj (by rw [hQ₁map]; exact hWel), ?_⟩
  rw [← UC6S846.card_map_of_disjoint_ker π Q₁ hQ₁disj, hQ₁map, hWcard]

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229u3orb_normalizes {M Y : Subgroup G} (hY : Y ∈ calC M) {y : G} (hy : y ∈ M)
    {r q : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hyr : orderOf y = r) (hq : q.Prime) (hq2 : q ≠ 2)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) (hXZ : U3ZFree Y X)
    (hrank : CFSG.Open.pRank q M ≤ 3) : y ∈ normalizer (Y : Set G) := by
  classical
  by_contra hyn
  let f : ℕ → MulAut G := fun i => MulAut.conj (y ^ i)
  have hM : ∀ i, M.map (f i).toMonoidHom = M := fun i =>
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem hy i))
  have hYi : ∀ i, Y.map (f i).toMonoidHom ∈ calC M := fun i => UC6S846.calC_map M (f i) (hM i) hY
  have hYiM : ∀ i, Y.map (f i).toMonoidHom ≤ M := fun i => (hYi i).1.le
  have hdist : ∀ i j : ℕ, i < j → j < 4 → Y.map (f i).toMonoidHom ≠ Y.map (f j).toMonoidHom := by
    intro i j hij hj4 heq
    have hcomp : f j = f i * f (j - i) := by
      show MulAut.conj (y ^ j) = MulAut.conj (y ^ i) * MulAut.conj (y ^ (j - i))
      rw [← map_mul, ← pow_add]
      congr 2
      omega
    have h1 : Y.map (f j).toMonoidHom = (Y.map (f (j - i)).toMonoidHom).map (f i).toMonoidHom := by
      rw [hcomp, Subgroup.map_map]
      rfl
    rw [h1] at heq
    have h2 : Y = Y.map (f (j - i)).toMonoidHom := Subgroup.map_injective (f i).injective heq
    exact hyn (CFSG.RepresentationTheory.pow_mem_normalizer_of_prime hr (by omega) (by omega)
      (by rw [← hyr]; exact pow_orderOf_eq_one y) (UC6S846.mem_normalizer_iff_map_conj.2 h2.symm))
  have hXel : IsElemAbelian q X := UC6S898.isElemAbelian_of_card_prime hq hXc
  have hEi : ∀ i, X.map (f i).toMonoidHom ≤ Y.map (f i).toMonoidHom := fun i =>
    Subgroup.map_mono hXY
  have hcalC := fun i => UC6S846.calC_subgroupOf (hYi i)
  obtain ⟨W, hWel, hWcard⟩ := uc22ine229u3orb_rank_sum (Y := ↥M) (ι := Fin 4)
    (A := fun i => (Y.map (f (i : ℕ)).toMonoidHom).subgroupOf M)
    (E := fun i => (X.map (f (i : ℕ)).toMonoidHom).subgroupOf M) (q := q) (a := fun _ => 1) hq hq2
    (fun i => (hcalC (i : ℕ)).1) (fun i => (hcalC (i : ℕ)).2.1) (fun i => (hcalC (i : ℕ)).2.2.1)
    (by
      intro i j hij
      by_contra hne
      have hmap := congrArg (Subgroup.map M.subtype) hij
      rw [Subgroup.map_subgroupOf_eq_of_le (hYiM i), Subgroup.map_subgroupOf_eq_of_le (hYiM j)]
        at hmap
      rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h) : (i : ℕ) ≠ (j : ℕ)) with hlt | hgt
      · exact hdist i j hlt j.2 hmap
      · exact hdist j i hgt i.2 hmap.symm)
    (fun i => hXZ.of_mulEquiv
      ((Subgroup.equivMapOfInjective Y (f i).toMonoidHom (f i).injective).trans
        (Subgroup.subgroupOfEquivOfLe (hYiM i)).symm)
      (fun x => (Subgroup.mem_map_iff_mem (f i).injective).symm))
    (fun i x hx => hEi i hx) (fun i => (hXel.map _).subgroupOf M)
    (fun i => by
      show Nat.card ((X.map (f (i : ℕ)).toMonoidHom).subgroupOf M) = q ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((hEi i).trans (hYiM i))).toEquiv,
        Subgroup.card_map_of_injective (f i).injective, hXc])
    Finset.univ
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin 4)), (fun _ : Fin 4 => 1) i) = 4 := by simp
  rw [hsum] at hWcard
  have h4 := UC6S846.le_pRank' hq (E := W.map M.subtype) (H := M) (Subgroup.map_subtype_le W)
    (hWel.map _) (by rw [Subgroup.card_map_of_injective M.subtype_injective, hWcard])
  omega

theorem uc22ine229u3orb_two_le_pRank (hSyl : UCK.U3SylOmega) {M Y : Subgroup G} (hY : Y ∈ calC M)
    {n : ℕ} (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hOp : F10.OpRes p M = M) (h4 : 4 ≤ CFSG.Open.pRank p M) {E : Subgroup G} (hEY : E ≤ Y)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hEq : IsPGroup q E) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) (hXZ : U3ZFree Y X) (hrank : CFSG.Open.pRank q M ≤ 3) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨B₁, hB₁M, hB₁el, hB₁c, hB₁C, -⟩ : ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧
      Nat.card B₁ = p ^ 2 ∧ B₁ ≤ centralizer (E : Set G) ∧
      ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
    by_cases hN : M ≤ normalizer (Y : Set G)
    · exact uc22ine229_exists_B₁_of_normal hY hN hX hp hp5 hOp h4 hEY hq hq2 hEq
    by_cases hpn : p ∣ 2 ^ n + 1
    · obtain ⟨B₀, hB₀M, hB₀el, hB₀c, hB₀Y⟩ :=
        uc22ine229_exists_conj_sq hSyl hY hX hp (by omega) hpn hN
      exact uc22ine229_exists_copy hY.1.le hp hp2 hq hq2 hB₀M hB₀el hB₀c hB₀Y hEY hEq
    obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h4
    have hBN : B ≤ normalizer (Y : Set G) := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      haveI : Fact p.Prime := ⟨hp⟩
      exact uc22ine229u3orb_normalizes hY (hBM hy) hp hp5 (orderOf_eq_prime (hBel.2 y hy) hy1) hq
        hq2 hXY hXc hXZ hrank
    obtain ⟨B₀, hB₀B, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229_exists_kernel hY.1 hp hBN hBel hBc
      (uc22ine229_card_le_of_not_dvd hX hp hp2 hp3 hpn ((hBel.subgroupOf _).map _))
    exact uc22ine229_exists_copy hY.1.le hp hp2 hq hq2 (hB₀B.trans hBM) hB₀el hB₀c hB₀Y hEY hEq
  exact UC6S846.le_pRank' hp (le_inf hB₁M hB₁C) hB₁el hB₁c

end CFSG.LocalAnalysis.UniquenessCase.UC22
