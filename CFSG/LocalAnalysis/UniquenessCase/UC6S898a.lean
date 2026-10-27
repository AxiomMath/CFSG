module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_one_of_central_of_pow_eq_one {Z : Type*} [Group Z] [Finite Z] {B : Subgroup Z} {q : ℕ}
    (hq : q.Prime) (hB : ¬ q ∣ Nat.card (center ↥B)) {z : Z} (hzB : z ∈ B)
    (hzc : ∀ b ∈ B, b * z = z * b) (hzq : z ^ q = 1) : z = 1 := by
  have hzc' : (⟨z, hzB⟩ : ↥B) ∈ Subgroup.center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hord1 : orderOf (⟨⟨z, hzB⟩, hzc'⟩ : ↥(Subgroup.center ↥B)) ∣ q := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simpa using hzq
  have hord2 := orderOf_dvd_natCard (⟨⟨z, hzB⟩, hzc'⟩ : ↥(Subgroup.center ↥B))
  have hcop : Nat.Coprime q (Nat.card (Subgroup.center ↥B)) :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 hB
  have h1 : orderOf (⟨⟨z, hzB⟩, hzc'⟩ : ↥(Subgroup.center ↥B)) ∣ Nat.gcd q
      (Nat.card (Subgroup.center ↥B)) := Nat.dvd_gcd hord1 hord2
  rw [hcop.gcd_eq_one] at h1
  have h2 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have := congrArg (fun w : ↥(Subgroup.center ↥B) => ((w : ↥B) : Z)) h2
  simpa using this

theorem exists_elemAbelian_le_sup_of_commute {Z : Type*} [Group Z] [Finite Z] {q a b : ℕ} (hq : q.Prime)
    {F F' : Subgroup Z} (hFel : IsElemAbelian q F) (hF'el : IsElemAbelian q F')
    (hFc : Nat.card F = q ^ a) (hF'c : Nat.card F' = q ^ b)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F', x * y = y * x) (hint : F ⊓ F' = ⊥) :
    ∃ W : Subgroup Z, W ≤ F ⊔ F' ∧ IsElemAbelian q W ∧ Nat.card W = q ^ (a + b) := by
  classical
  let φ : ↥F × ↥F' →* Z := MonoidHom.noncommCoprod F.subtype F'.subtype
    (fun m n => hcomm (m : Z) m.2 (n : Z) n.2)
  have hφ : ∀ x : ↥F, ∀ y : ↥F', φ (x, y) = (x : Z) * (y : Z) := fun x y => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h1 : (x : Z) * (y : Z) = 1 := by rw [← hφ]; exact hxy
    have h2 : (x : Z) = ((y : Z))⁻¹ := mul_eq_one_iff_eq_inv.1 h1
    have h3 : (x : Z) ∈ F ⊓ F' := ⟨x.2, by rw [h2]; exact F'.inv_mem y.2⟩
    rw [hint, Subgroup.mem_bot] at h3
    have hx : x = 1 := Subtype.ext h3
    have hy : y = 1 := by
      apply Subtype.ext
      have : (y : Z) = 1 := by rw [h3, one_mul] at h1; exact h1
      exact this
    simp [hx, hy]
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hφ]
    exact Subgroup.mul_mem_sup x.2 y.2
  · refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨⟨x₁, y₁⟩, hu⟩ := u.2
      obtain ⟨⟨x₂, y₂⟩, hv⟩ := v.2
      apply Subtype.ext
      show (u : Z) * (v : Z) = (v : Z) * (u : Z)
      rw [← hu, ← hv, hφ, hφ]
      have hx : (x₁ : Z) * x₂ = x₂ * x₁ := by
        have := hFel.1
        exact congrArg Subtype.val (mul_comm' x₁ x₂)
      have hy : (y₁ : Z) * y₂ = y₂ * y₁ := by
        have := hF'el.1
        exact congrArg Subtype.val (mul_comm' y₁ y₂)
      have h12 := hcomm _ x₁.2 _ y₂.2
      have h21 := hcomm _ x₂.2 _ y₁.2
      calc (x₁ : Z) * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
        _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h21]
        _ = (x₁ * x₂) * (y₁ * y₂) := by group
        _ = (x₂ * x₁) * (y₂ * y₁) := by rw [hx, hy]
        _ = x₂ * (x₁ * y₂) * y₁ := by group
        _ = x₂ * (y₂ * x₁) * y₁ := by rw [h12]
        _ = (x₂ : Z) * y₂ * (x₁ * y₁) := by group
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      have hx : (x : Z) ^ q = 1 := hFel.2 _ x.2
      have hy : (y : Z) ^ q = 1 := hF'el.2 _ y.2
      have hc : Commute (x : Z) (y : Z) := hcomm _ x.2 _ y.2
      rw [hc.mul_pow, hx, hy, one_mul]
  · have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_prod, hFc, hF'c, ← pow_add] at h1
    exact h1.symm

theorem rank_sum_of_family {ι : Type*} [DecidableEq ι] {A E : ι → Subgroup Y} {q : ℕ} {a : ι → ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hsn : ∀ i, CFSG.Open.IsSubnormal (A i) ⊤)
    (hp : ∀ i, ⁅A i, A i⁆ = A i)
    (hqs : ∀ i, CFSG.Open.IsQuasisimple (↥(A i) ⧸ CFSG.pCore 2 ↥(A i)))
    (hinj : Function.Injective A)
    (hZ : ∀ i, ¬ q ∣ Nat.card (center (↥(A i) ⧸ CFSG.pCore 2 ↥(A i))))
    (hEA : ∀ i, E i ≤ A i) (hEel : ∀ i, IsElemAbelian q (E i)) (hEc : ∀ i, Nat.card (E i) = q ^ a i)
    (S : Finset ι) :
    ∃ W : Subgroup Y, IsElemAbelian q W ∧ Nat.card W = q ^ (∑ i ∈ S, a i) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : Y →* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hdisj : ∀ {F : Subgroup Y}, IsElemAbelian q F → Disjoint F π.ker := by
    intro F hF
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hF.isPGroup hker hx hxk
  have hcomp : ∀ i, CFSG.IsComponent ((A i).map π) := fun i => isComponent_image (hsn i) (hqs i)
  have hcommA : ∀ i j, i ≠ j → ⁅(A i).map π, (A j).map π⁆ = ⊥ := by
    intro i j hij
    have hne : (A i).map π ≠ (A j).map π := fun h =>
      hij (hinj (image_injective (hsn i) (hp i) (hsn j) (hp j) h))
    exact (CFSG.LocalCores.distinct_components_commute (hcomp i) (hcomp j)).resolve_left hne
  have hEcard : ∀ i, Nat.card ((E i).map π) = q ^ a i := fun i => by
    rw [card_map_of_disjoint_ker π (E i) (hdisj (hEel i)), hEc i]
  have hcenI : ∀ i, ¬ q ∣ Nat.card (Subgroup.center ↥((A i).map π)) := fun i => by
    rw [← Nat.card_congr (Subgroup.centerCongr (barIso (hsn i))).toEquiv]
    exact hZ i
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
        have hyA : y ∈ (A j).map π := Subgroup.map_mono (hEA j) hy
        exact (Subgroup.mem_centralizer_iff.1 (hcentr (hWle hx)) y hyA).symm
      have hint : W ⊓ (E j).map π = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have hzA : z ∈ (A j).map π := Subgroup.map_mono (hEA j) hz.2
        have hzc : ∀ b ∈ (A j).map π, b * z = z * b :=
          fun b hb => Subgroup.mem_centralizer_iff.1 (hcentr (hWle hz.1)) b hb
        have hzq : z ^ q = 1 := ((hEel j).map π).2 z hz.2
        have := eq_one_of_central_of_pow_eq_one hq (hcenI j) hzA hzc hzq
        rw [this]
        exact Subgroup.one_mem _
      obtain ⟨W', hW'le, hW'el, hW'card⟩ := exists_elemAbelian_le_sup_of_commute hq hWel
        ((hEel j).map π) hWcard (hEcard j) hcommWE hint
      refine ⟨W', hW'el, ?_, ?_⟩
      · rw [hW'card, Finset.sum_insert hjS, add_comm]
      · refine hW'le.trans (sup_le ?_ ?_)
        · exact hWle.trans (iSup₂_le fun i hi =>
            le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl)
        · exact (Subgroup.map_mono (hEA j)).trans
            (le_iSup₂_of_le j (Finset.mem_insert_self j S) le_rfl)
  obtain ⟨W, hWel, hWcard, -⟩ := key S
  obtain ⟨Q₁, hQ₁p, hQ₁map, hQ₁disj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 W hWel.isPGroup
  refine ⟨Q₁, isElemAbelian_of_disjoint_ker π Q₁ hQ₁disj (by rw [hQ₁map]; exact hWel), ?_⟩
  rw [← card_map_of_disjoint_ker π Q₁ hQ₁disj, hQ₁map, hWcard]

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
