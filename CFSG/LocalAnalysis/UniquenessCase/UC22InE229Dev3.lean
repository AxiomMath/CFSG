module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Ker3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Conj3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229k_exists_conj_nine {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ}
    (hX : IsSU3 (Bar2 Y) n) (h3 : 3 ∣ 2 ^ n + 1) (hnorm : ¬ M ≤ normalizer (Y : Set G)) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian 3 B₀ ∧ Nat.card B₀ = 3 ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnorm
  let π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  obtain ⟨E₀, hE₀, hE₀c⟩ := uc22ine229u3e9_exists_elemAbelian_sq
    ((QuotientGroup.mk' (center (Bar2 Y))).comp π)
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) Nat.prime_three
    (by norm_num) (uc22ine229u3e9_two_le_pRank hX.2 h3)
  let E : Subgroup G := E₀.map Y.subtype
  have hEY : E ≤ Y := Subgroup.map_subtype_le _
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hE₀c]
  let f : MulAut G := MulAut.conj m
  have hM : M.map f.toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hY' : Y.map f.toMonoidHom ∈ calC M := UC6S846.calC_map M f hM hY
  have hne : Y.map f.toMonoidHom ≠ Y := fun h => hmN (UC6S846.mem_normalizer_iff_map_conj.2 h)
  refine ⟨E.map f.toMonoidHom, (Subgroup.map_mono hEY).trans hY'.1.le, (hE₀.map _).map _, ?_,
    fun b hb y hy => uc22ine229_commutator_mem_of_ne hY' hY hne (Subgroup.map_mono hEY hb) hy⟩
  rw [Subgroup.card_map_of_injective f.injective, hEc]

private theorem conj_mem_pCoreOf {M : Subgroup G} {x o : G} (hx : x ∈ M)
    (ho : o ∈ pCoreOf 2 M) : x * o * x⁻¹ ∈ pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.1
    ((Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)) hx) o).1 ho

private def centO2 (M Y : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M}
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun y hy => ?_⟩
    have h1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
        a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
    rw [h1]
    exact (pCoreOf 2 M).mul_mem (conj_mem_pCoreOf haM (hb y hy)) (ha y hy)
  one_mem' := ⟨M.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun y hy => ?_⟩
    have h1 : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h1]
    exact conj_mem_pCoreOf (M.inv_mem haM) (inv_mem (ha y hy))

private theorem mem_normalizer_of_map_eq {Y : Subgroup G} {a b : G}
    (h : Y.map (MulAut.conj a).toMonoidHom = Y.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ normalizer (Y : Set G) := by
  have hcomp : MulAut.conj a = MulAut.conj b * MulAut.conj (b⁻¹ * a) := by
    rw [← map_mul, mul_inv_cancel_left]
  have h1 : Y.map (MulAut.conj a).toMonoidHom =
      (Y.map (MulAut.conj (b⁻¹ * a)).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
    rw [hcomp, Subgroup.map_map]
    rfl
  rw [h1] at h
  exact UC6S846.mem_normalizer_iff_map_conj.2
    (Subgroup.map_injective (MulAut.conj b).injective h)

theorem uc22ine229k_exists_three_conj {M Y : Subgroup G} (hY : Y ∈ calC M)
    (hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 Y))) (h3Y : 3 ∣ Nat.card (Bar2 Y)) {m : G} (hm : m ∈ M)
    (hm3 : m ^ 3 = 1) (hmN : m ∉ normalizer (Y : Set G)) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian 3 B₀ ∧ Nat.card B₀ = 3 ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have h3Y' : 3 ∣ Nat.card ↥Y :=
    h3Y.trans (Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      (QuotientGroup.mk'_surjective _))
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3Y'
  let X₀ : Subgroup G := Subgroup.zpowers (y₀ : G)
  have hX₀c : Nat.card X₀ = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy₀]
  have hX₀Y : X₀ ≤ Y := Subgroup.zpowers_le.2 y₀.2
  have hX₀el : IsElemAbelian 3 X₀ := UC6S898.isElemAbelian_of_card_prime hp3 hX₀c
  let g : Fin 2 → MulAut G := fun i => MulAut.conj (m ^ (i.val + 1))
  have hgM : ∀ i, M.map (g i).toMonoidHom = M := fun i =>
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem hm _))
  have hYi : ∀ i, Y.map (g i).toMonoidHom ∈ calC M := fun i => UC6S846.calC_map M (g i) (hgM i) hY
  have hmN2 : m ^ 2 ∉ normalizer (Y : Set G) := fun h => hmN (by
    have h4 : m = (m ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc m = m * m ^ 3 := by rw [hm3, mul_one]
        _ = m ^ (2 * 2) := by rw [← pow_succ']
    rw [h4]
    exact Subgroup.pow_mem _ h 2)
  have hne0 : ∀ i, Y.map (g i).toMonoidHom ≠ Y := by
    intro i h
    have h1 := UC6S846.mem_normalizer_iff_map_conj.2 h
    fin_cases i
    · exact hmN (by simpa [g] using h1)
    · exact hmN2 (by simpa [g] using h1)
  have h01 : Y.map (g 0).toMonoidHom ≠ Y.map (g 1).toMonoidHom := by
    intro h
    have h1 : (m ^ 2)⁻¹ * m ^ 1 ∈ normalizer (Y : Set G) := mem_normalizer_of_map_eq h
    have h2 : (m ^ 2)⁻¹ * m ^ 1 = m⁻¹ := by
      rw [pow_one, pow_two, mul_inv_rev, inv_mul_cancel_right]
    rw [h2] at h1
    exact hmN (by simpa using inv_mem h1)
  have hne : ∀ i j : Fin 2, i ≠ j → Y.map (g i).toMonoidHom ≠ Y.map (g j).toMonoidHom := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h01.symm
    · exact absurd rfl hij
  let H : Subgroup G := centO2 M Y
  have hHM : H ≤ M := fun x hx => hx.1
  have hYiH : ∀ i, Y.map (g i).toMonoidHom ≤ H := fun i x hx =>
    ⟨(hYi i).1.le hx, fun y hy =>
      uc22ine229_commutator_mem_of_ne (hYi i) hY (hne0 i) hx hy⟩
  have hYiCH : ∀ i, Y.map (g i).toMonoidHom ∈ calC H := fun i =>
    ⟨by
      have h1 := IsSubnormal.inf_of_le (hYi i).1 hHM
      rwa [inf_eq_left.2 (hYiH i)] at h1, (hYi i).2⟩
  have hcalC := fun i => UC6S846.calC_subgroupOf (hYiCH i)
  have hEi : ∀ i, X₀.map (g i).toMonoidHom ≤ Y.map (g i).toMonoidHom := fun i =>
    Subgroup.map_mono hX₀Y
  obtain ⟨W, hWel, hWcard⟩ := UC6S898.rank_sum_of_family (Y := ↥H) (ι := Fin 2)
    (A := fun i => (Y.map (g i).toMonoidHom).subgroupOf H)
    (E := fun i => (X₀.map (g i).toMonoidHom).subgroupOf H) (q := 3) (a := fun _ => 1) hp3
    (by norm_num) (fun i => (hcalC i).1) (fun i => (hcalC i).2.1) (fun i => (hcalC i).2.2.1)
    (by
      intro i j hij
      by_contra hne'
      have hmap := congrArg (Subgroup.map H.subtype) hij
      rw [Subgroup.map_subgroupOf_eq_of_le (hYiH i), Subgroup.map_subgroupOf_eq_of_le (hYiH j)]
        at hmap
      exact hne i j hne' hmap)
    (fun i => by
      rw [(hcalC i).2.2.2, UC6S846.card_center_bar2_map]
      exact hZ3)
    (fun i x hx => hEi i hx) (fun i => (hX₀el.map _).subgroupOf H)
    (fun i => by
      have hEH : X₀.map (g i).toMonoidHom ≤ H := (hEi i).trans (hYiH i)
      show Nat.card ((X₀.map (g i).toMonoidHom).subgroupOf H) = 3 ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv,
        Subgroup.card_map_of_injective (g i).injective, hX₀c])
    Finset.univ
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin 2)), (fun _ : Fin 2 => 1) i) = 2 := by simp
  rw [hsum] at hWcard
  refine ⟨W.map H.subtype, (Subgroup.map_subtype_le W).trans hHM, hWel.map _, ?_,
    fun b hb y hy => ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hWcard]
  · obtain ⟨w, -, rfl⟩ := hb
    exact w.2.2 y hy

theorem uc22ine229k_exists_B₀ {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) (hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 Y)))
    (hrank : CFSG.Open.pRank q M ≤ 3) (h4 : 4 ≤ CFSG.Open.pRank 3 M)
    (hbd : ∀ R : Subgroup (MulAut (Bar2 Y)), IsElemAbelian 3 R → Nat.card R ≤ 3 ^ 2)
    (hbd' : ¬ 3 ∣ Nat.card (Bar2 Y) →
      ∀ R : Subgroup (MulAut (Bar2 Y)), IsElemAbelian 3 R → Nat.card R ≤ 3) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian 3 B₀ ∧ Nat.card B₀ = 3 ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  classical
  obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three h4
  set A : Subgroup G := B ⊓ normalizer (Y : Set G) with hAdef
  have hAB : A ≤ B := inf_le_left
  have hAN : A ≤ normalizer (Y : Set G) := inf_le_right
  have hAel : IsElemAbelian 3 A := hBel.mono hAB
  have hA27 : 27 ≤ Nat.card A := uc22ine229c3_card_inf_normalizer hY hq hq2 hXY hXc hZ hrank hBM hBc
  set R : Subgroup (MulAut (Bar2 Y)) :=
    (A.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y) with hRdef
  have hRel : IsElemAbelian 3 R := (hAel.subgroupOf _).map _
  have hR9 : Nat.card R ≤ 3 ^ 2 := hbd R hRel
  by_cases hker : 3 ^ 2 * Nat.card R ≤ Nat.card A
  · obtain ⟨B₀, hB₀A, hB₀el, hB₀c, hB₀Y⟩ :=
      uc22ine229k_exists_kernel hY.1 Nat.prime_three hAN hAel hker
    exact ⟨B₀, (hB₀A.trans hAB).trans hBM, hB₀el, hB₀c, hB₀Y⟩
  push Not at hker
  have hR3 : 3 < Nat.card R := by omega
  have h3Y : 3 ∣ Nat.card (Bar2 Y) := by
    by_contra h
    have := hbd' h R hRel
    omega
  obtain ⟨m, hmB, hmN⟩ : ∃ m ∈ B, m ∉ normalizer (Y : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ A := fun x hx => ⟨hx, hcon x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  exact uc22ine229k_exists_three_conj hY hZ3 h3Y (hBM hmB) (hBel.2 m hmB) hmN

end CFSG.LocalAnalysis.UniquenessCase.UC22
