module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Pi
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup

private lemma a210sa_le_centralizer {X : Type} [Group X] (A : Fin 4 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (i j : Fin 4) (hij : i ≠ j) : A j ≤ Subgroup.centralizer (A i : Set X) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm i j hij a ha w hw

private lemma a210sa_normalized {X : Type} [Group X] (A : Fin 4 → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (i : Fin 4) : ∀ w ∈ ⨆ j, A j, ∀ a ∈ A i, w * a * w⁻¹ ∈ A i := by
  intro w hw
  refine Subgroup.iSup_induction (C := fun x => ∀ a ∈ A i, x * a * x⁻¹ ∈ A i)
    (fun j => A j) hw (fun j x hxj a ha => ?_) ?_ ?_
  · by_cases hij : j = i
    · rw [hij] at hxj
      exact (A i).mul_mem ((A i).mul_mem hxj ha) ((A i).inv_mem hxj)
    · have hxC : x ∈ Subgroup.centralizer (A i : Set X) :=
        a210sa_le_centralizer A hcomm i j (Ne.symm hij) hxj
      have hxa : x * a = a * x := ((Subgroup.mem_centralizer_iff.mp hxC) a ha).symm
      rw [hxa, mul_assoc, mul_inv_cancel, mul_one]
      exact ha
  · intro a ha
    simpa using ha
  · intro x y hx hy a ha
    have h1 : x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
    rw [h1]
    exact hx _ (hy a ha)

theorem exists_pi_of_commuting_quasisimple {X : Type} [Group X] [Finite X]
    (A : Fin 4 → Subgroup X) (hq : ∀ i, CFSG.IsQuasisimple ↥(A i))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (h3 : ∀ i, 3 ∣ Nat.card ↥(A i)) :
    ∃ (W : Subgroup X) (B : Fin 4 → Type) (_ : ∀ i, Group (B i)) (_ : ∀ i, Finite (B i))
      (θ : ↥W →* ∀ i, B i), Function.Surjective θ ∧ SimpleFactors B := by
  let W : Subgroup X := ⨆ i, A i
  have hAW : ∀ i, A i ≤ W := fun i => le_iSup (fun i => A i) i
  let C : ∀ i, Subgroup X := fun i => Subgroup.centralizer (A i : Set X)
  have hCj : ∀ i j, i ≠ j → A j ≤ C i :=
    fun i j hij => a210sa_le_centralizer A hcomm i j hij
  have hnorm : ∀ i, ∀ w : X, w ∈ W → ∀ a ∈ A i, w * a * w⁻¹ ∈ A i := by
    intro i w hw a ha
    exact a210sa_normalized A hcomm i w hw a ha
  let N : ∀ i, Subgroup ↥W := fun i => (C i).subgroupOf W
  have hN : ∀ i, (N i).Normal := by
    intro i
    refine ⟨fun n hn w => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro a ha
    have ha' : (w : X)⁻¹ * a * w ∈ A i := by
      simpa using hnorm i (w : X)⁻¹ (W.inv_mem w.2) a ha
    have hna' : ((w : X)⁻¹ * a * w) * (n : X) = (n : X) * ((w : X)⁻¹ * a * w) :=
      hn _ ha'
    calc a * ((w : X) * (n : X) * (w : X)⁻¹)
        = (w : X) * (((w : X)⁻¹ * a * w) * (n : X)) * (w : X)⁻¹ := by group
      _ = (w : X) * ((n : X) * ((w : X)⁻¹ * a * w)) * (w : X)⁻¹ := by rw [hna']
      _ = ((w : X) * (n : X) * (w : X)⁻¹) * a := by group
  have hWC : ∀ i, ∀ w : X, w ∈ W → ∃ a ∈ A i, ∃ n ∈ C i, w = a * n := by
    intro i w hw
    refine Subgroup.iSup_induction (C := fun x => ∃ a ∈ A i, ∃ n ∈ C i, x = a * n)
      (fun j => A j) hw (fun j x hxj => ?_) ?_ ?_
    · by_cases hij : j = i
      · rw [hij] at hxj
        exact ⟨x, hxj, 1, (C i).one_mem, by simp⟩
      · exact ⟨1, (A i).one_mem, x, hCj i j (Ne.symm hij) hxj, by simp⟩
    · exact ⟨1, (A i).one_mem, 1, (C i).one_mem, by simp⟩
    · rintro x y ⟨a, ha, n, hn, hx⟩ ⟨a', ha', n', hn', hy⟩
      refine ⟨a * a', (A i).mul_mem ha ha', n * n', (C i).mul_mem hn hn', ?_⟩
      have hna' : n * a' = a' * n := ((Subgroup.mem_centralizer_iff.mp hn) a' ha').symm
      rw [hx, hy]
      calc (a * n) * (a' * n') = a * (n * a') * n' := by group
        _ = a * (a' * n) * n' := by rw [hna']
        _ = (a * a') * (n * n') := by group
  let α : ∀ i, ↥(A i) →* ↥W ⧸ N i := fun i =>
    (QuotientGroup.mk' (N i)).comp (Subgroup.inclusion (hAW i))
  have hker : ∀ i, (α i).ker = Subgroup.center ↥(A i) := by
    intro i
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have hmem : Subgroup.inclusion (hAW i) a ∈ N i := by
        rw [← QuotientGroup.eq_one_iff]
        exact h
      have hcen := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
      exact Subtype.ext (by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion] using hcen g g.2)
    · intro h
      change (Subgroup.inclusion (hAW i) a : ↥W ⧸ N i) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro b hb
      simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion] using
        congrArg Subtype.val (h ⟨b, hb⟩)
  have hα : ∀ i, Function.Surjective (α i) := by
    intro i y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, n, hn, hwn⟩ := hWC i (w : X) w.2
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← hw]
    change ((⟨a, hAW i ha⟩ : ↥W) : ↥W ⧸ N i) = (w : ↥W ⧸ N i)
    have hnx : (⟨a, hAW i ha⟩ : ↥W)⁻¹ * w ∈ N i := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : (((⟨a, hAW i ha⟩ : ↥W)⁻¹ * w : ↥W) : X) = n := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hwn]
        change a⁻¹ * (a * n) = n
        group
      rw [hcoe]
      exact hn
    exact (QuotientGroup.eq (a := (⟨a, hAW i ha⟩ : ↥W)) (b := w)).mpr hnx
  let e : ∀ i, (↥(A i) ⧸ Subgroup.center ↥(A i)) ≃* (↥W ⧸ N i) := fun i =>
    (QuotientGroup.quotientMulEquivOfEq (hker i).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (α i) (hα i))
  refine ⟨W, fun i => ↥W ⧸ N i, fun i => QuotientGroup.Quotient.group (N i),
    fun i => inferInstance, Pi.monoidHom (fun i => QuotientGroup.mk' (N i)), ?_, ?_⟩
  ·
    intro f
    have hsurj : ∀ i, ∃ w : ↥W, (w : ↥W ⧸ N i) = f i :=
      fun i => QuotientGroup.mk_surjective (f i)
    choose w hw using hsurj
    choose a ha n hn hwn using fun i => hWC i (w i : X) (w i).2
    let x : ∀ i, ↥W := fun i => ⟨a i, hAW i (ha i)⟩
    have hxmem : ∀ i j, j ≠ i → x j ∈ N i := by
      intro i j hji
      rw [Subgroup.mem_subgroupOf]
      exact hCj i j (Ne.symm hji) (ha j)
    have hxj : ∀ i j, j ≠ i → (x j : ↥W ⧸ N i) = 1 := by
      intro i j hji
      rw [QuotientGroup.eq_one_iff]
      exact hxmem i j hji
    have hxw : ∀ i, (x i : ↥W ⧸ N i) = f i := by
      intro i
      have hmem : (x i)⁻¹ * w i ∈ N i := by
        rw [Subgroup.mem_subgroupOf]
        have hxa : ((x i : ↥W) : X) = a i := rfl
        have hcoe : (((x i)⁻¹ * w i : ↥W) : X) = n i := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hxa, hwn]
          group
        rw [hcoe]
        exact hn i
      rw [← hw i]
      exact (QuotientGroup.eq (a := x i) (b := w i)).mpr hmem
    refine ⟨x 0 * x 1 * x 2 * x 3, ?_⟩
    funext i
    fin_cases i
    · change QuotientGroup.mk' (N 0) (x 0 * x 1 * x 2 * x 3) = f 0
      simp only [map_mul, QuotientGroup.mk'_apply]
      rw [hxj 0 1 (by decide), hxj 0 2 (by decide), hxj 0 3 (by decide), hxw 0]
      simp
    · change QuotientGroup.mk' (N 1) (x 0 * x 1 * x 2 * x 3) = f 1
      simp only [map_mul, QuotientGroup.mk'_apply]
      rw [hxj 1 0 (by decide), hxj 1 2 (by decide), hxj 1 3 (by decide), hxw 1]
      simp
    · change QuotientGroup.mk' (N 2) (x 0 * x 1 * x 2 * x 3) = f 2
      simp only [map_mul, QuotientGroup.mk'_apply]
      rw [hxj 2 0 (by decide), hxj 2 1 (by decide), hxj 2 3 (by decide), hxw 2]
      simp
    · change QuotientGroup.mk' (N 3) (x 0 * x 1 * x 2 * x 3) = f 3
      simp only [map_mul, QuotientGroup.mk'_apply]
      rw [hxj 3 0 (by decide), hxj 3 1 (by decide), hxj 3 2 (by decide), hxw 3]
      simp
  ·
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨_, hsimple, _, _, _⟩ := hq i
      exact (e i).isSimpleGroup_congr.mp hsimple
    · intro i
      obtain ⟨_, _, a, b, hab⟩ := hq i
      refine ⟨e i a, e i b, fun h => hab ?_⟩
      have h' : e i (a * b) = e i (b * a) := by
        rw [map_mul, map_mul]
        exact h
      exact (e i).injective h'
    · intro i
      obtain ⟨hperf, _, _, _, _⟩ := hq i
      have hdiv := CFSG.RankThree.PartTwo.Sec4.RonanK432.three_dvd_card_quot_center hperf (h3 i)
      rwa [Nat.card_congr (e i).toEquiv] at hdiv

end CFSG.LocalAnalysis.WeakClosure81.Asch210
