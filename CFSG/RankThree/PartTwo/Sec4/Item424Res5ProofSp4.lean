module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofBlock
public import CFSG.LieType.SeitzGeneration.SpFourData

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP
open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace Item424Res5

section Form

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_form_ne_zero {ω : LinearMap.BilinForm K V} (hω : ω.IsAlt) {A : V →ₗ[K] V}
    (hiso : ∀ x y, ω (A x) (A y) = ω x y) {P : Submodule K V} (hstab : ∀ v ∈ P, A v ∈ P)
    (hnorm : ∀ v ∈ P, v + A v + A (A v) = 0) (hnd : (ω.restrict P).Nondegenerate)
    (hP : P ≠ ⊥) (h3 : (3 : K) ≠ 0) : ∃ u ∈ P, ω u (A u) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hP
  rw [eq_bot_iff]
  intro v hv
  have key : ∀ x ∈ P, ∀ y ∈ P, ω x (A y) = ω (A x) y := by
    intro x hx y hy
    have h1 := hcon (x + y) (P.add_mem hx hy)
    simp only [map_add, LinearMap.add_apply] at h1
    rw [hcon x hx, hcon y hy] at h1
    have h2 : ω y (A x) = -ω (A x) y := (hω.neg_eq (A x) y).symm
    rw [h2] at h1
    linear_combination h1
  have hzero : ∀ y ∈ P, ω (A (A v) - v) y = 0 := by
    intro y hy
    have h1 := key (A v) (hstab v hv) y hy
    rw [hiso] at h1
    rw [map_sub, LinearMap.sub_apply, ← h1, sub_self]
  have hmem : A (A v) - v ∈ P := P.sub_mem (hstab _ (hstab v hv)) hv
  have hAAv : A (A v) = v := by
    have h1 := hnd.1 ⟨A (A v) - v, hmem⟩ (fun y => hzero y y.2)
    have h2 : A (A v) - v = 0 := congrArg Subtype.val h1
    exact sub_eq_zero.mp h2
  have hn := hnorm v hv
  have hAv : A v = -(2 : K) • v := by
    linear_combination (norm := module) hn - hAAv
  have hAAv' : A (A v) = (4 : K) • v := by
    rw [hAv, map_smul, hAv, smul_smul]
    norm_num
  have h3v : (3 : K) • v = 0 := by
    linear_combination (norm := module) hAAv - hAAv'
  exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3v).resolve_left h3)

theorem exists_form_eq [Finite K] {ω : LinearMap.BilinForm K V} (hω : ω.IsAlt) {A : V →ₗ[K] V}
    (hiso : ∀ x y, ω (A x) (A y) = ω x y) {P : Submodule K V} (hstab : ∀ v ∈ P, A v ∈ P)
    (hnorm : ∀ v ∈ P, v + A v + A (A v) = 0) (hnd : (ω.restrict P).Nondegenerate)
    (hP : P ≠ ⊥) (h3 : (3 : K) ≠ 0) (c : K) : ∃ u ∈ P, ω u (A u) = c := by
  obtain ⟨u₀, hu₀, hc₀⟩ := exists_form_ne_zero hω hiso hstab hnorm hnd hP h3
  obtain ⟨s, t, hst⟩ := exists_normForm_eq h3 (c / ω u₀ (A u₀))
  refine ⟨s • u₀ + t • A u₀, P.add_mem (P.smul_mem s hu₀) (P.smul_mem t (hstab u₀ hu₀)), ?_⟩
  have hAA : A (A u₀) = -u₀ - A u₀ := by
    have := hnorm u₀ hu₀
    rw [← sub_eq_zero, ← this]
    abel
  have huu := hω u₀
  have hAuAu := hω (A u₀)
  have hAuu : ω (A u₀) u₀ = -ω u₀ (A u₀) := (hω.neg_eq u₀ (A u₀)).symm
  simp only [map_add, map_smul, hAA, map_sub, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, huu, hAuAu, hAuu]
  have : c = (s ^ 2 - s * t + t ^ 2) * ω u₀ (A u₀) := by
    rw [hst, div_mul_cancel₀ c hc₀]
  rw [this]
  ring

end Form

theorem linearIndependent_block_of_form {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {ω : LinearMap.BilinForm K V} (hω : ω.IsAlt) {A B : V →ₗ[K] V} {u w : V}
    (huA : ω u (A u) = 1) (hwB : ω w (B w) = 1) (huw : ω u w = 0) (huBw : ω u (B w) = 0)
    (hAuw : ω (A u) w = 0) (hAuBw : ω (A u) (B w) = 0) :
    LinearIndependent K ![u, A u, w, B w] := by
  have hskew : ∀ x y : V, ω y x = -ω x y := fun x y => (hω.neg_eq x y).symm
  have hAuu : ω (A u) u = -1 := by rw [hskew, huA]
  have hBww : ω (B w) w = -1 := by rw [hskew, hwB]
  have hwu : ω w u = 0 := by rw [hskew, huw, neg_zero]
  have hBwu : ω (B w) u = 0 := by rw [hskew, huBw, neg_zero]
  have hwAu : ω w (A u) = 0 := by rw [hskew, hAuw, neg_zero]
  have hBwAu : ω (B w) (A u) = 0 := by rw [hskew, hAuBw, neg_zero]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hc
  have e0 := congrArg (ω u) hc
  have e1 := congrArg (ω (A u)) hc
  have e2 := congrArg (ω w) hc
  have e3 := congrArg (ω (B w)) hc
  simp only [map_add, map_smul, map_zero, smul_eq_mul, hω u, hω (A u), hω w, hω (B w), huA, hwB,
    huw, huBw, hAuw, hAuBw, hAuu, hBww, hwu, hBwu, hwAu, hBwAu, mul_zero, mul_one, zero_add,
    add_zero, mul_neg] at e0 e1 e2 e3
  intro i
  fin_cases i
  · simpa using e1
  · simpa using e0
  · simpa using e3
  · simpa using e2

variable {K : Type} [Field K]

theorem exists_weyl_sp4 [Finite K] (h3 : (3 : K) ≠ 0) (E : Subgroup (StatedSp 2 K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) :
    ∃ g : StatedSp 2 K, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹ := by
  obtain ⟨a, b, P₀, P₁, B⟩ := exists_planeBlocks h3 hcomm hexp hcard
  have hω : (spForm 2 K).IsAlt := spForm_isAlt
  have hP₀ : P₀ ≠ ⊥ := fun h => by
    have := B.rank₀
    rw [h, finrank_bot] at this
    norm_num at this
  have hP₁ : P₁ ≠ ⊥ := fun h => by
    have := B.rank₁
    rw [h, finrank_bot] at this
    norm_num at this
  obtain ⟨u, hu, huA⟩ := exists_form_eq hω (spEnd_isometry a) B.stab_a₀ B.norm_a B.nd₀ hP₀ h3 1
  obtain ⟨w, hw, hwB⟩ := exists_form_eq hω (spEnd_isometry b) B.stab_b₁ B.norm_b B.nd₁ hP₁ h3 1
  obtain ⟨s, t, hst⟩ := exists_normForm_eq h3 (-1)
  have hAA : u + spEnd a u + spEnd a (spEnd a u) = 0 := B.norm_a u hu
  have hAw : spEnd a w = w := B.fix_a w hw
  have hABw : spEnd a (spEnd b w) = spEnd b w := B.fix_a _ (B.stab_b₁ w hw)
  have hBu : spEnd b u = u := B.fix_b u hu
  have hBAu : spEnd b (spEnd a u) = spEnd a u := B.fix_b _ (B.stab_a₀ u hu)
  have hBB : w + spEnd b w + spEnd b (spEnd b w) = 0 := B.norm_b w hw
  have huw : spForm 2 K u w = 0 := B.orth u hu w hw
  have huBw : spForm 2 K u (spEnd b w) = 0 := B.orth u hu _ (B.stab_b₁ w hw)
  have hAuw : spForm 2 K (spEnd a u) w = 0 := B.orth _ (B.stab_a₀ u hu) w hw
  have hAuBw : spForm 2 K (spEnd a u) (spEnd b w) = 0 :=
    B.orth _ (B.stab_a₀ u hu) _ (B.stab_b₁ w hw)
  have hli : LinearIndependent K ![u, spEnd a u, w, spEnd b w] :=
    linearIndependent_block_of_form hω huA hwB huw huBw hAuw hAuBw
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  set g := blockWeyl hli hV s t with hgdef
  have hdet : LinearMap.det g = 1 := by
    rw [hgdef, det_blockWeyl, hst]
    ring
  have hunit : IsUnit g := (LinearMap.isUnit_iff_isUnit_det g).mpr (by rw [hdet]; exact isUnit_one)
  have hmem : hunit.unit ∈ sesqUnitaryGroup (spForm 2 K) :=
    mem_sesqUnitaryGroup.mpr (blockWeyl_isometry hli hV (spForm 2 K) hω huA hwB huw huBw hAuw
      hAuBw hst)
  rw [← range_spLin] at hmem
  obtain ⟨G, hG⟩ := hmem
  have hGg : spEnd G = g := by
    change ((spLin 2 K G : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
      Module.End K (Fin 2 ⊕ Fin 2 → K)) = g
    rw [hG, IsUnit.unit_spec]
  have hGa : G * a = b * G := by
    apply spLin_injective
    refine Units.ext ?_
    change spEnd (G * a) = spEnd (b * G)
    rw [spEnd_mul, spEnd_mul, hGg]
    exact blockWeyl_comp_A hli hV s t hAA hAw hABw hBu hBAu hBB
  have hGb : G * b = a * a * G := by
    apply spLin_injective
    refine Units.ext ?_
    change spEnd (G * b) = spEnd (a * a * G)
    rw [spEnd_mul, spEnd_mul, spEnd_mul, hGg]
    exact blockWeyl_comp_B hli hV s t hAA hAw hABw hBu hBAu hBB
  have ha3 : a ^ 3 = 1 := hexp a B.ha
  have hGa' : G * a * G⁻¹ = b := by rw [hGa, mul_inv_cancel_right]
  have hGb' : G * b * G⁻¹ = a⁻¹ := by
    rw [hGb, mul_inv_cancel_right]
    rw [eq_inv_iff_mul_eq_one, ← ha3, pow_three, mul_assoc]
  have hba : b ∉ Subgroup.zpowers a := by
    intro hb
    let S : Subgroup (StatedSp 2 K) :=
      { carrier := {x | spEnd x w = w}
        mul_mem' := fun {x y} hx hy => by
          change spEnd x w = w at hx
          change spEnd y w = w at hy
          change spEnd (x * y) w = w
          rw [spEnd_comp_apply, hy, hx]
        one_mem' := spEnd_one_apply w
        inv_mem' := fun {x} hx => by
          change spEnd x w = w at hx
          change spEnd x⁻¹ w = w
          conv_lhs => rw [← hx]
          rw [← spEnd_comp_apply, inv_mul_cancel, spEnd_one_apply] }
    have hle : Subgroup.zpowers a ≤ S := (Subgroup.zpowers_le).mpr hAw
    have hbw : spEnd b w = w := hle hb
    rw [hbw, hbw] at hBB
    have h3w : (3 : K) • w = 0 := by
      rw [← hBB]
      module
    have hw0 : w = 0 := (smul_eq_zero.mp h3w).resolve_left h3
    rw [hw0, map_zero, LinearMap.zero_apply] at hwB
    exact zero_ne_one hwB
  exact ⟨G, weyl_of_gens hcomm hexp hcard B.ha B.hb B.ha1 hba hGa' hGb'⟩

theorem projSp_eq_map (K : Type) [Field K] :
    projSp 2 K = (StatedSp 2 K).map (ProjGenLinGroup.mk : GL (Fin 2 ⊕ Fin 2) K →* _) :=
  rfl

theorem sq_eq_one_of_mk_eq_one {z : StatedSp 2 K}
    (hz : ProjGenLinGroup.mk (z : GL (Fin 2 ⊕ Fin 2) K) = 1) : z ^ 2 = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, hc⟩ := hz
  have hsc : ∀ v, spEnd z v = (c : K) • v := by
    intro v
    rw [spEnd_apply, ← hc]
    simp [Matrix.GeneralLinearGroup.scalar]
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin 2 ⊕ Fin 2 → K, spForm 2 K x y ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := spForm_nondegenerate.1 (Pi.single (Sum.inl 0) 1) (fun y => h _ y)
    have := congrFun h0 (Sum.inl 0)
    simp at this
  have h1 := spEnd_isometry z x y
  rw [hsc, hsc, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  have hc2 : (c : K) * c = 1 := by
    have : ((c : K) * c - 1) * spForm 2 K x y = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hxy)
  have hcu : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two, hc2, Units.val_one])
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hcu, map_one]
  rfl

theorem census424_of_projSp {X : Type} [Group X] [Finite X] [Finite K] (h3 : (3 : K) ≠ 0)
    (eX : X ≃* projSp 2 K) : Census424 X := by
  let π₀ : StatedSp 2 K →* projSp 2 K :=
    ((ProjGenLinGroup.mk : GL (Fin 2 ⊕ Fin 2) K →* _).comp (StatedSp 2 K).subtype).codRestrict
      (projSp 2 K) (fun x => ⟨x, x.2, rfl⟩)
  have hπ₀ : Function.Surjective π₀ := by
    rintro ⟨y, hy⟩
    rw [projSp_eq_map, Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hπ : Function.Surjective (eX.symm.toMonoidHom.comp π₀) :=
    eX.symm.surjective.comp hπ₀
  refine census424_of_cover _ hπ (fun z hz => ?_) (fun E => exists_weyl_sp4 h3 E)
  have h1 : π₀ z = 1 := by
    apply eX.symm.injective
    rw [map_one]
    exact hz
  have h2 := sq_eq_one_of_mk_eq_one (congrArg Subtype.val h1)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]

end Item424Res5

end CFSG.RankThree.PartTwo.Sec4
