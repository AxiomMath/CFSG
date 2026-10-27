module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalizerA
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] noncomputable def Z : Subgroup G := t.d.AA ⊓ Subgroup.centralizer ({t.y} : Set G)

theorem Z_le_AA : t.Z ≤ t.d.AA := inf_le_left

theorem Z_le_centralizer : t.Z ≤ Subgroup.centralizer ({t.y} : Set G) := inf_le_right

theorem le_centralizer_Z : t.P ≤ Subgroup.centralizer (t.Z : Set G) := by
  rw [← t.hPy]
  refine sup_le ?_ ?_
  · intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact t.d.S_commute z s (t.Z_le_AA.trans t.d.AA_le_S hz) hs
  · exact Subgroup.zpowers_le.mpr fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mp (t.Z_le_centralizer hz)

private theorem inf_A_sup_A_eq_bot {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    t.d.A i ⊓ (t.d.A j ⊔ t.d.A k) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact t.d.eq_one_of_mem_Lf_of_mem_sup hij hik hjk (t.d.A_le_S i hx.1)
    ((t.d.A_le_H i).trans (t.d.H_le_Lf i) hx.1)
    (by
      have hjk : t.d.A j ⊔ t.d.A k ≤ t.d.Lf j ⊔ t.d.Lf k :=
        sup_le (fun y hy => Subgroup.mem_sup_left
            ((t.d.A_le_H j).trans (t.d.H_le_Lf j) hy))
          (fun y hy => Subgroup.mem_sup_right
            ((t.d.A_le_H k).trans (t.d.H_le_Lf k) hy))
      exact hjk hx.2)

private theorem eq_of_mul_eq_of_mem_A_of_mem_sup {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {a b u v : G} (ha : a ∈ t.d.A i) (hb : b ∈ t.d.A i)
    (hu : u ∈ t.d.A j ⊔ t.d.A k) (hv : v ∈ t.d.A j ⊔ t.d.A k) (h : a * u = b * v) : a = b := by
  have hmem : b⁻¹ * a ∈ t.d.A i ⊓ (t.d.A j ⊔ t.d.A k) := by
    refine Subgroup.mem_inf.mpr ⟨(t.d.A i).mul_mem ((t.d.A i).inv_mem hb) ha, ?_⟩
    have heq : b⁻¹ * a = v * u⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * u) * u⁻¹ := by group
        _ = b⁻¹ * (b * v) * u⁻¹ := by rw [h]
        _ = v * u⁻¹ := by group
    rw [heq]
    exact (t.d.A j ⊔ t.d.A k).mul_mem hv ((t.d.A j ⊔ t.d.A k).inv_mem hu)
  rw [inf_A_sup_A_eq_bot t hij hik hjk] at hmem
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem)).symm

theorem eq_of_mem_A_mul_eq {a0 b0 a1 b1 a2 b2 : G} (ha0 : a0 ∈ t.d.A 0) (hb0 : b0 ∈ t.d.A 0)
    (ha1 : a1 ∈ t.d.A 1) (hb1 : b1 ∈ t.d.A 1) (ha2 : a2 ∈ t.d.A 2) (hb2 : b2 ∈ t.d.A 2)
    (h : a0 * a1 * a2 = b0 * b1 * b2) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  have h0 : a0 = b0 := by
    refine eq_of_mul_eq_of_mem_A_of_mem_sup t (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide) ha0 hb0 ?_ ?_ (by simpa [mul_assoc] using h)
    · exact Subgroup.mul_mem_sup ha1 ha2
    · exact Subgroup.mul_mem_sup hb1 hb2
  have hcancel : a1 * a2 = b1 * b2 := by
    have h' : b0 * (a1 * a2) = b0 * (b1 * b2) := by
      simpa [mul_assoc, h0] using h
    exact mul_left_cancel h'
  have h1 : a1 = b1 := by
    refine eq_of_mul_eq_of_mem_A_of_mem_sup t (i := 1) (j := 2) (k := 0)
      (by decide) (by decide) (by decide) ha1 hb1 ?_ ?_ hcancel
    · exact Subgroup.mem_sup_left ha2
    · exact Subgroup.mem_sup_left hb2
  have h2 : a2 = b2 := by
    have h' : b1 * a2 = b1 * b2 := by simpa [h1] using hcancel
    exact mul_left_cancel h'
  exact ⟨h0, h1, h2⟩

private theorem A_le_normalizer_A {i j : Fin 3} :
    t.d.A i ≤ Subgroup.normalizer (t.d.A j : Set G) := by
  refine (show t.d.A i ≤ Subgroup.centralizer (t.d.A j : Set G) from ?_).trans
    (Subgroup.centralizer_le_normalizer _)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (t.d.S_commute a b (t.d.A_le_S i ha) (t.d.A_le_S j hb)).symm

theorem exists_mem_A_mul_mem_A_mul {x : G} (hx : x ∈ t.d.AA) :
    ∃ a0 ∈ t.d.A 0, ∃ a1 ∈ t.d.A 1, ∃ a2 ∈ t.d.A 2, a0 * a1 * a2 = x := by
  have hxjoin : x ∈ (t.d.A 0 ⊔ t.d.A 1) ⊔ t.d.A 2 := by
    simpa [t.d.AA_def] using hx
  have hnorm : (t.d.A 0 ⊔ t.d.A 1) ≤
      Subgroup.normalizer (((t.d.A 2 : Subgroup G)) : Set G) := by
    refine (show (t.d.A 0 ⊔ t.d.A 1) ≤
        Subgroup.centralizer (((t.d.A 2 : Subgroup G)) : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have haS : a ∈ t.d.S :=
      (sup_le (t.d.A_le_S 0) (t.d.A_le_S 1) : t.d.A 0 ⊔ t.d.A 1 ≤ t.d.S) ha
    exact (t.d.S_commute a b haS (t.d.A_le_S 2 hb)).symm
  have hxmul : x ∈ ((t.d.A 0 ⊔ t.d.A 1 : Subgroup G) : Set G) * (t.d.A 2 : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (t.d.A 0 ⊔ t.d.A 1) (t.d.A 2) hnorm]
    exact hxjoin
  obtain ⟨u, hu, a2, ha2, rfl⟩ := hxmul
  have hnorm01 : t.d.A 0 ≤ Subgroup.normalizer ((t.d.A 1 : Subgroup G) : Set G) :=
    A_le_normalizer_A t (i := 0) (j := 1)
  have humul : u ∈ ((t.d.A 0 : Subgroup G) : Set G) * ((t.d.A 1 : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (t.d.A 0) (t.d.A 1) hnorm01]
    exact hu
  obtain ⟨a0, ha0, a1, ha1, rfl⟩ := humul
  exact ⟨a0, ha0, a1, ha1, a2, ha2, rfl⟩

private theorem exists_ne_one_A0 : ∃ a : ↥(t.d.A 0), a ≠ 1 := by
  have hcard : Nat.card (t.d.A 0) = 3 := t.d.card_A 0
  haveI : Nontrivial ↥(t.d.A 0) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  exact exists_ne (1 : ↥(t.d.A 0))

private noncomputable def a0 : ↥(t.d.A 0) := Classical.choose (exists_ne_one_A0 t)

private theorem a0_ne_one : (t.a0 : ↥(t.d.A 0)) ≠ 1 :=
  Classical.choose_spec (exists_ne_one_A0 t)

private theorem a0_ne_one_G : (t.a0 : G) ≠ 1 := fun h => t.a0_ne_one (Subtype.ext h)

private theorem map_conj_A_two (i : Fin 3) :
    (t.d.A i).map (MulAut.conj (t.y ^ 2)).toMonoidHom = t.d.A (i + 2) := by
  have hcomp : (MulAut.conj (t.y ^ 2)).toMonoidHom =
      (MulAut.conj t.y).toMonoidHom.comp (MulAut.conj t.y).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show t.y ^ 2 * z * (t.y ^ 2)⁻¹ = t.y * (t.y * z * t.y⁻¹) * t.y⁻¹ by
      rw [pow_two]; group]
  rw [hcomp, ← Subgroup.map_map, t.map_conj_A i, t.map_conj_A (i + 1)]
  congr 1
  fin_cases i <;> rfl

private noncomputable def zP1 : G := t.y * (t.a0 : G) * t.y⁻¹

private noncomputable def zP2 : G := t.y ^ 2 * (t.a0 : G) * (t.y ^ 2)⁻¹

private noncomputable def zPt : G := (t.a0 : G) * t.zP1 * t.zP2

private theorem zP0_mem_A0 : (t.a0 : G) ∈ t.d.A 0 := t.a0.2

private theorem zP1_mem_A1 : t.zP1 ∈ t.d.A 1 := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom (t.a0.2)
  rwa [t.map_conj_A 0] at h

private theorem zP2_mem_A2 : t.zP2 ∈ t.d.A 2 := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj (t.y ^ 2)).toMonoidHom (t.a0.2)
  rwa [t.map_conj_A_two 0] at h

private theorem zP1_ne_one : t.zP1 ≠ 1 := by
  intro h
  apply t.a0_ne_one_G
  calc (t.a0 : G) = t.y⁻¹ * (t.y * (t.a0 : G) * t.y⁻¹) * t.y := by group
    _ = t.y⁻¹ * 1 * t.y := by rw [← zP1, h]
    _ = 1 := by group

private theorem zP2_ne_one : t.zP2 ≠ 1 := by
  intro h
  apply t.a0_ne_one_G
  calc (t.a0 : G) = (t.y ^ 2)⁻¹ * (t.y ^ 2 * (t.a0 : G) * (t.y ^ 2)⁻¹) * t.y ^ 2 := by
        group
    _ = (t.y ^ 2)⁻¹ * 1 * t.y ^ 2 := by rw [← zP2, h]
    _ = 1 := by group

private theorem S_commute' {a b : G} (ha : a ∈ t.d.S) (hb : b ∈ t.d.S) : a * b = b * a :=
  t.d.S_commute a b ha hb

private theorem mul_rotate_S {a b c : G} (ha : a ∈ t.d.S) (hb : b ∈ t.d.S) (hc : c ∈ t.d.S) :
    a * b * c = b * c * a := by
  letI : CommGroup ↥(t.d.S) :=
    { (inferInstance : Group ↥(t.d.S)) with
      mul_comm := fun x y => Subtype.ext (t.d.S_commute x y x.2 y.2) }
  let a' : ↥(t.d.S) := ⟨a, ha⟩
  let b' : ↥(t.d.S) := ⟨b, hb⟩
  let c' : ↥(t.d.S) := ⟨c, hc⟩
  have h : a' * b' * c' = b' * c' * a' := mul_rotate a' b' c'
  simpa [a', b', c'] using congrArg Subtype.val h

private theorem zPt_mem_AA : t.zPt ∈ t.d.AA := by
  rw [t.d.AA_def]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup (t.zP0_mem_A0) (t.zP1_mem_A1))
    (t.zP2_mem_A2)

private theorem y_conj_zP0 : t.y * (t.a0 : G) * t.y⁻¹ = t.zP1 := rfl

private theorem y_conj_zP1 : t.y * t.zP1 * t.y⁻¹ = t.zP2 := by
  rw [zP1, zP2, pow_two]
  group

private theorem y_conj_zP2 : t.y * t.zP2 * t.y⁻¹ = (t.a0 : G) := by
  rw [zP2]
  calc t.y * (t.y ^ 2 * (t.a0 : G) * (t.y ^ 2)⁻¹) * t.y⁻¹
      = (t.y * t.y ^ 2) * (t.a0 : G) * ((t.y ^ 2)⁻¹ * t.y⁻¹) := by group
    _ = (t.a0 : G) := by
        rw [show t.y * t.y ^ 2 = t.y ^ 3 by group, t.hy3]
        rw [show (t.y ^ 2)⁻¹ * t.y⁻¹ = (t.y * t.y ^ 2)⁻¹ by group]
        rw [show t.y * t.y ^ 2 = t.y ^ 3 by group, t.hy3]
        group

private theorem zPt_conj_y : t.y * t.zPt * t.y⁻¹ = t.zPt := by
  have hrot : t.zP1 * t.zP2 * (t.a0 : G) = (t.a0 : G) * t.zP1 * t.zP2 := by
    have h12 : t.zP1 * t.zP2 = t.zP2 * t.zP1 :=
      S_commute' t (t.d.A_le_S 1 t.zP1_mem_A1) (t.d.A_le_S 2 t.zP2_mem_A2)
    have h02 : (t.a0 : G) * t.zP2 = t.zP2 * (t.a0 : G) :=
      S_commute' t (t.d.A_le_S 0 t.zP0_mem_A0) (t.d.A_le_S 2 t.zP2_mem_A2)
    have h01 : (t.a0 : G) * t.zP1 = t.zP1 * (t.a0 : G) :=
      S_commute' t (t.d.A_le_S 0 t.zP0_mem_A0) (t.d.A_le_S 1 t.zP1_mem_A1)
    calc t.zP1 * t.zP2 * (t.a0 : G)
        = t.zP1 * (t.zP2 * (t.a0 : G)) := by group
      _ = t.zP1 * ((t.a0 : G) * t.zP2) := by rw [h02]
      _ = (t.zP1 * (t.a0 : G)) * t.zP2 := by group
      _ = ((t.a0 : G) * t.zP1) * t.zP2 := by rw [h01]
      _ = (t.a0 : G) * t.zP1 * t.zP2 := by group
  calc t.y * t.zPt * t.y⁻¹
      = (t.y * (t.a0 : G) * t.y⁻¹) * (t.y * t.zP1 * t.y⁻¹) *
          (t.y * t.zP2 * t.y⁻¹) := by
        rw [zPt]; group
    _ = t.zP1 * t.zP2 * (t.a0 : G) := by rw [y_conj_zP0, y_conj_zP1, y_conj_zP2]
    _ = (t.a0 : G) * t.zP1 * t.zP2 := hrot
    _ = t.zPt := by rw [zPt]

private theorem zPt_comm_y : t.zPt * t.y = t.y * t.zPt := by
  calc t.zPt * t.y = (t.y * t.zPt * t.y⁻¹) * t.y := by rw [zPt_conj_y]
    _ = t.y * t.zPt := by group

private theorem zPt_mem_Z : t.zPt ∈ t.Z :=
  Subgroup.mem_inf.mpr ⟨t.zPt_mem_AA,
    Subgroup.mem_centralizer_singleton_iff.mpr t.zPt_comm_y⟩

private theorem zPt_pow_three : t.zPt ^ 3 = 1 :=
  t.d.isElemAbelian_AA.2 t.zPt t.zPt_mem_AA

private theorem zPt_ne_one : t.zPt ≠ 1 := by
  intro h
  have hcoord := t.eq_of_mem_A_mul_eq (a0 := (t.a0 : G)) (b0 := 1)
    (a1 := t.zP1) (b1 := 1) (a2 := t.zP2) (b2 := 1)
    t.zP0_mem_A0 (t.d.A 0).one_mem t.zP1_mem_A1 (t.d.A 1).one_mem
    t.zP2_mem_A2 (t.d.A 2).one_mem (by simpa [zPt] using h)
  exact t.a0_ne_one (Subtype.ext hcoord.1)

private theorem zPt_orderOf : orderOf t.zPt = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime t.zPt_pow_three t.zPt_ne_one

private theorem z_coord_shift {x b0 b1 b2 : G} (hxZ : x ∈ t.Z) (hx : x = b0 * b1 * b2)
    (hb0 : b0 ∈ t.d.A 0) (hb1 : b1 ∈ t.d.A 1) (hb2 : b2 ∈ t.d.A 2) :
    t.y * b0 * t.y⁻¹ = b1 ∧ t.y * b1 * t.y⁻¹ = b2 ∧ t.y * b2 * t.y⁻¹ = b0 := by
  have hxy : x * t.y = t.y * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (t.Z_le_centralizer hxZ)
  have hyx : t.y * x * t.y⁻¹ = x := by
    calc t.y * x * t.y⁻¹ = x * t.y * t.y⁻¹ := by rw [← hxy]
      _ = x := by group
  have hc0 : t.y * b0 * t.y⁻¹ ∈ t.d.A 1 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom hb0
    rwa [t.map_conj_A 0] at h
  have hc1 : t.y * b1 * t.y⁻¹ ∈ t.d.A 2 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom hb1
    rwa [t.map_conj_A 1] at h
  have hc2 : t.y * b2 * t.y⁻¹ ∈ t.d.A 0 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom hb2
    rwa [t.map_conj_A 2, show (2 : Fin 3) + 1 = 0 by decide] at h
  have hs0 : t.y * b0 * t.y⁻¹ ∈ t.d.S := t.d.A_le_S 1 hc0
  have hs1 : t.y * b1 * t.y⁻¹ ∈ t.d.S := t.d.A_le_S 2 hc1
  have hs2 : t.y * b2 * t.y⁻¹ ∈ t.d.S := t.d.A_le_S 0 hc2
  have hexpand : t.y * x * t.y⁻¹ =
      (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) * (t.y * b2 * t.y⁻¹) := by
    rw [hx]; group
  have hrot : (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) * (t.y * b2 * t.y⁻¹) =
      (t.y * b2 * t.y⁻¹) * (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) := by
    calc (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) * (t.y * b2 * t.y⁻¹)
        = (t.y * b1 * t.y⁻¹) * (t.y * b2 * t.y⁻¹) * (t.y * b0 * t.y⁻¹) :=
          mul_rotate_S t hs0 hs1 hs2
      _ = (t.y * b2 * t.y⁻¹) * (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) := by
          rw [mul_rotate_S t hs1 hs2 hs0]
  have hprod : (t.y * b2 * t.y⁻¹) * (t.y * b0 * t.y⁻¹) * (t.y * b1 * t.y⁻¹) =
      b0 * b1 * b2 := by
    rw [← hrot, ← hexpand, hyx, hx]
  have huniq := t.eq_of_mem_A_mul_eq hc2 hb0 hc0 hb1 hc1 hb2 hprod
  exact ⟨huniq.2.1, huniq.2.2, huniq.1⟩

private theorem le_zpowers_zPt : t.Z ≤ Subgroup.zpowers t.zPt := by
  intro x hxZ
  have hxA : x ∈ t.d.AA := t.Z_le_AA hxZ
  obtain ⟨b0, hb0, b1, hb1, b2, hb2, hx⟩ := t.exists_mem_A_mul_mem_A_mul hxA
  obtain ⟨hs0, hs1, hs2⟩ := t.z_coord_shift hxZ hx.symm hb0 hb1 hb2
  by_cases hb0_one : b0 = 1
  · have hb1_one : b1 = 1 := by rw [← hs0, hb0_one]; group
    have hb2_one : b2 = 1 := by rw [← hs1, hb1_one]; group
    rw [← hx, hb0_one, hb1_one, hb2_one, mul_one, mul_one]
    exact Subgroup.one_mem _
  · have hA0 : t.d.A 0 = Subgroup.zpowers (t.a0 : G) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t.a0.2) ?_).symm
      rw [Nat.card_zpowers, orderOf_eq_prime ((t.d.mem_A_iff 0).mp t.a0.2).2 t.a0_ne_one_G,
        t.d.card_A 0]
    have hb0_mem : b0 ∈ Subgroup.zpowers (t.a0 : G) := by rw [← hA0]; exact hb0
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hb0_mem
    have hb1_eq : b1 = t.zP1 ^ e := by
      rw [← hs0, ← he]
      have hmap : (MulAut.conj t.y) ((t.a0 : G) ^ e) = ((MulAut.conj t.y) (t.a0 : G)) ^ e :=
        map_zpow (MulAut.conj t.y) (t.a0 : G) e
      simpa [MulAut.conj_apply, zP1] using hmap
    have hb2_eq : b2 = t.zP2 ^ e := by
      rw [← hs1, hb1_eq]
      have hmap : (MulAut.conj t.y) (t.zP1 ^ e) = ((MulAut.conj t.y) t.zP1) ^ e :=
        map_zpow (MulAut.conj t.y) t.zP1 e
      have hconj : (MulAut.conj t.y) t.zP1 = t.zP2 := by
        simpa [MulAut.conj_apply] using t.y_conj_zP1
      simpa [hconj, zP2] using hmap
    have h01 : Commute (t.a0 : G) t.zP1 :=
      S_commute' t (t.d.A_le_S 0 t.zP0_mem_A0) (t.d.A_le_S 1 t.zP1_mem_A1)
    have h02 : Commute (t.a0 : G) t.zP2 :=
      S_commute' t (t.d.A_le_S 0 t.zP0_mem_A0) (t.d.A_le_S 2 t.zP2_mem_A2)
    have h12 : Commute t.zP1 t.zP2 :=
      S_commute' t (t.d.A_le_S 1 t.zP1_mem_A1) (t.d.A_le_S 2 t.zP2_mem_A2)
    have h012 : Commute ((t.a0 : G) * t.zP1) t.zP2 := h02.mul_left h12
    have hx_eq : x = t.zPt ^ e := by
      rw [← hx, ← he, hb1_eq, hb2_eq, zPt]
      rw [← h01.mul_zpow e, ← h012.mul_zpow e]
    exact Subgroup.mem_zpowers_iff.mpr ⟨e, hx_eq.symm⟩

private theorem eq_zpowers_zPt : t.Z = Subgroup.zpowers t.zPt := by
  refine le_antisymm t.le_zpowers_zPt ?_
  exact Subgroup.zpowers_le.mpr t.zPt_mem_Z

theorem card_Z : Nat.card t.Z = 3 := by
  rw [t.eq_zpowers_zPt, Nat.card_zpowers, t.zPt_orderOf]

private theorem L_normal_in_M : t.d.M ≤ Subgroup.normalizer (t.d.L : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hperm' : ∀ m ∈ t.d.M, ∀ i, ∃ j,
      (t.d.Lf i).map (MulAut.conj m).toMonoidHom = t.d.Lf j := by
    intro m hm i
    exact t.hperm m (t.hdM ▸ hm) i
  let σ : Equiv.Perm (Fin 3) := t.d.permHom t.hinj hperm' ⟨m, hm⟩
  have hσ (i : Fin 3) : (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) = t.d.Lf (σ i) :=
    t.d.map_conj_Lf_eq t.hinj hperm' ⟨m, hm⟩ i
  apply le_antisymm
  · rw [t.d.hL, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hσ 0]; simpa [t.d.hL] using t.d.Lf_le_L (σ 0)
    · rw [hσ 1]; simpa [t.d.hL] using t.d.Lf_le_L (σ 1)
    · rw [hσ 2]; simpa [t.d.hL] using t.d.Lf_le_L (σ 2)
  · conv_lhs => rw [t.d.hL]
    refine sup_le (sup_le ?_ ?_) ?_
    · obtain ⟨i, hi⟩ := σ.surjective 0
      have h : t.d.Lf 0 = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := by
        calc t.d.Lf 0 = t.d.Lf (σ i) := by rw [hi]
          _ = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := (hσ i).symm
      exact h ▸ Subgroup.map_mono (t.d.Lf_le_L i)
    · obtain ⟨i, hi⟩ := σ.surjective 1
      have h : t.d.Lf 1 = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := by
        calc t.d.Lf 1 = t.d.Lf (σ i) := by rw [hi]
          _ = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := (hσ i).symm
      exact h ▸ Subgroup.map_mono (t.d.Lf_le_L i)
    · obtain ⟨i, hi⟩ := σ.surjective 2
      have h : t.d.Lf 2 = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := by
        calc t.d.Lf 2 = t.d.Lf (σ i) := by rw [hi]
          _ = (t.d.Lf i).map (↑(MulAut.conj m) : G →* G) := (hσ i).symm
      exact h ▸ Subgroup.map_mono (t.d.Lf_le_L i)

private theorem A_le_AA (i : Fin 3) : t.d.A i ≤ t.d.AA := by
  rw [t.d.AA_def]
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private theorem AA_le_M : t.d.AA ≤ t.d.M := by
  rw [t.hdM]
  exact (t.d.AA_le_L.trans (by rw [t.hdL]; exact c.hyp81.1))

private theorem L_le_M : t.d.L ≤ t.d.M := by
  rw [t.hdL, t.hdM]
  exact c.hyp81.1

theorem exists_sign (i : Fin 3) :
    ∃ l ∈ c.L, ∀ j : Fin 3, ∀ a ∈ t.d.A j, l * a * l⁻¹ = if j = i then a⁻¹ else a := by
  obtain ⟨l, hlL, -, hsign⟩ := t.d.exists_sign_in_product i
  exact ⟨l, t.hdL ▸ hlL, hsign⟩

private theorem eq_inv_of_ne_of_mem_card_three {A : Subgroup G} (hA : Nat.card A = 3)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : b ≠ a) :
    b = a⁻¹ := by
  classical
  have ha3 : a ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
    rw [hA] at h
    simpa using congrArg (fun z : ↥A => (z : G)) h
  have hA3 : (A : Set G).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hA
  have hsub : ({1, a, b} : Set G) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
  have hpair : ({1, a, b} : Set G).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, a, b, ha1.symm, hb1.symm, hne.symm, rfl⟩
  have hAeq : ({1, a, b} : Set G) = A :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hA3, hpair])
  have hmem : a⁻¹ ∈ ({1, a, b} : Set G) := by
    rw [hAeq]
    exact A.inv_mem ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | ha' | hb'
  · exact absurd (inv_eq_one.mp h1) ha1
  · exfalso
    have ha2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [ha']
        _ = 1 := mul_inv_cancel a
    have : a = 1 := by
      calc a = a * 1 := by rw [mul_one]
        _ = a * (a * a) := by rw [ha2, mul_one]
        _ = a ^ 3 := (pow_three a).symm
        _ = 1 := ha3
    exact ha1 this
  · exact hb'.symm

private theorem conj_three {l0 l1 l2 x y0 y1 y2 : G}
    (h0 : l0 * x * l0⁻¹ = y0) (h1 : l1 * y0 * l1⁻¹ = y1)
    (h2 : l2 * y1 * l2⁻¹ = y2) :
    (l2 * l1 * l0) * x * (l2 * l1 * l0)⁻¹ = y2 := by
  rw [← h2, ← h1, ← h0]
  group

theorem exists_conj_mem_Z {x : G} (hx : x ∈ t.d.AA)
    (hxij : ∀ i j : Fin 3, x ∉ t.d.A i ⊔ t.d.A j) :
    ∃ l ∈ c.L, l * x * l⁻¹ ∈ t.Z := by
  classical
  obtain ⟨b0, hb0, b1, hb1, b2, hb2, hx'⟩ := t.exists_mem_A_mul_mem_A_mul hx
  have hx_eq : x = b0 * b1 * b2 := hx'.symm
  have hb0_ne : b0 ≠ 1 := by
    intro h0
    exact hxij 1 2 (by rw [hx_eq, h0, one_mul]; exact Subgroup.mul_mem_sup hb1 hb2)
  have hb1_ne : b1 ≠ 1 := by
    intro h1
    exact hxij 0 2 (by rw [hx_eq, h1, mul_one]; exact Subgroup.mul_mem_sup hb0 hb2)
  have hb2_ne : b2 ≠ 1 := by
    intro h2
    exact hxij 0 1 (by rw [hx_eq, h2, mul_one]; exact Subgroup.mul_mem_sup hb0 hb1)
  obtain ⟨s0, hs0L, hs0⟩ := t.exists_sign 0
  obtain ⟨s1, hs1L, hs1⟩ := t.exists_sign 1
  obtain ⟨s2, hs2L, hs2⟩ := t.exists_sign 2
  let l0 : G := if b0 = (t.a0 : G) then 1 else s0
  let l1 : G := if b1 = t.zP1 then 1 else s1
  let l2 : G := if b2 = t.zP2 then 1 else s2
  have hl0L : l0 ∈ c.L := by
    by_cases h : b0 = (t.a0 : G)
    · simp [l0, h]
    · simpa [l0, h] using hs0L
  have hl1L : l1 ∈ c.L := by
    by_cases h : b1 = t.zP1
    · simp [l1, h]
    · simpa [l1, h] using hs1L
  have hl2L : l2 ∈ c.L := by
    by_cases h : b2 = t.zP2
    · simp [l2, h]
    · simpa [l2, h] using hs2L
  have hl0_b0 : l0 * b0 * l0⁻¹ = (t.a0 : G) := by
    by_cases h : b0 = (t.a0 : G)
    · simp [l0, h]
    · have hb0inv : b0 = (t.a0 : G)⁻¹ :=
        eq_inv_of_ne_of_mem_card_three (t.d.card_A 0) t.a0.2 hb0 t.a0_ne_one_G hb0_ne h
      dsimp [l0]
      rw [if_neg h, hb0inv]
      simpa using hs0 0 ((t.a0 : G)⁻¹) ((t.d.A 0).inv_mem t.a0.2)
  have hl1_b1 : l1 * b1 * l1⁻¹ = t.zP1 := by
    by_cases h : b1 = t.zP1
    · simp [l1, h]
    · have hb1inv : b1 = t.zP1⁻¹ :=
        eq_inv_of_ne_of_mem_card_three (t.d.card_A 1) t.zP1_mem_A1 hb1
          t.zP1_ne_one hb1_ne h
      dsimp [l1]
      rw [if_neg h, hb1inv]
      simpa using hs1 1 (t.zP1⁻¹) ((t.d.A 1).inv_mem t.zP1_mem_A1)
  have hl2_b2 : l2 * b2 * l2⁻¹ = t.zP2 := by
    by_cases h : b2 = t.zP2
    · simp [l2, h]
    · have hb2inv : b2 = t.zP2⁻¹ :=
        eq_inv_of_ne_of_mem_card_three (t.d.card_A 2) t.zP2_mem_A2 hb2
          t.zP2_ne_one hb2_ne h
      dsimp [l2]
      rw [if_neg h, hb2inv]
      simpa using hs2 2 (t.zP2⁻¹) ((t.d.A 2).inv_mem t.zP2_mem_A2)
  have hl0_b1 : l0 * b1 * l0⁻¹ = b1 := by
    by_cases h : b0 = (t.a0 : G)
    · simp [l0, h]
    · dsimp [l0]
      rw [if_neg h]
      simpa using hs0 1 b1 hb1
  have hl0_b2 : l0 * b2 * l0⁻¹ = b2 := by
    by_cases h : b0 = (t.a0 : G)
    · simp [l0, h]
    · dsimp [l0]
      rw [if_neg h]
      simpa using hs0 2 b2 hb2
  have hl1_a0 : l1 * (t.a0 : G) * l1⁻¹ = (t.a0 : G) := by
    by_cases h : b1 = t.zP1
    · simp [l1, h]
    · dsimp [l1]
      rw [if_neg h]
      simpa using hs1 0 (t.a0 : G) t.a0.2
  have hl1_b2 : l1 * b2 * l1⁻¹ = b2 := by
    by_cases h : b1 = t.zP1
    · simp [l1, h]
    · dsimp [l1]
      rw [if_neg h]
      simpa using hs1 2 b2 hb2
  have hl2_a0 : l2 * (t.a0 : G) * l2⁻¹ = (t.a0 : G) := by
    by_cases h : b2 = t.zP2
    · simp [l2, h]
    · dsimp [l2]
      rw [if_neg h]
      simpa using hs2 0 (t.a0 : G) t.a0.2
  have hl2_a1 : l2 * t.zP1 * l2⁻¹ = t.zP1 := by
    by_cases h : b2 = t.zP2
    · simp [l2, h]
    · dsimp [l2]
      rw [if_neg h]
      simpa using hs2 1 t.zP1 t.zP1_mem_A1
  have hstep0 : l0 * x * l0⁻¹ = (t.a0 : G) * b1 * b2 := by
    rw [hx_eq]
    calc l0 * (b0 * b1 * b2) * l0⁻¹ =
        (l0 * b0 * l0⁻¹) * (l0 * b1 * l0⁻¹) * (l0 * b2 * l0⁻¹) := by group
      _ = (t.a0 : G) * b1 * b2 := by rw [hl0_b0, hl0_b1, hl0_b2]
  have hstep1 : l1 * ((t.a0 : G) * b1 * b2) * l1⁻¹ = (t.a0 : G) * t.zP1 * b2 := by
    calc l1 * ((t.a0 : G) * b1 * b2) * l1⁻¹ =
        (l1 * (t.a0 : G) * l1⁻¹) * (l1 * b1 * l1⁻¹) * (l1 * b2 * l1⁻¹) := by group
      _ = (t.a0 : G) * t.zP1 * b2 := by rw [hl1_a0, hl1_b1, hl1_b2]
  have hstep2 : l2 * ((t.a0 : G) * t.zP1 * b2) * l2⁻¹ = t.zPt := by
    calc l2 * ((t.a0 : G) * t.zP1 * b2) * l2⁻¹ =
        (l2 * (t.a0 : G) * l2⁻¹) * (l2 * t.zP1 * l2⁻¹) * (l2 * b2 * l2⁻¹) := by group
      _ = (t.a0 : G) * t.zP1 * t.zP2 := by rw [hl2_a0, hl2_a1, hl2_b2]
      _ = t.zPt := by rw [zPt]
  refine ⟨l2 * l1 * l0, ?_, ?_⟩
  · rw [← t.hdL]
    exact t.d.L.mul_mem (t.d.L.mul_mem (t.hdL.symm ▸ hl2L) (t.hdL.symm ▸ hl1L))
      (t.hdL.symm ▸ hl0L)
  · rw [conj_three (l0 := l0) (l1 := l1) (l2 := l2) hstep0 hstep1 hstep2]
    exact t.zPt_mem_Z

section

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem centralizer_le_of_mem_AA {p : ℕ} (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {x : G} (hx : x ∈ t.d.AA) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ c.S.M := by
  classical
  by_cases hpair : ∃ i j : Fin 3, i ≠ j ∧ x ∈ t.d.A i ⊔ t.d.A j
  · obtain ⟨i, j, hij, hxij⟩ := hpair
    have hY : Subgroup.zpowers x ≤ t.d.A i ⊔ t.d.A j := Subgroup.zpowers_le.mpr hxij
    have hY1 : Subgroup.zpowers x ≠ ⊥ := by
      intro h
      exact hx1 (Subgroup.zpowers_eq_bot.mp h)
    have hNle := hN.normalizer_le hij hY hY1
    have hCZ : Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro y hy
    apply hNle
    have hy' : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rwa [← hCZ]
    exact Subgroup.centralizer_le_normalizer _ hy'
  · push Not at hpair
    have hxij : ∀ i j : Fin 3, x ∉ t.d.A i ⊔ t.d.A j := by
      intro i j hmem
      by_cases hij : i = j
      · subst hij
        have hj' : ∃ j' : Fin 3, j' ≠ i := by
          fin_cases i
          · exact ⟨1, by decide⟩
          · exact ⟨0, by decide⟩
          · exact ⟨0, by decide⟩
        obtain ⟨j', hj'⟩ := hj'
        exact hpair i j' (Ne.symm hj') (Subgroup.mem_sup_left (by simpa using hmem))
      · exact hpair i j hij hmem
    obtain ⟨l, hlL, hlZ⟩ := t.exists_conj_mem_Z hx hxij
    have hlM : l ∈ c.S.M := c.hyp81.1 (t.hdL ▸ hlL)
    let y : G := l * x * l⁻¹
    have hyZ : y ∈ t.Z := hlZ
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      calc x = l⁻¹ * y * l := by
            rw [show y = l * x * l⁻¹ from rfl]
            group
        _ = l⁻¹ * 1 * l := by rw [h]
        _ = 1 := by group
    have hygen : t.Z = Subgroup.zpowers y := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyZ) ?_).symm
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Nat.card_zpowers,
        orderOf_eq_prime (t.d.isElemAbelian_AA.2 y (t.Z_le_AA hyZ)) hy1, t.card_Z]
    have hCeq : Subgroup.centralizer (t.Z : Set G) =
        Subgroup.centralizer ({y} : Set G) := by
      rw [hygen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hCy : Subgroup.centralizer ({y} : Set G) ≤ c.S.M := by
      rw [← hCeq]
      exact hZ
    intro z hz
    have hzy : l * z * l⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
      have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l * z * l⁻¹) * y = l * (z * x) * l⁻¹ := by simp [y, mul_assoc]
        _ = l * (x * z) * l⁻¹ := by rw [hzx]
        _ = y * (l * z * l⁻¹) := by simp [y, mul_assoc]
    have hzM : l * z * l⁻¹ ∈ c.S.M := hCy hzy
    have hlM' : l⁻¹ ∈ c.S.M := c.S.M.inv_mem hlM
    have hz_eq : z = l⁻¹ * (l * z * l⁻¹) * l := by group
    rw [hz_eq]
    exact c.S.M.mul_mem (c.S.M.mul_mem hlM' hzM) hlM

theorem normalizer_Z_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.normalizer (t.Z : Set G) ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let CZ : Subgroup G := Subgroup.centralizer (t.Z : Set G)
  have hPZ : CFSG.ABGLocalTools.IsSylowOf 3 t.P CZ :=
    (t.isSylowOf_top hp hN).of_le t.le_centralizer_Z le_top
  intro h hh
  have hhN : h ∈ Subgroup.normalizer (t.Z : Set G) := hh
  let P' : Subgroup G := t.P.map (MulAut.conj h).toMonoidHom
  have hCZmap : CZ.map (MulAut.conj h).toMonoidHom = CZ := by
    rw [show CZ = Subgroup.centralizer (t.Z : Set G) from rfl,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv]
    congr 1
    exact congrArg (fun H : Subgroup G => (H : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hhN)
  have hP'Z : CFSG.ABGLocalTools.IsSylowOf 3 P' CZ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨?_, ?_, ?_⟩
    · calc P' = t.P.map (MulAut.conj h).toMonoidHom := rfl
        _ ≤ CZ.map (MulAut.conj h).toMonoidHom := Subgroup.map_mono t.le_centralizer_Z
        _ = CZ := hCZmap
    · exact (t.isSylowOf_top hp hN).isPGroup.map _
    · have hrel : P'.relIndex CZ = t.P.relIndex CZ := by
        have h := Subgroup.relIndex_map_map_of_injective (H := t.P) (K := CZ)
          (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
        rw [hCZmap] at h
        simpa [P'] using h
      rw [hrel]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hPZ).2.2
  obtain ⟨k, hkC, hk⟩ := hPZ.exists_mem_conj hP'Z
  have hkZ : k ∈ CZ := hkC
  have hkM : k ∈ c.S.M := hZ hkZ
  have hkNormP : k⁻¹ * h ∈ Subgroup.normalizer (t.P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxP' : h * x * h⁻¹ ∈ P' := by
        exact Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hx
      have := (hk (h * x * h⁻¹)).mp hxP'
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hx
      have hxP' : h * x * h⁻¹ ∈ P' := by
        exact (hk (h * x * h⁻¹)).mpr (by simpa [MulAut.conj_apply, mul_assoc] using hx)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP'
      have hyx' : h * y * h⁻¹ = h * x * h⁻¹ := by
        simpa [MulAut.conj_apply] using hyx
      have hyx'' : y = x := by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [hyx']
          _ = x := by group
      rwa [hyx''] at hy
  have hkM' : k⁻¹ * h ∈ c.S.M := normalizer_P_le t hp hN hkNormP
  have hk_inv : k⁻¹ ∈ c.S.M := c.S.M.inv_mem hkM
  have h_eq : h = k * (k⁻¹ * h) := by group
  rw [h_eq]
  exact c.S.M.mul_mem hkM hkM'

end

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
