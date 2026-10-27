module

public import CFSG.Timmesfeld.Transvection.TriangleCoordsG

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped Matrix commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

namespace Coords

variable {S : TriangleSetting Δ A E B t} (c : S.Coords)

theorem commutator_mem {n : G} (hn : n ∈ corrN A E t) {a : G} (ha : a ∈ A)
    {s : GaloisField 2 c.k} (hs : c.mat a = lowerElt _ s) :
    ⁅n, a⁆ ∈ corrN A E t ⊓ Subgroup.centralizer (A : Set G) ∧
      c.vec ⁅n, a⁆ = ![0, s * c.vec n 0] := by
  have haX : a ∈ A ⊔ E := Subgroup.mem_sup_left ha
  have h1 : a * n⁻¹ * a⁻¹ ∈ corrN A E t := conj_mem_corrN haX (Subgroup.inv_mem _ hn)
  have hmN : ⁅n, a⁆ ∈ corrN A E t := by
    rw [commutatorElement_def, show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
    exact Subgroup.mul_mem _ hn h1
  have hinv : c.vec n⁻¹ = c.vec n := by rw [c.vec_inv hn, CharTwo.neg_eq]
  have hvec : c.vec ⁅n, a⁆ = ![0, s * c.vec n 0] := by
    rw [commutatorElement_def, show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group,
      c.vec_mul hn h1, c.vec_conj haX (Subgroup.inv_mem _ hn), hs, lowerElt_mulVec, hinv]
    ext i
    fin_cases i
    · simp [CharTwo.add_self_eq_zero]
    · simp only [Fin.mk_one, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  refine ⟨⟨hmN, Subgroup.mem_centralizer_iff.2 fun a' ha' => ?_⟩, hvec⟩
  have h0 : c.vec ⁅n, a⁆ 0 = 0 := by rw [hvec]; rfl
  exact ((c.commute_A_iff hmN).2 h0 a' ha').symm.eq

end Coords

variable (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (hq : 4 ≤ Nat.card A)
include S htY hq

theorem commutator_eq_conj_mul [Finite G] (hpts : PointsDetermined Δ) {D : Subgroup G}
    (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) (c : S.Coords) {w : G} (hw : w ∈ A ⊔ E)
    (hwm : c.mat w = weylElt _) {x : G} (hx : x ∈ corrN A E t) {a : G} (ha : a ∈ A)
    {s : GaloisField 2 c.k} (hs : c.mat a = lowerElt _ s) {y : G} (hy : y ∈ corrN A E t)
    (hyv : c.vec y = ![s * c.vec x 0, 0]) : ∃ d ∈ D, ⁅x, a⁆ = w * y * w⁻¹ * d := by
  obtain ⟨hm, hmv⟩ := c.commutator_mem hx ha hs
  have hr : w * y * w⁻¹ ∈ corrN A E t := conj_mem_corrN hw hy
  have hrv : c.vec (w * y * w⁻¹) = ![0, s * c.vec x 0] := by
    rw [c.vec_conj hw hy, hwm, hyv]
    ext i
    fin_cases i <;> simp [coe_weylElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd : (w * y * w⁻¹)⁻¹ * ⁅x, a⁆ ∈ corrN A E t :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hr) hm.1
  have hd0 : c.vec ((w * y * w⁻¹)⁻¹ * ⁅x, a⁆) = 0 := by
    rw [c.vec_mul (Subgroup.inv_mem _ hr) hm.1, c.vec_inv hr, hrv, hmv, neg_add_cancel]
  refine ⟨(w * y * w⁻¹)⁻¹ * ⁅x, a⁆, ?_, by group⟩
  rw [S.eq_corrN_inf_centralizer htY hq hpts hD hDE]
  exact ⟨hd, (c.vec_eq_zero_iff hd).1 hd0⟩

end TriangleSetting

end CFSG.Timmesfeld.Transvection
