module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Lemma216

variable {Γ : Type*} [Group Γ]

theorem conj_eq_commutator_mul (x y : Γ) : x * y * x⁻¹ = ⁅x, y⁆ * y := by
  simp [commutatorElement_def]

theorem commutator_mem_of_mem_normalizer {X : Subgroup Γ} {x y : Γ}
    (hx : x ∈ Subgroup.normalizer (X : Set Γ)) (hy : y ∈ X) : ⁅x, y⁆ ∈ X := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have := mul_mem h1 (inv_mem hy)
  simpa [commutatorElement_def] using this

theorem mem_normalizer_inf {b : Γ} {X Y : Subgroup Γ} (hX : b ∈ Subgroup.normalizer (X : Set Γ))
    (hY : b ∈ Subgroup.normalizer (Y : Set Γ)) :
    b ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective, hX, hY]

theorem mem_normalizer_sup {b : Γ} {X Y : Subgroup Γ} (hX : b ∈ Subgroup.normalizer (X : Set Γ))
    (hY : b ∈ Subgroup.normalizer (Y : Set Γ)) :
    b ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_sup, hX, hY]

theorem conj_mem_centralizer {b z : Γ} {Y : Subgroup Γ} (hb : b ∈ Subgroup.normalizer (Y : Set Γ))
    (hz : z ∈ Subgroup.centralizer (Y : Set Γ)) :
    b * z * b⁻¹ ∈ Subgroup.centralizer (Y : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro y hy
  have hy' : b⁻¹ * y * b ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) y).mp hy
    simpa using this
  have h := hz _ hy'
  calc y * (b * z * b⁻¹) = b * ((b⁻¹ * y * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * y * b)) * b⁻¹ := by rw [h]
    _ = b * z * b⁻¹ * y := by group

theorem mem_normalizer_centralizer {b : Γ} {Y : Subgroup Γ}
    (hb : b ∈ Subgroup.normalizer (Y : Set Γ)) :
    b ∈ Subgroup.normalizer ((Subgroup.centralizer (Y : Set Γ) : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_centralizer hb hz, fun hz => ?_⟩
  have := conj_mem_centralizer (inv_mem hb) hz
  simpa [mul_assoc] using this

theorem mem_normalizer_cenIn {b : Γ} {X Y : Subgroup Γ} (hX : b ∈ Subgroup.normalizer (X : Set Γ))
    (hY : b ∈ Subgroup.normalizer (Y : Set Γ)) :
    b ∈ Subgroup.normalizer ((cenIn X (Y : Set Γ) : Subgroup Γ) : Set Γ) :=
  mem_normalizer_inf hX (mem_normalizer_centralizer hY)

theorem mem_normalizer_norIn {b : Γ} {X Y : Subgroup Γ} (hX : b ∈ Subgroup.normalizer (X : Set Γ))
    (hY : b ∈ Subgroup.normalizer (Y : Set Γ)) :
    b ∈ Subgroup.normalizer ((norIn X (Y : Set Γ) : Subgroup Γ) : Set Γ) :=
  mem_normalizer_inf hX (Subgroup.le_normalizer hY)

theorem mem_normalizer_fittingSubgroupOf {a : Γ} {H : Subgroup Γ}
    (ha : a ∈ Subgroup.normalizer (H : Set Γ)) :
    a ∈ Subgroup.normalizer ((CFSG.fittingSubgroupOf H : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => fittingSubgroupOf_conj_mem_of_mem_normalizer ha hx, fun hx => ?_⟩
  have := fittingSubgroupOf_conj_mem_of_mem_normalizer (inv_mem ha) hx
  simpa [mul_assoc] using this

theorem le_normalizer_of_le_centralizer {B Y : Subgroup Γ}
    (h : Y ≤ Subgroup.centralizer (B : Set Γ)) : B ≤ Subgroup.normalizer (Y : Set Γ) := by
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have := Subgroup.mem_centralizer_iff.mp (h hx) c hc
  have e : c * x * c⁻¹ = x := by rw [this]; group
  rw [e]
  exact hx

theorem mem_sectionCentralizer_iff_of_le {X Y : Subgroup Γ} (hXY : X ≤ Y) {x : Γ} :
    x ∈ sectionCentralizer X Y ↔
      x ∈ Subgroup.normalizer (X : Set Γ) ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ X := by
  constructor
  · rintro ⟨hx, -, h⟩
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_, h⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [conj_eq_commutator_mul]
      exact mul_mem (hXY (h y hy)) hy
    · intro hz
      have h1 : ⁅x⁻¹, x * y * x⁻¹⁆ = x⁻¹ * ⁅x, x * y * x⁻¹⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      have h2 : ⁅x⁻¹, x * y * x⁻¹⁆ ∈ X := by
        rw [h1]
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) _).mp (inv_mem (h _ hz))
        simpa using this
      have h3 : y = ⁅x⁻¹, x * y * x⁻¹⁆ * (x * y * x⁻¹) := by
        have := conj_eq_commutator_mul x⁻¹ (x * y * x⁻¹)
        simp only [inv_inv] at this
        rw [← this]
        group
      rw [h3]
      exact mul_mem (hXY h2) hz

theorem cenIn_inf_kOf (G A : Subgroup Γ) : cenIn G A ⊓ kOf G = cenIn (kOf G) A := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hxK⟩ := Subgroup.mem_inf.mp hx
    exact mem_cenIn_iff.mpr ⟨hxK, (mem_cenIn_iff.mp hxD).2⟩
  · intro hx
    obtain ⟨hxK, hxc⟩ := mem_cenIn_iff.mp hx
    exact Subgroup.mem_inf.mpr ⟨mem_cenIn_iff.mpr ⟨kOf_le G hxK, hxc⟩, hxK⟩

theorem cenIn_kOf_le (G A : Subgroup Γ) : cenIn (kOf G) A ≤ cenIn G A :=
  inf_le_inf_right _ (kOf_le G)

theorem admits_cenIn_kOf [Finite Γ] (G A : Subgroup Γ) :
    Admits (cenIn G A ⊔ A) (cenIn (kOf G) A) := by
  refine sup_le (fun d hd => ?_) (le_normalizer_of_le_centralizer inf_le_right)
  obtain ⟨hdG, hdc⟩ := mem_cenIn_iff.mp hd
  exact mem_normalizer_cenIn (Nonsolv.le_normalizer_kOf G hdG)
    (Subgroup.centralizer_le_normalizer _ hdc)

variable {p : ℕ} {A G S : Subgroup Γ}

structure Hyp (p : ℕ) (A G S : Subgroup Γ) : Prop where
  near : NearAsolvAction p A G
  sol_eq : sol G = ⊥
  ne_bot : G ≠ ⊥
  greatest :
    IsGreatest {Z : Subgroup Γ | Z ≤ G ∧ Admits (cenIn G A ⊔ A) Z ∧ Group.IsSolvable Z} S

namespace Hyp

variable [Finite Γ] (H : Hyp p A G S)

include H

theorem A_le_normalizer : A ≤ Subgroup.normalizer (kOf G : Set Γ) :=
  fun _ ha => Nonsolv.mem_normalizer_kOf_of_mem_normalizer (H.near.admits ha)

theorem kOf_ne_bot : kOf G ≠ ⊥ := fun h => H.ne_bot ((Nonsolv.kOf_eq_bot_iff G).mp h)

theorem semisimpleAction : SemisimpleAction p A (kOf G) where
  prime := H.near.prime
  odd := H.near.odd
  elemAbelian := H.near.elemAbelian
  admits := H.A_le_normalizer
  nearPSolvable := signalizerNearPSolvable_of_le (kOf_le G) H.near.nearPSolvable
  solvable_cen := by
    have : Group.IsSolvable ↥(G ⊓ Subgroup.centralizer (A : Set Γ)) := H.near.solvable_cen
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_inf_right _ (kOf_le G) :
        kOf G ⊓ Subgroup.centralizer (A : Set Γ) ≤ G ⊓ Subgroup.centralizer (A : Set Γ)))
  semisimple := isSemisimple_kOf H.sol_eq
  ne_bot := H.kOf_ne_bot

theorem lcal_kOf : lcal (kOf G) = lcal G := by
  have hss : IsSemisimple (kOf G) := isSemisimple_kOf H.sol_eq
  rw [hss.lcal_eq, simpleComponents_kOf H.sol_eq]

theorem cenIn_kOf_le_self : cenIn (kOf G) A ≤ S := by
  refine H.greatest.2 ⟨inf_le_left.trans (kOf_le G), admits_cenIn_kOf G A, ?_⟩
  have : Group.IsSolvable ↥(cenIn G A) := H.near.solvable_cen
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (cenIn_kOf_le G A))

theorem admits_mOf : Admits (cenIn G A ⊔ A) (mOf A (kOf G)) := by
  refine sup_le (fun d hd => ?_) H.semisimpleAction.admits_mOf
  obtain ⟨hdG, -⟩ := mem_cenIn_iff.mp hd
  have h1 : d ∈ Subgroup.normalizer ((cenIn (kOf G) A : Subgroup Γ) : Set Γ) :=
    admits_cenIn_kOf G A (Subgroup.mem_sup_left hd)
  have h2 := mem_normalizer_fittingSubgroupOf h1
  exact mem_normalizer_norIn (Nonsolv.le_normalizer_kOf G hdG)
    (mem_normalizer_cenIn (Nonsolv.le_normalizer_kOf G hdG) h2)

theorem s0_eq_mOf :
    s0 G S = mOf A (kOf G) := by
  have hb := thm210b H.semisimpleAction
  have hSs : Group.IsSolvable ↥S := H.greatest.1.2.2
  refine le_antisymm ?_
    (le_inf (H.greatest.2 ⟨hb.1.1.trans (kOf_le G), H.admits_mOf, hb.1.2.2⟩) hb.1.1)
  refine hb.2 ⟨inf_le_right, le_inf H.cenIn_kOf_le_self inf_le_left, ?_⟩
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (inf_le_left : S ⊓ kOf G ≤ S))

theorem s0_eq_kProd :
    s0 G S = kProd A (kOf G) :=
  H.s0_eq_mOf.trans H.semisimpleAction.mOf_eq_kProd

theorem s1_eq :
    s1 G S = fProd A (kOf G) := by
  unfold s1
  rw [H.s0_eq_kProd]
  exact H.semisimpleAction.fittingSubgroupOf_kProd

theorem d0_eq :
    d0 A G S = cenIn (kOf G) A := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hxD, hxS⟩ := Subgroup.mem_inf.mp hx
    rw [← cenIn_inf_kOf G A]
    exact Subgroup.mem_inf.mpr ⟨hxD, (Subgroup.mem_inf.mp hxS).2⟩
  · refine Subgroup.mem_inf.mpr ⟨cenIn_kOf_le G A hx, ?_⟩
    rw [H.s0_eq_mOf]
    exact (thm210b H.semisimpleAction).1.2.1 hx

theorem d1_eq
    : d1 A G S = CFSG.fittingSubgroupOf (cenIn (kOf G) A) := by
  unfold d1
  rw [H.d0_eq]

end Hyp

end Lemma216

end CFSG.SignalizerFunctorTheorem.McBride.Near
