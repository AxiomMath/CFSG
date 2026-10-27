module

public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.FFC7D
public import CFSG.Quasithin.EmptyFaithful.LRed4IrrB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace E9

variable {V : Type} [CommGroup V]

theorem sup_inf_fixV_eq_bot {X : Subgroup (MulAut V)} {A₀ A₁ : Subgroup V} (h01 : A₀ ⊓ A₁ = ⊥)
    (hi₀ : ∀ x ∈ X, ∀ a ∈ A₀, x a ∈ A₀) (hi₁ : ∀ x ∈ X, ∀ a ∈ A₁, x a ∈ A₁)
    (hf₀ : fixV X ⊓ A₀ = ⊥) (hf₁ : fixV X ⊓ A₁ = ⊥) : (A₀ ⊔ A₁) ⊓ fixV X = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw, hwf⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  have hab : ∀ x ∈ X, x a = a ∧ x b = b := by
    intro x hx
    have h1 : x (a * b) = a * b := mem_fixV.mp hwf x hx
    rw [map_mul] at h1
    have h2 : x a * a⁻¹ = b * (x b)⁻¹ := by
      rw [eq_mul_inv_of_mul_eq h1, mul_comm _ a⁻¹, mul_assoc, inv_mul_cancel_left]
    have h3 : x a * a⁻¹ ∈ A₀ ⊓ A₁ :=
      ⟨A₀.mul_mem (hi₀ x hx a ha) (A₀.inv_mem ha), h2 ▸ A₁.mul_mem hb (A₁.inv_mem (hi₁ x hx b hb))⟩
    rw [h01, Subgroup.mem_bot, mul_inv_eq_one] at h3
    refine ⟨h3, ?_⟩
    rw [h3, mul_inv_cancel, eq_comm, mul_inv_eq_one] at h2
    exact h2.symm
  have ha1 : a ∈ fixV X ⊓ A₀ := ⟨mem_fixV.mpr fun x hx => (hab x hx).1, ha⟩
  have hb1 : b ∈ fixV X ⊓ A₁ := ⟨mem_fixV.mpr fun x hx => (hab x hx).2, hb⟩
  rw [hf₀, Subgroup.mem_bot] at ha1
  rw [hf₁, Subgroup.mem_bot] at hb1
  rw [ha1, hb1, mul_one]
  exact Subgroup.one_mem _

end E9

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_sub326iii_of_case3 (h3 : Case10_1_1Three T L I) : ¬ Sub326iii T L I := by
  rintro ⟨-, hcVM, -, hsum, -⟩
  obtain ⟨-, hcV1, hnat⟩ := h3
  obtain ⟨K, _, _, hK, π₁, hπ₁⟩ := hnat
  have hV1 : Nat.card ↥(fsuUL T L I) = 8 * Nat.card ↥(cV1 T L I) := by
    have h := G64.RealizesVia.card_eq hπ₁
    rw [G64.card_natMod, hK, Subgroup.card_top] at h
    simpa using h
  obtain ⟨Ic, π, -, hind, hsup, hreal⟩ := hsum
  have hcard : ∀ j, Nat.card ↥(Ic j) = 8 := fun j => by
    have h := G64.RealizesVia.card_eq (hreal j)
    rw [G64.card_natMod, Nat.card_zmod, Subgroup.card_bot] at h
    simpa using h
  have h01 : Ic 0 ⊓ Ic 1 = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_left _ ?_) (hind 0).le)
    exact le_sup_of_le_right (le_iSup₂_of_le (f := fun (j : Fin 4) (_ : j ≠ 0) => Ic j)
      (1 : Fin 4) (by decide) le_rfl)
  have hnat' : ∀ j, BinaryNaturalSL (autOn L (fsuVM T L I)) (Ic j) ⊥ 3 1 := fun j =>
    ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, π, hreal j⟩
  have hfix := E9.sup_inf_fixV_eq_bot h01 (fun x hx a ha => (hreal 0).2.2.2.1 ⟨x, hx⟩ a ha)
    (fun x hx a ha => (hreal 1).2.2.2.1 ⟨x, hx⟩ a ha)
    (FFC.B510.fixV_inf_eq_bot_of_natural (by norm_num) (hnat' 0))
    (FFC.B510.fixV_inf_eq_bot_of_natural (by norm_num) (hnat' 1))
  set B := (Ic 0 ⊔ Ic 1).map (fsuVM T L I).subtype with hB
  set C₁ := (cV1 T L I).map (fsuUL T L I).subtype with hC₁
  have hBV : B ≤ fsuUL T L I := by
    have hle : Ic 0 ⊔ Ic 1 ≤ (fsuUL T L I).subgroupOf (fsuVM T L I) := by
      rw [← hsup]
      exact le_sup_of_le_right (sup_le (le_iSup Ic 0) (le_iSup Ic 1))
    refine (Subgroup.map_mono hle).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hC₁ : C₁ = Subgroup.centralizer (fsuL0 T L : Set G) ⊓ fsuUL T L I :=
    Subgroup.subgroupOf_map_subtype _ _
  have hBC : B ⊓ C₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy, rfl⟩, hxC⟩
    rw [hC₁] at hxC
    have hyf : y ∈ fixV (autOn L (fsuVM T L I)) := by
      refine mem_fixV.mpr fun φ hφ => ?_
      obtain ⟨l, hl, hlL, rfl⟩ := mem_autOn_iff_exists.mp hφ
      apply Subtype.ext
      rw [InternalSec.coe_conjAct_apply]
      have h1 := Subgroup.mem_centralizer_iff.mp hxC.1 l (SecA.le_fsuL0 T L hlL)
      simp only [Subgroup.coe_subtype] at h1
      rw [h1, mul_inv_cancel_right]
    have hy1 : y ∈ (Ic 0 ⊔ Ic 1) ⊓ fixV (autOn L (fsuVM T L I)) := ⟨hy, hyf⟩
    rw [hfix, Subgroup.mem_bot] at hy1
    rw [hy1, map_one]
    exact Subgroup.one_mem _
  have hcomm : ∀ a ∈ B, ∀ b ∈ C₁, a * b = b * a := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (hcVM.is_comm.comm ⟨(a : G), a.2⟩
      ⟨((b : ↥(fsuUL T L I)) : G),
        SecA.fsuUL_le_fsuVM T L I (b : ↥(fsuUL T L I)).2⟩)
  have hcardB : Nat.card ↥B = 64 := by
    rw [hB, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      LRed4.card_sup_of_commute (fun x _ y _ => mul_comm x y) h01, hcard, hcard]
  have hcardC : Nat.card ↥C₁ = Nat.card ↥(cV1 T L I) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hle := Subgroup.card_le_of_le (sup_le hBV (hC₁ ▸ inf_le_right : C₁ ≤ fsuUL T L I))
  rw [LRed4.card_sup_of_commute hcomm hBC, hcardB, hcardC, hV1] at hle
  have hpos : 0 < Nat.card ↥(cV1 T L I) := Nat.card_pos
  omega

theorem fsuV_eq_of_case3 (hyp : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    fsuV T I = fsuVM T L I := by
  obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
  rcases hc with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨he, hsum, h5⟩
  · exact h
  · exact h
  · exact absurd ⟨hyp.lt, hab, he, hsum, h5⟩ (not_sub326iii_of_case3 h3)

theorem inf_centralizer_eq_pCoreOf_of_case3 (h3228 : TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) :
    T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) = pCoreOf 2 (fsuL0 T L ⊔ T) := by
  obtain ⟨-, -, h⟩ := h3228 G T L I hyp.fsu
  rw [h, fsuV_eq_of_case3 hyp h3]

end CFSG.Quasithin.Vol2.Ch10.SecB
