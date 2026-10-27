module

public import CFSG.Monster.B.TwoA.Amalgam.Flag1Action
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public meta import CFSG.Monster.B.TwoA.Unitary.Planes
public import Certificates.Certificate3063
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3175
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate16016
import all CFSG.Fischer.F4
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary Matrix Module
open CFSG.Monster.B.Classical.UnitarySix (bar mul_bar_of_ne_zero)

theorem planeRow_one_rows : planeRow 1 1 = e6 1 ∧ planeRow 1 2 = e6 2 := by decide +kernel

theorem planeRow_four_rows : planeRow 4 0 = e6 1 ∧ planeRow 4 1 = e6 2 := by decide +kernel

theorem planeRow_fortynine_row : planeRow 49 0 = e6 2 := by decide +kernel

theorem plane_zero_coords :
    (∀ a, planeRow 0 a 3 = 0) ∧ (∀ a, planeRow 0 a 4 = 0) ∧ (∀ a, planeRow 0 a 5 = 0) := by
  decide +kernel

theorem plane_one_coords :
    (∀ a, planeRow 1 a 4 = 0) ∧ (∀ a, planeRow 1 a 5 = 0) ∧
      (∀ a, planeRow 1 a 3 = planeRow 1 a 0) := by
  decide +kernel

theorem plane_four_coords :
    (∀ a, planeRow 4 a 0 = 0) ∧ (∀ a, planeRow 4 a 4 = 0) ∧ (∀ a, planeRow 4 a 5 = 0) := by
  decide +kernel

theorem plane_fortynine_coords :
    (∀ a, planeRow 49 a 0 = 0) ∧ (∀ a, planeRow 49 a 1 = 0) ∧ (∀ a, planeRow 49 a 5 = 0) := by
  decide +kernel

theorem e6_one_mem_Hsp : e6 1 ∈ Hsp := Submodule.subset_span (Set.mem_insert _ _)

theorem e6_two_mem_Hsp : e6 2 ∈ Hsp := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

theorem e6_two_mem_Rsp : e6 2 ∈ Rsp := Submodule.subset_span rfl

theorem Hsp_le_plane {j : Fin 891} (h1 : e6 1 ∈ plane j) (h2 : e6 2 ∈ plane j) :
    Hsp ≤ plane j := by
  rw [Hsp, Submodule.span_le]
  rintro x (rfl | rfl)
  · exact h1
  · exact h2

theorem Hsp_le_plane_zero : Hsp ≤ plane 0 := Tsp_eq_plane ▸ Hsp_le_Tsp

theorem Hsp_le_plane_one : Hsp ≤ plane 1 :=
  Hsp_le_plane (planeRow_one_rows.1 ▸ mem_plane_row 1 1) (planeRow_one_rows.2 ▸ mem_plane_row 1 2)

theorem Hsp_le_plane_four : Hsp ≤ plane 4 :=
  Hsp_le_plane (planeRow_four_rows.1 ▸ mem_plane_row 4 0) (planeRow_four_rows.2 ▸ mem_plane_row 4 1)

theorem Rsp_le_plane_fortynine : Rsp ≤ plane 49 := by
  rw [Rsp, Submodule.span_le, Set.singleton_subset_iff]
  exact planeRow_fortynine_row ▸ mem_plane_row 49 0

theorem mem_Hsp_of {x : V6} (h0 : x 0 = 0) (h3 : x 3 = 0) (h4 : x 4 = 0) (h5 : x 5 = 0) :
    x ∈ Hsp := by
  have hx : x = x 1 • e6 1 + x 2 • e6 2 := by
    funext i
    fin_cases i <;> simp [e6, h0, h3, h4, h5]
  rw [hx]
  exact Hsp.add_mem (Hsp.smul_mem _ e6_one_mem_Hsp) (Hsp.smul_mem _ e6_two_mem_Hsp)

theorem mem_Rsp_of {x : V6} (h0 : x 0 = 0) (h1 : x 1 = 0) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (h5 : x 5 = 0) : x ∈ Rsp := by
  have hx : x = x 2 • e6 2 := by
    funext i
    fin_cases i <;> simp [e6, h0, h1, h3, h4, h5]
  rw [hx]
  exact Rsp.smul_mem _ e6_two_mem_Rsp

theorem plane_zero_inf_four : plane 0 ⊓ plane 4 = Hsp := by
  refine le_antisymm (fun x hx => ?_) (le_inf Hsp_le_plane_zero Hsp_le_plane_four)
  obtain ⟨c3, c4, c5⟩ := plane_zero_coords
  obtain ⟨d0, -, -⟩ := plane_four_coords
  exact mem_Hsp_of (plane_coord_zero d0 hx.2) (plane_coord_zero c3 hx.1) (plane_coord_zero c4 hx.1)
    (plane_coord_zero c5 hx.1)

theorem plane_zero_inf_one : plane 0 ⊓ plane 1 = Hsp := by
  refine le_antisymm (fun x hx => ?_) (le_inf Hsp_le_plane_zero Hsp_le_plane_one)
  obtain ⟨c3, c4, c5⟩ := plane_zero_coords
  obtain ⟨-, -, d30⟩ := plane_one_coords
  have h3 : x 3 = 0 := plane_coord_zero c3 hx.1
  have h0 : x 0 = 0 := (plane_coord_eq d30 hx.2).symm.trans h3
  exact mem_Hsp_of h0 h3 (plane_coord_zero c4 hx.1) (plane_coord_zero c5 hx.1)

theorem plane_one_inf_four : plane 1 ⊓ plane 4 = Hsp := by
  refine le_antisymm (fun x hx => ?_) (le_inf Hsp_le_plane_one Hsp_le_plane_four)
  obtain ⟨c4, c5, c30⟩ := plane_one_coords
  obtain ⟨d0, -, -⟩ := plane_four_coords
  have h0 : x 0 = 0 := plane_coord_zero d0 hx.2
  have h3 : x 3 = 0 := (plane_coord_eq c30 hx.1).trans h0
  exact mem_Hsp_of h0 h3 (plane_coord_zero c4 hx.1) (plane_coord_zero c5 hx.1)

theorem Tsp_inf_plane_fortynine : Tsp ⊓ plane 49 = Rsp := by
  refine le_antisymm (fun x hx => ?_) (le_inf (Rsp_le_Hsp.trans Hsp_le_Tsp) Rsp_le_plane_fortynine)
  rw [Tsp_eq_plane] at hx
  obtain ⟨c3, c4, c5⟩ := plane_zero_coords
  obtain ⟨d0, d1, -⟩ := plane_fortynine_coords
  exact mem_Rsp_of (plane_coord_zero d0 hx.2) (plane_coord_zero d1 hx.2) (plane_coord_zero c3 hx.1)
    (plane_coord_zero c4 hx.1) (plane_coord_zero c5 hx.1)

theorem planes_through_H :
    ∀ j : Fin 891, expand j (Pi.single 1 1) = Pi.single 1 1 →
    expand j (Pi.single 2 1) = Pi.single 2 1 → j = 0 ∨ j = 1 ∨ j = 4 :=
  Certificates.certificate3063.1

@[expose] def ThroughH (P : Submodule F4 V6) : Prop := P = plane 0 ∨ P = plane 1 ∨ P = plane 4

theorem throughH_of_le
    {P : Submodule F4 V6} (hP : IsMaxIso P)
    (hH : Hsp ≤ P) : ThroughH P := by
  obtain ⟨j, rfl⟩ := exists_plane_of_isMaxIso hP
  have h1 := (mem_plane_iff j _).1 (hH e6_one_mem_Hsp)
  have h2 := (mem_plane_iff j _).1 (hH e6_two_mem_Hsp)
  rcases planes_through_H j h1 h2 with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem inf_eq_Hsp_of_throughH {P P' : Submodule F4 V6} (hP : ThroughH P) (hP' : ThroughH P')
    (hne : P ≠ P') : P ⊓ P' = Hsp := by
  rcases hP with rfl | rfl | rfl <;> rcases hP' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact plane_zero_inf_one
  · exact plane_zero_inf_four
  · rw [inf_comm]; exact plane_zero_inf_one
  · exact absurd rfl hne
  · exact plane_one_inf_four
  · rw [inf_comm]; exact plane_zero_inf_four
  · rw [inf_comm]; exact plane_one_inf_four
  · exact absurd rfl hne

theorem sigmaAct_Hsp_iff
    (x : SigmaU6) :
    (ThroughH (sigmaAct (plane 0) x) ∧ ThroughH (sigmaAct (plane 4) x)) ↔
      sigmaAct Hsp x = Hsp := by
  constructor
  · rintro ⟨h0, h4⟩
    have hne : sigmaAct (plane 0) x ≠ sigmaAct (plane 4) x := fun h =>
      absurd (plane_injective (sigmaAct_left_injective x h)) (by decide)
    have e : sigmaAct Hsp x = sigmaAct (plane 0) x ⊓ sigmaAct (plane 4) x := by
      rw [← sigmaAct_inf, plane_zero_inf_four]
    rw [e]
    exact inf_eq_Hsp_of_throughH h0 h4 hne
  · intro hx
    refine ⟨throughH_of_le (isMaxIso_sigmaAct (isMaxIso_plane 0) x) ?_,
      throughH_of_le (isMaxIso_sigmaAct (isMaxIso_plane 4) x) ?_⟩
    · rw [← hx]
      exact sigmaAct_mono Hsp_le_plane_zero x
    · rw [← hx]
      exact sigmaAct_mono Hsp_le_plane_four x

@[expose] def tvecR (v : V6) : V6 := v + hU v (e6 2) • e6 2

theorem hU_e6_two (v : V6) : hU v (e6 2) = v 5 := hU_single_right v 2

theorem b6Mat_six : b6Mat 6 = 1 + vecMulVec (e6 5) (e6 2) := by decide +kernel

theorem vecMul_b6Mat_six (v : V6) : v ᵥ* b6Mat 6 = tvecR v := by
  rw [b6Mat_six, vecMul_add, vecMul_one, vecMul_vecMulVec, tvecR, hU_e6_two, e6,
    dotProduct_single, mul_one]

theorem b6Frob_six : b6Frob 6 = 0 := by
  rw [b6Frob_eq]
  rfl

theorem slElt_six_eq :
    slElt 6 = ⟨(b6SU 6 : SUh ⧸ Zh), Multiplicative.ofAdd 0⟩ := by
  rw [slElt, b6Frob_six]

theorem semMap_b6SU_six (v : V6) :
    semMap (b6SU 6) 0 v = tvecR v := by
  rw [semMap, coe_b6SU, b6N, b6Frob_six, barPowM, ite_eq_left rfl, barPowV, ite_eq_left rfl,
    vecMul_b6Mat_six]

theorem coe_sigmaAct_slElt_six (S : Submodule F4 V6) :
    ((sigmaAct S (slElt 6) : Submodule F4 V6) : Set V6) = tvecR '' S := by
  rw [slElt_six_eq, coe_sigmaAct]
  congr 1
  funext v
  exact semMap_b6SU_six v

theorem tvecR_of_mem {P : Submodule F4 V6} (hP : ∀ s ∈ P, ∀ t ∈ P, hU s t = 0) (hR : Rsp ≤ P)
    {v : V6} (hv : v ∈ P) : tvecR v = v := by
  rw [tvecR, hP v hv _ (hR e6_two_mem_Rsp), zero_smul, add_zero]

theorem sigmaAct_slElt_six_of_le {P : Submodule F4 V6}
    (hP : ∀ s ∈ P, ∀ t ∈ P, hU s t = 0)
    (hR : Rsp ≤ P) : sigmaAct P (slElt 6) = P := by
  apply SetLike.coe_injective
  rw [coe_sigmaAct_slElt_six]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [tvecR_of_mem hP hR hw]
    exact hw
  · intro hv
    exact ⟨v, hv, tvecR_of_mem hP hR hv⟩

theorem planes_e2_or_row : ∀ j : Fin 891,
    expand j (Pi.single 2 1) = Pi.single 2 1 ∨ ∃ a : Fin 3, planeRow j a 5 ≠ 0 :=
  Certificates.certificate3063.2

theorem Rsp_le_of_sigmaAct_slElt_six
    {P : Submodule F4 V6}
    (hP : IsMaxIso P)
    (h : sigmaAct P (slElt 6) = P) : Rsp ≤ P := by
  obtain ⟨j, rfl⟩ := exists_plane_of_isMaxIso hP
  have he2 : e6 2 ∈ plane j := by
    rcases planes_e2_or_row j with h1 | ⟨a, ha⟩
    · exact (mem_plane_iff j _).2 h1
    · have hr : tvecR (planeRow j a) ∈ plane j := by
        have hm : tvecR (planeRow j a) ∈ ((sigmaAct (plane j) (slElt 6) :
            Submodule F4 V6) : Set V6) := by
          rw [coe_sigmaAct_slElt_six]
          exact ⟨_, mem_plane_row j a, rfl⟩
        rw [h] at hm
        exact hm
      have hd : hU (planeRow j a) (e6 2) • e6 2 ∈ plane j := by
        have := (plane j).sub_mem hr (mem_plane_row j a)
        rwa [tvecR, add_sub_cancel_left] at this
      rw [hU_e6_two] at hd
      have := (plane j).smul_mem (planeRow j a 5)⁻¹ hd
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  rw [Rsp, Submodule.span_le, Set.singleton_subset_iff]
  exact he2

theorem semMap_zero (g : SUh) (ε : ZMod 2) : semMap g ε 0 = 0 := by
  have h := semMap_smul g ε 0 0
  rwa [zero_smul, barPowF_zero_right, zero_smul] at h

theorem commute_slElt_six_of_stab {x : SigmaU6}
    (hx : sigmaAct Rsp x = Rsp) :
    x * slElt 6 = slElt 6 * x := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  have he2 : semMap g ε (e6 2) ∈ Rsp := by
    rw [← hx]
    exact mem_sigmaAct_iff.2 ⟨e6 2, e6_two_mem_Rsp, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 he2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← semMap_zero g ε] at hc
    exact e6_ne_zero 2 (semMap_injective g ε hc.symm)
  have hcomm : ∀ v, semMap g ε (tvecR v) = tvecR (semMap g ε v) := by
    intro v
    have h1 : barPowF ε (hU v (e6 2)) = bar c * hU (semMap g ε v) (e6 2) := by
      rw [← hU_semMap g ε v (e6 2), ← hc, hU_smul_right]
    rw [tvecR, semMap_add, semMap_smul, ← hc, h1, smul_smul, tvecR]
    congr 2
    linear_combination (hU (semMap g ε v) (e6 2)) * mul_bar_of_ne_zero hc0
  have hset : ∀ P : Submodule F4 V6, sigmaAct (sigmaAct P (slElt 6))
      ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ =
        sigmaAct (sigmaAct P ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩) (slElt 6) := by
    intro P
    apply SetLike.coe_injective
    rw [coe_sigmaAct, coe_sigmaAct_slElt_six, coe_sigmaAct_slElt_six, coe_sigmaAct,
      Set.image_image, Set.image_image]
    congr 1
    funext v
    exact hcomm v
  set y : SigmaU6 := ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩
  have h1 : (slElt 6 * y) * (y * slElt 6)⁻¹ = 1 := eq_one_of_sigmaAct_plane _ fun j =>
    calc sigmaAct (plane j) ((slElt 6 * y) * (y * slElt 6)⁻¹)
        = sigmaAct (sigmaAct (plane j) (slElt 6 * y)) (y * slElt 6)⁻¹ := sigmaAct_mul _ _ _
      _ = sigmaAct (sigmaAct (plane j) (y * slElt 6)) (y * slElt 6)⁻¹ := by
        rw [sigmaAct_mul (plane j) (slElt 6) y, hset, ← sigmaAct_mul (plane j) y (slElt 6)]
      _ = plane j := sigmaAct_sigmaAct_inv _ _
  exact (mul_inv_eq_one.1 h1).symm

theorem stab_of_commute_slElt_six
    {x : SigmaU6}
    (hx : x * slElt 6 = slElt 6 * x) :
    sigmaAct Rsp x = Rsp := by
  have key : ∀ y : SigmaU6, y * slElt 6 = slElt 6 * y → ∀ P : Submodule F4 V6, IsMaxIso P →
      Rsp ≤ P → Rsp ≤ sigmaAct P y := by
    intro y hy P hP hRP
    apply Rsp_le_of_sigmaAct_slElt_six (isMaxIso_sigmaAct hP y)
    rw [← sigmaAct_mul, hy, sigmaAct_mul, sigmaAct_slElt_six_of_le hP.2 hRP]
  have hinv : x⁻¹ * slElt 6 = slElt 6 * x⁻¹ :=
    (Commute.inv_left (hx : Commute x (slElt 6)) : Commute x⁻¹ (slElt 6)).eq
  have hle : ∀ P : Submodule F4 V6, IsMaxIso P → Rsp ≤ P → sigmaAct Rsp x ≤ P := by
    intro P hP hRP
    have := sigmaAct_mono (key x⁻¹ hinv P hP hRP) x
    rwa [sigmaAct_inv_sigmaAct] at this
  have h1 := hle Tsp isMaxIso_Tsp (Rsp_le_Hsp.trans Hsp_le_Tsp)
  have h2 := hle (plane 49) (isMaxIso_plane 49) Rsp_le_plane_fortynine
  have h3 : sigmaAct Rsp x ≤ Rsp := (le_inf h1 h2).trans Tsp_inf_plane_fortynine.le
  exact Submodule.eq_of_le_of_finrank_eq h3 (finrank_sigmaAct Rsp x)

theorem commute_slElt_six_iff
    (x : SigmaU6) :
    x * slElt 6 = slElt 6 * x ↔ sigmaAct Rsp x = Rsp :=
  ⟨stab_of_commute_slElt_six, commute_slElt_six_of_stab⟩

end CFSG.Monster.B.TwoA.Amalgam
