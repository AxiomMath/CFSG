module

public import CFSG.RankThree.GF2n.Tim79aSec23One
public import CFSG.RankThree.GF2n.Tim79aSec22Cw

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def cX (V H : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∀ y ∈ xOf V H, ⁅x, y⁆ ∈ wOf V H}
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  mul_mem' := by
    rintro x x' ⟨hx, hx1⟩ ⟨hx', hx1'⟩
    refine ⟨H.mul_mem hx hx', fun y hy => ?_⟩
    have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine (wOf V H).mul_mem ?_ (hx1 y hy)
    exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hx) _).mp (hx1' y hy)
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    refine ⟨H.inv_mem hx, fun y hy => ?_⟩
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * (⁅x, y⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem hx)) _).mp
      ((wOf V H).inv_mem (hx1 y hy))
    simpa [mul_assoc] using this

@[expose] def cPbar (V H P : Subgroup G) : Subgroup G := P ⊓ cX V H

variable {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem cPbar_centralizes_wOf {c : G} (hcP : c ∈ cPbar V H P) :
    ∀ w ∈ wOf V H, c * w = w * c := by
  have hle : wOf V H ≤ Subgroup.centralizer ({c} : Set G) := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    obtain ⟨x, hx, hconj⟩ := hc.exists_conj_xOf hh
    intro u hu
    have hu1 : u ∈ conjSubgroup x V := hconj ▸ hu.1
    have hu2 : u ∈ wOf V H := inf_pCore_le_wOf (conjSubgroup_mem_omegaOf hh) hu
    have hv : x⁻¹ * u * x ∈ V := mem_conjSubgroup.mp hu1
    have hcP' : c ∈ P := (Subgroup.mem_inf.mp hcP).1
    have hcv : (x⁻¹ * u * x) * c = c * (x⁻¹ * u * x) := hc.commute_of_mem_P hcP' hv
    have hcx : ⁅c, x⁆ ∈ wOf V H := ((Subgroup.mem_inf.mp hcP).2).2 x hx
    have hWab : ⁅c, x⁆ * u = u * ⁅c, x⁆ := hc.wOf_isElemAbelian.comm hcx hu2
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have e1 : z * x * z⁻¹ = ⁅z, x⁆ * x := by simp only [commutatorElement_def]; group
    have e2 : z * (x⁻¹ * u * x) * z⁻¹ = x⁻¹ * u * x := by rw [← hcv]; group
    have e3 : z * x⁻¹ * z⁻¹ = (⁅z, x⁆ * x)⁻¹ := by
      rw [← e1]; group
    have key : z * u * z⁻¹ = u := by
      calc z * u * z⁻¹ = (z * x * z⁻¹) * (z * (x⁻¹ * u * x) * z⁻¹) * (z * x⁻¹ * z⁻¹) := by group
        _ = (⁅z, x⁆ * x) * (x⁻¹ * u * x) * (⁅z, x⁆ * x)⁻¹ := by rw [e1, e2, e3]
        _ = ⁅z, x⁆ * u * ⁅z, x⁆⁻¹ := by group
        _ = u := by rw [hWab]; group
    calc z * u = z * u * z⁻¹ * z := by group
      _ = u * z := by rw [key]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hle hw) c rfl)

theorem commutator_cPbar_eq_bot : ⁅cPbar V H P, cPbar V H P⁆ = ⊥ := by
  set C := cPbar V H P with hC
  have hCP : C ≤ P := inf_le_left
  have hCW : ⁅C, xOf V H⁆ ≤ wOf V H := by
    rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hcC, y, hy, rfl⟩
    exact ((Subgroup.mem_inf.mp hcC).2).2 y hy
  have h1 : ⁅⁅C, xOf V H⁆, C⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha c hcC
    have hw := hCW ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hc.cPbar_centralizes_wOf hcC a hw).symm
  have h2 : ⁅⁅xOf V H, C⁆, C⁆ = ⊥ := by rw [Subgroup.commutator_comm (xOf V H) C]; exact h1
  have h3 : ⁅⁅C, C⁆, xOf V H⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hP2 : IsPGroup 2 ↥P := hc.isPGroup_P
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  have hcomm_le : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ V := by
    intro a ha b hb
    have h := CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
    have hmem : (⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ : ↥P) ∈ frattini ↥P :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact hc.frattini_P_le ⟨_, hmem, by simp [commutatorElement_def]⟩
  rw [eq_bot_iff]
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hV : ⁅a, b⁆ ∈ V := hcomm_le a (hCP ha) b (hCP hb)
  have hZ : ⁅a, b⁆ ∈ Subgroup.centralizer (xOf V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : ⁅⁅a, b⁆, y⁆ ∈ (⊥ : Subgroup G) := by
      rw [← h3]
      exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator ha hb) hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have : ⁅a, b⁆ ∈ V ⊓ Subgroup.centralizer (xOf V H : Set G) := ⟨hV, hZ⟩
  rw [hc.inf_centralizer_xOf_eq_bot] at this
  exact this

theorem xOf_sup_cPbar_eq_H (hsplit : P ≤ (P ⊓ xOf V H) ⊔ cPbar V H P) :
    xOf V H ⊔ cPbar V H P = H := by
  refine le_antisymm (sup_le (xOf_le_H hc.V_le_H) (inf_le_left.trans hc.PleH)) ?_
  calc H = xOf V H ⊔ P := hc.xOf_sup_P_eq_H.symm
    _ ≤ xOf V H ⊔ cPbar V H P :=
      sup_le le_sup_left (hsplit.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right))

end MinCex

end CFSG.RankThree.GF2n.Tim79a
