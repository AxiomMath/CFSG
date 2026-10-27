module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzSub
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Tools

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem caseI_Zv_le_Qv_zero {E : Subgroup G} (hZ₀E : t.Zv 1 ≤ E) (hEQ₁ : E ≤ t.Qv 0) :
    t.Zv 1 ≤ t.Qv 0 ∧ t.Zv (-1) ≤ t.Qv 0 := by
  have h1 : t.Zv 1 ≤ t.Qv 0 := hZ₀E.trans hEQ₁
  refine ⟨h1, ?_⟩
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) h1
  rw [t.map_Zv_x₁ 1, t.map_Qv_x₁ 0] at h
  simpa using h

theorem caseI_not_Zv_le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Q E : Subgroup G}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hQE : Q ≤ E) (hZ₀E : t.Zv 1 ≤ E)
    (hZ₀Q : t.Zv 1 ⊓ Q = ⊥) (hEQ₂ : E ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ Q)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1) : ¬ t.Zv (-1) ≤ t.Qv 1 := by
  intro hZ
  have hZ1 : t.Zv 1 ≤ t.Qv (-1) := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hZ
    rw [t.map_Zv_x₁ (-1), t.map_Qv_x₁ 1] at h
    simpa using h
  have hZQ' : t.Zv 1 ≤ t.Zv 0 ⊔ Q := (le_inf hZ₀E hZ1).trans hEQ₂
  have hXN : t.Zv 0 ≤ normalizer (Q : Set G) := by
    have hcent : t.Zv 0 ≤ centralizer (Q : Set G) := by
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (hEab z (hZ₀E (hZ₁Z₀ hz)) q (hQE hq)).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer (Q : Set G))
  have hZ1Z0 : t.Zv 1 ≤ t.Zv 0 := by
    intro z hz
    have h : z ∈ (t.Zv 0 ⊔ Q) ⊓ t.Zv 1 := Subgroup.mem_inf.mpr ⟨hZQ' hz, hz⟩
    rwa [sup_inf_eq_sup_inf_of_le_normalizer hZ₁Z₀ hXN, inf_comm, hZ₀Q, sup_bot_eq] at h
  have heq : t.Zv 1 = t.Zv 0 := le_antisymm hZ1Z0 hZ₁Z₀
  exact Z1_ne_Z2 hfr (by rw [← t.Zv_zero, ← t.Zv_one]; exact heq.symm)

theorem caseI_commutator_Zv
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) :
    (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      ∀ x ∈ t.Qv 2, ∀ z ∈ t.Zv 3, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 2 := by
  have hc : ⁅t.Qv 0, t.Zv 1⁆ ≤ t.Zv 0 := Subgroup.commutator_le.mpr hQ₁Z₀
  have hc₁ : ⁅t.Qv 0, t.Zv (-1)⁆ ≤ t.Zv 0 := by
    have hmap : (⁅t.Qv 0, t.Zv 1⁆).map (MulAut.conj t.x₁).toMonoidHom =
        ⁅t.Qv 0, t.Zv (-1)⁆ := by
      rw [Subgroup.map_commutator, t.map_Qv_x₁ 0, t.map_Zv_x₁ 1,
        show (-0 : ℤ) = 0 by norm_num]
    rw [← hmap]
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hc
    rwa [t.map_Zv_x₁ 0] at h
  constructor
  · exact Subgroup.commutator_le.mp hc₁
  · have hc₂ : ⁅t.Qv 2, t.Zv 3⁆ ≤ t.Zv 2 := by
      have hmap : (⁅t.Qv 0, t.Zv (-1)⁆).map (MulAut.conj t.x₂).toMonoidHom =
          ⁅t.Qv 2, t.Zv 3⁆ := by
        rw [Subgroup.map_commutator, t.map_Qv_x₂ 0, t.map_Zv_x₂ (-1),
          show (2 : ℤ) - 0 = 2 by norm_num, show (2 : ℤ) - -1 = 3 by norm_num]
      rw [← hmap]
      have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hc₁
      rwa [t.map_Zv_x₂ 0] at h
    exact Subgroup.commutator_le.mp hc₂

theorem caseI_S_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) (hZ : ¬ t.Zv (-1) ≤ t.Qv 1) :
    S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1 := by
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hQ2le : pCoreOf 2 L2 ≤ t.Qv 1 := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm] at h
    rw [t.Qv_one]
    exact h
  have hTQ' : S ⊓ L2 ≤ normalizer (t.Qv 1 : Set G) := by
    have h : P2 L1 L2 S ≤ normalizer (t.Qv 1 : Set G) := by
      rw [← t.Gv_one]
      exact t.Gv_le_normalizer_Qv 1
    exact inf_le_right.trans (le_sup_left.trans h)
  have hYS : t.Zv (-1) ≤ S := by
    refine hZQ.trans ?_
    rw [t.Qv_zero]
    exact Q1_le_S hfr.hF
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) :=
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := S_eq_sup_right hfr
      _ = (S ⊓ L2) ⊔ t.Qv 1 := by rw [t.Qv_one]
      _ = t.Qv 1 ⊔ (S ⊓ L2) := sup_comm (S ⊓ L2) (t.Qv 1)
  have hXN : t.D2 ≤ normalizer (((t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) : Subgroup G) : Set G) := by
    intro d hd
    refine A4.mem_normalizer_inf ?_ (t.hD2hall.1 hd).2
    exact Subgroup.inf_normalizer_le_normalizer_sup (t.Zv (-1)) (t.Qv 1)
      (Subgroup.mem_inf.mpr
        ⟨t.Gv_le_normalizer_Zv (-1) ((le_sup_right : t.D2 ≤ t.K).trans (t.K_le_Gv (-1)) hd),
          t.Gv_le_normalizer_Qv 1 ((le_sup_right : t.D2 ≤ t.K).trans (t.K_le_Gv 1) hd)⟩)
  have hXnot : ¬ ((t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) ≤ pCoreOf 2 L2) := by
    intro hX
    apply hZ
    intro y hy
    have hyS : y ∈ t.Qv 1 ⊔ (S ⊓ L2) := hSQ.le (hYS hy)
    obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ').mp hyS
    have hτy : τ = q⁻¹ * y := by rw [hyqτ]; group
    have hτX : τ ∈ (t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) := by
      refine Subgroup.mem_inf.mpr ⟨?_, hτ⟩
      rw [hτy]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
    rw [hyqτ]
    exact mul_mem hq (hQ2le (hX hτX))
  have hKI : S ⊓ L2 ≤ ((t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2)) ⊔ pCoreOf 2 L2 :=
    le_sup_pCoreOf_of_torus_of_l2 hfr.hf hfr.hL2 hTsyl t.hD2hall inf_le_right hXN hXnot
  have hSinf : S ⊓ L2 ≤ t.Zv (-1) ⊔ t.Qv 1 :=
    hKI.trans (sup_le inf_le_left (hQ2le.trans le_sup_right))
  have hSmain : S ≤ t.Zv (-1) ⊔ t.Qv 1 :=
    hSQ.le.trans (sup_le le_sup_right hSinf)
  refine ⟨hSmain, ?_⟩
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hSmain
  rw [Subgroup.map_sup, t.map_Zv_x₂ (-1), t.map_Qv_x₂ 1] at h
  simpa only [show (2 : ℤ) - -1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num] using h

private theorem mem_normalizer_W_of_forall {Z C : Subgroup G} {z : G} (hCW : C ≤ t.W)
    (h : ∀ u ∈ Z, ∀ w ∈ t.W, w * u * w⁻¹ * u⁻¹ ∈ C) (hz : z ∈ Z) (hz' : z⁻¹ ∈ Z) :
    z ∈ normalizer (t.W : Set G) := by
  have key : ∀ u ∈ Z, ∀ w ∈ t.W, u * w * u⁻¹ ∈ t.W := by
    intro u hu w hw
    have hmem : (w * u * w⁻¹ * u⁻¹)⁻¹ * w ∈ t.W :=
      t.W.mul_mem (t.W.inv_mem (hCW (h u hu w hw))) hw
    have e : u * w * u⁻¹ = (w * u * w⁻¹ * u⁻¹)⁻¹ * w := by group
    rwa [e]
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key z hz w, fun hw => ?_⟩
  have h := key z⁻¹ hz' (z * w * z⁻¹) hw
  have e : z⁻¹ * (z * w * z⁻¹) * (z⁻¹)⁻¹ = w := by group
  rwa [e] at h

theorem caseI_W {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1) (hZQ₀ : t.Zv 1 ≤ t.Qv 0)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1) :
    t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G) := by
  have hZ1Q2 : t.Zv 1 ≤ t.Qv 2 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hZQ₀
    rw [t.map_Zv_x₂ 1, t.map_Qv_x₂ 0] at h
    simpa using h
  have hZ1W : t.Zv 1 ≤ t.W := le_inf hZQ₀ hZ1Q2
  have hZ2Z1 : t.Zv 2 ≤ t.Zv 1 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hZ₁Z₀
    rw [t.map_Zv_x₂ 0, t.map_Zv_x₂ 1] at h
    simpa using h
  have hZ0W : t.Zv 0 ≤ t.W := hZ₁Z₀.trans hZ1W
  have hZ2W : t.Zv 2 ≤ t.W := hZ2Z1.trans hZ1W
  have hcomm := t.caseI_commutator_Zv hQ₁Z₀
  have hZN1 : t.Zv (-1) ≤ normalizer (t.W : Set G) := by
    intro z hz
    exact t.mem_normalizer_W_of_forall (Z := t.Zv (-1)) (C := t.Zv 0) hZ0W
      (fun u hu w hw => hcomm.1 w hw.1 u hu) hz ((t.Zv (-1)).inv_mem hz)
  have hZN3 : t.Zv 3 ≤ normalizer (t.W : Set G) := by
    intro z hz
    exact t.mem_normalizer_W_of_forall (Z := t.Zv 3) (C := t.Zv 2) hZ2W
      (fun u hu w hw => hcomm.2 w hw.2 u hu) hz ((t.Zv 3).inv_mem hz)
  have hQ1N : t.Qv 1 ≤ normalizer (t.W : Set G) := by
    have h := t.Qv_one_le_normalizer_Qv hfr
    exact (le_inf h.1 h.2).trans Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨hZ1W, t.W_le_Qv_one hfr, ?_⟩
  show S ⊔ t.Sm ≤ normalizer (t.W : Set G)
  exact sup_le (hS.1.trans (sup_le hZN1 hQ1N)) (hS.2.trans (sup_le hZN3 hQ1N))

theorem caseI_trichotomy {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hSQ : S ≤ t.Qv 1 ⊔ t.Qv 0) :
    t.Am ≤ t.Qv 0 ∨
      ((∀ x ∈ t.Am, x * x ∈ t.Qv 0) ∧ ∀ s ∈ S, s * s ∈ t.Qv 0 → s ∈ t.Am ⊔ t.Qv 0) ∨
      S ≤ t.Am ⊔ t.Qv 0 := by
  have hAmS : t.Am ≤ S := by
    refine (inf_le_left : t.Am ≤ t.Qv 1).trans ?_
    rw [t.Qv_one]
    exact Q2_le_S hfr.hF
  have hQ0S : t.Qv 0 ≤ S := by
    rw [t.Qv_zero]
    exact Q1_le_S hfr.hF
  have hQ1Am : t.Qv 1 ≤ normalizer (t.Am : Set G) := by
    intro g hg
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
      ((t.Qv_one_le_normalizer_Qv hfr).2 hg)
  have hQ1X : t.Qv 1 ≤ normalizer ((t.Am ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hQ1Am (t.Qv_one_le_normalizer_Qv hfr).1
  have hQ0X : t.Qv 0 ≤ normalizer ((t.Am ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    (le_sup_right : t.Qv 0 ≤ t.Am ⊔ t.Qv 0).trans Subgroup.le_normalizer
  have hKAm : t.K ≤ normalizer (t.Am : Set G) := by
    intro g hg
    exact A4.mem_normalizer_inf (t.K_le_normalizer_Qv 1 hg) (t.K_le_normalizer_Qv 2 hg)
  have hKX : t.K ≤ normalizer ((t.Am ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hKAm (t.K_le_normalizer_Qv 0)
  have htri := t.trichotomy_Qv_zero hfr (X := t.Am ⊔ t.Qv 0) (sup_le hAmS hQ0S)
    (hSQ.trans (sup_le hQ1X hQ0X)) hKX
  rcases htri with h | ⟨h1, h2⟩ | h
  · exact Or.inl ((le_sup_left : t.Am ≤ t.Am ⊔ t.Qv 0).trans h)
  · refine Or.inr (Or.inl ⟨fun x hx => h1 x (Subgroup.mem_sup_left hx), fun s hs => ?_⟩)
    simpa only [sup_assoc, sup_idem] using h2 s hs
  · exact Or.inr (Or.inr (by simpa only [sup_assoc, sup_idem] using h))

end Track

end CFSG.Quasithin.Stroth.Rq

end
