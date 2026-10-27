module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_commutator_x_conjugate_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆ ≤
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  classical
  set X := str83X L1 L2 S with hXdef
  set W := CFSG.conjugate X d.w with hWdef
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hQ2conj : CFSG.conjugate (Q2 L1 L2 S) d.w = Q2 L1 L2 S := str83G4_conjugate_q2_eq d
  have hWleS : W ≤ S := by
    rw [hWdef]
    exact str83G4_conjugate_x_le_s hfr d hX
  have hWleP1 : W ≤ P1 L1 L2 S :=
    (hWleS.trans ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
  have hWNX : W ≤ Subgroup.normalizer (X : Set G) :=
    hWleP1.trans (le_normalizer_str83X L1 L2 S)
  have hXQ2 : X ≤ Q2 L1 L2 S := by
    rw [hXdef]
    exact str83G4_x_le_q2 hfr hX
  have hXleP1w : X ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
    calc X ≤ Q2 L1 L2 S := hXQ2
      _ = CFSG.conjugate (Q2 L1 L2 S) d.w := hQ2conj.symm
      _ ≤ CFSG.conjugate S d.w := Subgroup.map_mono hQ2S
      _ ≤ CFSG.conjugate (P1 L1 L2 S) d.w :=
          Subgroup.map_mono ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hconjN : CFSG.conjugate (P1 L1 L2 S) d.w ≤
      Subgroup.normalizer (CFSG.conjugate X d.w : Set G) := by
    calc CFSG.conjugate (P1 L1 L2 S) d.w
        ≤ CFSG.conjugate (Subgroup.normalizer (X : Set G)) d.w :=
          Subgroup.map_mono (le_normalizer_str83X L1 L2 S)
      _ = Subgroup.normalizer (CFSG.conjugate X d.w : Set G) := by
          simpa [CFSG.conjugate] using
            (Subgroup.map_equiv_normalizer_eq X (MulAut.conj d.w⁻¹))
  have hXNW : X ≤ Subgroup.normalizer (W : Set G) := by
    rw [hWdef]
    exact hXleP1w.trans hconjN
  have hcommX : ⁅X, W⁆ ≤ X := by
    refine Subgroup.commutator_le.mpr fun x hx w hw => ?_
    have h1 : w * x⁻¹ * w⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hWNX hw) x⁻¹).mp (X.inv_mem hx)
    have e : ⁅x, w⁆ = x * (w * x⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem hx h1
  have hcommW : ⁅X, W⁆ ≤ W := by
    refine Subgroup.commutator_le.mpr fun x hx w hw => ?_
    have h1 : x * w * x⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hXNW hx) w).mp hw
    have e : ⁅x, w⁆ = (x * w * x⁻¹) * w⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact W.mul_mem h1 (W.inv_mem hw)
  have h := le_inf hcommX hcommW
  simpa [hXdef, hWdef] using h

theorem str83G4_commutator_commutator_x_conjugate_eq_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ⁅⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆,
      CFSG.conjugate (str83X L1 L2 S) d.w⁆ = ⊥ := by
  classical
  set X := str83X L1 L2 S with hXdef
  set W := CFSG.conjugate X d.w with hWdef
  have h1 : ⁅X, W⁆ ≤ W := by
    have h : ⁅X, W⁆ ≤ X ⊓ W := by
      simpa [hXdef, hWdef] using str83G4_commutator_x_conjugate_le hfr d hX
    exact fun y hy => (h hy).2
  have hWabel : IsElemAbelian 2 W := by
    rw [hWdef]
    exact str83G4_isElemAbelian_conjugate_x d hX
  have hWW : ⁅W, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (B6.isElemAbelian_iff.mp hWabel).1 v hv w hw
  have h := (Subgroup.commutator_mono h1 le_rfl).trans (le_of_eq hWW)
  exact le_bot_iff.mp (by simpa [hXdef, hWdef] using h)

end CFSG.Quasithin.Stroth

end
