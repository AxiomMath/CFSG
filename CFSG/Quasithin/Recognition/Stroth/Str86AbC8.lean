module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth

import CFSG.Quasithin.Recognition.Stroth.Str86AbBase
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_false_of_commutator_oTwoUpper_le
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {X : Subgroup G}
    (hVX : conjClosure (Z2 L1 L2 S) L1 ≤ X)
    (hX : ⁅X, oTwoUpper (u3H L1 L2 S)⁆ ≤ Z2 L1 L2 S) : False := by
  have hF := hI.hF
  obtain ⟨hVQ, hP1V, -⟩ := str86_conjClosure_frame hI hZQ
  have hZV : Z2 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 := le_conjClosure _ _
  have key : ∀ y ∈ oTwoUpper (u3H L1 L2 S), ∀ v ∈ conjClosure (Z2 L1 L2 S) L1,
      y * v * y⁻¹ ∈ conjClosure (Z2 L1 L2 S) L1 := by
    intro y hy v hv
    have hc : ⁅v, y⁆ ∈ Z2 L1 L2 S := hX (Subgroup.commutator_mem_commutator (hVX hv) hy)
    have hc' : ⁅v, y⁆⁻¹ ∈ conjClosure (Z2 L1 L2 S) L1 := hZV ((Z2 L1 L2 S).inv_mem hc)
    have e : y * v * y⁻¹ = ⁅v, y⁆⁻¹ * v := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hc' hv
  have hON : oTwoUpper (u3H L1 L2 S) ≤
      Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨key y hy v, fun hv => ?_⟩
    have h' := key y⁻¹ ((oTwoUpper (u3H L1 L2 S)).inv_mem hy) _ hv
    rwa [show y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ = v by group] at h'
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hBV : bigB L1 L2 S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hP1V
  have hHV : u3H L1 L2 S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) := by
    rw [str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hI.hm hI.hL2]
    exact sup_le hON ((hQ2S.trans le_sup_right).trans hBV)
  have hP2V : P2 L1 L2 S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    sup_le ((le_sup_left : L2 ≤ u3H L1 L2 S).trans hHV) hBV
  have hG0 : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1V hP2V
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hVS : conjClosure (Z2 L1 L2 S) L1 ≤ S := hVQ.trans hQ1S
  have hVO : conjClosure (Z2 L1 L2 S) L1 ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 (hVS.trans le_sup_right) hG0 (hF.1.h1.pgroup.to_le hVS)
  rw [hF.1.o2] at hVO
  exact hI.critHypN.ne_bot (le_bot_iff.mp (hZV.trans hVO))

end CFSG.Quasithin.Stroth

end
