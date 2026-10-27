module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86_z1_inf_conj_eq_bot {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {h : G}
    (hh : h ∈ P2 L1 L2 S) (hhB : h ∉ bigB L1 L2 S) :
    Z1 L1 L2 S ⊓ MulAut.conj h • Z1 L1 L2 S = ⊥ := by
  classical
  have hF := hI.hF
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hI.hSB h1 hI.hB2 h2 hI.hZI
  have hcent := str86_centralizer_u3H_z2 hF hI.hSB h1 hI.hB2 h2 hI.hZI
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB (Or.inr (Or.inl h1))
  have hSC : S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (hS1.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)).trans hI.hZI
  have hBZ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf _)
  set W' : Subgroup G := ⨅ h' ∈ P2 L1 L2 S, MulAut.conj h' • Z1 L1 L2 S with hW'
  have hmemW' : ∀ x, x ∈ W' ↔ ∀ h' ∈ P2 L1 L2 S, h'⁻¹ * x * h' ∈ Z1 L1 L2 S := by
    intro x
    simp only [hW', Subgroup.mem_iInf, mem_conj_smul_iff']
  have hW'Z1 : W' ≤ Z1 L1 L2 S := fun x hx => by
    simpa using (hmemW' x).mp hx 1 (P2 L1 L2 S).one_mem
  have hWW' : Z1 L1 L2 S ⊓ MulAut.conj h • Z1 L1 L2 S ≤ W' := by
    intro x hx
    obtain ⟨hx1, hxh⟩ := Subgroup.mem_inf.mp hx
    have hxh' : h⁻¹ * x * h ∈ Z1 L1 L2 S := mem_conj_smul_iff'.mp hxh
    refine (hmemW' x).mpr fun h' hh' => ?_
    by_cases hh'B : h' ∈ bigB L1 L2 S
    · have h' := (Subgroup.mem_normalizer_iff.mp (hBZ1 ((bigB L1 L2 S).inv_mem hh'B)) x).mp hx1
      rwa [inv_inv] at h'
    · obtain ⟨s, hs, hb⟩ :=
        str86_exists_mem_mul_inv_mem_bigB hF hI.hSB hI.hm hI.hL2 hh hhB hh' hh'B
      have hxs : x * s = s * x := Subgroup.mem_centralizer_iff.mp (hSC hs) x hx1
      have hsx : s⁻¹ * x * s = x := by
        rw [mul_assoc, hxs, ← mul_assoc, inv_mul_cancel, one_mul]
      have e : h'⁻¹ * x * h' =
          ((s * h)⁻¹ * h')⁻¹ * (h⁻¹ * (s⁻¹ * x * s) * h) * ((s * h)⁻¹ * h') := by group
      rw [e, hsx]
      have h'' := (Subgroup.mem_normalizer_iff.mp (hBZ1 ((bigB L1 L2 S).inv_mem hb)) _).mp hxh'
      rwa [inv_inv] at h''
  have hP2W' : P2 L1 L2 S ≤ Subgroup.normalizer (W' : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine (hmemW' _).mpr fun h' hh' => ?_
      have := (hmemW' x).mp hx (p⁻¹ * h') ((P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hp) hh')
      rwa [show (p⁻¹ * h')⁻¹ * x * (p⁻¹ * h') = h'⁻¹ * (p * x * p⁻¹) * h' by group] at this
    · intro hx
      refine (hmemW' _).mpr fun h' hh' => ?_
      have := (hmemW' _).mp hx (p * h') ((P2 L1 L2 S).mul_mem hp hh')
      rwa [show (p * h')⁻¹ * (p * x * p⁻¹) * (p * h') = h'⁻¹ * x * h' by group] at this
  have hHP2 : u3H L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (W' : Set G) :=
    (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)).trans
      (Subgroup.centralizer_le (hW'Z1.trans hZ1Z2))
  have hSC' : S ≤ Subgroup.centralizer (W' : Set G) := hSC.trans (Subgroup.centralizer_le hW'Z1)
  have hKn : L2 ⊔ Q2 L1 L2 S ≤
      Subgroup.normalizer ((u3H L1 L2 S ⊓ Subgroup.centralizer (W' : Set G) : Subgroup G) :
        Set G) := fun x hx =>
    A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((hHP2.trans (hP2W'.trans (F7.normalizer_le_normalizer_centralizer W'))) hx)
  rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hI.hm hI.hL2
      (inf_le_left : u3H L1 L2 S ⊓ Subgroup.centralizer (W' : Set G) ≤ L2 ⊔ Q2 L1 L2 S) hKn
      (le_inf le_sup_right hQ2C) with hC | hC
  · exfalso
    have hSQ : S ≤ Q2 L1 L2 S :=
      hC ▸ le_inf (str86_s_le_u3H hF.toW hI.hSB hI.hm hI.hL2) hSC'
    have h' := str86_relIndex_q2_s hF.toW hI.hSB hI.hm hI.hL2
    rw [Subgroup.relIndex_eq_one.mpr hSQ] at h'
    have : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hI.hm
    omega
  · have hHC : u3H L1 L2 S ≤ Subgroup.centralizer (W' : Set G) :=
      (le_of_eq hC.symm).trans inf_le_right
    have hW'C : W' ≤ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp hHC
    have hW'bot : W' = ⊥ := by
      rw [← le_bot_iff, ← hcent]
      exact le_inf (hW'Z1.trans hZ1Z2) hW'C
    rw [← le_bot_iff, ← hW'bot]
    exact hWW'

end CFSG.Quasithin.Stroth

end
