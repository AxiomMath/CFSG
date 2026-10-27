module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2D
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Step3
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Step4
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Step5
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2E1
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2F5
import CFSG.Quasithin.Recognition.Stroth.Str86NaturalFixedPointFree
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeDefs

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem str86_b2_commute_conj
    {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) :
    ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ MulAut.conj g • Z2 L1 L2 S, x * y = y * x := by
  classical
  by_contra hnc
  obtain ⟨hWQ1, hWS, hWc, hst, hnc', A, hAS, hAe, hkA, hzA⟩ :=
    str86_b2_e1 hF hSB hk hFc hU3 hB2 hn hL2 hZI hZ hg hnc
  have hpH : pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hn hL2
  have hZ2H : Z2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans le_sup_right
  have hfree : ∀ ω ∈ L2, orderOf ω = 3 → ∀ z ∈ Z2 L1 L2 S, ⁅z, ω⁆ = 1 → z = 1 := by
    intro ω hωL hω3 z hz hzω
    refine eq_one_of_commutatorElement_eq_one_of_natural (H := L2 ⊔ Q2 L1 L2 S)
      (V := Z2 L1 L2 S) (A := A) hn (str86_isL2Quot_u3H hF.toW hL2)
      (SmithC27.isElemAbelian_omegaOneCenterOf _) hZ2H hst hnc' hAe (hAS.trans hSH) ?_ ?_
      ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S) hωL) (by rw [hω3]; decide) ?_ hz hzω
    · rw [centralizerMod_bot_eq]
      exact hzA
    · rw [hpH]
      exact hkA
    · rw [hpH]
      intro hωQ
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 (P2 L1 L2 S)) ⟨ω, hωQ⟩
      have hj' : ω ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hdvd : 3 ∣ 2 ^ j := by
        rw [← hω3]
        exact orderOf_dvd_of_pow_eq_one hj'
      have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
      exact absurd h2 (by norm_num)
  have hcore : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      Q1 L1 L2 S ⊓ (MulAut.conj h • Q1 L1 L2 S) = str86Core L1 L2 S :=
    fun h hh hhB => str86_b2_core hF hSB hn hL2 hZ hWQ1 hWS hWc hh hhB
  obtain ⟨htri, -⟩ := str86_b2_relIndex_D hF hSB hk hFc hU3 hn hL2 hcore
  rcases htri with hd | hd | hd
  · exact str86_b2_false_of_inf_le_core hF hSB hk hFc hU3 hn hL2 hZ hWQ1 hWS hWc hfree
      (Subgroup.relIndex_eq_one.mp hd)
  · exact str86_b2_false_of_relIndex_D_eq_q hF hSB hk hFc hU3 hn hL2 hZ hWQ1 hWS hWc hcore hd
  · exact str86_b2_false_of_relIndex_D_eq_cube hF hSB hk hFc hU3 hn hL2 hcore hd

theorem str86ZNotLeNonab_holds :
    Str86ZNotLeNonab := by
  intro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI hZ
  classical
  obtain ⟨k, hk, F, hFld, hFin, hFc, hU3⟩ := h1
  letI : Field F := hFld
  letI : Finite F := hFin
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hL1P1 : L1 ≤ P1 L1 L2 S := le_sup_left
  have hgen : ∀ a ∈ {x | ∃ h ∈ L1, ∃ z ∈ Z2 L1 L2 S, h * z * h⁻¹ = x},
      ∀ b ∈ {x | ∃ h ∈ L1, ∃ z ∈ Z2 L1 L2 S, h * z * h⁻¹ = x}, a * b = b * a := by
    rintro _ ⟨h, hh, z, hz, rfl⟩ _ ⟨h', hh', z', hz', rfl⟩
    have hg : h⁻¹ * h' ∈ P1 L1 L2 S :=
      (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem (hL1P1 hh)) (hL1P1 hh')
    have hy : (h⁻¹ * h') * z' * (h⁻¹ * h')⁻¹ ∈ MulAut.conj (h⁻¹ * h') • Z2 L1 L2 S := by
      rw [mem_conj_smul_iff']
      have e : (h⁻¹ * h')⁻¹ * ((h⁻¹ * h') * z' * (h⁻¹ * h')⁻¹) * (h⁻¹ * h') = z' := by group
      rw [e]
      exact hz'
    have hc := str86_b2_commute_conj hF hSB hk hFc hU3 hB2 hn hL2 hZI hZ hg z hz _ hy
    calc h * z * h⁻¹ * (h' * z' * h'⁻¹) =
        h * (z * ((h⁻¹ * h') * z' * (h⁻¹ * h')⁻¹)) * h⁻¹ := by group
      _ = h * (((h⁻¹ * h') * z' * (h⁻¹ * h')⁻¹) * z) * h⁻¹ := by rw [hc]
      _ = h' * z' * h'⁻¹ * (h * z * h⁻¹) := by group
  intro x hx y hy
  have hle1 : conjClosure (Z2 L1 L2 S) L1 ≤
      Subgroup.centralizer {x | ∃ h ∈ L1, ∃ z ∈ Z2 L1 L2 S, h * z * h⁻¹ = x} := by
    rw [conjClosure, Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hgen b hb a ha
  have hxC := hle1 hx
  have hle2 : conjClosure (Z2 L1 L2 S) L1 ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [conjClosure, Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    rw [hc]
    exact ((Subgroup.mem_centralizer_iff.mp hxC) b hb).symm
  have h' := hle2 hy
  rw [Subgroup.mem_centralizer_iff] at h'
  exact h' x (Set.mem_singleton x)

end CFSG.Quasithin.Stroth

end
