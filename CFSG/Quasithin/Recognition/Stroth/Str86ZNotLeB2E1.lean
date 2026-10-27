module


import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2F5
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_smul_inf_centralizer (h : G) (X Y : Subgroup G) :
    MulAut.conj h • (X ⊓ Subgroup.centralizer (Y : Set G)) =
      (MulAut.conj h • X) ⊓ Subgroup.centralizer ((MulAut.conj h • Y : Subgroup G) : Set G) := by
  ext x
  simp only [mem_conj_smul_iff', Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun hc y hy => ?_, fun hc y hy => ?_⟩
  · have h' := hc _ hy
    calc y * x = h * ((h⁻¹ * y * h) * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x * h) * (h⁻¹ * y * h)) * h⁻¹ := by rw [h']
      _ = x * y := by group
  · have h' := hc (h * y * h⁻¹) (by simpa [mul_assoc] using hy)
    calc y * (h⁻¹ * x * h) = h⁻¹ * ((h * y * h⁻¹) * x) * h := by group
      _ = h⁻¹ * (x * (h * y * h⁻¹)) * h := by rw [h']
      _ = h⁻¹ * x * h * y := by group

theorem isElemAbelian_conj_smul {X : Subgroup G} (hX : IsElemAbelian 2 X) (h : G) :
    IsElemAbelian 2 (MulAut.conj h • X) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hx := mem_conj_smul_iff'.mp x.2
    have hy := mem_conj_smul_iff'.mp y.2
    have hxy := congrArg Subtype.val
      (hX.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩ : (⟨_, hx⟩ : ↥X) * ⟨_, hy⟩ = ⟨_, hy⟩ * ⟨_, hx⟩)
    simp only [Subgroup.coe_mul] at hxy
    simp only [Subgroup.coe_mul]
    calc (x : G) * y = h * ((h⁻¹ * x * h) * (h⁻¹ * y * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * y * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [hxy]
      _ = y * x := by group
  · have h' := hX.2 _ (mem_conj_smul_iff'.mp hx)
    rw [pow_two] at h' ⊢
    calc x * x = h * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = 1 := by rw [h']; group

theorem str86_b2_e1 {L1 L2 S : Subgroup G} {k n : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hnc : ¬ ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ MulAut.conj g • Z2 L1 L2 S, x * y = y * x) :
    MulAut.conj g • Z2 L1 L2 S ≤ Q1 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊔ Q2 L1 L2 S = S ∧
      ⁅Q1 L1 L2 S, MulAut.conj g • Z2 L1 L2 S⁆ ≤ Z2 L1 L2 S ∧
      IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧
        (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ n ∧
        (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ n := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨n, hL2⟩
  obtain ⟨-, hZ1Z2, -, hSCZ2, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hP1Q1 : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  have hP1Z1 : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hconjQ1 : ∀ h ∈ P1 L1 L2 S, MulAut.conj h • Z2 L1 L2 S ≤ Q1 L1 L2 S := by
    intro h hh x hx
    have h' := (Subgroup.mem_normalizer_iff.mp (hP1Q1 hh) _).mp (hZ (mem_conj_smul_iff'.mp hx))
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at h'
  set W : Subgroup G := MulAut.conj g • Z2 L1 L2 S with hWdef
  set W' : Subgroup G := MulAut.conj g⁻¹ • Z2 L1 L2 S with hW'def
  have hginv : g⁻¹ ∈ P1 L1 L2 S := (P1 L1 L2 S).inv_mem hg
  have hWQ1 : W ≤ Q1 L1 L2 S := hconjQ1 g hg
  have hW'Q1 : W' ≤ Q1 L1 L2 S := hconjQ1 g⁻¹ hginv
  have hWS : W ≤ S := hWQ1.trans hQ1S
  have hW'S : W' ≤ S := hW'Q1.trans hQ1S
  have hWe : IsElemAbelian 2 W := isElemAbelian_conj_smul hZ2e g
  have hW'e : IsElemAbelian 2 W' := isElemAbelian_conj_smul hZ2e g⁻¹
  have hgg : MulAut.conj g • W' = Z2 L1 L2 S := by
    rw [hW'def, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hWQ2 : ¬ W ≤ Q2 L1 L2 S := by
    intro hle
    apply hnc
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQ2CZ (hle hy)) x hx)
  have hW'Q2 : ¬ W' ≤ Q2 L1 L2 S := by
    intro hle
    apply hnc
    intro x hx y hy
    have hx' : g⁻¹ * x * g ∈ W' := by
      rw [hW'def, mem_conj_smul_iff', inv_inv]
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hx
    have hy' : g⁻¹ * y * g ∈ Z2 L1 L2 S := mem_conj_smul_iff'.mp hy
    have h' := Subgroup.mem_centralizer_iff.mp (hQ2CZ (hle hx')) _ hy'
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [← h']
      _ = y * x := by group
  have hCQ : ∀ X : Subgroup G, X ≤ S →
      X ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = X ⊓ Q2 L1 L2 S := by
    intro X hX
    rw [← hSCZ2, ← inf_assoc, inf_eq_left.mpr hX]
  have hrel1 : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W : Set G)).relIndex (Z2 L1 L2 S) =
      (W' ⊓ Q2 L1 L2 S).relIndex W' := by
    have h' := Subgroup.relIndex_pointwise_smul (MulAut.conj g)
      (W' ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)) W'
    rw [conj_smul_inf_centralizer, hgg, hCQ W' hW'S] at h'
    exact h'
  have hrel2 : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)).relIndex (Z2 L1 L2 S) =
      (W ⊓ Q2 L1 L2 S).relIndex W := by
    have h' := Subgroup.relIndex_pointwise_smul (MulAut.conj g)
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)) (Z2 L1 L2 S)
    rw [conj_smul_inf_centralizer, hgg, ← hWdef, hCQ W hWS] at h'
    exact h'.symm
  have hF5 : ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧
      (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ n ∧
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ n ∧
      IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      (∀ z ∈ Z2 L1 L2 S, ∀ s ∈ S, ⁅z, s⁆ ∈ Z1 L1 L2 S) ∧
      (W ⊓ Q2 L1 L2 S).relIndex W = 2 ^ n := by
    by_cases hcase : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W : Set G)).relIndex (Z2 L1 L2 S) ≤
        (W ⊓ Q2 L1 L2 S).relIndex W
    · obtain ⟨hk1, hz1, hst, hnc1, hq1⟩ :=
        str86_b2_f5 hF hSB hk hFc hU3 hB2 hn hL2 hZI hWS hWe hWQ2 hcase
      exact ⟨W, hWS, hWe, hk1, hz1, hst, hnc1, hq1, hk1⟩
    · have hcase' : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)).relIndex (Z2 L1 L2 S) ≤
          (W' ⊓ Q2 L1 L2 S).relIndex W' := by
        rw [hrel2, ← hrel1]
        omega
      obtain ⟨hk1, hz1, hst, hnc1, hq1⟩ :=
        str86_b2_f5 hF hSB hk hFc hU3 hB2 hn hL2 hZI hW'S hW'e hW'Q2 hcase'
      exact ⟨W', hW'S, hW'e, hk1, hz1, hst, hnc1, hq1, hrel2.symm.trans hz1⟩
  obtain ⟨A, hAS, hAe, hkA, hzA, hst, hnc', hquad, hWrel⟩ := hF5
  have hWN : W ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hWS.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hWQS : W ⊔ Q2 L1 L2 S = S := by
    have hle : W ⊔ Q2 L1 L2 S ≤ S := sup_le hWS hQ2S
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := W) (K := Q2 L1 L2 S) hWN).2
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Q2 L1 L2 S ≤ W ⊔ Q2 L1 L2 S) hle
    rw [hsec, hWrel, str86_relIndex_q2_s hF.toW hSB hn hL2] at hmul
    have h1' : (W ⊔ Q2 L1 L2 S).relIndex S = 1 := by
      have h' : 2 ^ n * (W ⊔ Q2 L1 L2 S).relIndex S = 2 ^ n * 1 := by rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1')
  have hWc : ⁅Q1 L1 L2 S, W⁆ ≤ Z2 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro q hq w hw
    have hw' : g⁻¹ * w * g ∈ Z2 L1 L2 S := mem_conj_smul_iff'.mp hw
    have hq' : g⁻¹ * q * g ∈ S := by
      have h' := (Subgroup.mem_normalizer_iff.mp (hP1Q1 hginv) q).mp hq
      rw [inv_inv] at h'
      exact hQ1S h'
    have hc := (Z1 L1 L2 S).inv_mem (hquad _ hw' _ hq')
    rw [commutatorElement_inv] at hc
    have h' := (Subgroup.mem_normalizer_iff.mp (hP1Z1 hg) _).mp hc
    have e : g * ⁅g⁻¹ * q * g, g⁻¹ * w * g⁆ * g⁻¹ = ⁅q, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e] at h'
    exact hZ1Z2 h'
  exact ⟨hWQ1, hWQS, hWc, hst, hnc', A, hAS, hAe, hkA, hzA⟩

end CFSG.Quasithin.Stroth

end
