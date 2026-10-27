module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIBasics
public import CFSG.Quasithin.Recognition.Stroth.Str86Props
public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.Quasithin.Recognition.Stroth.BenderChief
public import CFSG.Quasithin.Recognition.Stroth.BenderOriented
public import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def u3Y (L1 L2 S : Subgroup G) : Subgroup G :=
  Z2 L1 L2 S ⊓ Q1 L1 L2 S

theorem str86_p1_inf_normalizer_le_bigB {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    P1 L1 L2 S ⊓ Subgroup.normalizer (S : Set G) ≤ bigB L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBsyl : bigB L1 L2 S = P1 L1 L2 S ⊓
      Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    F1.bigB_eq_parabolic_inf hR
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hBL
  intro x hx
  obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
  rw [hBsyl]
  exact Subgroup.mem_inf.mpr ⟨hxP, Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.mpr ⟨hxN, hP1N hxP⟩)⟩

theorem bigB_le_normalizer_z2_sup_q1 {L1 L2 S : Subgroup G} :
    bigB L1 L2 S ≤
      Subgroup.normalizer ((Z2 L1 L2 S ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := by
    rw [P2, bigB_comm]
    exact le_sup_right
  have hBQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hBP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (hBP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  exact F1.le_normalizer_sup hBZ hBQ

theorem u3X1_le_q1 {L1 L2 S : Subgroup G} : u3X1 L1 L2 S ≤ Q1 L1 L2 S := by
  refine conjClosure_le fun l hl y hy => ?_
  have hlP : l ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hl
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hlP) y).mp
    (Subgroup.mem_inf.mp hy).2

theorem u3Y_le_u3X1 {L1 L2 S : Subgroup G} : u3Y L1 L2 S ≤ u3X1 L1 L2 S := by
  rw [u3Y, u3X1]
  exact le_conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1

theorem le_normalizer_u3X1_left {L1 L2 S : Subgroup G} :
    L1 ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
  le_normalizer_conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1

theorem le_normalizer_z2_of_sylow {L1 L2 S : Subgroup G} :
    S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
  have hSP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  exact (hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))).trans
    (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))

theorem le_normalizer_q1_of_sylow {L1 L2 S : Subgroup G} :
    S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  exact hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))

theorem le_normalizer_u3Y_of_sylow {L1 L2 S : Subgroup G} :
    S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) := by
  exact (le_inf (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S))
    (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_u3X1_sylow {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) := by
  have key : ∀ t ∈ S, ∀ x ∈ u3X1 L1 L2 S, t * x * t⁻¹ ∈ u3X1 L1 L2 S := by
    intro t ht x hx
    rw [u3X1] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, y, hy, rfl⟩ := hx
      have htL : t * l * t⁻¹ ∈ L1 :=
        (Subgroup.mem_normalizer_iff.mp (hF.1.h1.normalizes ht) l).mp hl
      have hty : t * y * t⁻¹ ∈ Z2 L1 L2 S ⊓ Q1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_u3Y_of_sylow (L1 := L1) (L2 := L2) (S := S) ht) y).mp hy
      simpa [mul_assoc] using mem_conjClosure htL hty
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1).mul_mem ihx ihy
    | inv x _ ih =>
      simpa [mul_assoc] using (conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1).inv_mem ih
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key s hs x
  · intro hx
    have h := key s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) hx
    simpa [mul_assoc] using h


theorem str86_z2_sup_q1_eq_X0 {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ∃ X0 : Subgroup G,
      (∀ t, t ∈ X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S) ∧
        Q1 L1 L2 S ≤ X0 ∧ (Q1 L1 L2 S).relIndex X0 = 2 ^ k ∧
        Z2 L1 L2 S ⊔ Q1 L1 L2 S = X0 ∧
        (Z2 L1 L2 S ⊓ Q1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ k := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hLhat : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) :=
    isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hqLhat : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) (2 ^ k) := by
    refine Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hVU3Lhat : VU3Big (L1 ⊔ Q1 L1 L2 S) := by
    refine ⟨k, hk, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hrelS : (Q1 L1 L2 S).relIndex S = (2 ^ k) ^ 3 := by
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      have h := relIndex_pCoreOf_sylow_su (L := L1 ⊔ Q1 L1 L2 S) (T := S)
        hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
      rwa [pCoreOf_sup_pCoreOf hF.1] at h
    · obtain ⟨eL⟩ := h
      have h := relIndex_pCoreOf_sylow_psu (L := L1 ⊔ Q1 L1 L2 S) (T := S)
        hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
      rwa [pCoreOf_sup_pCoreOf hF.1] at h
  obtain ⟨X0, hmemX0, hQ1X0, hrelX0, -⟩ := exists_X0 hqLhat hT
  rw [pCoreOf_sup_pCoreOf hF.1] at hmemX0 hQ1X0 hrelX0
  have hX0S : X0 ≤ S := fun t ht => ((hmemX0 t).mp ht).1
  have hX0neS : X0 ≠ S := by
    intro hX0S'
    have h1 : (Q1 L1 L2 S).relIndex S = 2 ^ k := hX0S' ▸ hrelX0
    have heq : (2 ^ k) ^ 3 = 2 ^ k := by
      rw [← hrelS]
      exact h1
    have hq4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hqpos : 0 < 2 ^ k := by positivity
    have hcube : (2 ^ k) ^ 3 = 2 ^ k * (2 ^ k * 2 ^ k) := by ring
    nlinarith
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hZ2NQ1 : Z2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hZ2S.trans (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S))
  set X : Subgroup G := Z2 L1 L2 S ⊔ Q1 L1 L2 S with hXdef
  have hXS : X ≤ S := sup_le hZ2S hQ1S
  have hXX0 : X ≤ X0 := by
    intro x hx
    rw [hmemX0 x]
    refine ⟨hXS hx, ?_⟩
    obtain ⟨z, hz, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hZ2NQ1).mp hx
    have hz2 : z * z = 1 := by
      simpa [pow_two] using
        (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hz
    have hq1 : z * q * z⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hZ2NQ1 hz) q).mp hq
    have hq2 : z * (z * q * z⁻¹) * z⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hZ2NQ1 hz) _).mp hq1
    have he : (z * q) * (z * q) =
        (z * q * z⁻¹) * (z * (z * q * z⁻¹) * z⁻¹) * (z * z) := by group
    rw [pow_two, he, hz2, mul_one]
    exact (Q1 L1 L2 S).mul_mem hq1 hq2
  have hXN : (L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    intro g hg
    obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgP1 : g ∈ P1 L1 L2 S :=
      (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S) (pCoreOf_le 2 (P1 L1 L2 S))) hgL
    have hgB : g ∈ bigB L1 L2 S :=
      str86_p1_inf_normalizer_le_bigB hF.toW hSB (Subgroup.mem_inf.mpr ⟨hgP1, hgN⟩)
    exact bigB_le_normalizer_z2_sup_q1 (L1 := L1) (L2 := L2) (S := S) hgB
  have htrich := vertex_trichotomy (L := L1 ⊔ Q1 L1 L2 S) (T := S) (X := X)
    (Or.inr hVU3Lhat) hT (by rw [pCoreOf_sup_pCoreOf hF.1]; exact le_sup_right) hXS hXN
  rw [pCoreOf_sup_pCoreOf hF.1] at htrich
  have hXeqX0 : X = X0 := by
    rcases htrich with hXQ | hXS' | hthird
    · exfalso
      apply hZQ
      intro z hz
      have hzX : z ∈ X := Subgroup.mem_sup_left hz
      rw [hXQ] at hzX
      exact hzX
    · exfalso
      apply hX0neS
      exact le_antisymm hX0S (hXS' ▸ hXX0)
    · apply le_antisymm
      · intro t ht
        rw [hmemX0 t]
        exact ⟨hXS ht, (hthird t (hXS ht)).mp ht⟩
      · intro t ht
        have htS : t ∈ S := ((hmemX0 t).mp ht).1
        exact (hthird t htS).mpr ((hmemX0 t).mp ht).2
  have hrelX : (Q1 L1 L2 S).relIndex X = 2 ^ k := by
    rw [hXeqX0, hrelX0]
  have hYrel : (Z2 L1 L2 S ⊓ Q1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ k := by
    have hQ1Z2 : Q1 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      hQ1S.trans (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := Q1 L1 L2 S) (K := Z2 L1 L2 S) hQ1Z2).1
    rw [inf_comm, ← hsec, sup_comm, ← hXdef, hrelX]
  exact ⟨X0, hmemX0, hQ1X0, hrelX0, hXdef ▸ hXeqX0, hYrel⟩


theorem le_normalizer_u3X1_sup {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    L1 ⊔ S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
  sup_le le_normalizer_u3X1_left (le_normalizer_u3X1_sylow hF)

theorem str86_commutator_u3X1_ne_bot {L1 L2 S : Subgroup G}
    {k : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ⁅u3X1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≠ ⊥ := by
  classical
  intro hcbot
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨z, hzZ2, hzQ1⟩ : ∃ z : G, z ∈ Z2 L1 L2 S ∧ z ∉ Q1 L1 L2 S := by
    by_contra hcon
    exact hZQ fun z hz => by
      by_contra hzq
      exact hcon ⟨z, hz, hzq⟩
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hzS : z ∈ S := (omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S hzZ2
  have hzP1 : z ∈ P1 L1 L2 S :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right) hzS
  have hNP1 : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hNP2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hc : ∀ x ∈ Q1 L1 L2 S, x * z * x⁻¹ * z⁻¹ ∈ u3X1 L1 L2 S := by
    intro x hx
    have hxS : x ∈ S := hQ1S hx
    have hxP2 : x ∈ P2 L1 L2 S :=
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right) hxS
    have hxz : x * z * x⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hNP2 hxP2) z).mp hzZ2
    have hzx : z * x * z⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hNP1 hzP1) x).mp hx
    have hmemY : x * z * x⁻¹ * z⁻¹ ∈ u3Y L1 L2 S := by
      rw [u3Y]
      constructor
      · have he : x * z * x⁻¹ * z⁻¹ = (x * z * x⁻¹) * z⁻¹ := by group
        rw [he]
        exact (Z2 L1 L2 S).mul_mem hxz ((Z2 L1 L2 S).inv_mem hzZ2)
      · have he : x * z * x⁻¹ * z⁻¹ = x * (z * x * z⁻¹)⁻¹ := by group
        rw [he]
        exact (Q1 L1 L2 S).mul_mem hx ((Q1 L1 L2 S).inv_mem hzx)
    exact u3Y_le_u3X1 hmemY
  exact false_of_commutator_le_of_bender (q := 2 ^ k) hF.1 hSB hS1 hq
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S))
    (le_normalizer_u3X1_sup hF) hcbot hzS hzQ1 hc

theorem oTwoUpper_le_of_sup_eq {H C Q : Subgroup G} (hH : C ⊔ Q = H)
    (hCN : H ≤ Subgroup.normalizer (C : Set G)) (hQ2 : IsPGroup 2 Q) :
    oTwoUpper H ≤ C := by
  classical
  have hCH : C ≤ H := le_sup_left.trans hH.le
  have hQH : Q ≤ H := le_sup_right.trans hH.le
  have hQN : Q ≤ Subgroup.normalizer (C : Set G) := hQH.trans hCN
  have hCsubN : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hCN
  let π : ↥H →* ↥H ⧸ C.subgroupOf H := QuotientGroup.mk' (C.subgroupOf H)
  refine oTwoUpper_le_of_pow_mem ?_
  intro x hxH
  have hxK : x ∈ C ⊔ Q := hH.symm ▸ hxH
  obtain ⟨c, hc, q, hq, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp hxK
  obtain ⟨n, hn⟩ := hQ2.exists_pow_pow_eq_one ⟨q, hq⟩
  have hqpow : q ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hcπ : π ⟨c, hCH hc⟩ = 1 := by
    change QuotientGroup.mk (⟨c, hCH hc⟩ : ↥H) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hc
  have hπcq : π ⟨c * q, hxH⟩ = π ⟨q, hQH hq⟩ := by
    rw [show (⟨c * q, hxH⟩ : ↥H) = ⟨c, hCH hc⟩ * ⟨q, hQH hq⟩ from Subtype.ext rfl,
      map_mul, hcπ, one_mul]
  have hqpowH : (⟨q, hQH hq⟩ : ↥H) ^ 2 ^ n = 1 := by
    ext
    simpa using hqpow
  have hxpow : (π ⟨c * q, hxH⟩) ^ 2 ^ n = 1 := by
    rw [hπcq, ← map_pow, hqpowH, map_one]
  have hxsub : (⟨(c * q) ^ 2 ^ n, H.pow_mem hxH _⟩ : ↥H) ∈ C.subgroupOf H := by
    refine (QuotientGroup.eq_one_iff (N := C.subgroupOf H)
      (⟨(c * q) ^ 2 ^ n, H.pow_mem hxH _⟩ : ↥H)).mp ?_
    change π ⟨(c * q) ^ 2 ^ n, H.pow_mem hxH _⟩ = 1
    rw [show (⟨(c * q) ^ 2 ^ n, H.pow_mem hxH _⟩ : ↥H) =
      (⟨c * q, hxH⟩ : ↥H) ^ 2 ^ n from Subtype.ext rfl]
    rw [map_pow, hxpow]
  exact ⟨n, Subgroup.mem_subgroupOf.mp hxsub⟩

theorem str86_commutator_u3X1_z2_not_le_z1
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ¬ ⁅u3X1 L1 L2 S, Z2 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  classical
  intro hcomm
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hZ1X1 : Z1 L1 L2 S ≤ u3X1 L1 L2 S := by
    have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
      (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.1
    have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S := omegaOneCenterOf_le (Q1 L1 L2 S)
    exact (le_inf hZ1Z2 hZ1Q1).trans (u3Y_le_u3X1 (L1 := L1) (L2 := L2) (S := S))
  obtain ⟨z, hzZ2, hzQ1⟩ : ∃ z : G, z ∈ Z2 L1 L2 S ∧ z ∉ Q1 L1 L2 S := by
    by_contra hcon
    exact hZQ fun z hz => by
      by_contra hzq
      exact hcon ⟨z, hz, hzq⟩
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hzS : z ∈ S := (omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S hzZ2
  have hz2 : z * z = 1 := by
    simpa [pow_two] using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hzZ2
  let Lh : Subgroup G := L1 ⊔ S
  let C : Subgroup G := centralizerSection Lh (u3X1 L1 L2 S) (Z1 L1 L2 S)
  have hLhX : Lh ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    le_normalizer_u3X1_sup hF
  have hLhCent : Lh ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [show Lh = L1 ⊔ Q1 L1 L2 S from hLhatQ]
    exact hZI
  have hLhZ : Lh ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hLhCent.trans (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hCN : Lh ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact conj_mem_centralizerSection (Subgroup.le_normalizer hg) (hLhX hg) (hLhZ hg) hc
    · intro hc
      have h := conj_mem_centralizerSection (Subgroup.le_normalizer (Lh.inv_mem hg))
        (hLhX (Lh.inv_mem hg)) (hLhZ (Lh.inv_mem hg)) hc
      simpa [mul_assoc] using h
  have hQ1Lh : Q1 L1 L2 S ≤ Lh := by
    rw [show Lh = L1 ⊔ Q1 L1 L2 S from hLhatQ]
    exact le_sup_right
  have hQLh : Lh ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    rw [show Lh = L1 ⊔ Q1 L1 L2 S from hLhatQ]
    exact sup_le ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))) Subgroup.le_normalizer
  have hCLh : C ≤ Lh := centralizerSection_le_left Lh (u3X1 L1 L2 S) (Z1 L1 L2 S)
  let K : Subgroup G := C ⊔ Q1 L1 L2 S
  have hKH : K ≤ Lh := sup_le hCLh hQ1Lh
  have hKN : Lh ≤ Subgroup.normalizer (K : Set G) :=
    F1.le_normalizer_sup (X := Lh) hCN hQLh
  have hqLh : IsSzU3Quot (oTwoQuot ↥Lh) (2 ^ k) := by
    have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
      Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
    have he : oTwoQuot ↥Lh ≃* oTwoQuot ↥L1 := by
      rw [show Lh = L1 ⊔ Q1 L1 L2 S from hLhatQ]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he hq
  have hQcore : pCoreOf 2 Lh = Q1 L1 L2 S := by
    rw [show Lh = L1 ⊔ Q1 L1 L2 S from hLhatQ]
    exact pCoreOf_sup_pCoreOf hF.1
  have hzLh : z ∈ Lh := (le_sup_right : S ≤ L1 ⊔ S) hzS
  have hzC : z ∈ C := by
    refine (mem_centralizerSection_iff_of_le hZ1X1).mpr ⟨hzLh, fun x hx => ?_⟩
    have h := (Subgroup.commutator_le.mp hcomm) x hx z hzZ2
    simpa [commutatorElement_def] using h
  have hzK : z ∈ K := Subgroup.mem_sup_left hzC
  have hKeq : K = Lh := by
    rcases eq_or_mem_pCoreOf_of_normal (H := Lh) (K := K) hqLh hKH hKN
      (by rw [hQcore]; exact le_sup_right) with h | h
    · exact h
    · exfalso
      apply hzQ1
      rw [← hQcore]
      exact h z hzK ⟨1, by simpa [pow_two] using hz2⟩
  have hO2C : oTwoUpper Lh ≤ C := by
    have hKeq' : C ⊔ Q1 L1 L2 S = Lh := hKeq
    exact oTwoUpper_le_of_sup_eq hKeq' hCN (pCoreOf_isPGroup 2 (P1 L1 L2 S))
  have hO2cent : oTwoUpper Lh ≤ Subgroup.centralizer (u3X1 L1 L2 S : Set G) := by
    rw [oTwoUpper]
    refine (Subgroup.closure_le _).mpr ?_
    rintro e ⟨heLh, heOdd⟩
    have heO : e ∈ oTwoUpper Lh := Subgroup.subset_closure ⟨heLh, heOdd⟩
    have heC : e ∈ C := hO2C heO
    have heNX : e ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
      centralizerSection_le_normalizer_left Lh (u3X1 L1 L2 S) (Z1 L1 L2 S) heC
    have heCe := (mem_centralizerSection_iff_of_le hZ1X1).mp heC
    change ∀ y ∈ u3X1 L1 L2 S, y * e = e * y
    intro x hx
    have hcentral := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series
      (X := G) heOdd
      ((pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le (u3X1_le_q1 (L1 := L1) (L2 := L2)
        (S := S))) hZ1X1 ?_ ?_ ?_ x hx
    calc x * e = (e * x * e⁻¹) * e := by rw [hcentral]
      _ = e * x := by group
    · intro y hy
      exact (Subgroup.mem_normalizer_iff.mp heNX y).mp hy
    · intro y hy
      have hye : y * e = e * y :=
        (Subgroup.mem_centralizer_iff.mp (hLhCent heLh) y hy)
      calc e * y * e⁻¹ = y * e * e⁻¹ := by rw [hye]
        _ = y := by group
    · intro y hy
      have hmem : y * e * y⁻¹ * e⁻¹ ∈ Z1 L1 L2 S := heCe.2 y hy
      have heq : ⁅e, y⁆ = (y * e * y⁻¹ * e⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact (Z1 L1 L2 S).inv_mem hmem
  have hbot : ⁅u3X1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hO2cent he) x hx).symm
  exact (str86_commutator_u3X1_ne_bot hF hSB hk hFc hU3 hZQ) hbot

theorem relIndex_pCoreOf_sylow_of_isL2Quot
    {L T : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = 2 ^ f := by
  classical
  obtain ⟨e⟩ := e
  let K1 := ↥L
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (CFSG.pCore 2 K1)
  let T1 : Subgroup K1 := T.subgroupOf L
  have hmap1 : (pCoreOf 2 L).relIndex T = (CFSG.pCore 2 K1).relIndex T1 := by
    rw [CFSG.Open.pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact Subgroup.relIndex_map_map_of_injective (f := L.subtype) (CFSG.pCore 2 K1) T1
      L.subtype_injective
  have hmap2 : (CFSG.pCore 2 K1).relIndex T1 = Nat.card (T1.map π) := by
    have h := Subgroup.relIndex_ker (K := T1) π
    rwa [QuotientGroup.ker_mk'] at h
  have hT1syl : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm, ?_⟩
    rw [show (T1.subgroupOf ⊤).index = T1.index from by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]]
    exact hT.2.2
  have hcard : Nat.card (T1.map π) = 2 ^ f := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P1 : Sylow 2 K1 := hT1syl.2.1.toSylow (by
      have h := hT1syl.2.2
      rwa [show (T1.subgroupOf ⊤).index = T1.index from by
        rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]] at h)
    let P2 : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
    have hcoe : (P2 : Subgroup (oTwoQuot K1)) = T1.map π :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
    have hB : BenderType (oTwoQuot K1) f 1 1 := BenderType.linear f hf e
    obtain ⟨t, hc⟩ := hB.exists_benderCore P2
    rw [hcoe] at hc
    simpa using hc.card_eq
  rw [hmap1, hmap2, hcard]

theorem str86_inf_p1_q1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L1 ⊓ Q1 L1 L2 S = pCoreOf 2 L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  set P : Subgroup G := L1 ⊔ bigB L1 L2 S with hP
  set Q : Subgroup G := pCoreOf 2 P with hQ
  have hL1P : L1 ≤ P := le_sup_left
  have hL1N : L1 ≤ Subgroup.normalizer (Q : Set G) :=
    hL1P.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (F1.parabolic_le_normalizer hR).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  have hQle : pCoreOf 2 L1 ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans hL1P) hPN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L1)
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L1) hQle)
  have hN : ((L1 ⊓ Q).subgroupOf L1).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro x hx
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer hx) (hL1N hx)
  have hQ2 : IsPGroup 2 ↥(L1 ⊓ Q) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le
      (inf_le_right : L1 ⊓ Q ≤ Q)
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hN hQ2

theorem str86_inf_l2_q2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L2 ⊓ Q2 L1 L2 S = pCoreOf 2 L2 := by
  have h := str86_inf_p1_q1 (L1 := L2) (L2 := L1) (S := S) hF.symm
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

theorem str86_relIndex_q2_s {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (Q2 L1 L2 S).relIndex S = 2 ^ n := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  have hS2P : S ⊓ L2 ≤ P2 L1 L2 S := inf_le_right.trans le_sup_left
  have hS2N : S ⊓ L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hS2P.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  have hrel : Q.relIndex S = Q.relIndex (S ⊓ L2) := by
    conv_lhs => rw [hS2]
    exact F1.relIndex_sup_eq_of_le_normalizer (D := Q) (T := S ⊓ L2) hS2N
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  have hinfQ : (S ⊓ L2) ⊓ Q = pCoreOf 2 L2 := by
    rw [hQ]
    have hEq : (S ⊓ L2) ⊓ Q2 L1 L2 S = L2 ⊓ Q2 L1 L2 S := by
      refine le_antisymm ?_ ?_
      · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
      · refine le_inf (le_inf (inf_le_right.trans hQ2S) inf_le_left) inf_le_right
    rw [hEq, str86_inf_l2_q2 hF]
  rw [hrel, ← Subgroup.inf_relIndex_left (H := S ⊓ L2) (K := Q), hinfQ]
  exact relIndex_pCoreOf_sylow_of_isL2Quot hn hL2 hF.1.h2.sylow

theorem str86_chief_count_bound
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    1 ≤ c ∧ ((2 ^ k) ^ 2) ^ c ≤ 2 ^ n := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hLhatQ]
    exact pCoreOf_sup_pCoreOf hF.1
  have hqLh : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
      Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hLhatQ]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he hq
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hX1Lh : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans
      (hQ1S.trans le_sup_right)
  have hcpos : 1 ≤ c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    have hbot := D14.commutator_eq_bot_of_zero (H := L1 ⊔ S) (U := u3X1 L1 L2 S)
      (pCoreOf_isPGroup 2 (P1 L1 L2 S) |>.to_le
        (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S))) hser hc0
    exact (str86_commutator_u3X1_ne_bot hF hSB hk hFc hU3 hZQ) hbot
  obtain ⟨z, hzZ2, hzQ1⟩ : ∃ z : G, z ∈ Z2 L1 L2 S ∧ z ∉ Q1 L1 L2 S := by
    by_contra hcon
    exact hZQ fun z hz => by
      by_contra hzq
      exact hcon ⟨z, hz, hzq⟩
  have hzS : z ∈ S := (omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S hzZ2
  have hzLh : z ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) hzS
  have hz2 : z * z = 1 := by
    simpa [pow_two] using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hzZ2
  have hzsq : z * z ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQcore]
    simpa [hz2] using (Q1 L1 L2 S).one_mem
  have hzO : z ∉ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hQcore]
  have hM6 := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := u3X1 L1 L2 S)
    (q := 2 ^ k) (c := c) hqLh
    ((pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le
      (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S))) hX1Lh hser hzLh hzsq hzO
  have hX1P2 : u3X1 L1 L2 S ≤ P2 L1 L2 S :=
    ((u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans hQ1S).trans
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hX1NQ2 : u3X1 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hX1P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hinfC : u3X1 L1 L2 S ⊓ Q2 L1 L2 S ≤
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hyQ2 : y ∈ Q2 L1 L2 S := (Subgroup.mem_inf.mp hy).2
    have hzy : z * y = y * z :=
      (Subgroup.mem_centralizer_iff.mp
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hyQ2) z hzZ2)
    exact ((Commute.zpow_right (show Commute y z from hzy.symm) j).eq).symm
  have hle1 : (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).relIndex
        (u3X1 L1 L2 S) ≤ (u3X1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_left hinfC (D15Proof.relIndex_ne_zero _ _)
  have hsecond : (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S ⊔ Q2 L1 L2 S) =
      (u3X1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := u3X1 L1 L2 S) (K := Q2 L1 L2 S) hX1NQ2).2
  have hsupS : u3X1 L1 L2 S ⊔ Q2 L1 L2 S ≤ S :=
    sup_le (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S) |>.trans hQ1S) hQ2S
  have hle2 : (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S ⊔ Q2 L1 L2 S) ≤
      (Q2 L1 L2 S).relIndex S :=
    Subgroup.relIndex_le_of_le_right hsupS (D15Proof.relIndex_ne_zero _ _)
  have hq2s : (Q2 L1 L2 S).relIndex S = 2 ^ n := str86_relIndex_q2_s hF.toW hSB hn hL2
  refine ⟨hcpos, ?_⟩
  calc ((2 ^ k) ^ 2) ^ c ≤
        (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).relIndex
          (u3X1 L1 L2 S) := hM6
    _ ≤ (u3X1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (u3X1 L1 L2 S) := hle1
    _ = (Q2 L1 L2 S).relIndex (u3X1 L1 L2 S ⊔ Q2 L1 L2 S) := hsecond.symm
    _ ≤ (Q2 L1 L2 S).relIndex S := hle2
    _ = 2 ^ n := hq2s

theorem bigB_le_normalizer_u3X1 {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) := by
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := by
    rw [P2, bigB_comm]
    exact le_sup_right
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF
  have hBQ : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hBP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (hBP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hBY : bigB L1 L2 S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
    (le_inf hBZ hBQ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have key : ∀ t ∈ bigB L1 L2 S, ∀ x ∈ u3X1 L1 L2 S,
      t * x * t⁻¹ ∈ u3X1 L1 L2 S := by
    intro t ht x hx
    rw [u3X1] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, y, hy, rfl⟩ := hx
      have htL : t * l * t⁻¹ ∈ L1 :=
        (Subgroup.mem_normalizer_iff.mp (hBL ht) l).mp hl
      have hty : t * y * t⁻¹ ∈ u3Y L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hBY ht) y).mp hy
      rw [u3Y] at hty
      simpa [mul_assoc] using mem_conjClosure htL hty
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1).mul_mem ihx ihy
    | inv x _ ih =>
      simpa [mul_assoc] using (conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1).inv_mem ih
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key b hb x
  · intro hx
    have h := key b⁻¹ ((bigB L1 L2 S).inv_mem hb) (b * x * b⁻¹) hx
    simpa [mul_assoc] using h


theorem str86_borel_transitive_mod_q2_of_inf
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S)
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    {s t : G} (hsS2 : s ∈ S ⊓ L2) (htS2 : t ∈ S ⊓ L2)
    (hsQ : s ∉ Q2 L1 L2 S) (htQ : t ∉ Q2 L1 L2 S) :
    ∃ b ∈ borelOf L2 S, b * s * b⁻¹ * t⁻¹ ∈ Q2 L1 L2 S := by
  classical
  let K1 := ↥L2
  let π : K1 →* oTwoQuot K1 := QuotientGroup.mk' (CFSG.pCore 2 K1)
  let T1 : Subgroup K1 := (S ⊓ L2).subgroupOf L2
  have hsL2 : s ∈ L2 := (Subgroup.mem_inf.mp hsS2).2
  have htL2 : t ∈ L2 := (Subgroup.mem_inf.mp htS2).2
  have hsT1 : (⟨s, hsL2⟩ : K1) ∈ T1 := Subgroup.mem_subgroupOf.mpr hsS2
  have htT1 : (⟨t, htL2⟩ : K1) ∈ T1 := Subgroup.mem_subgroupOf.mpr htS2
  have hT1syl : IsSylowTwoOf T1 ⊤ := by
    refine ⟨le_top, hF.1.h2.sylow.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe hF.1.h2.sylow.1).symm, ?_⟩
    rw [show (T1.subgroupOf ⊤).index = T1.index from by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]]
    exact hF.1.h2.sylow.2.2
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P1 : Sylow 2 K1 := hT1syl.2.1.toSylow (by
    have h := hT1syl.2.2
    rwa [show (T1.subgroupOf ⊤).index = T1.index from by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]] at h)
  let P : Sylow 2 (oTwoQuot K1) := P1.mapSurjective (QuotientGroup.mk'_surjective _)
  have hPcoe : (P : Subgroup (oTwoQuot K1)) = T1.map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) P1
  have hsP : π ⟨s, hsL2⟩ ∈ (P : Subgroup (oTwoQuot K1)) := by
    rw [hPcoe]
    exact Subgroup.mem_map_of_mem π hsT1
  have htP : π ⟨t, htL2⟩ ∈ (P : Subgroup (oTwoQuot K1)) := by
    rw [hPcoe]
    exact Subgroup.mem_map_of_mem π htT1
  have hO2Q2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
    rw [← str86_inf_l2_q2 hF.toW]
    exact inf_le_right
  have hs1 : π ⟨s, hsL2⟩ ≠ 1 := by
    intro h
    apply hsQ
    exact hO2Q2 ((CFSG.mem_openPCoreOf_iff (⟨s, hsL2⟩ : K1)).mpr
      ((QuotientGroup.eq_one_iff (⟨s, hsL2⟩ : K1)).mp h))
  have ht1 : π ⟨t, htL2⟩ ≠ 1 := by
    intro h
    apply htQ
    exact hO2Q2 ((CFSG.mem_openPCoreOf_iff (⟨t, htL2⟩ : K1)).mpr
      ((QuotientGroup.eq_one_iff (⟨t, htL2⟩ : K1)).mp h))
  obtain ⟨d, hdN, hds⟩ := psl2_normalizer_transitive (n := n) (by omega) hL2 P hsP htP hs1 ht1
  have hmap := (F1.map_borelOf_eq_normalizer hF.1.h2.sylow).2.2
  have hdT : d ∈ Subgroup.normalizer ((T1.map π : Subgroup (oTwoQuot K1)) :
      Set (oTwoQuot K1)) := by
    simpa [hPcoe] using hdN
  have hdImg : d ∈ ((borelOf L2 S).subgroupOf L2).map π := by
    have hdT' : d ∈ Subgroup.normalizer
        ((((S ⊓ L2).subgroupOf L2).map π : Subgroup (oTwoQuot K1)) : Set (oTwoQuot K1)) := by
      simpa [T1] using hdT
    rw [← hmap] at hdT'
    exact hdT' 
  obtain ⟨b, hb, hbd⟩ := Subgroup.mem_map.mp hdImg
  refine ⟨(b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
  have hπ1 : π (b * (⟨s, hsL2⟩ : K1) * b⁻¹ * (⟨t, htL2⟩ : K1)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hbd, hds]
    group
  have hmemO2 : b * (⟨s, hsL2⟩ : K1) * b⁻¹ * (⟨t, htL2⟩ : K1)⁻¹ ∈
      CFSG.pCore 2 K1 := (QuotientGroup.eq_one_iff _).mp hπ1
  have hmemG : (b : G) * s * (b : G)⁻¹ * t⁻¹ ∈ pCoreOf 2 L2 :=
    (CFSG.mem_openPCoreOf_iff _).mpr hmemO2
  exact hO2Q2 hmemG


theorem str86_borel_transitive_mod_q2
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ x ∈ S, x ∉ Q2 L1 L2 S → ∀ y ∈ S, y ∉ Q2 L1 L2 S →
      ∃ b ∈ borelOf L2 S, b * x * b⁻¹ * y⁻¹ ∈ Q2 L1 L2 S := by
  intro x hxS hxQ y hyS hyQ
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB
      (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  have hS2P : S ⊓ L2 ≤ P2 L1 L2 S := inf_le_right.trans le_sup_left
  have hS2N : S ⊓ L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hS2P.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hSP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  obtain ⟨s, hsS2, q, hqQ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hS2N).mp (hS2 ▸ hxS)
  obtain ⟨t, htS2, r, hrQ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hS2N).mp (hS2 ▸ hyS)
  have hsQ : s ∉ Q2 L1 L2 S := by
    intro hs
    exact hxQ ((Q2 L1 L2 S).mul_mem hs hqQ)
  have htQ : t ∉ Q2 L1 L2 S := by
    intro ht
    exact hyQ ((Q2 L1 L2 S).mul_mem ht hrQ)
  obtain ⟨b, hbB2, hbA⟩ :=
    str86_borel_transitive_mod_q2_of_inf hF hn hL2 hsS2 htS2 hsQ htQ
  refine ⟨b, hbB2, ?_⟩
  have hB2P2 : borelOf L2 S ≤ P2 L1 L2 S :=
    (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S).trans le_sup_right
  have hB2NQ : borelOf L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hB2P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hq' : b * q * b⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hB2NQ hbB2) q).mp hqQ
  have hsec0 : (b * q * b⁻¹) * r⁻¹ ∈ Q2 L1 L2 S :=
    (Q2 L1 L2 S).mul_mem hq' ((Q2 L1 L2 S).inv_mem hrQ)
  have htS : t ∈ S := (Subgroup.mem_inf.mp htS2).1
  have htN : t ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))) htS
  have hsec : t * ((b * q * b⁻¹) * r⁻¹) * t⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp htN _).mp hsec0
  have he : b * (s * q) * b⁻¹ * (t * r)⁻¹ =
      (b * s * b⁻¹ * t⁻¹) * (t * ((b * q * b⁻¹) * r⁻¹) * t⁻¹) := by group
  rw [he]
  exact (Q2 L1 L2 S).mul_mem hbA hsec


theorem str86_u3X1_sup_q2_ne
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    u3X1 L1 L2 S ⊔ Q2 L1 L2 S ≠ Q2 L1 L2 S := by
  classical
  intro hY
  have hX1Q2 : u3X1 L1 L2 S ≤ Q2 L1 L2 S := by
    rw [← hY]
    exact le_sup_left
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hLhatQ : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hLhatQ]
    exact pCoreOf_sup_pCoreOf hF.1
  have hqLh : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
      Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hLhatQ]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he hq
  have hcpos : 1 ≤ c := (str86_chief_count_bound hF hSB hk hFc hU3 hn hL2 hZQ hser).1
  obtain ⟨z, hzZ2, hzQ1⟩ : ∃ z : G, z ∈ Z2 L1 L2 S ∧ z ∉ Q1 L1 L2 S := by
    by_contra hcon
    exact hZQ fun z hz => by
      by_contra hzq
      exact hcon ⟨z, hz, hzq⟩
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hzS : z ∈ S := (omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S hzZ2
  have hzLh : z ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) hzS
  have hz2 : z * z = 1 := by
    simpa [pow_two] using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hzZ2
  have hzsq : z * z ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQcore]
    simpa [hz2] using (Q1 L1 L2 S).one_mem
  have hzO : z ∉ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hQcore]
  have hX1Lh : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans
      ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)).trans
        le_sup_right)
  have hM6 := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := u3X1 L1 L2 S)
    (q := 2 ^ k) (c := c) hqLh
    ((pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le
      (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S))) hX1Lh hser hzLh hzsq hzO
  have hC1 : (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).relIndex
      (u3X1 L1 L2 S) = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hxQ2 : x ∈ Q2 L1 L2 S := hX1Q2 hx
    have hzx : z * x = x * z :=
      (Subgroup.mem_centralizer_iff.mp
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hxQ2) z hzZ2)
    exact ((Commute.zpow_right (show Commute x z from hzx.symm) j).eq).symm
  have hle1 : ((2 ^ k) ^ 2) ^ c ≤ 1 := by
    calc ((2 ^ k) ^ 2) ^ c ≤
          (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).relIndex
            (u3X1 L1 L2 S) := hM6
      _ = 1 := hC1
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hbase : 1 ≤ (2 ^ k) ^ 2 := by
    have hpos : 0 < (2 ^ k) ^ 2 := pow_pos (by positivity) 2
    omega
  have hle : (2 ^ k) ^ 2 ≤ ((2 ^ k) ^ 2) ^ c := by
    simpa using Nat.pow_le_pow_right hbase hcpos
  have hfin : (2 ^ k) ^ 2 ≤ 1 := hle.trans hle1
  have hsq : (2 ^ k) ^ 2 = 2 ^ k * 2 ^ k := by ring
  nlinarith


theorem str86_u3X1_sup_q2
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  classical
  set Y : Subgroup G := u3X1 L1 L2 S ⊔ Q2 L1 L2 S with hY
  have hYQ2 : Q2 L1 L2 S ≤ Y := le_sup_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hYS : Y ≤ S := sup_le
    ((u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans hQ1S) hQ2S
  have hYne : Y ≠ Q2 L1 L2 S := by
    rw [hY]
    exact str86_u3X1_sup_q2_ne hF hSB hk hFc hU3 hn hL2 hZQ hser
  refine le_antisymm hYS ?_
  by_contra hnot
  have hxex : ∃ x ∈ Y, x ∉ Q2 L1 L2 S := by
    by_contra hcon
    apply hYne
    refine le_antisymm ?_ hYQ2
    intro x hx
    by_contra hxq
    exact hcon ⟨x, hx, hxq⟩
  have hyex : ∃ y ∈ S, y ∉ Y := by
    by_contra hcon
    apply hnot
    intro y hy
    by_contra hyY
    exact hcon ⟨y, hy, hyY⟩
  obtain ⟨x, hxY, hxQ2⟩ := hxex
  obtain ⟨y, hyS, hyY⟩ := hyex
  have hxS : x ∈ S := hYS hxY
  have hyQ2 : y ∉ Q2 L1 L2 S := fun hy => hyY (hYQ2 hy)
  obtain ⟨b, hbB2, hbxy⟩ :=
    str86_borel_transitive_mod_q2 hF hSB hn hL2 x hxS hxQ2 y hyS hyQ2
  have hB2big : borelOf L2 S ≤ bigB L1 L2 S := by
    rw [bigB]
    exact le_sup_right.trans le_sup_left
  have hB2NX : borelOf L2 S ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    hB2big.trans (bigB_le_normalizer_u3X1 hF.1)
  have hB2P2 : borelOf L2 S ≤ P2 L1 L2 S :=
    hB2big.trans le_sup_right
  have hB2NQ2 : borelOf L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hB2P2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hbNY : b ∈ Subgroup.normalizer (Y : Set G) :=
    F1.le_normalizer_sup (X := borelOf L2 S) hB2NX hB2NQ2 hbB2
  have hbx : b * x * b⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp hbNY x).mp hxY
  have hbxyY : b * x * b⁻¹ * y⁻¹ ∈ Y := hYQ2 hbxy
  have hyY' : y ∈ Y := by
    have he : y = (b * x * b⁻¹ * y⁻¹)⁻¹ * (b * x * b⁻¹) := by group
    rw [he]
    exact Y.mul_mem (Y.inv_mem hbxyY) hbx
  exact hyY hyY'


theorem str86_u3Y_not_normal
    {L1 L2 S : Subgroup G} {k n c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) c) :
    ¬ (L1 ⊔ S ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G)) := by
  intro hN
  have hL1N : L1 ≤ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ L1 ⊔ S).trans hN
  have hXeqY : u3X1 L1 L2 S = u3Y L1 L2 S := by
    refine le_antisymm ?_ (u3Y_le_u3X1 (L1 := L1) (L2 := L2) (S := S))
    exact conjClosure_le fun l hl y hy =>
      (Subgroup.mem_normalizer_iff.mp (hL1N hl) y).mp hy
  have hYleZ : u3Y L1 L2 S ≤ Z2 L1 L2 S := by
    rw [u3Y]
    exact inf_le_left
  have hXleQ2 : u3X1 L1 L2 S ≤ Q2 L1 L2 S := by
    calc u3X1 L1 L2 S = u3Y L1 L2 S := hXeqY
      _ ≤ Z2 L1 L2 S := hYleZ
      _ ≤ Q2 L1 L2 S := omegaOneCenterOf_le (Q2 L1 L2 S)
  have hsup : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = Q2 L1 L2 S :=
    sup_eq_right.mpr hXleQ2
  exact str86_u3X1_sup_q2_ne hF hSB hk hFc hU3 hn hL2 hZQ hser hsup


end CFSG.Quasithin.Stroth
