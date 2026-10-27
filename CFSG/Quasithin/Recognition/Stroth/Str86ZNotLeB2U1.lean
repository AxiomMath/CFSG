module


import CFSG.Quasithin.Recognition.Stroth.Str86U3SylowNonab
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_q1_trichotomy {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {X : Subgroup G} (hQX : Q1 L1 L2 S ≤ X) (hXS : X ≤ S)
    (hXN : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G)) :
    X = Q1 L1 L2 S ∨ X = S ∨ ∀ t ∈ S, t ∈ X ↔ t ^ 2 ∈ Q1 L1 L2 S := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hVU3Lhat : VU3Big (L1 ⊔ Q1 L1 L2 S) := by
    refine ⟨k, hk, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hXN' : (L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    intro g hg
    obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgP1 : g ∈ P1 L1 L2 S :=
      (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S) (pCoreOf_le 2 (P1 L1 L2 S))) hgL
    exact hXN (str86_p1_inf_normalizer_le_bigB hF.toW hSB (Subgroup.mem_inf.mpr ⟨hgP1, hgN⟩))
  have htrich := vertex_trichotomy (L := L1 ⊔ Q1 L1 L2 S) (T := S) (X := X)
    (Or.inr hVU3Lhat) hT (by rw [pCoreOf_sup_pCoreOf hF.1]; exact hQX) hXS hXN'
  rwa [pCoreOf_sup_pCoreOf hF.1] at htrich

theorem str86_exists_X0_commutator {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    ∃ X0 : Subgroup G, (∀ t, t ∈ X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S) ∧ Q1 L1 L2 S ≤ X0 ∧
      (Q1 L1 L2 S).relIndex X0 = 2 ^ k ∧ ⁅S, S⁆ ⊔ Q1 L1 L2 S = X0 ∧
      ⁅X0, S⁆ ≤ Q1 L1 L2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB
      (Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩))
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hqLhat : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) (2 ^ k) := by
    refine Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  obtain ⟨X0, hmemX0, hQX0, hrelX0, -⟩ := exists_X0 hqLhat hT
  rw [pCoreOf_sup_pCoreOf hF.1] at hmemX0 hQX0 hrelX0
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSp : IsPGroup 2 S := hF.1.h1.pgroup
  have hSQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S)
  have hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hQ1ne : Q1 L1 L2 S ≠ S := by
    intro h
    have hrel := str86_relIndex_q1_s hF hSB hk hFc hU3
    rw [h, Subgroup.relIndex_self] at hrel
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h64 : 64 ≤ (2 ^ k) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left this 3
    omega
  have hnonab := str86_not_commutator_le_q1 hF hSB hk hFc hU3
  have hthird : ∀ X : Subgroup G, (∀ t ∈ S, t ∈ X ↔ t ^ 2 ∈ Q1 L1 L2 S) → X ≤ S → X = X0 := by
    intro X hX hXS
    ext t
    rw [hmemX0]
    exact ⟨fun ht => ⟨hXS ht, (hX t (hXS ht)).mp ht⟩, fun ⟨htS, ht2⟩ => (hX t htS).mpr ht2⟩
  have hcommS : ⁅S, S⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hBcomm : bigB L1 L2 S ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) := by
    intro g hg
    have h := hSB hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
    rw [Subgroup.map_commutator, h]
  have hcommeq : ⁅S, S⁆ ⊔ Q1 L1 L2 S = X0 := by
    rcases str86_q1_trichotomy hF hSB hk hFc hU3 (le_sup_right : Q1 L1 L2 S ≤ ⁅S, S⁆ ⊔ _)
      (sup_le hcommS hQ1S) (F1.le_normalizer_sup hBcomm hBQ1) with h | h | h
    · exact absurd (le_sup_left.trans h.le) hnonab
    · have hlt := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup (p := 2) (X := S) (Q := S)
        (V := Q1 L1 L2 S) le_rfl hSp Subgroup.le_normalizer hSQ1 hQ1S hQ1ne
      exact absurd h hlt.ne
    · exact hthird _ h (sup_le hcommS hQ1S)
  set Z : Subgroup G := centralizerMod (Q1 L1 L2 S) S S with hZdef
  have hZS : Z ≤ S := centralizerMod_le_left _ _ _
  have hQZ : Q1 L1 L2 S ≤ Z := by
    intro x hx
    refine mem_centralizerMod.mpr ⟨hQ1S hx, Subgroup.le_normalizer hx, fun u hu => ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hSQ1 hu) x⁻¹).mp ((Q1 L1 L2 S).inv_mem hx)
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact (Q1 L1 L2 S).mul_mem hx h
  have hZN : bigB L1 L2 S ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_centralizerMod hBQ1 hSB hSB
  have hZeq : Z = X0 := by
    rcases str86_q1_trichotomy hF hSB hk hFc hU3 hQZ hZS hZN with h | h | h
    · exfalso
      obtain ⟨s, hs, hsQ, hsc⟩ := CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
        (p := 2) (P := S) (Q := S) (K₀ := Q1 L1 L2 S) hSp hSp (lt_of_le_of_ne hQ1S hQ1ne)
        hSQ1 Subgroup.le_normalizer hSQ1
      apply hsQ
      rw [← h]
      refine mem_centralizerMod.mpr ⟨hs, hSQ1 hs, fun u hu => ?_⟩
      have h' := (Q1 L1 L2 S).inv_mem (hsc u hu)
      rwa [commutatorElement_inv, commutatorElement_def] at h'
    · exfalso
      apply hnonab
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haZ : a ∈ Z := by rw [h]; exact ha
      have h' := (mem_centralizerMod.mp haZ).2.2 b hb
      rwa [commutatorElement_def]
    · exact hthird _ h hZS
  refine ⟨X0, hmemX0, hQX0, hrelX0, hcommeq, ?_⟩
  rw [Subgroup.commutator_le]
  intro x hx u hu
  have hxZ : x ∈ Z := by rw [hZeq]; exact hx
  have h := (mem_centralizerMod.mp hxZ).2.2 u hu
  rwa [commutatorElement_def]

end CFSG.Quasithin.Stroth

end
