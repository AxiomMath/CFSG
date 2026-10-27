module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Setup

import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2D
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Tools
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2U1
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Step3
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Step4
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_b2_false_of_relIndex_D_eq_q
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {W : Subgroup G} (hWQ1 : W ≤ Q1 L1 L2 S) (hWS : W ⊔ Q2 L1 L2 S = S)
    (hWc : ⁅Q1 L1 L2 S, W⁆ ≤ Z2 L1 L2 S)
    (hcore : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      Q1 L1 L2 S ⊓ (MulAut.conj h • Q1 L1 L2 S) = str86Core L1 L2 S)
    (hd : (str86Core L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = 2 ^ k) : False := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h4k : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hSQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S)
  have hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hQ2P2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  have hQ2le : Q2 L1 L2 S ≤ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S)
  have hKP2 : P2 L1 L2 S ≤ Subgroup.normalizer (str86Core L1 L2 S : Set G) :=
    le_normalizer_str86Core L1 L2 S
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  have hSP2 : S ≤ P2 L1 L2 S := hSB'.trans hBP2
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hn hL2
  have hHP2 : L2 ⊔ Q2 L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hKQ1 : str86Core L1 L2 S ≤ Q1 L1 L2 S := str86Core_le_q1 L1 L2 S
  have hSQ2 : ¬ S ≤ Q2 L1 L2 S := by
    intro hle
    have h' := str86_relIndex_q2_s hF.toW hSB hn hL2
    rw [Subgroup.relIndex_eq_one.mpr hle] at h'
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hNinf : Q2 L1 L2 S ≤
      Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hSQ1 (hQ2S hx)) y,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y]
  have hcommQ2le : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ Q2 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem ha hb)
      ((Q2 L1 L2 S).inv_mem ha)) ((Q2 L1 L2 S).inv_mem hb)
  have hstep := (str86_b2_relIndex_D hF hSB hk hFc hU3 hn hL2 hcore).2
  obtain ⟨X0, hmemX0, hQX0, -, hcommX0, hX0S⟩ := str86_exists_X0_commutator hF hSB hk hFc hU3
  have hBX0 : bigB L1 L2 S ≤ Subgroup.normalizer (X0 : Set G) := by
    rw [← hcommX0]
    refine F1.le_normalizer_sup (fun g hg => ?_) hBQ1
    have h := hSB hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
    rw [Subgroup.map_commutator, h]
  have hX0D : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S = X0 := by
    intro h hh hhB
    have hrel := hstep h hh hhB
    rw [hd] at hrel
    have hXS : (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ Q1 L1 L2 S ≤ S :=
      sup_le (inf_le_right.trans hQ2S) hQ1S
    rcases str86_q1_trichotomy hF hSB hk hFc hU3 le_sup_right hXS
      (str86_bigB_le_normalizer_D_sup hF hSB h1 hn hL2 hh hhB) with hX | hX | hX
    · rw [hX, Subgroup.relIndex_self] at hrel
      omega
    · rw [hX, str86_relIndex_q1_s hF hSB hk hFc hU3] at hrel
      have hlt : 2 ^ k < (2 ^ k) ^ 3 := by
        calc 2 ^ k = (2 ^ k) ^ 1 := (pow_one _).symm
          _ < (2 ^ k) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    · ext t
      rw [hmemX0]
      exact ⟨fun ht => ⟨hXS ht, (hX t (hXS ht)).mp ht⟩, fun ⟨htS, ht2⟩ => (hX t htS).mpr ht2⟩
  have hED : ∀ h ∈ P2 L1 L2 S, h ∉ bigB L1 L2 S →
      X0 ⊓ Q2 L1 L2 S = (MulAut.conj h • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
    intro h hh hhB
    rw [← hX0D h hh hhB]
    exact sup_inf_eq_sup_inf_of_le_normalizer inf_le_right ((inf_le_right.trans hQ2S).trans hSQ1)
  set E : Subgroup G := X0 ⊓ Q2 L1 L2 S with hEdef
  have hQE : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ E := inf_le_inf_right _ hQX0
  have hconjE : ∀ g ∈ P2 L1 L2 S, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    by_cases hgB : g ∈ bigB L1 L2 S
    · obtain ⟨hx0, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBX0 hgB) x).mp hx0,
        (Subgroup.mem_normalizer_iff.mp (hQ2P2 hg) x).mp hx2⟩
    · have hginv : g⁻¹ ∈ P2 L1 L2 S := (P2 L1 L2 S).inv_mem hg
      have hginvB : g⁻¹ ∉ bigB L1 L2 S := fun h => hgB (by simpa using (bigB L1 L2 S).inv_mem h)
      have hx' := hx
      rw [hED g⁻¹ hginv hginvB] at hx'
      obtain ⟨d, hd', q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        (inf_le_right.trans (str86_q2_le_normalizer_D hginv hQ2S))).mp hx'
      rw [hED g hg hgB]
      obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.mp hd'
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.mp hq
      rw [mem_conj_smul_iff', inv_inv] at hd1
      have hgd : g * d * g⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
        Subgroup.mem_inf.mpr ⟨hd1, (Subgroup.mem_normalizer_iff.mp (hQ2P2 hg) d).mp hd2⟩
      have hgq : g * q * g⁻¹ ∈ (MulAut.conj g • Q1 L1 L2 S) ⊓ Q2 L1 L2 S := by
        refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp (hQ2P2 hg) q).mp hq2⟩
        rw [mem_conj_smul_iff']
        have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
        rw [e]
        exact hq1
      have e : g * (d * q) * g⁻¹ = (g * d * g⁻¹) * (g * q * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgd) (Subgroup.mem_sup_left hgq)
  have hEN : P2 L1 L2 S ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconjE g hg x hx, fun hx => ?_⟩
    have h := hconjE g⁻¹ ((P2 L1 L2 S).inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h
  have hEQ2 : ∀ x ∈ E, ∀ m ∈ Q2 L1 L2 S, ⁅x, m⁆ ∈ str86Core L1 L2 S := by
    intro x hx m hm
    obtain ⟨h, hh, hhB⟩ := str86_exists_mem_p2_not_mem_bigB hF hn hL2
    rw [← hcore h hh hhB]
    refine Subgroup.mem_inf.mpr ⟨hX0S (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mp hx).1 (hQ2S hm)), ?_⟩
    rw [mem_conj_smul_iff']
    have hx' : h⁻¹ * x * h ∈ E := by
      have h' := hconjE h⁻¹ ((P2 L1 L2 S).inv_mem hh) x hx
      rwa [inv_inv] at h'
    have hm' : h⁻¹ * m * h ∈ Q2 L1 L2 S := by
      have h' := (Subgroup.mem_normalizer_iff.mp (hQ2P2 ((P2 L1 L2 S).inv_mem hh)) m).mp hm
      rwa [inv_inv] at h'
    have e : h⁻¹ * ⁅x, m⁆ * h = ⁅h⁻¹ * x * h, h⁻¹ * m * h⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hX0S (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hx').1 (hQ2S hm'))
  have hHE : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (E : Set G) := hHP2.trans hEN
  set C1 : Subgroup G := centralizerMod E (L2 ⊔ Q2 L1 L2 S) (Q2 L1 L2 S) with hC1def
  have hC1n : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (C1 : Set G) :=
    le_normalizer_centralizerMod hHE Subgroup.le_normalizer (hHP2.trans hQ2P2)
  have hQ1C1 : Q1 L1 L2 S ≤ C1 := by
    intro x hx
    have hxS : x ∈ S := hQ1S hx
    refine mem_centralizerMod.mpr ⟨hSH hxS, hHE (hSH hxS), fun u hu => hQE ?_⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hSQ1 (hQ2S hu)) x⁻¹).mp
        ((Q1 L1 L2 S).inv_mem hx)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]
      exact (Q1 L1 L2 S).mul_mem hx h
    · have h := (Subgroup.mem_normalizer_iff.mp (hQ2P2 (hSP2 hxS)) u).mp hu
      exact (Q2 L1 L2 S).mul_mem h ((Q2 L1 L2 S).inv_mem hu)
  have hQ2C1 : Q2 L1 L2 S ≤ C1 := by
    intro x hx
    have hxH : x ∈ L2 ⊔ Q2 L1 L2 S := (le_sup_right : Q2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S) hx
    refine mem_centralizerMod.mpr ⟨hxH, hHE hxH, fun u hu => ?_⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := Subgroup.commutator_mem_commutator (hQ2S hx) (hQ2S hu)
      rw [commutatorElement_def] at h
      exact (le_sup_left.trans hcommX0.le) h
    · exact (Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem hx hu)
        ((Q2 L1 L2 S).inv_mem hx)) ((Q2 L1 L2 S).inv_mem hu)
  have hSC1 : S ≤ C1 := hWS.symm.le.trans (sup_le (hWQ1.trans hQ1C1) hQ2C1)
  have hC1eq : C1 = L2 ⊔ Q2 L1 L2 S := by
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 (centralizerMod_le_left _ _ _) hC1n
      hQ2C1 with h | h
    · exact absurd (hSC1.trans h.le) hSQ2
    · exact h
  set C2 : Subgroup G := centralizerMod (str86Core L1 L2 S) (Q2 L1 L2 S) (L2 ⊔ Q2 L1 L2 S)
    with hC2def
  have hcommC2 : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ C2 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ Q2 L1 L2 S :=
      hcommQ2le (Subgroup.commutator_mem_commutator hx hy)
    refine mem_centralizerMod.mpr ⟨hxy, hKP2 (hQ2le hxy), fun g hg => ?_⟩
    have hgC1 : g ∈ C1 := by rw [hC1eq]; exact hg
    have he : ∀ z ∈ Q2 L1 L2 S, ⁅z⁻¹, g⁆ ∈ E := by
      intro z hz
      have h' := (mem_centralizerMod.mp hgC1).2.2 z hz
      have e : ⁅z⁻¹, g⁆ = z⁻¹ * (g * z * g⁻¹ * z⁻¹) * z⁻¹⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hEN (hQ2le ((Q2 L1 L2 S).inv_mem hz))) _).mp h'
    have key := commutatorElement_mul_mul_mul_inv_mem (X := Q2 L1 L2 S) (Z := E)
      (K := str86Core L1 L2 S) inf_le_right (hQ2le.trans hKP2) hEQ2 hx hy (he x hx) (he y hy)
    have e : ⁅x * ⁅x⁻¹, g⁆, y * ⁅y⁻¹, g⁆⁆ * ⁅x, y⁆⁻¹ = g * ⁅x, y⁆ * g⁻¹ * ⁅x, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e] at key
    have e2 : ⁅x, y⁆ * g * ⁅x, y⁆⁻¹ * g⁻¹ = (g * ⁅x, y⁆ * g⁻¹ * ⁅x, y⁆⁻¹)⁻¹ := by group
    rw [e2]
    exact (str86Core L1 L2 S).inv_mem key
  have hEdec : E ≤ ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
    have hS21 : S = Q2 L1 L2 S ⊔ Q1 L1 L2 S :=
      le_antisymm (hWS.symm.le.trans (sup_le (hWQ1.trans le_sup_right) le_sup_left))
        (sup_le hQ2S hQ1S)
    have hX0le : X0 ≤ ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ⊔ Q1 L1 L2 S := by
      rw [← hcommX0]
      refine sup_le ?_ le_sup_right
      have h := commutator_sup_le_sup_of_le_normalizer (D := Q2 L1 L2 S) (Q := Q1 L1 L2 S)
        (hQ2S.trans hSQ1)
      rwa [← hS21] at h
    calc E ≤ (⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ⊔ Q1 L1 L2 S) ⊓ Q2 L1 L2 S := inf_le_inf_right _ hX0le
      _ = ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) :=
        sup_inf_eq_sup_inf_of_le_normalizer hcommQ2le (hcommQ2le.trans (hQ2S.trans hSQ1))
  set C3 : Subgroup G := centralizerMod (str86Core L1 L2 S) (L2 ⊔ Q2 L1 L2 S) E with hC3def
  have hWC3 : W ≤ C3 := by
    intro w hw
    have hwS : w ∈ S := hQ1S (hWQ1 hw)
    refine mem_centralizerMod.mpr ⟨hSH hwS, hKP2 (hSP2 hwS), fun y hy => ?_⟩
    obtain ⟨c, hc, d, hd', rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer (hcommQ2le.trans hNinf)).mp (hEdec hy)
    have hc1 : ⁅w, c⁆ ∈ str86Core L1 L2 S := by
      have h' := (mem_centralizerMod.mp (hcommC2 hc)).2.2 w (hSH hwS)
      have e : ⁅w, c⁆ = (c * w * c⁻¹ * w⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (str86Core L1 L2 S).inv_mem h'
    have hc2 : ⁅w, d⁆ ∈ str86Core L1 L2 S := by
      have h' := hWc (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hd').1 hw)
      rw [← commutatorElement_inv]
      exact (str86Core L1 L2 S).inv_mem (z2_le_str86Core hZ h')
    have e : w * (c * d) * w⁻¹ * (c * d)⁻¹ = ⁅w, c⁆ * (c * ⁅w, d⁆ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (str86Core L1 L2 S).mul_mem hc1
      ((Subgroup.mem_normalizer_iff.mp (hKP2 (hQ2le (hcommQ2le hc))) _).mp hc2)
  have hC3Q : ¬ C3 ≤ Q2 L1 L2 S := fun hle =>
    hSQ2 (hWS.symm.le.trans (sup_le (hWC3.trans hle) le_rfl))
  have hOC3 : oTwoUpper (L2 ⊔ Q2 L1 L2 S) ≤ C3 :=
    str86_oTwoUpper_le_of_normal hF hn hL2 (centralizerMod_le_left _ _ _)
      (le_normalizer_centralizerMod (hHP2.trans hKP2) Subgroup.le_normalizer hHE) hC3Q
  obtain ⟨ω, hωL, hω3⟩ := exists_orderOf_three_of_isL2Quot (by omega) hL2
  have hωO : ω ∈ oTwoUpper (L2 ⊔ Q2 L1 L2 S) :=
    mem_oTwoUpper_of_odd ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S) hωL) (by rw [hω3]; decide)
  have hOsup : oTwoUpper (L2 ⊔ Q2 L1 L2 S) ⊔ Q2 L1 L2 S = L2 ⊔ Q2 L1 L2 S := by
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 (sup_le (oTwoUpper_le _) le_sup_right)
      (F1.le_normalizer_sup (le_normalizer_oTwoUpper _) (hHP2.trans hQ2P2)) le_sup_right
      with h | h
    · exfalso
      have hωQ : ω ∈ Q2 L1 L2 S := h.le (Subgroup.mem_sup_left hωO)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 (P2 L1 L2 S)) ⟨ω, hωQ⟩
      have hj' : ω ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hdvd : 3 ∣ 2 ^ j := by
        rw [← hω3]
        exact orderOf_dvd_of_pow_eq_one hj'
      have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
      exact absurd h2 (by norm_num)
    · exact h
  have hexg : ∃ g ∈ oTwoUpper (L2 ⊔ Q2 L1 L2 S), g ∉ bigB L1 L2 S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h, hh, hhB⟩ := str86_exists_mem_p2_not_mem_bigB hF hn hL2
    apply hhB
    have hHB : L2 ⊔ Q2 L1 L2 S ≤ bigB L1 L2 S := by
      rw [← hOsup]
      exact sup_le (fun g hg => hcon g hg) (hQ2S.trans hSB')
    exact (sup_le ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S).trans hHB) le_rfl :
      P2 L1 L2 S ≤ bigB L1 L2 S) hh
  obtain ⟨g, hgO, hgB⟩ := hexg
  have hgP2 : g ∈ P2 L1 L2 S := hHP2 (oTwoUpper_le _ hgO)
  have hle : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ str86Core L1 L2 S := by
    intro x hx
    have hxE : x ∈ E := hQE hx
    have hc := (mem_centralizerMod.mp (hOC3 hgO)).2.2 x hxE
    have hgx : g * x * g⁻¹ ∈ Q1 L1 L2 S ⊓ (MulAut.conj g • Q1 L1 L2 S) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
        rw [e]
        exact (Q1 L1 L2 S).mul_mem (hKQ1 hc) (Subgroup.mem_inf.mp hx).1
      · rw [mem_conj_smul_iff']
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
        exact (Subgroup.mem_inf.mp hx).1
    rw [hcore g hgP2 hgB] at hgx
    have h' := (Subgroup.mem_normalizer_iff.mp (hKP2 ((P2 L1 L2 S).inv_mem hgP2)) _).mp hgx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h'
  rw [Subgroup.relIndex_eq_one.mpr hle] at hd
  omega

end CFSG.Quasithin.Stroth

end
