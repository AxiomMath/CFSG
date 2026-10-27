module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoModule

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_relIndex_q1_s {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    (Q1 L1 L2 S).relIndex S = (2 ^ k) ^ 3 := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hT : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hS1
  rcases hU3 with h | h
  · obtain ⟨eL⟩ := h
    have h := relIndex_pCoreOf_sylow_su (L := L1 ⊔ Q1 L1 L2 S) (T := S)
      hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
    rwa [pCoreOf_sup_pCoreOf hF.1] at h
  · obtain ⟨eL⟩ := h
    have h := relIndex_pCoreOf_sylow_psu (L := L1 ⊔ Q1 L1 L2 S) (T := S)
      hk hFc ((oTwoQuotSupEquiv hF.1).trans eL) hT
    rwa [pCoreOf_sup_pCoreOf hF.1] at h

theorem u3Y_le_z2 {L1 L2 S : Subgroup G} : u3Y L1 L2 S ≤ Z2 L1 L2 S := by
  rw [u3Y]
  exact inf_le_left

theorem map_mulDistrib_eq_smul (a : MulAut G) (H : Subgroup G) :
    H.map (MulDistribMulAction.toMonoidHom G a) = a • H := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem le_normalizer_q2_of_sylow {L1 L2 S : Subgroup G} :
    S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
  have hSP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  exact hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

theorem str86_u3Y_conj_centralizer_bound
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) {g : G} (hg : g ∈ L1 ⊔ S) :
    (Z2 L1 L2 S ⊓ Subgroup.centralizer
      (MulAut.conj g • u3Y L1 L2 S : Set G)).relIndex (Z2 L1 L2 S) ≤
        2 ^ k * 2 ^ n := by
  classical
  have hZ2Y : (u3Y L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ k :=
    (str86_z2_sup_q1_eq_X0 hF hSB hk hFc hU3 hZQ).choose_spec.2.2.2.2
  have hQ1Y : u3Y L1 L2 S ≤ Q1 L1 L2 S := by
    rw [u3Y]
    exact inf_le_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hYS : u3Y L1 L2 S ≤ S := (hQ1Y.trans hQ1S)
  have hbig : L1 ⊔ S ≤ L1 ⊔ bigB L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hYgS : u3Y L1 L2 S ≤ MulAut.conj g • S := by
    by_cases hgB : g ∈ bigB L1 L2 S
    · have hgN : g ∈ Subgroup.normalizer (S : Set G) := hSB hgB
      have hconj : MulAut.conj g • S = S := by
        rw [mulAut_conj_smul_eq_conjAct]
        exact Subgroup.conjAct_pointwise_smul_eq_self hgN
      rw [hconj]
      exact hYS
    · have hTI := f112_sylow_inf_conj_eq_pCoreOf_left hF.toW hSB
        (Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩)) (hbig hg) hgB
      have hQ1gS : Q1 L1 L2 S ≤ MulAut.conj g • S := by
        rw [← hTI]
        exact inf_le_right
      exact hQ1Y.trans hQ1gS
  have hgQ2gS : MulAut.conj g • Q2 L1 L2 S ≤ MulAut.conj g • S :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQ2S
  have hYNgQ : u3Y L1 L2 S ≤ Subgroup.normalizer
      (MulAut.conj g • Q2 L1 L2 S : Set G) := by
    have hSN : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S)
    let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj g)
    have hconjN : MulAut.conj g • S ≤ Subgroup.normalizer
        (MulAut.conj g • Q2 L1 L2 S : Set G) := by
      have h := (Subgroup.map_mono (f := f) hSN).trans
        (Subgroup.le_normalizer_map (H := Q2 L1 L2 S) (f := f))
      rw [map_mulDistrib_eq_smul] at h
      exact h
    exact hYgS.trans hconjN
  have hsecond := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := u3Y L1 L2 S) (K := MulAut.conj g • Q2 L1 L2 S) hYNgQ).2
  have hsup_le : u3Y L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S ≤ MulAut.conj g • S :=
    sup_le hYgS hgQ2gS
  have hle_rel : (MulAut.conj g • Q2 L1 L2 S).relIndex
      (u3Y L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S) ≤
        (MulAut.conj g • Q2 L1 L2 S).relIndex (MulAut.conj g • S) :=
    Subgroup.relIndex_le_of_le_right hsup_le (D15Proof.relIndex_ne_zero _ _)
  have hconjrel : (MulAut.conj g • Q2 L1 L2 S).relIndex (MulAut.conj g • S) =
      (Q2 L1 L2 S).relIndex S :=
    Subgroup.relIndex_pointwise_smul (MulAut.conj g) (Q2 L1 L2 S) S
  have hrelr : (Q2 L1 L2 S).relIndex S = 2 ^ n := str86_relIndex_q2_s hF.toW hSB hn hL2
  have hYK : (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (u3Y L1 L2 S) ≤ 2 ^ n := by
    calc (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (u3Y L1 L2 S)
        = (MulAut.conj g • Q2 L1 L2 S).relIndex
            (u3Y L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S) := hsecond.symm
      _ ≤ (MulAut.conj g • Q2 L1 L2 S).relIndex (MulAut.conj g • S) := hle_rel
      _ = (Q2 L1 L2 S).relIndex S := hconjrel
      _ = 2 ^ n := hrelr
  have hKcent : u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S ≤
      Subgroup.centralizer (MulAut.conj g • u3Y L1 L2 S : Set G) := by
    intro y hy
    obtain ⟨hyY, hyQ⟩ := Subgroup.mem_inf.mp hy
    have hQ2Z2 : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
    let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj g)
    have hgQ2 : MulAut.conj g • Q2 L1 L2 S ≤
        Subgroup.centralizer (MulAut.conj g • Z2 L1 L2 S : Set G) := by
      have h := (Subgroup.map_mono (f := f) hQ2Z2).trans
        (Subgroup.map_centralizer_le_centralizer_image (Z2 L1 L2 S : Set G) f)
      rw [map_mulDistrib_eq_smul] at h
      exact h
    have hYgZ : MulAut.conj g • u3Y L1 L2 S ≤ MulAut.conj g • Z2 L1 L2 S :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hc := Subgroup.mem_centralizer_iff.mp (hgQ2 hyQ) e (hYgZ he)
    exact hc
  have hKZ : u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S ≤ Z2 L1 L2 S :=
    inf_le_left.trans (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S))
  have hle_left : (Z2 L1 L2 S ⊓ Subgroup.centralizer
      (MulAut.conj g • u3Y L1 L2 S : Set G)).relIndex (Z2 L1 L2 S) ≤
        (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (Z2 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_left (le_inf hKZ hKcent) (D15Proof.relIndex_ne_zero _ _)
  have hmul : (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (Z2 L1 L2 S) =
      (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (u3Y L1 L2 S) *
        (u3Y L1 L2 S).relIndex (Z2 L1 L2 S) :=
    (Subgroup.relIndex_mul_relIndex (H := u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S)
      (K := u3Y L1 L2 S) (L := Z2 L1 L2 S) inf_le_left
      (u3Y_le_z2 (L1 := L1) (L2 := L2) (S := S))).symm
  calc (Z2 L1 L2 S ⊓ Subgroup.centralizer
        (MulAut.conj g • u3Y L1 L2 S : Set G)).relIndex (Z2 L1 L2 S)
      ≤ (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (Z2 L1 L2 S) := hle_left
    _ = (u3Y L1 L2 S ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex (u3Y L1 L2 S) *
          (u3Y L1 L2 S).relIndex (Z2 L1 L2 S) := hmul
    _ ≤ 2 ^ n * 2 ^ k := Nat.mul_le_mul hYK hZ2Y.le
    _ = 2 ^ k * 2 ^ n := Nat.mul_comm _ _
