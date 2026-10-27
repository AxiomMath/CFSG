module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core

import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def str86Core (L1 L2 S : Subgroup G) : Subgroup G :=
  ⨅ h ∈ P2 L1 L2 S, MulAut.conj h • Q1 L1 L2 S

theorem mem_str86Core_iff {L1 L2 S : Subgroup G} {x : G} :
    x ∈ str86Core L1 L2 S ↔ ∀ h ∈ P2 L1 L2 S, h⁻¹ * x * h ∈ Q1 L1 L2 S := by
  simp only [str86Core, Subgroup.mem_iInf, mem_conj_smul_iff']

theorem str86_s_inf_conj_bigB_le_q2 {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    {g : G} (hg : g ∈ P2 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) :
    S ⊓ (MulAut.conj g • bigB L1 L2 S) ≤ Q2 L1 L2 S := by
  classical
  set B : Subgroup G := bigB L1 L2 S with hB
  have hSB_le : S ≤ B := le_sup_right
  have hSylB : IsSylowTwoOf S B :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSB_le le_sup_right
  have hSylgB : IsSylowTwoOf (MulAut.conj g • S) (MulAut.conj g • B) :=
    F7.isSylowTwoOf_conj hSylB g
  have hgBN : MulAut.conj g • B ≤ Subgroup.normalizer (MulAut.conj g • S : Set G) := by
    let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj g)
    have h := (Subgroup.map_mono (f := f) hSB).trans (Subgroup.le_normalizer_map (H := S) f)
    simpa [f, CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul] using h
  have hle_gSB : MulAut.conj g • S ≤ MulAut.conj g • B :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hSB_le
  have hNnormal : ((MulAut.conj g • S).subgroupOf (MulAut.conj g • B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle_gSB).mpr hgBN
  have hT2 : IsPGroup 2 ↥(S ⊓ (MulAut.conj g • B)) :=
    hF.1.h1.pgroup.to_le inf_le_left
  have hle : S ⊓ (MulAut.conj g • B) ≤ MulAut.conj g • S :=
    CFSG.Quasithin.Stroth.le_of_isSylowTwoOf_normal hSylgB hNnormal inf_le_right hT2
  have hTI := f112_sylow_inf_conj_eq_pCoreOf_right hF.toW hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩)) hg hgB
  calc S ⊓ (MulAut.conj g • B) ≤ S ⊓ (MulAut.conj g • S) := le_inf inf_le_left hle
    _ = Q2 L1 L2 S := hTI

theorem str86_exists_mem_mul_inv_mem_bigB {L1 L2 S : Subgroup G}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {g g' : G} (hg : g ∈ P2 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hg' : g' ∈ P2 L1 L2 S) (hg'B : g' ∉ bigB L1 L2 S) :
    ∃ s ∈ S, (s * g)⁻¹ * g' ∈ bigB L1 L2 S := by
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hidx : (bigB L1 L2 S).relIndex (P2 L1 L2 S) = (Q2 L1 L2 S).relIndex S + 1 := by
    rw [f112_relIndex_right_l2 hF.toW (by omega) hL2, str86_relIndex_q2_s hF.toW hSB hn hL2]
  exact exists_mem_mul_inv_mem_of_relIndex le_sup_right le_sup_right hQ2S hidx
    (fun _ hg hgB => str86_s_inf_conj_bigB_le_q2 hF hSB hn hL2 hg hgB) hg hgB hg' hg'B

theorem str86_exists_mem_p2_not_mem_bigB {L1 L2 S : Subgroup G}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ g ∈ P2 L1 L2 S, g ∉ bigB L1 L2 S := by
  by_contra hcon
  push Not at hcon
  have hle : P2 L1 L2 S ≤ bigB L1 L2 S := fun g hg => hcon g hg
  have h1 : (bigB L1 L2 S).relIndex (P2 L1 L2 S) = 1 := Subgroup.relIndex_eq_one.mpr hle
  rw [f112_relIndex_right_l2 hF.toW (by omega) hL2] at h1
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem le_normalizer_str86Core (L1 L2 S : Subgroup G) :
    P2 L1 L2 S ≤ Subgroup.normalizer (str86Core L1 L2 S : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [mem_str86Core_iff]
  constructor
  · intro hx h hh
    have := hx (p⁻¹ * h) ((P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hp) hh)
    have e : (p⁻¹ * h)⁻¹ * x * (p⁻¹ * h) = h⁻¹ * (p * x * p⁻¹) * h := by group
    rwa [e] at this
  · intro hx h hh
    have := hx (p * h) ((P2 L1 L2 S).mul_mem hp hh)
    have e : (p * h)⁻¹ * (p * x * p⁻¹) * (p * h) = h⁻¹ * x * h := by group
    rwa [e] at this

theorem z2_le_str86Core {L1 L2 S : Subgroup G} (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    Z2 L1 L2 S ≤ str86Core L1 L2 S := by
  intro z hz
  rw [mem_str86Core_iff]
  intro h hh
  have hN := SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) ((P2 L1 L2 S).inv_mem hh)
  have := (Subgroup.mem_normalizer_iff.mp hN z).mp hz
  rw [inv_inv] at this
  exact hZ this

theorem str86Core_le_q1 (L1 L2 S : Subgroup G) : str86Core L1 L2 S ≤ Q1 L1 L2 S := by
  intro x hx
  have := (mem_str86Core_iff.mp hx) 1 (P2 L1 L2 S).one_mem
  simpa using this

theorem str86Core_le_q2 {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    str86Core L1 L2 S ≤ Q2 L1 L2 S := by
  obtain ⟨g, hg, hgB⟩ := str86_exists_mem_p2_not_mem_bigB hF hn hL2
  have hTI := f112_sylow_inf_conj_eq_pCoreOf_right hF.toW hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩)) hg hgB
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  rw [← hTI]
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨hQ1S (str86Core_le_q1 L1 L2 S hx), ?_⟩
  rw [mem_conj_smul_iff']
  exact hQ1S ((mem_str86Core_iff.mp hx) g hg)

theorem str86_b2_core {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {W : Subgroup G} (hWQ1 : W ≤ Q1 L1 L2 S) (hWS : W ⊔ Q2 L1 L2 S = S)
    (hWc : ⁅Q1 L1 L2 S, W⁆ ≤ Z2 L1 L2 S) {g : G} (hg : g ∈ P2 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) :
    Q1 L1 L2 S ⊓ (MulAut.conj g • Q1 L1 L2 S) = str86Core L1 L2 S := by
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hBR : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  have hWN : W ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (hWQ1.trans hQ1S).trans
      (((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans (le_normalizer_pCoreOf 2 _))
  have hAQ : ∀ s ∈ S, ∃ a ∈ W, a⁻¹ * s ∈ Q2 L1 L2 S := by
    intro s hs
    rw [← hWS] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hWN).mp hs
    exact ⟨a, ha, by simpa using hb⟩
  exact inf_conj_eq_iInf_of_transitive (H := P2 L1 L2 S) (B := bigB L1 L2 S) (S := S)
    (Q := Q2 L1 L2 S) (R := Q1 L1 L2 S) (A := W) (Z := Z2 L1 L2 S) le_sup_right le_sup_right
    hQ2S (le_normalizer_pCoreOf 2 _)
    (fun _ hg hgB _ hg' hg'B => str86_exists_mem_mul_inv_mem_bigB hF hSB hn hL2 hg hgB hg' hg'B)
    hBR hWQ1 hAQ hZ (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)) hWc hg hgB

end CFSG.Quasithin.Stroth

end
