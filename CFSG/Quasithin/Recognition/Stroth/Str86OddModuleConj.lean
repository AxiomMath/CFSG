module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_conj_not_mem_bigB {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {g a : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) (haS : a ∈ S)
    (haQ : a ∉ Q1 L1 L2 S) :
    g⁻¹ * a * g ∉ bigB L1 L2 S := by
  intro hgaB
  have hSB_le : S ≤ bigB L1 L2 S := le_sup_right
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF.toW) hSB_le hBP1
  have hNnormal : ((S.subgroupOf (bigB L1 L2 S))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB_le).mpr hSB
  have hTleB : Subgroup.zpowers (g⁻¹ * a * g) ≤ bigB L1 L2 S :=
    Subgroup.zpowers_le.mpr hgaB
  have hSconj : IsPGroup 2 (MulAut.conj g⁻¹ • S : Subgroup G) :=
    hF.1.h1.pgroup.map (MulAut.conj g⁻¹).toMonoidHom
  have hmemConj : g⁻¹ * a * g ∈ MulAut.conj g⁻¹ • S := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g⁻¹)⁻¹ • (g⁻¹ * a * g) = a := by
      rw [← map_inv]
      simp [MulAut.conj_apply]
      group
    rwa [hinv]
  have hTp : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * a * g)) :=
    hSconj.to_le (Subgroup.zpowers_le.mpr hmemConj)
  have hTleS : Subgroup.zpowers (g⁻¹ * a * g) ≤ S :=
    le_of_isSylowTwoOf_normal hSylB hNnormal hTleB hTp
  have hgaS : g⁻¹ * a * g ∈ S := hTleS (Subgroup.mem_zpowers _)
  have hconj : a ∈ MulAut.conj g • S := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g)⁻¹ • a = g⁻¹ * a * g := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rwa [hinv]
  have hTI : S ⊓ (MulAut.conj g • S) = Q1 L1 L2 S := by
    refine f112_sylow_inf_conj_eq_pCoreOf_left hF.toW hSB ?_ hg hgB
    exact Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩)
  exact haQ (hTI ▸ Subgroup.mem_inf.mpr ⟨haS, hconj⟩)

private theorem r2_s_inf_conj_bigB_le_q1
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {g : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) :
    S ⊓ (MulAut.conj g • bigB L1 L2 S) ≤ Q1 L1 L2 S := by
  set B : Subgroup G := bigB L1 L2 S with hB
  have hSB_le : S ≤ B := le_sup_right
  have hSylB : IsSylowTwoOf S B :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF.toW) hSB_le le_sup_right
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
  have h1 : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1) :=
    Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩)
  have hTI := f112_sylow_inf_conj_eq_pCoreOf_left hF.toW hSB h1 hg hgB
  calc S ⊓ (MulAut.conj g • B) ≤ S ⊓ (MulAut.conj g • S) := le_inf inf_le_left hle
    _ = Q1 L1 L2 S := hTI

theorem str86_exists_q2_mul_inv_mem
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {g h : G} (hg : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) (hh : h ∈ P1 L1 L2 S)
    (hhB : h ∉ bigB L1 L2 S) :
    ∃ u ∈ Q2 L1 L2 S, (u * g)⁻¹ * h ∈ bigB L1 L2 S := by
  classical
  have hU3big : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hspan : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf (n := m) hF.toW hSB (Or.inr hU3big) hm hL2
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSP1 : S ≤ P1 L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hidx : (bigB L1 L2 S).relIndex (P1 L1 L2 S) = (Q1 L1 L2 S).relIndex S + 1 := by
    change (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = (Q1 L1 L2 S).relIndex S + 1
    rw [f112_relIndex_bigB_of_u3 hF hk hFc hU3, str86_relIndex_q1_s hF hSB hk hFc hU3]
  obtain ⟨s, hsS, hsB⟩ := exists_mem_mul_inv_mem_of_relIndex
    (H := P1 L1 L2 S) (B := bigB L1 L2 S) (S := S) (Q := Q1 L1 L2 S)
    le_sup_right le_sup_right hQ1S hidx
    (fun g hg hgB => r2_s_inf_conj_bigB_le_q1 hF hSB hk hFc hU3 hg hgB) hg hgB hh hhB
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ2N : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (hQ2S.trans hSP1).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hs : s ∈ Q1 L1 L2 S ⊔ Q2 L1 L2 S := by rw [hspan]; exact hsS
  obtain ⟨q, hq, u, hu, hqu⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N).mp hs
  have huP1 : u * g ∈ P1 L1 L2 S :=
    (P1 L1 L2 S).mul_mem (hSP1 (hQ2S hu)) hg
  have hcQ1 : (u * g)⁻¹ * q * (u * g) ∈ Q1 L1 L2 S := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) ((P1 L1 L2 S).inv_mem huP1)) q).mp hq
    simpa using h
  have hcB : (u * g)⁻¹ * q * (u * g) ∈ bigB L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S) (hQ1S hcQ1)
  refine ⟨u, hu, ?_⟩
  have heq : (u * g)⁻¹ * h = ((u * g)⁻¹ * q * (u * g)) * ((s * g)⁻¹ * h) := by
    rw [hqu]; group
  rw [heq]
  exact (bigB L1 L2 S).mul_mem hcB hsB

private theorem r3_conj_mem_of_mem_bigB {L1 L2 S X : Subgroup G}
    (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    {g h x : G} (hhB : g⁻¹ * h ∈ bigB L1 L2 S) (hx : g⁻¹ * x * g ∈ X) :
    h⁻¹ * x * h ∈ X := by
  have hmem := (Subgroup.mem_normalizer_iff.mp
    (hXB ((bigB L1 L2 S).inv_mem hhB)) (g⁻¹ * x * g)).mp hx
  have e : h⁻¹ * x * h = (g⁻¹ * h)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * h) := by group
  rw [e]
  simpa using hmem

private theorem r3_conj_mem_of_not_mem_bigB
    {L1 L2 S X : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    (hXQ : Q2 L1 L2 S ≤ Subgroup.centralizer (X : Set G))
    {g y h x : G} (hg : g ∈ P1 L1 L2 S) (hy : y ∈ P1 L1 L2 S) (hh : h ∈ P1 L1 L2 S)
    (hgy : g⁻¹ * y ∉ bigB L1 L2 S) (hhB : g⁻¹ * h ∉ bigB L1 L2 S)
    (hx : g⁻¹ * x * g ∈ X) (hxy : y⁻¹ * x * y ∈ X) :
    h⁻¹ * x * h ∈ X := by
  obtain ⟨u, huQ2, hub⟩ := str86_exists_q2_mul_inv_mem hF hSB hk hFc hU3 hm hL2
    (g := g⁻¹ * y) (h := g⁻¹ * h)
    ((P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hg) hy) hgy
    ((P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hg) hh) hhB
  set b : G := (u * (g⁻¹ * y))⁻¹ * (g⁻¹ * h) with hbdef
  have hbB : b ∈ bigB L1 L2 S := hub
  have hgeq : g⁻¹ * h = u * (g⁻¹ * y) * b := by
    rw [hbdef]; group
  have hx'' : (g⁻¹ * y)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * y) ∈ X := by
    have e : (g⁻¹ * y)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * y) = y⁻¹ * x * y := by group
    rwa [e]
  have hucomm : u * (g⁻¹ * x * g) = (g⁻¹ * x * g) * u :=
    (Subgroup.mem_centralizer_iff.mp (hXQ huQ2) (g⁻¹ * x * g) hx).symm
  have huC : u⁻¹ * (g⁻¹ * x * g) * u = g⁻¹ * x * g := by
    calc u⁻¹ * (g⁻¹ * x * g) * u = u⁻¹ * ((g⁻¹ * x * g) * u) := by group
      _ = u⁻¹ * (u * (g⁻¹ * x * g)) := by rw [← hucomm]
      _ = g⁻¹ * x * g := by group
  have hbX : b⁻¹ * ((g⁻¹ * y)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * y)) * b ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hXB ((bigB L1 L2 S).inv_mem hbB))
      ((g⁻¹ * y)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * y))).mp hx''
    simpa using this
  have e : h⁻¹ * x * h =
      b⁻¹ * ((g⁻¹ * y)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * y)) * b := by
    have e1 : h⁻¹ * x * h = (g⁻¹ * h)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * h) := by group
    rw [e1, hgeq]
    have e2 : (u * (g⁻¹ * y) * b)⁻¹ * (g⁻¹ * x * g) * (u * (g⁻¹ * y) * b) =
        b⁻¹ * ((g⁻¹ * y)⁻¹ * (u⁻¹ * (g⁻¹ * x * g) * u) * (g⁻¹ * y)) * b := by
      group
    rw [e2, huC]
  rw [e]
  exact hbX

private theorem r3_conj_mem
    {L1 L2 S X : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    (hXQ : Q2 L1 L2 S ≤ Subgroup.centralizer (X : Set G))
    {g y h x : G} (hg : g ∈ P1 L1 L2 S) (hy : y ∈ P1 L1 L2 S) (hh : h ∈ P1 L1 L2 S)
    (hgy : g⁻¹ * y ∉ bigB L1 L2 S)
    (hx : g⁻¹ * x * g ∈ X) (hxy : y⁻¹ * x * y ∈ X) :
    h⁻¹ * x * h ∈ X := by
  by_cases hhB : g⁻¹ * h ∈ bigB L1 L2 S
  · exact r3_conj_mem_of_mem_bigB hXB hhB hx
  · exact r3_conj_mem_of_not_mem_bigB hF hSB hk hFc hU3 hm hL2 hXB hXQ hg hy hh hgy hhB hx hxy

theorem str86_conj_inf_conj_eq_iInf
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {X : Subgroup G} (hXB : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G))
    (hXQ : Q2 L1 L2 S ≤ Subgroup.centralizer (X : Set G))
    {g y : G} (hg : g ∈ P1 L1 L2 S) (hy : y ∈ P1 L1 L2 S) (hgy : g⁻¹ * y ∉ bigB L1 L2 S) :
    MulAut.conj g • X ⊓ MulAut.conj y • X =
      ⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • X := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxg, hxy⟩ := hx
    have hxg' : g⁻¹ * x * g ∈ X := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxg
      have hinv : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
        rw [MulAut.smul_def, MulAut.conj_inv_apply]
      rwa [hinv] at hxg
    have hxy' : y⁻¹ * x * y ∈ X := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxy
      have hinv : (MulAut.conj y)⁻¹ • x = y⁻¹ * x * y := by
        rw [MulAut.smul_def, MulAut.conj_inv_apply]
      rwa [hinv] at hxy
    refine Subgroup.mem_iInf.mpr fun h => Subgroup.mem_iInf.mpr fun hh => ?_
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj h)⁻¹ • x = h⁻¹ * x * h := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rw [hinv]
    exact r3_conj_mem hF hSB hk hFc hU3 hm hL2 hXB hXQ hg hy hh hgy hxg' hxy'
  · exact le_inf (iInf₂_le g hg) (iInf₂_le y hy)

end CFSG.Quasithin.Stroth

end
