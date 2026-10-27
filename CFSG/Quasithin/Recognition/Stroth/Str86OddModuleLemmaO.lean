module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleTransport

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_orth_le_q2_of_isMaxElemAbelian
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {E : Subgroup G} (hEmax : IsMaxElemAbelian S E) :
    E ≤ Q2 L1 L2 S := by
  classical
  by_contra hEQ
  have hcase := str86_caseI_basics hF hSB ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
    hB2 ⟨m, hL2⟩ hZI
  have hQ2S : Q2 L1 L2 S ≤ S := by
    rw [← hcase.2.2.2.1]
    exact inf_le_left
  have hZ2S : Z2 L1 L2 S ≤ S := (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hT1 := str86_orth_pow_mul_relIndex_le hF hSB hm hL2 hstepW hE e hl hml horth
    hEmax.1 hEQ
  have hmono : (Subgroup.centralizer (E : Set G)).relIndex W ≤
      (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_right hWZ2 (D15Proof.relIndex_ne_zero _ _)
  have hasm : (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) ≤
      (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E :=
    Ch3g316.relIndex_centralizer_le hEmax hZ2S hZ2e
  have hCZ : Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ E = Q2 L1 L2 S ⊓ E := by
    rw [show Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ E =
        Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ (S ⊓ E) by
      rw [inf_eq_right.mpr hEmax.1],
      ← inf_assoc, inf_comm (Subgroup.centralizer (Z2 L1 L2 S : Set G)) S,
      hcase.2.2.2.1]
  have hidx3 : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E =
      (Q2 L1 L2 S).relIndex E := by
    rw [show (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E =
        (Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ E).relIndex E from
      (Subgroup.inf_relIndex_right _ _).symm, hCZ, Subgroup.inf_relIndex_right]
  have hchain : 2 ^ l * (Q2 L1 L2 S).relIndex E ≤ (Q2 L1 L2 S).relIndex E :=
    hT1.trans (hmono.trans (hasm.trans (le_of_eq hidx3)))
  have hn : (Q2 L1 L2 S).relIndex E ≠ 0 := D15Proof.relIndex_ne_zero _ _
  have hle1 : 2 ^ l ≤ 1 := by
    have h' : 2 ^ l * (Q2 L1 L2 S).relIndex E ≤ 1 * (Q2 L1 L2 S).relIndex E := by
      simpa using hchain
    exact Nat.le_of_mul_le_mul_right h' (Nat.pos_of_ne_zero hn)
  have hl1 : 1 ≤ l := by omega
  have h2l : 2 ≤ 2 ^ l := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl1
  omega

private theorem o2_eq_of_le_of_relIndex_eq {A H K : Subgroup G}
    (hHA : H ≤ A) (hKA : K ≤ A) (hHK : H ≤ K)
    (hrel : H.relIndex A = K.relIndex A) : H = K := by
  haveI : H.IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hH := Subgroup.relIndex_mul_card H A
  have hK := Subgroup.relIndex_mul_card K A
  rw [inf_eq_left.mpr hHA] at hH
  rw [inf_eq_left.mpr hKA] at hK
  have hr : H.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero
  have hcard : Nat.card H = Nat.card K := by
    refine Nat.mul_left_cancel (Nat.pos_of_ne_zero hr) ?_
    rw [hH, hrel]
    exact hK.symm
  exact Subgroup.eq_of_le_of_card_ge hHK (le_of_eq hcard.symm)

private theorem o2s_pow_mul_relIndex_le_centralizer
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {A : Subgroup G} {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgA : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    2 ^ l * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) ≤
      (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) := by
  classical
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hgQ1 : g ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg
  have hconjQ1 : MulAut.conj g • Q1 L1 L2 S = Q1 L1 L2 S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hgQ1
  have hDS : A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • S := by
    calc A ⊓ Q1 L1 L2 S ≤ Q1 L1 L2 S := inf_le_right
      _ = MulAut.conj g • Q1 L1 L2 S := hconjQ1.symm
      _ ≤ MulAut.conj g • S :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQ1S
  exact str86_orth_pow_mul_relIndex_le_conj hF hSB hm hL2 hstepW hWZ2 hE e hl hml
    horth hDS hgA

private theorem o2s_centralizer_relIndex_le {L1 L2 S A : Subgroup G} {g : G}
    (hAe : IsElemAbelian 2 A) :
    (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
  have hleCent : MulAut.conj g • Z2 L1 L2 S ⊓ A ≤
      Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hAe.comm hx.2 hy.1).symm
  haveI : (MulAut.conj g • Z2 L1 L2 S ⊓ A).IsFiniteRelIndex
      (MulAut.conj g • Z2 L1 L2 S) := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hle : MulAut.conj g • Z2 L1 L2 S ⊓ A ≤
      Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G) ⊓
        MulAut.conj g • Z2 L1 L2 S :=
    le_inf hleCent inf_le_left
  have h := Subgroup.relIndex_le_of_le_left
    (H := MulAut.conj g • Z2 L1 L2 S ⊓ A)
    (K := Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G) ⊓
      MulAut.conj g • Z2 L1 L2 S)
    (L := MulAut.conj g • Z2 L1 L2 S) hle
    (Subgroup.relIndex_ne_zero (H := MulAut.conj g • Z2 L1 L2 S ⊓ A)
      (K := MulAut.conj g • Z2 L1 L2 S))
  simpa only [Subgroup.inf_relIndex_right] using h

private theorem o2s_relIndex_le_mul {L1 L2 S A : Subgroup G} {g : G} :
    (MulAut.conj g • Q2 L1 L2 S).relIndex A ≤
        ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A ∧
      ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
        (A ⊓ Q1 L1 L2 S).relIndex A *
          (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by
  constructor
  · have hle : (A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S ≤
        MulAut.conj g • Q2 L1 L2 S ⊓ A :=
      le_inf inf_le_right (inf_le_left.trans inf_le_left)
    haveI : ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).IsFiniteRelIndex A :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    have h := Subgroup.relIndex_le_of_le_left
      (H := (A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S)
      (K := MulAut.conj g • Q2 L1 L2 S ⊓ A) (L := A) hle
      (Subgroup.relIndex_ne_zero
        (H := (A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S) (K := A))
    simpa only [Subgroup.inf_relIndex_right] using h
  · have h := Subgroup.relIndex_mul_relIndex
      (H := (A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S)
      (K := A ⊓ Q1 L1 L2 S) (L := A) inf_le_left inf_le_left
    rw [Subgroup.inf_relIndex_left] at h
    rw [← h, mul_comm]

private theorem o2s_chain_eq {L1 L2 S A : Subgroup G} {g : G} {k l m d : ℕ}
    (hkm : 2 * k ≤ m) (hml : m = 2 * l)
    (hT1c : 2 ^ l * d ≤
      (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S))
    (hC_le : (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S))
    (hH6 : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hmono : (MulAut.conj g • Q2 L1 L2 S).relIndex A ≤
      ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hmul : ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (A ⊓ Q1 L1 L2 S).relIndex A * d)
    (hH5 : (A ⊓ Q1 L1 L2 S).relIndex A ≤ 2 ^ k)
    (hdpos : 0 < d) (hdne1 : d ≠ 1) : l = k ∧ 2 ≤ d := by
  have hchain : 2 ^ l * d ≤ 2 ^ k * d := by
    calc 2 ^ l * d ≤
          (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
            (MulAut.conj g • Z2 L1 L2 S) := hT1c
      _ ≤ (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex
            (MulAut.conj g • Z2 L1 L2 S) := hC_le
      _ ≤ (MulAut.conj g • Q2 L1 L2 S).relIndex A := hH6
      _ ≤ ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A := hmono
      _ = (A ⊓ Q1 L1 L2 S).relIndex A * d := hmul
      _ ≤ 2 ^ k * d := Nat.mul_le_mul_right d hH5
  have hsk : 2 ^ l ≤ 2 ^ k := Nat.le_of_mul_le_mul_right hchain hdpos
  have hkl : k ≤ l := by omega
  have hks : 2 ^ k ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hkl
  have hsl : 2 ^ l = 2 ^ k := le_antisymm hsk hks
  have hlk : l = k := Nat.pow_right_injective (by norm_num) hsl
  have hdge2 : 2 ≤ d := by omega
  exact ⟨hlk, hdge2⟩

private theorem o2s_index_eq {L1 L2 S A : Subgroup G} {g : G} {k l d : ℕ}
    (hlk : l = k)
    (hT1c : 2 ^ l * d ≤
      (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S))
    (hC_le : (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S))
    (hH6 : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hmono : (MulAut.conj g • Q2 L1 L2 S).relIndex A ≤
      ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hmul : ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (A ⊓ Q1 L1 L2 S).relIndex A * d)
    (hH5 : (A ⊓ Q1 L1 L2 S).relIndex A ≤ 2 ^ k)
    (hdge2 : 2 ≤ d) :
    (MulAut.conj g • Q2 L1 L2 S).relIndex A =
        ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A ∧
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
        (MulAut.conj g • Q2 L1 L2 S).relIndex A ∧
      (A ⊓ Q1 L1 L2 S).relIndex A = 2 ^ k := by
  classical
  let D : Subgroup G := A ⊓ Q1 L1 L2 S
  let Zg : Subgroup G := MulAut.conj g • Z2 L1 L2 S
  let Qg : Subgroup G := MulAut.conj g • Q2 L1 L2 S
  have hT1c' : 2 ^ l * d ≤ (Subgroup.centralizer (D : Set G)).relIndex Zg := hT1c
  have hC_le' : (Subgroup.centralizer (D : Set G)).relIndex Zg ≤
      (Zg ⊓ A).relIndex Zg := hC_le
  have hH6' : (Zg ⊓ A).relIndex Zg ≤ Qg.relIndex A := hH6
  have hmono' : Qg.relIndex A ≤ (D ⊓ Qg).relIndex A := hmono
  have hmul' : (D ⊓ Qg).relIndex A = D.relIndex A * d := hmul
  have hH5' : D.relIndex A ≤ 2 ^ k := hH5
  have hsl : 2 ^ l = 2 ^ k := by rw [hlk]
  have hH5l : D.relIndex A ≤ 2 ^ l := hH5'.trans (le_of_eq hsl.symm)
  have hmono_eq : Qg.relIndex A = (D ⊓ Qg).relIndex A := by
    refine le_antisymm hmono' ?_
    calc (D ⊓ Qg).relIndex A = D.relIndex A * d := hmul'
      _ ≤ 2 ^ l * d := Nat.mul_le_mul_right d hH5l
      _ ≤ (Subgroup.centralizer (D : Set G)).relIndex Zg := hT1c'
      _ ≤ (Zg ⊓ A).relIndex Zg := hC_le'
      _ ≤ Qg.relIndex A := hH6'
  have hB1 : (Zg ⊓ A).relIndex Zg = Qg.relIndex A := by
    refine le_antisymm hH6' ?_
    calc Qg.relIndex A = (D ⊓ Qg).relIndex A := hmono_eq
      _ = D.relIndex A * d := hmul'
      _ ≤ 2 ^ l * d := Nat.mul_le_mul_right d hH5l
      _ ≤ (Subgroup.centralizer (D : Set G)).relIndex Zg := hT1c'
      _ ≤ (Zg ⊓ A).relIndex Zg := hC_le'
  have hf_eq : D.relIndex A = 2 ^ k := by
    have hlow : 2 ^ k * d ≤ D.relIndex A * d := by
      calc 2 ^ k * d = 2 ^ l * d := by rw [← hsl]
        _ ≤ (Subgroup.centralizer (D : Set G)).relIndex Zg := hT1c'
        _ ≤ (Zg ⊓ A).relIndex Zg := hC_le'
        _ ≤ Qg.relIndex A := hH6'
        _ ≤ (D ⊓ Qg).relIndex A := hmono'
        _ = D.relIndex A * d := hmul'
    refine le_antisymm hH5' (Nat.le_of_mul_le_mul_right hlow (by omega))
  exact ⟨hmono_eq, hB1, hf_eq⟩

private theorem o2s_conclusion {L1 L2 S A : Subgroup G} {g : G} {k d : ℕ}
    (hmono_eq : (MulAut.conj g • Q2 L1 L2 S).relIndex A =
      ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hmul : ((A ⊓ Q1 L1 L2 S) ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (A ⊓ Q1 L1 L2 S).relIndex A * d)
    (hf_eq : (A ⊓ Q1 L1 L2 S).relIndex A = 2 ^ k)
    (hB1 : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A)
    (hdge2 : 2 ≤ d) :
    A ⊓ MulAut.conj g • Q2 L1 L2 S ≤ Q1 L1 L2 S ∧
      2 * 2 ^ k ≤ (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex
        (MulAut.conj g • Z2 L1 L2 S) := by
  classical
  let D : Subgroup G := A ⊓ Q1 L1 L2 S
  let Zg : Subgroup G := MulAut.conj g • Z2 L1 L2 S
  let Qg : Subgroup G := MulAut.conj g • Q2 L1 L2 S
  have hmono_eq' : Qg.relIndex A = (D ⊓ Qg).relIndex A := hmono_eq
  have hmul' : (D ⊓ Qg).relIndex A = D.relIndex A * d := hmul
  have hf_eq' : D.relIndex A = 2 ^ k := hf_eq
  have hB1' : (Zg ⊓ A).relIndex Zg = Qg.relIndex A := hB1
  have hDA : D ≤ A := by
    intro x hx
    exact hx.1
  have hDQleA : D ⊓ Qg ≤ A := by
    intro x hx
    exact hDA hx.1
  have hQ1 : A ⊓ Qg ≤ Q1 L1 L2 S := by
    have hrel : (D ⊓ Qg).relIndex A = (Qg ⊓ A).relIndex A := by
      rw [Subgroup.inf_relIndex_right, hmono_eq']
    have hHKeq : D ⊓ Qg = Qg ⊓ A :=
      o2_eq_of_le_of_relIndex_eq (A := A) (H := D ⊓ Qg) (K := Qg ⊓ A)
        hDQleA inf_le_right (le_inf inf_le_right hDQleA) hrel
    calc A ⊓ Qg = Qg ⊓ A := inf_comm _ _
      _ = D ⊓ Qg := hHKeq.symm
      _ ≤ Q1 L1 L2 S := inf_le_left.trans inf_le_right
  refine ⟨hQ1, ?_⟩
  calc 2 * 2 ^ k = 2 ^ k * 2 := by ring
    _ ≤ 2 ^ k * d := Nat.mul_le_mul_left (2 ^ k) hdge2
    _ = D.relIndex A * d := by rw [hf_eq']
    _ = (D ⊓ Qg).relIndex A := hmul'.symm
    _ = Qg.relIndex A := hmono_eq'.symm
    _ = (Zg ⊓ A).relIndex Zg := hB1'.symm

theorem str86_orth_chain {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgA : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    l = k ∧ A ⊓ MulAut.conj g • Q2 L1 L2 S ≤ Q1 L1 L2 S ∧
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
        (MulAut.conj g • Q2 L1 L2 S).relIndex A ∧
      2 * 2 ^ k ≤ (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
  classical
  let D : Subgroup G := A ⊓ Q1 L1 L2 S
  let Zg : Subgroup G := MulAut.conj g • Z2 L1 L2 S
  let Qg : Subgroup G := MulAut.conj g • Q2 L1 L2 S
  let d : ℕ := Qg.relIndex D
  haveI : (Zg ⊓ A).IsFiniteRelIndex Zg := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : (D ⊓ Qg).IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : Qg.IsFiniteRelIndex D := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hm : 2 ≤ m := by omega
  have hT1c : 2 ^ l * d ≤ (Subgroup.centralizer (D : Set G)).relIndex Zg :=
    o2s_pow_mul_relIndex_le_centralizer hF hSB hm hL2 hstepW hWZ2 hE e hl hml horth hg hgA
  have hC_le : (Subgroup.centralizer (D : Set G)).relIndex Zg ≤
      (Zg ⊓ A).relIndex Zg := o2s_centralizer_relIndex_le hA.2.1
  have hH6 : (Zg ⊓ A).relIndex Zg ≤ Qg.relIndex A :=
    str86_conj_z2_index_le hF hSB hZQ hab hA hg
  obtain ⟨hmono, hmul⟩ :=
    o2s_relIndex_le_mul (L1 := L1) (L2 := L2) (S := S) (A := A) (g := g)
  have hH5 : D.relIndex A ≤ 2 ^ k :=
    str86_relIndex_inf_q1_le hF hSB hk hFc hU3 hA.1 hA.2.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (Subgroup.relIndex_ne_zero (H := Qg) (K := D))
  have hdne1 : d ≠ 1 := by
    intro h1
    exact hgA (Subgroup.relIndex_eq_one.mp h1)
  obtain ⟨hlk, hdge2⟩ :=
    o2s_chain_eq hkm hml hT1c hC_le hH6 hmono hmul hH5 hdpos hdne1
  obtain ⟨hmono_eq, hB1, hf_eq⟩ :=
    o2s_index_eq hlk hT1c hC_le hH6 hmono hmul hH5 hdge2
  obtain ⟨hQ1, hfin⟩ := o2s_conclusion hmono_eq hmul hf_eq hB1 hdge2
  exact ⟨hlk, hQ1, hB1, hfin⟩

private theorem o3_isElemAbelian_smul {a : MulAut G} {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (a • E) := by
  rw [Subgroup.pointwise_smul_def]
  exact hE.map a.toMonoidHom

private theorem o3_card_smul (a : MulAut G) (E : Subgroup G) :
    Nat.card ↥(a • E) = Nat.card E := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective a.injective

private theorem o3_card_sup_eq {Z Q A R E : Subgroup G} (hR : R = A ⊓ Q)
    (hE : E = Z ⊔ R) (hZR : ∀ x ∈ Z, ∀ y ∈ R, x * y = y * x)
    (hZQ : Z ≤ Q) (hRA : R ≤ A)
    (hd : (Z ⊓ A).relIndex Z = R.relIndex A) :
    Nat.card E = Nat.card A := by
  have hinfR : Z ⊓ R = Z ⊓ A := by
    rw [hR, ← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hZQ)]
  have hprod : Nat.card E * Nat.card ↥(Z ⊓ A) = Nat.card Z * Nat.card R := by
    have h := CFSG.QuasithinUnique.Setup.Campbell.card_sup_mul_card_inf
      (L := Z) (R := R) hZR
    rw [hinfR] at h
    rw [hE]
    exact h
  have hz : (Z ⊓ A).relIndex Z * Nat.card ↥(Z ⊓ A) = Nat.card Z := by
    have h := Subgroup.relIndex_mul_card (H := Z ⊓ A) (K := Z)
    rw [inf_eq_left.mpr (inf_le_left : (Z ⊓ A : Subgroup G) ≤ Z)] at h
    exact h
  have ha : R.relIndex A * Nat.card R = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := A)
    rw [inf_eq_left.mpr hRA] at h
    exact h
  have hkey : Nat.card E * Nat.card ↥(Z ⊓ A) = Nat.card A * Nat.card ↥(Z ⊓ A) := by
    rw [hprod]
    calc Nat.card Z * Nat.card R
        = ((Z ⊓ A).relIndex Z * Nat.card ↥(Z ⊓ A)) * Nat.card R := by rw [← hz]
      _ = (R.relIndex A * Nat.card ↥(Z ⊓ A)) * Nat.card R := by rw [hd]
      _ = (R.relIndex A * Nat.card R) * Nat.card ↥(Z ⊓ A) := by ring
      _ = Nat.card A * Nat.card ↥(Z ⊓ A) := by rw [ha]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hkey

private theorem o3_le_centralizer {Z L E V Q : Subgroup G} (hV : V = conjClosure Z L)
    (hO1 : ∀ h ∈ L, MulAut.conj h⁻¹ • E ≤ Q)
    (hQZ : Q ≤ Subgroup.centralizer (Z : Set G)) :
    V ≤ Subgroup.centralizer (E : Set G) := by
  rw [hV]
  refine CFSG.Quasithin.conjClosure_le ?_
  intro h hh z hz
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heQ : h⁻¹ * e * h ∈ Q := by
    have hmem : h⁻¹ * e * h ∈ MulAut.conj h⁻¹ • E := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply, show (h⁻¹)⁻¹ * (h⁻¹ * e * h) * h⁻¹ = e from by group]
      exact he
    exact hO1 h hh hmem
  have hcomm : (h⁻¹ * e * h) * z = z * (h⁻¹ * e * h) :=
    (Subgroup.mem_centralizer_iff.mp (hQZ heQ) z hz).symm
  calc e * (h * z * h⁻¹) = h * ((h⁻¹ * e * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * e * h)) * h⁻¹ := by rw [hcomm]
    _ = (h * z * h⁻¹) * e := by group

private theorem o3_eq_sup_of_relIndex_le {Z V A R : Subgroup G} (hZ : Z ≤ V)
    (hV : IsElemAbelian 2 V) (hG1 : (V ⊓ A).relIndex V ≤ R.relIndex A)
    (hd : (Z ⊓ A).relIndex Z = R.relIndex A) :
    V = Z ⊔ (V ⊓ A) := by
  have hMle : Z ⊔ (V ⊓ A) ≤ V := sup_le hZ inf_le_left
  have hMcard : Nat.card V ≤ Nat.card ↥(Z ⊔ (V ⊓ A)) := by
    have hcpos : 0 < Nat.card ↥(Z ⊓ A) := Nat.card_pos
    have hMcomm : ∀ x ∈ Z, ∀ y ∈ V ⊓ A, x * y = y * x :=
      fun x hx y hy => hV.comm (hZ hx) hy.1
    have hinf2 : Z ⊓ (V ⊓ A) = Z ⊓ A := by
      rw [← inf_assoc, inf_eq_left.mpr hZ]
    have hsupcard : Nat.card ↥(Z ⊔ (V ⊓ A)) * Nat.card ↥(Z ⊓ A) =
        Nat.card Z * Nat.card ↥(V ⊓ A) := by
      have h := CFSG.QuasithinUnique.Setup.Campbell.card_sup_mul_card_inf
        (L := Z) (R := V ⊓ A) hMcomm
      rwa [hinf2] at h
    have hVcard : Nat.card V = Nat.card ↥(V ⊓ A) * (V ⊓ A).relIndex V := by
      have h := Subgroup.relIndex_mul_card (H := V ⊓ A) (K := V)
      rw [inf_eq_left.mpr (inf_le_left : (V ⊓ A : Subgroup G) ≤ V), mul_comm] at h
      exact h.symm
    have hZcard : Nat.card Z = Nat.card ↥(Z ⊓ A) * (Z ⊓ A).relIndex Z := by
      have h := Subgroup.relIndex_mul_card (H := Z ⊓ A) (K := Z)
      rw [inf_eq_left.mpr (inf_le_left : (Z ⊓ A : Subgroup G) ≤ Z), mul_comm] at h
      exact h.symm
    have hrel : (V ⊓ A).relIndex V ≤ (Z ⊓ A).relIndex Z := by
      rw [hd]
      exact hG1
    have hstep : Nat.card ↥(V ⊓ A) * (V ⊓ A).relIndex V * Nat.card ↥(Z ⊓ A)
        ≤ Nat.card ↥(V ⊓ A) * (Z ⊓ A).relIndex Z * Nat.card ↥(Z ⊓ A) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrel)
    have hcalc : Nat.card V * Nat.card ↥(Z ⊓ A)
        ≤ Nat.card ↥(Z ⊔ (V ⊓ A)) * Nat.card ↥(Z ⊓ A) := by
      calc Nat.card V * Nat.card ↥(Z ⊓ A)
          = Nat.card ↥(V ⊓ A) * (V ⊓ A).relIndex V * Nat.card ↥(Z ⊓ A) := by
              rw [hVcard]
        _ ≤ Nat.card ↥(V ⊓ A) * (Z ⊓ A).relIndex Z * Nat.card ↥(Z ⊓ A) := hstep
        _ = Nat.card ↥(V ⊓ A) * Nat.card Z := by
              rw [mul_assoc, mul_comm ((Z ⊓ A).relIndex Z), ← hZcard]
        _ = Nat.card ↥(Z ⊔ (V ⊓ A)) * Nat.card ↥(Z ⊓ A) := by
              rw [hsupcard, mul_comm]
    exact Nat.le_of_mul_le_mul_right hcalc hcpos
  exact (Subgroup.eq_of_le_of_card_ge hMle hMcard).symm

private theorem o3s_E_elemAbelian_card {L1 L2 S A : Subgroup G} {g : G}
    (hA : IsMaxElemAbelian S A)
    (hidx : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A) :
    IsElemAbelian 2 (MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S)) ∧
      Nat.card ↥(MulAut.conj g • Z2 L1 L2 S ⊔
        (A ⊓ MulAut.conj g • Q2 L1 L2 S) : Subgroup G) = Nat.card A := by
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := CFSG.Quasithin.A4.omegaOneCenterOf_le _
  have hZ2el : IsElemAbelian 2 (Z2 L1 L2 S) :=
    CFSG.Quasithin.SmithC27.isElemAbelian_omegaOneCenterOf _
  have hQ2cent : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZgQg : MulAut.conj g • Z2 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hZ2Q2
  have hZgR : ∀ x ∈ MulAut.conj g • Z2 L1 L2 S,
      ∀ y ∈ A ⊓ MulAut.conj g • Q2 L1 L2 S, x * y = y * x := by
    intro x hx y hy
    have hx' : g⁻¹ * x * g ∈ Z2 L1 L2 S := by
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply] at hx
    have hy' : g⁻¹ * y * g ∈ Q2 L1 L2 S := by
      have hyq : y ∈ MulAut.conj g • Q2 L1 L2 S := hy.2
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply] at hyq
    have hcomm : (g⁻¹ * x * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_iff.mp (hQ2cent hy') _ hx'
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = y * x := by group
  have hEel : IsElemAbelian 2
      (MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (o3_isElemAbelian_smul hZ2el)
      (CFSG.Open.IsElemAbelian.mono hA.2.1 inf_le_left) hZgR
  have hRQ : (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A := by
    rw [inf_comm (A : Subgroup G), Subgroup.inf_relIndex_right]
  have hd : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A := by
    rw [hRQ]
    exact hidx
  have hEcard : Nat.card ↥(MulAut.conj g • Z2 L1 L2 S ⊔
      (A ⊓ MulAut.conj g • Q2 L1 L2 S) : Subgroup G) = Nat.card A :=
    o3_card_sup_eq (Z := MulAut.conj g • Z2 L1 L2 S) (Q := MulAut.conj g • Q2 L1 L2 S)
      (R := A ⊓ MulAut.conj g • Q2 L1 L2 S) (E := MulAut.conj g • Z2 L1 L2 S ⊔
        (A ⊓ MulAut.conj g • Q2 L1 L2 S)) rfl rfl hZgR hZgQg inf_le_left hd
  exact ⟨hEel, hEcard⟩

private theorem o3s_E_le_q1 {L1 L2 S A : Subgroup G} {g : G}
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hAQ : A ⊓ MulAut.conj g • Q2 L1 L2 S ≤ Q1 L1 L2 S)
    (hg : g ∈ P1 L1 L2 S) :
    MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S) ≤ Q1 L1 L2 S := by
  have hQ1conj : ∀ h ∈ P1 L1 L2 S, MulAut.conj h • Q1 L1 L2 S = Q1 L1 L2 S := by
    intro h hh
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hh)
  have hZgQ1 : MulAut.conj g • Z2 L1 L2 S ≤ Q1 L1 L2 S := by
    calc MulAut.conj g • Z2 L1 L2 S ≤ MulAut.conj g • Q1 L1 L2 S :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hZQ
      _ = Q1 L1 L2 S := hQ1conj g hg
  exact sup_le hZgQ1 hAQ

private theorem o3s_conjClosure_le_centralizer
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {A E : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hEel : IsElemAbelian 2 E) (hEQ1 : E ≤ Q1 L1 L2 S)
    (hEcard : Nat.card E = Nat.card A) :
    conjClosure (Z2 L1 L2 S) L1 ≤ Subgroup.centralizer (E : Set G) := by
  have hQ2cent : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ1conj : ∀ h ∈ P1 L1 L2 S, MulAut.conj h • Q1 L1 L2 S = Q1 L1 L2 S := by
    intro h hh
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hh)
  have hO1 : ∀ h ∈ L1, MulAut.conj h⁻¹ • E ≤ Q2 L1 L2 S := by
    intro h hh
    have hhP : h ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hh
    have hES : MulAut.conj h⁻¹ • E ≤ S := by
      calc MulAut.conj h⁻¹ • E ≤ MulAut.conj h⁻¹ • Q1 L1 L2 S :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hEQ1
        _ = Q1 L1 L2 S := hQ1conj h⁻¹ ((P1 L1 L2 S).inv_mem hhP)
        _ ≤ S := hQ1S
    have hEmax : IsMaxElemAbelian S (MulAut.conj h⁻¹ • E) := by
      refine ⟨hES, o3_isElemAbelian_smul hEel, fun B hBS hB => ?_⟩
      calc Nat.card B ≤ Nat.card A := hA.2.2 B hBS hB
        _ = Nat.card E := hEcard.symm
        _ = Nat.card ↥(MulAut.conj h⁻¹ • E) := (o3_card_smul (MulAut.conj h⁻¹) E).symm
    exact str86_orth_le_q2_of_isMaxElemAbelian hF hSB hk hFc hU3 hB2 hm hL2 hZI
      hstepW hWZ2 hE e hl hml horth hEmax
  exact o3_le_centralizer rfl hO1 hQ2cent

private theorem o3s_conjClosure_eq_sup_aux
    {L1 L2 S A : Subgroup G} {g : G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1,
      x * y = y * x)
    (hA : IsMaxElemAbelian S A) (hg : g ∈ P1 L1 L2 S)
    (hVE : conjClosure (Z2 L1 L2 S) L1 ≤ Subgroup.centralizer
      ((MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S) : Subgroup G) : Set G))
    (hidx : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A) :
    conjClosure (Z2 L1 L2 S) L1 =
      MulAut.conj g • Z2 L1 L2 S ⊔ (conjClosure (Z2 L1 L2 S) L1 ⊓ A) := by
  obtain ⟨hVel, hVQ1, _hVnorm, hVgen⟩ := str86_conjClosure_basics hF hSB hZQ hab
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hECV : MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S) ≤
      Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (Subgroup.le_centralizer_iff (H := conjClosure (Z2 L1 L2 S) L1)
      (K := MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S))).mp hVE
  have hRY : A ⊓ MulAut.conj g • Q2 L1 L2 S ≤
      Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (le_sup_right : A ⊓ MulAut.conj g • Q2 L1 L2 S ≤
      MulAut.conj g • Z2 L1 L2 S ⊔ (A ⊓ MulAut.conj g • Q2 L1 L2 S)).trans hECV
  have hG1 : (conjClosure (Z2 L1 L2 S) L1 ⊓ A).relIndex (conjClosure (Z2 L1 L2 S) L1) ≤
      (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A :=
    relIndex_inf_le_relIndex_of_isMaxElemAbelian hA (hVQ1.trans hQ1S) hVel inf_le_left hRY
  have hRQ : (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A := by
    rw [inf_comm (A : Subgroup G), Subgroup.inf_relIndex_right]
  have hd : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (A ⊓ MulAut.conj g • Q2 L1 L2 S).relIndex A := by
    rw [hRQ]
    exact hidx
  exact o3_eq_sup_of_relIndex_le (hVgen g hg) hVel hG1 hd

theorem str86_orth_conjClosure_eq_sup {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hAQ : A ⊓ MulAut.conj g • Q2 L1 L2 S ≤ Q1 L1 L2 S)
    (hidx : (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) =
      (MulAut.conj g • Q2 L1 L2 S).relIndex A) :
    conjClosure (Z2 L1 L2 S) L1 =
      MulAut.conj g • Z2 L1 L2 S ⊔ (conjClosure (Z2 L1 L2 S) L1 ⊓ A) := by
  classical
  have hEfacts := o3s_E_elemAbelian_card hA hidx
  have hEQ1 := o3s_E_le_q1 hZQ hAQ hg
  have hVE := o3s_conjClosure_le_centralizer hF hSB hk hFc hU3 hB2 hm hL2 hZI
    hstepW hWZ2 hE e hl hml horth hA hEfacts.1 hEQ1 hEfacts.2
  exact o3s_conjClosure_eq_sup_aux hF hSB hZQ hab hA hg hVE hidx

private theorem o4_bigB_le_normalizer_iInf {L1 L2 S : Subgroup G} {Z W' : Subgroup G}
    (hW' : W' = ⨅ k : P1 L1 L2 S, MulAut.conj (k : G) • Z) :
    bigB L1 L2 S ≤ Subgroup.normalizer (W' : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hW'] at hx ⊢
    rw [Subgroup.mem_iInf] at hx ⊢
    intro k
    have hk : b⁻¹ * (k : G) ∈ P1 L1 L2 S :=
      (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem
        ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hb)) k.2
    have hmem := hx ⟨b⁻¹ * (k : G), hk⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hmem ⊢
    have heq : (k : G)⁻¹ * (b * x * b⁻¹) * (k : G) =
        (b⁻¹ * (k : G))⁻¹ * x * (b⁻¹ * (k : G)) := by group
    rw [heq]
    exact hmem
  · intro hx
    rw [hW'] at hx ⊢
    rw [Subgroup.mem_iInf] at hx ⊢
    intro k
    have hk : b * (k : G) ∈ P1 L1 L2 S :=
      (P1 L1 L2 S).mul_mem ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hb) k.2
    have hmem := hx ⟨b * (k : G), hk⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hmem ⊢
    have heq : (k : G)⁻¹ * x * (k : G) =
        (b * (k : G))⁻¹ * (b * x * b⁻¹) * (b * (k : G)) := by group
    rw [heq]
    exact hmem

private theorem o4_z1_le_iInf {L1 L2 S : Subgroup G} {Z W' : Subgroup G}
    (hW' : W' = ⨅ k : P1 L1 L2 S, MulAut.conj (k : G) • Z)
    (hZ1Z : Z1 L1 L2 S ≤ Z) :
    Z1 L1 L2 S ≤ W' := by
  intro z hz
  rw [hW']
  rw [Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hP1normZ1 : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hzh : (k : G)⁻¹ * z * (k : G) ∈ Z1 L1 L2 S := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hP1normZ1 ((P1 L1 L2 S).inv_mem k.2)) z).mp hz
  exact hZ1Z hzh

theorem str86_orth_iInf_eq_z1 {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S) (hZ2 : Z2 L1 L2 S = W)
    {A : Subgroup G} (hZA : Z2 L1 L2 S ≤ A) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hidx : 2 * 2 ^ l ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S)) :
    ⨅ (h : G) (_ : h ∈ P1 L1 L2 S), MulAut.conj h • Z2 L1 L2 S = Z1 L1 L2 S := by
  classical
  rw [iInf_subtype']
  let Z2' : Subgroup G := Z2 L1 L2 S
  let W' : Subgroup G := ⨅ k : P1 L1 L2 S, MulAut.conj (k : G) • Z2'
  have hW'def : W' = ⨅ k : P1 L1 L2 S, MulAut.conj (k : G) • Z2' := rfl
  change W' = Z1 L1 L2 S
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2' := by
    rw [← hWS, ← hZ2]
    exact inf_le_left
  have hBnorm : bigB L1 L2 S ≤ Subgroup.normalizer (W' : Set G) :=
    o4_bigB_le_normalizer_iInf hW'def
  have hZ1W' : Z1 L1 L2 S ≤ W' := o4_z1_le_iInf hW'def hZ1Z2
  have hW'Z2 : W' ≤ Z2' := by
    have h := iInf_le (fun k : P1 L1 L2 S => MulAut.conj (k : G) • Z2')
      (⟨1, one_mem _⟩ : P1 L1 L2 S)
    simpa using h
  have hW'Z2g : W' ≤ MulAut.conj g • Z2' :=
    iInf_le (fun k : P1 L1 L2 S => MulAut.conj (k : G) • Z2') ⟨g, hg⟩
  have hW'A : W' ≤ A := hW'Z2.trans hZA
  by_contra hne
  have hT2 := str86_orth_card_le_of_bigB_invariant hF hSB hm hL2 hstepW hE e hl hml horth
    hWS (hW'Z2.trans (le_of_eq hZ2)) hBnorm hZ1W' hne
  let Z2g : Subgroup G := MulAut.conj g • Z2'
  let C : Subgroup G := Z2g ⊓ A
  have hidx' : 2 * 2 ^ l ≤ C.relIndex Z2g := hidx
  have hW'C : W' ≤ C := le_inf hW'Z2g hW'A
  have hrelC : C.relIndex Z2g * Nat.card ↥C = Nat.card ↥Z2g := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := Z2g)
    rwa [show C ⊓ Z2g = C from inf_eq_left.mpr inf_le_left] at h
  have hcardZ2g : Nat.card ↥Z2g = Nat.card ↥Z2' := by
    show Nat.card ↥(MulAut.conj g • Z2') = Nat.card ↥Z2'
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Z2').toEquiv).symm
  have h1 : 2 * 2 ^ l * Nat.card W' ≤ Nat.card W := by
    calc 2 * 2 ^ l * Nat.card W'
        ≤ C.relIndex Z2g * Nat.card ↥C := Nat.mul_le_mul hidx' (Subgroup.card_le_of_le hW'C)
      _ = Nat.card ↥Z2g := hrelC
      _ = Nat.card ↥Z2' := hcardZ2g
      _ = Nat.card W := by
        change Nat.card ↥(Z2 L1 L2 S) = Nat.card ↥W
        rw [hZ2]
  have h2 : 2 * Nat.card W ≤ Nat.card W := by
    calc 2 * Nat.card W ≤ 2 * (2 ^ l * Nat.card W') := Nat.mul_le_mul_left 2 hT2
      _ = 2 * 2 ^ l * Nat.card W' := by rw [mul_assoc]
      _ ≤ Nat.card W := h1
  have hpos : 0 < Nat.card W := Nat.card_pos
  have hle : 2 ≤ 1 := by
    have h' : 2 * Nat.card W ≤ 1 * Nat.card W := by simpa using h2
    exact Nat.le_of_mul_le_mul_right h' hpos
  omega

end CFSG.Quasithin.Stroth

end
