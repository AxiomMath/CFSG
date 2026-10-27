module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleFrame
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans2
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_not_thompsonJ_le_q1_inf_q2 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (_hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    ¬ thompsonJ S ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  intro hJ
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S := hJ.trans inf_le_left
  have hJQ2 : thompsonJ S ≤ Q2 L1 L2 S := hJ.trans inf_le_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hJeq1 : thompsonJ (Q1 L1 L2 S) = thompsonJ S :=
    (CFSG.Quasithin.thompsonJ_eq_of_le hJQ1 hQ1S).symm
  have hJeq2 : thompsonJ (Q2 L1 L2 S) = thompsonJ S :=
    (CFSG.Quasithin.thompsonJ_eq_of_le hJQ2 hQ2S).symm
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    have hchar : ((thompsonJ (Q1 L1 L2 S)).subgroupOf (Q1 L1 L2 S)).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (Q1 L1 L2 S)
    have hmap : ((thompsonJ (Q1 L1 L2 S)).subgroupOf (Q1 L1 L2 S)).map
        (Q1 L1 L2 S).subtype = thompsonJ S := by
      rw [Subgroup.map_subgroupOf_eq_of_le (thompsonJ_le_self (Q1 L1 L2 S))]
      exact hJeq1
    have h := (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (normalizer_le_normalizer_map_of_characteristic
        ((thompsonJ (Q1 L1 L2 S)).subgroupOf (Q1 L1 L2 S)))
    rwa [hmap] at h
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    have hchar : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (Q2 L1 L2 S)
    have hmap : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).map
        (Q2 L1 L2 S).subtype = thompsonJ S := by
      rw [Subgroup.map_subgroupOf_eq_of_le (thompsonJ_le_self (Q2 L1 L2 S))]
      exact hJeq2
    have h := (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_map_of_characteristic
        ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)))
    rwa [hmap] at h
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1N hP2N
  have hJp : IsPGroup 2 (thompsonJ S) := hF.1.h1.pgroup.to_le (thompsonJ_le_self S)
  have hJleO : thompsonJ S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 ((thompsonJ_le_self S).trans le_sup_right) hG0N hJp
  rw [hF.1.o2] at hJleO
  have hSne : S ≠ ⊥ := by
    intro hS
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
      (le_bot_iff.mp (by simpa [hS] using omegaOneCenterOf_le S))
  exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hF.1.h1.pgroup hSne
    (le_bot_iff.mp hJleO)

theorem str86_not_le_normalizer_z2
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    ¬ L1 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
  intro hle
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := by
    intro hbot
    have hle : omegaOneCenterOf S ≤ Z2 L1 L2 S := by
      have h := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf
        (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using h
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
      (le_bot_iff.mp (hle.trans (le_of_eq hbot)))
  have hL2le : L2 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hG0le : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [show L1 ⊔ L2 ⊔ S = (L1 ⊔ S) ⊔ L2 by ac_rfl]
    exact sup_le hle hL2le
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))
  have hZ2G0 : Z2 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := hZ2S.trans le_sup_right
  have hZ2p : IsPGroup 2 (Z2 L1 L2 S) :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).isPGroup
  have hpc : Z2 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZ2G0 hG0le hZ2p
  rw [hF.1.o2] at hpc
  exact hZ2ne (le_bot_iff.mp hpc)

theorem str86_chief_count_ne_zero
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hsyl : IsSylowTwoOf S (L1 ⊔ S))
    (hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1)) {c : ℕ}
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) c) : c ≠ 0 := by
  intro hc0
  have hcomm : ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
    D14.commutator_eq_bot_of_zero hV hser hc0
  have hcomm' : ⁅oTwoUpper (L1 ⊔ S), conjClosure (Z2 L1 L2 S) L1⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm]
  have hO2C : oTwoUpper (L1 ⊔ S) ≤
      Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  have hZ2V : Z2 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 := le_conjClosure _ _
  have hO2Z : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    hO2C.trans (Subgroup.centralizer_le hZ2V)
  have hHNZ : L1 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf hsyl]
    exact sup_le (hO2Z.trans (Subgroup.centralizer_le_normalizer (Z2 L1 L2 S : Set G)))
      le_normalizer_z2_of_sylow
  exact str86_not_le_normalizer_z2 hF hHNZ

theorem str86_sq_le_relIndex_conjClosure
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {a : G} (haS : a ∈ S) (haQ : a ∉ Q1 L1 L2 S) (ha2 : a * a = 1) :
    (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) := by
  classical
  obtain ⟨hVea, hVQ1, hP1NV, -⟩ := str86_conjClosure_basics hF hSB hZQ hab
  have hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) := hVea.isPGroup
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hVH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S :=
    hVQ1.trans (hQ1S.trans le_sup_right)
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
          conv_lhs => rw [sup_eq_left.mpr (show S ⊓ L1 ≤ L1 from inf_le_right)]
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
  have hX : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hsup1]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he hq
  have hHV : L1 ⊔ S ≤
      Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans hP1NV
  have hnorm : IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hHV hg) x).mp hx⟩
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom
    (conjClosure (Z2 L1 L2 S) L1) hnorm
  have haH : a ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) haS
  have ha2p : a * a ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQcore, ha2]
    exact (Q1 L1 L2 S).one_mem
  have haO : a ∉ pCoreOf 2 (L1 ⊔ S) := by rwa [hQcore]
  have hM6 := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S)
    (U := conjClosure (Z2 L1 L2 S) L1) (q := 2 ^ k) (c := c)
    hX hV hVH hser haH ha2p haO
  have hc : c ≠ 0 := str86_chief_count_ne_zero hF hSyl hV hser
  have hbase : 1 ≤ (2 ^ k) ^ 2 :=
    one_le_pow₀ (Nat.one_le_pow k 2 (by norm_num))
  exact (le_self_pow hbase hc).trans hM6

private theorem p3_inf_q1_le_centralizer_conjClosure {L1 L2 S A : Subgroup G}
    (hR : ∀ g ∈ L1, A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    A ⊓ Q1 L1 L2 S ≤
      Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun g hg z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hcentQ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hcentConj : MulAut.conj g • Q2 L1 L2 S ≤
      Subgroup.centralizer ((MulAut.conj g • Z2 L1 L2 S : Subgroup G) : Set G) := by
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := (MulAut.conj g : MulAut G))).mpr hcentQ
    rwa [smul_centralizer] at h
  have hzConj : (MulAut.conj g) • z ∈ MulAut.conj g • Z2 L1 L2 S :=
    Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (Z2 L1 L2 S) hz
  have hcomm := Subgroup.mem_centralizer_iff.mp (hcentConj (hR g hg hr)) _ hzConj
  simpa [MulAut.smul_def, MulAut.conj_apply] using hcomm.symm

theorem str86_exists_conj_not_le
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAQ : ¬ A ≤ Q1 L1 L2 S) :
    ∃ g ∈ L1, ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S := by
  by_contra hconj
  push Not at hconj
  have hVQ1 : conjClosure (Z2 L1 L2 S) L1 ≤ Q1 L1 L2 S :=
    (str86_conjClosure_basics hF hSB hZQ hab).2.1
  have hVab : IsElemAbelian 2 (conjClosure (Z2 L1 L2 S) L1) :=
    (str86_conjClosure_basics hF hSB hZQ hab).1
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hVS : conjClosure (Z2 L1 L2 S) L1 ≤ S := hVQ1.trans hQ1S
  have hRV : A ⊓ Q1 L1 L2 S ≤
      Subgroup.centralizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    p3_inf_q1_le_centralizer_conjClosure hconj
  have hG1 := relIndex_inf_le_relIndex_of_isMaxElemAbelian
    (T := S) (A := A) (Y := conjClosure (Z2 L1 L2 S) L1) (R := A ⊓ Q1 L1 L2 S)
    hA hVS hVab inf_le_left hRV
  have hH5 := str86_relIndex_inf_q1_le hF hSB hk hFc hU3 hA.1 hA.2.1
  have hle : (conjClosure (Z2 L1 L2 S) L1 ⊓ A).relIndex
      (conjClosure (Z2 L1 L2 S) L1) ≤ 2 ^ k := hG1.trans hH5
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
  have haS : a ∈ S := hA.1 haA
  have ha2 : a * a = 1 := by
    simpa [pow_two] using hA.2.1.2 a haA
  have hP2 := str86_sq_le_relIndex_conjClosure (a := a)
    hF hSB hk hFc hU3 hZQ hab haS haQ ha2
  have hAcent : A ≤ Subgroup.centralizer (A : Set G) := by
    haveI : IsMulCommutative ↥A := hA.2.1.1
    exact Subgroup.le_centralizer A
  have hsub : conjClosure (Z2 L1 L2 S) L1 ⊓ A ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) :=
    (inf_le_right.trans hAcent).trans
      (Subgroup.centralizer_le fun x hx => Subgroup.zpowers_le.mpr haA hx)
  have hmono := Subgroup.relIndex_le_of_le_left (L := conjClosure (Z2 L1 L2 S) L1)
    hsub (D15Proof.relIndex_ne_zero _ _)
  have hfin : (2 ^ k) ^ 2 ≤ 2 ^ k := hP2.trans (hmono.trans hle)
  have hlt : 2 ^ k < (2 ^ k) ^ 2 := by
    rw [pow_two]
    exact Nat.lt_mul_self_iff.mpr (Nat.one_lt_two_pow (by omega))
  exact (not_lt_of_ge hfin) hlt

theorem str86_displacement_of_not_le_q2 {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAQ : ¬ A ≤ Q2 L1 L2 S) :
    (Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex A := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hVL2 : VL2 L2 := ⟨m, hL2⟩
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hZ2S : Z2 L1 L2 S ≤ S := (omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hCS : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    (str86_caseI_basics hF hSB h1 hB2 hVL2 hZI).2.2.2.1
  have hCinf : Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ A = Q2 L1 L2 S ⊓ A := by
    refine le_antisymm ?_ ?_
    · refine le_inf ?_ inf_le_right
      rw [← hCS]
      exact le_inf (inf_le_right.trans hA.1) inf_le_left
    · have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
        hCS ▸ inf_le_right
      exact le_inf (inf_le_left.trans hQ2C) inf_le_right
  calc (Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S)
      ≤ (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A :=
        Ch3g316.relIndex_centralizer_le hA hZ2S hZ2e
    _ = (Q2 L1 L2 S).relIndex A := by
        rw [← Subgroup.inf_relIndex_right
          (H := Subgroup.centralizer (Z2 L1 L2 S : Set G)) (K := A), hCinf,
          Subgroup.inf_relIndex_right]
    _ ≤ 2 ^ k * (Q2 L1 L2 S).relIndex A :=
        Nat.le_mul_of_pos_left _ (by positivity)

private theorem p4b_main_le {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1,
      x * y = y * x)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G} (hg : g ∈ P1 L1 L2 S) :
    (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) ≤
      2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := by
    intro H K
    letI : H.IsFiniteRelIndex ⊤ :=
      Subgroup.isFiniteRelIndex_top_iff.mpr (Subgroup.finiteIndex_of_finite (H := H))
    haveI : H.IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_le_right H le_top
    exact Subgroup.relIndex_ne_zero
  have hA1 : A ≤ S := hA.1
  have hXleA : A ⊓ Q1 L1 L2 S ≤ A := inf_le_left
  have hAcent : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.2.1.1
  have hC1 : MulAut.conj g • Z2 L1 L2 S ⊓ A ≤
      Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G) :=
    (inf_le_right.trans hAcent).trans (Subgroup.centralizer_le (fun x hx => hXleA hx))
  have h6 := str86_conj_z2_index_le hF hSB hZQ hab hA hg
  have hH5 : (A ⊓ Q1 L1 L2 S).relIndex A ≤ 2 ^ k :=
    str86_relIndex_inf_q1_le hF hSB hk hFc hU3 hA1 hA.2.1
  have hstep1 : (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
      (MulAut.conj g • Z2 L1 L2 S) ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_left hC1 (hne _ _)
  have hstep2 : (MulAut.conj g • Q2 L1 L2 S).relIndex A ≤
      2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by
    have htower : (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex A =
        (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex (A ⊓ Q1 L1 L2 S) *
          (A ⊓ Q1 L1 L2 S).relIndex A :=
      (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hXleA).symm
    have hleft : (MulAut.conj g • Q2 L1 L2 S).relIndex A ≤
        (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex A := by
      rw [show (MulAut.conj g • Q2 L1 L2 S).relIndex A =
        (MulAut.conj g • Q2 L1 L2 S ⊓ A).relIndex A from
        (Subgroup.inf_relIndex_right (H := MulAut.conj g • Q2 L1 L2 S) (K := A)).symm]
      exact Subgroup.relIndex_le_of_le_left
        (le_inf inf_le_right (inf_le_left.trans hXleA)) (hne _ _)
    have hright : (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex
        (A ⊓ Q1 L1 L2 S) =
        (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by
      rw [inf_comm (A ⊓ Q1 L1 L2 S), Subgroup.inf_relIndex_right]
    calc (MulAut.conj g • Q2 L1 L2 S).relIndex A
        ≤ (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex A := hleft
      _ = (A ⊓ Q1 L1 L2 S ⊓ (MulAut.conj g • Q2 L1 L2 S)).relIndex
            (A ⊓ Q1 L1 L2 S) * (A ⊓ Q1 L1 L2 S).relIndex A := htower
      _ = (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) *
            (A ⊓ Q1 L1 L2 S).relIndex A := by rw [hright]
      _ ≤ (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) * 2 ^ k :=
          Nat.mul_le_mul_left _ hH5
      _ = 2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) :=
          Nat.mul_comm _ _
  calc (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S)
      ≤ (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex
          (MulAut.conj g • Z2 L1 L2 S) := hstep1
    _ ≤ (MulAut.conj g • Q2 L1 L2 S).relIndex A := h6
    _ ≤ 2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := hstep2

private theorem p4b_conj_transport {L1 L2 S : Subgroup G} {k : ℕ} {A : Subgroup G} {g : G}
    (hmain : (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
        (MulAut.conj g • Z2 L1 L2 S) ≤
      2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S)) :
    (Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) : Set G)).relIndex
        (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) := by
  have hXD : MulAut.conj g • (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) =
      A ⊓ Q1 L1 L2 S := by
    rw [smul_smul, map_inv MulAut.conj g, mul_inv_cancel, one_smul]
  have hconv1 :
      (Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) :
          Set G)).relIndex (Z2 L1 L2 S) =
        (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
          (MulAut.conj g • Z2 L1 L2 S) := by
    have h := Subgroup.relIndex_map_map_of_injective
      (f := MulDistribMulAction.toMonoidHom G (MulAut.conj g))
      (H := Subgroup.centralizer
        ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) : Set G))
      (K := Z2 L1 L2 S) (MulAut.conj g).injective
    have hmapC : (Subgroup.centralizer
        ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) : Set G)).map
        (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) =
        Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G) := by
      rw [map_mulDistrib_eq_smul, smul_centralizer,
        ← Subgroup.coe_pointwise_smul (MulAut.conj g)
          (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)), hXD, Subgroup.coe_inf]
      rfl
    have hmapZ : (Z2 L1 L2 S).map
        (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) =
        MulAut.conj g • Z2 L1 L2 S := by
      rw [map_mulDistrib_eq_smul]
    calc (Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) :
          Set G)).relIndex (Z2 L1 L2 S)
        = ((Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) :
              Set G)).map
              (MulDistribMulAction.toMonoidHom G (MulAut.conj g))).relIndex
            ((Z2 L1 L2 S).map
              (MulDistribMulAction.toMonoidHom G (MulAut.conj g))) := h.symm
      _ = (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
            (MulAut.conj g • Z2 L1 L2 S) := by rw [hmapC, hmapZ]
  have hconv2 :
      (Q2 L1 L2 S).relIndex (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) =
        (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by
    have h := Subgroup.relIndex_map_map_of_injective
      (f := MulDistribMulAction.toMonoidHom G (MulAut.conj g)) (H := Q2 L1 L2 S)
      (K := MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) (MulAut.conj g).injective
    have hmapQ : (Q2 L1 L2 S).map
        (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) =
        MulAut.conj g • Q2 L1 L2 S := by
      rw [map_mulDistrib_eq_smul]
    have hmapD : (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)).map
        (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) =
        A ⊓ Q1 L1 L2 S := by
      rw [map_mulDistrib_eq_smul, smul_smul, map_inv MulAut.conj g, mul_inv_cancel, one_smul]
    calc (Q2 L1 L2 S).relIndex (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S))
        = ((Q2 L1 L2 S).map
            (MulDistribMulAction.toMonoidHom G (MulAut.conj g))).relIndex
            ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)).map
              (MulDistribMulAction.toMonoidHom G (MulAut.conj g))) := h.symm
      _ = (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := by rw [hmapQ, hmapD]
  calc (Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) :
        Set G)).relIndex (Z2 L1 L2 S)
      = (Subgroup.centralizer (A ⊓ Q1 L1 L2 S : Set G)).relIndex
          (MulAut.conj g • Z2 L1 L2 S) := hconv1
    _ ≤ 2 ^ k * (MulAut.conj g • Q2 L1 L2 S).relIndex (A ⊓ Q1 L1 L2 S) := hmain
    _ = 2 ^ k * (Q2 L1 L2 S).relIndex (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) := by
        rw [← hconv2]

theorem str86_displacement_of_conj {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G} (hg : g ∈ P1 L1 L2 S)
    (hgA : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) ≤ S ∧
      ¬ MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) ≤ Q2 L1 L2 S ∧
      (Subgroup.centralizer ((MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) : Subgroup G) :
          Set G)).relIndex (Z2 L1 L2 S) ≤
        2 ^ k * (Q2 L1 L2 S).relIndex (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ1fix : MulAut.conj g⁻¹ • Q1 L1 L2 S = Q1 L1 L2 S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) ((P1 L1 L2 S).inv_mem hg))
  have hDleS : MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) ≤ S := by
    calc MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)
        ≤ MulAut.conj g⁻¹ • Q1 L1 L2 S :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr inf_le_right
      _ = Q1 L1 L2 S := hQ1fix
      _ ≤ S := hQ1S
  have hXD : MulAut.conj g • (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) =
      A ⊓ Q1 L1 L2 S := by
    rw [smul_smul, map_inv MulAut.conj g, mul_inv_cancel, one_smul]
  have hnot : ¬ MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S) ≤ Q2 L1 L2 S := by
    intro hle
    apply hgA
    have h : MulAut.conj g • (MulAut.conj g⁻¹ • (A ⊓ Q1 L1 L2 S)) ≤
        MulAut.conj g • Q2 L1 L2 S :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hle
    rwa [hXD] at h
  exact ⟨hDleS, hnot, p4b_conj_transport (p4b_main_le hF hSB hk hFc hU3 hZQ hab hA hg)⟩

theorem str86_exists_displacement
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x) :
    ∃ D : Subgroup G, D ≤ S ∧ ¬ D ≤ Q2 L1 L2 S ∧
      (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) ≤
        2 ^ k * (Q2 L1 L2 S).relIndex D := by
  have hJ := str86_not_thompsonJ_le_q1_inf_q2 hF hSB
  by_cases hJQ2 : thompsonJ S ≤ Q2 L1 L2 S
  · have hJQ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S :=
      fun hJQ1 => hJ (le_inf hJQ1 hJQ2)
    obtain ⟨A, hA, hAQ⟩ :=
      Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf (T := S) (Q := Q1 L1 L2 S) hJQ1
    obtain ⟨g, hgL1, hgA⟩ :=
      str86_exists_conj_not_le hF hSB hk hFc hU3 hZQ hab hA hAQ
    have hg : g ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hgL1
    obtain ⟨hDS, hDQ, hD⟩ :=
      str86_displacement_of_conj hF hSB hk hFc hU3 hZQ hab hA hg hgA
    exact ⟨_, hDS, hDQ, hD⟩
  · obtain ⟨A, hA, hAQ⟩ :=
      Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf (T := S) (Q := Q2 L1 L2 S) hJQ2
    exact ⟨A, hA.1, hAQ,
      str86_displacement_of_not_le_q2 hF hSB hk hFc hU3 hB2 hL2 hZI hA hAQ⟩

private theorem p5_chief_count_le_one
    {L1 L2 S : Subgroup G} {k m c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    {D : Subgroup G} (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S)
    (hD : (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex D)
    (hser : IsChiefSeriesFrom (u3H L1 L2 S) (Z2 L1 L2 S) (Z2 L1 L2 S) c) :
    c ≤ 1 := by
  classical
  have hm : 2 ≤ m := by omega
  obtain ⟨t, htD, htQ⟩ : ∃ t : G, t ∈ D ∧ t ∉ Q2 L1 L2 S := by
    by_contra hcon
    exact hDQ fun x hx => by
      by_contra hxq
      exact hcon ⟨x, hx, hxq⟩
  have htS : t ∈ S := hDS htD
  have htH : t ∈ u3H L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2 htS
  have ht : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H hF.toW]
    exact str86_sq_mem_q2 hF.toW hSB hm hL2 htS
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rwa [str86_pCoreOf_u3H hF.toW]
  have hU : IsPGroup 2 (Z2 L1 L2 S) :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).isPGroup
  have hUH : Z2 L1 L2 S ≤ u3H L1 L2 S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans (q2_le_u3H L1 L2 S)
  have hAH : Subgroup.zpowers t ≤ u3H L1 L2 S := Subgroup.zpowers_le.mpr htH
  have hL2u3 : IsL2Quot m (oTwoQuot ↥(u3H L1 L2 S)) := str86_isL2Quot_u3H hF.toW hL2
  have hkstep : ∀ L' N' : Subgroup G,
      IsChiefStep (u3H L1 L2 S) (Z2 L1 L2 S) L' N' →
      ¬ IsCentralStep (u3H L1 L2 S) L' N' →
      2 ^ m ≤ (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' := by
    intro L' N' hstep hnc
    exact l2ChiefSectionRep_pow_le_relIndex_centralizerMod (H := u3H L1 L2 S)
      (U := Z2 L1 L2 S) hm hL2u3 hU hUH hstep hnc htH ht htO
  have hpow := D15Proof.pow_le_relIndex hUH hAH hkstep hser
  have hCD : Subgroup.centralizer (D : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute t x from hx t htD) j).eq
  have hrelS : (Q2 L1 L2 S).relIndex S = 2 ^ m := str86_relIndex_q2_s hF.toW hSB hm hL2
  have hrelD : (Q2 L1 L2 S).relIndex D ≤ 2 ^ m := by
    rw [← hrelS]
    exact Subgroup.relIndex_le_of_le_right hDS (D15Proof.relIndex_ne_zero _ _)
  have hrel_t : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Z2 L1 L2 S) ≤ 2 ^ k * 2 ^ m := by
    refine (Subgroup.relIndex_le_of_le_left hCD (D15Proof.relIndex_ne_zero _ _)).trans ?_
    exact hD.trans (Nat.mul_le_mul_left _ hrelD)
  have hfin : (2 ^ m) ^ c ≤ 2 ^ k * 2 ^ m := hpow.trans hrel_t
  have hklt : k < m := by omega
  have hbase : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hlt : 2 ^ k * 2 ^ m < (2 ^ m) ^ 2 := by
    calc 2 ^ k * 2 ^ m < 2 ^ m * 2 ^ m :=
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hklt)
            (Nat.two_pow_pos m)
      _ = (2 ^ m) ^ 2 := by rw [pow_two]
  have hc2 : c < 2 := (Nat.pow_lt_pow_iff_right hbase).mp (hfin.trans_lt hlt)
  omega

private theorem p5_commutator_eq_bot_false
    {L1 L2 S : Subgroup G} {k m c : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hser : IsChiefSeriesFrom (u3H L1 L2 S) (Z2 L1 L2 S) (Z2 L1 L2 S) c) (hc : c = 0) :
    False := by
  classical
  have hm : 2 ≤ m := by omega
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := fun h =>
    hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq h)))
  have hU : IsPGroup 2 (Z2 L1 L2 S) :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).isPGroup
  have hbot := D14.commutator_eq_bot_of_zero (H := u3H L1 L2 S)
    (U := Z2 L1 L2 S) hU hser hc
  have hO : oTwoUpper (u3H L1 L2 S) ≤
      Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]
      exact hbot)
  have hQ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hHcent : u3H L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    rw [str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hm hL2]
    exact sup_le hO hQ
  have hle : Z2 L1 L2 S ≤
      Z2 L1 L2 S ⊓ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := by
    refine le_inf le_rfl ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hHcent hg) z hz).symm
  rw [str86_centralizer_u3H_z2 hF hSB h1 hB2 h2 hZI] at hle
  exact hZ2ne (le_bot_iff.mp hle)

theorem str86_chief_count_one {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {D : Subgroup G} (hDS : D ≤ S) (hDQ : ¬ D ≤ Q2 L1 L2 S)
    (hD : (Subgroup.centralizer (D : Set G)).relIndex (Z2 L1 L2 S) ≤
      2 ^ k * (Q2 L1 L2 S).relIndex D) :
    IsChiefSeriesFrom (u3H L1 L2 S) (Z2 L1 L2 S) (Z2 L1 L2 S) 1 := by
  classical
  have hN : IsNormalIn (u3H L1 L2 S) (Z2 L1 L2 S) (Z2 L1 L2 S) := by
    refine ⟨le_rfl, fun g hg x hx => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (str86_z2_normal_u3H L1 L2 S hg) x).mp hx
  obtain ⟨c, hser⟩ := CFSG.Quasithin.D15Proof.exists_isChiefSeriesFrom
    (H := u3H L1 L2 S) (U := Z2 L1 L2 S) (Z2 L1 L2 S) hN
  have hc1 : c ≤ 1 :=
    p5_chief_count_le_one (F := F) hF hSB hk hL2 hkm hDS hDQ hD hser
  have hc0 : c ≠ 0 := by
    intro hc
    exact p5_commutator_eq_bot_false (F := F) hF hSB hk hFc hU3 hB2 hL2 hkm hZI hser hc
  have hc : c = 1 := by omega
  rwa [hc] at hser

theorem str86_commutator_isChiefStep {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hc1 : IsChiefSeriesFrom (u3H L1 L2 S) (Z2 L1 L2 S) (Z2 L1 L2 S) 1) :
    IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ∧
      ¬ IsCentralStep (u3H L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ := by
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  have hZ2 : IsPGroup 2 (Z2 L1 L2 S) := by
    intro y
    exact ⟨1, Subtype.ext (by
      simpa using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 y y.2)⟩
  exact isChiefStep_commutator_of_count_one hZ2
    (omegaOneCenterOf_le (Q2 L1 L2 S))
    (q2_le_u3H L1 L2 S)
    (str86_z2_normal_u3H L1 L2 S)
    (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S))
    (str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hm hL2).symm
    (str86_centralizer_u3H_z2 hF hSB h1 hB2 h2 hZI)
    hc1

end CFSG.Quasithin.Stroth

end
