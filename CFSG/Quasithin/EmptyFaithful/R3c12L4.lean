module

public import CFSG.Quasithin.EmptyFaithful.R3c12Syl
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S146yBorel
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Quasithin.R3c12

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section L4

abbrev G4 : Type := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)

@[expose] def uMat (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a, d, f; 0, 1, b, e; 0, 0, 1, c; 0, 0, 0, 1]

theorem det_uMat (a b c d e f : ZMod 2) : (uMat a b c d e f).det = 1 := by
  simp [uMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def uElt (a b c d e f : ZMod 2) : G4 := ⟨uMat a b c d e f, det_uMat a b c d e f⟩

theorem coe_uElt (a b c d e f : ZMod 2) :
    ((uElt a b c d e f : G4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = uMat a b c d e f := rfl

theorem uElt_mem (a b c d e f : ZMod 2) : uElt a b c d e f ∈ unitriangular 4 (ZMod 2) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert hij; decide)
  · fin_cases i <;> rfl

theorem exists_uElt {A : G4} (hA : A ∈ unitriangular 4 (ZMod 2)) :
    ∃ a b c d e f : ZMod 2, A = uElt a b c d e f := by
  refine ⟨A 0 1, A 1 2, A 2 3, A 0 2, A 1 3, A 0 3, Subtype.ext ?_⟩
  have h1 := hA.1
  have h2 := hA.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uElt, uMat]
  all_goals first
    | (exact h2 _)
    | (exact h1 _ _ (by decide))

theorem uElt_zero : uElt 0 0 0 0 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uElt, uMat]

theorem center_bits : ∀ a b c d e f : ZMod 2,
    uMat a b c d e f * uMat 1 0 0 0 0 0 = uMat 1 0 0 0 0 0 * uMat a b c d e f →
    uMat a b c d e f * uMat 0 1 0 0 0 0 = uMat 0 1 0 0 0 0 * uMat a b c d e f →
    uMat a b c d e f * uMat 0 0 1 0 0 0 = uMat 0 0 1 0 0 0 * uMat a b c d e f →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  decide +kernel

theorem shape1 : ∀ a b c d e f : ZMod 2,
    (uMat a b c d e f * uMat 1 0 0 0 0 0 = uMat 1 0 0 0 0 0 * uMat a b c d e f ∨
      uMat 0 0 0 0 0 1 * uMat a b c d e f * uMat 1 0 0 0 0 0 =
        uMat 1 0 0 0 0 0 * uMat a b c d e f) → b = 0 := by
  decide +kernel

theorem shape2 : ∀ a b c d e f : ZMod 2,
    (uMat a b c d e f * uMat 0 1 0 0 0 0 = uMat 0 1 0 0 0 0 * uMat a b c d e f ∨
      uMat 0 0 0 0 0 1 * uMat a b c d e f * uMat 0 1 0 0 0 0 =
        uMat 0 1 0 0 0 0 * uMat a b c d e f) → a = 0 ∧ c = 0 := by
  decide +kernel

theorem zcomm_bits : (∀ a b c d e f : ZMod 2, uMat 0 0 0 0 0 1 * uMat a b c d e f =
    uMat a b c d e f * uMat 0 0 0 0 0 1) := by
  decide +kernel

theorem lower_bits (E : Matrix (Fin 4) (Fin 4) (ZMod 2)) (d e f : ZMod 2) (hde : d ≠ 0 ∨ e ≠ 0)
    (hz : E * uMat 0 0 0 0 0 1 = uMat 0 0 0 0 0 1 * E)
    (hu : E * uMat 0 0 0 d e f = uMat 0 0 0 d e f * E) :
    E 1 0 = 0 ∧ E 2 0 = 0 ∧ E 3 0 = 0 ∧ E 2 1 = 0 ∧ E 3 1 = 0 ∧ E 3 2 = 0 := by
  have z13 := congrFun (congrFun hz 1) 3
  have z23 := congrFun (congrFun hz 2) 3
  have z33 := congrFun (congrFun hz 3) 3
  have z01 := congrFun (congrFun hz 0) 1
  have z02 := congrFun (congrFun hz 0) 2
  have u01 := congrFun (congrFun hu 0) 1
  have u23 := congrFun (congrFun hu 2) 3
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_four] at z13 z23 z33 z01 z02 u01 u23
  have h21 : E 2 1 = 0 := by
    rw [z01] at u01
    rw [z23] at u23
    simp at u01 u23
    rcases hde with hd | he
    · exact u01.resolve_left hd
    · exact u23.resolve_right he
  exact ⟨z13, z23, z33, h21, z01, z02⟩

theorem diag_bits : ∀ x y z w : ZMod 2, x * y * z * w = 1 → x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 := by
  decide

local notation "U4" => (unitriangular 4 (ZMod 2) : Subgroup G4)

theorem isSylow_U4 : IsSylowTwoOf U4 ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 4) (by norm_num)
  refine K1.isSylowTwoOf_top_iff.mpr ⟨?_, ?_⟩
  · rw [← hP]
    exact P.isPGroup'
  · rw [← hP]
    exact P.not_dvd_index

theorem coe_mul_uElt (g h : G4) :
    ((g * h : G4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  Matrix.SpecialLinearGroup.coe_mul g h

theorem z0_mem {V : Subgroup G4} (hVU : V ≤ U4) (hV4 : Nat.card V = 4)
    (hUV : U4 ≤ Subgroup.normalizer (V : Set G4)) : uElt 0 0 0 0 0 1 ∈ V := by
  classical
  have hU2 : IsPGroup 2 ↥U4 := isSylow_U4.2.1
  have hnil : Group.IsNilpotent ↥U4 := hU2.isNilpotent
  have hVn : (V.subgroupOf U4).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mpr hUV
  have hV1 : V.subgroupOf U4 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (V.subgroupOf U4) = 1 := by rw [hb]; exact Subgroup.card_bot
    have h2 : Nat.card (V.subgroupOf U4) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    omega
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
  obtain ⟨⟨⟨x, hxU⟩, hxmem⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  have hxV : x ∈ V := Subgroup.mem_subgroupOf.mp hxmem.1
  obtain ⟨a, b, c, d, e, f, rfl⟩ := exists_uElt hxU
  have hcen' : ∀ t ∈ U4, t * uElt a b c d e f = uElt a b c d e f * t := fun t ht => by
    have := Subgroup.mem_center_iff.mp hxmem.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have c1 := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hcen' _ (uElt_mem 1 0 0 0 0 0))
  have c2 := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hcen' _ (uElt_mem 0 1 0 0 0 0))
  have c3 := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hcen' _ (uElt_mem 0 0 1 0 0 0))
  simp only [coe_mul_uElt, coe_uElt] at c1 c2 c3
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := center_bits a b c d e f c1.symm c2.symm c3.symm
  have hf : f = 1 := by
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) f with h0 | h1
    · exfalso
      apply hx1
      subst h0
      apply Subtype.ext
      apply Subtype.ext
      exact uElt_zero
    · exact h1
  subst hf
  exact hxV

theorem conj_cases {V : Subgroup G4} {z u t : G4}
    (hV : ∀ w ∈ V, w = 1 ∨ w = z ∨ w = u ∨ w = z * u) (hw : t * u * t⁻¹ ∈ V) (hu1 : u ≠ 1)
    (huz : u ≠ z) (htz : t * z = z * t) : u * t = t * u ∨ z * u * t = t * u := by
  have hu : u = t⁻¹ * (t * u * t⁻¹) * t := by group
  rcases hV _ hw with h | h | h | h
  · exfalso
    apply hu1
    rw [h] at hu
    simpa using hu
  · exfalso
    apply huz
    rw [h] at hu
    rw [hu]
    calc t⁻¹ * z * t = t⁻¹ * (z * t) := by rw [mul_assoc]
      _ = t⁻¹ * (t * z) := by rw [htz]
      _ = z := by group
  · left
    calc u * t = (t * u * t⁻¹) * t := by rw [h]
      _ = t * u := by group
  · right
    calc z * u * t = (t * u * t⁻¹) * t := by rw [h]
      _ = t * u := by group

theorem core_sl4 {V : Subgroup G4} {e : G4} (hVU : V ≤ U4) (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v * v = 1) (hUV : U4 ≤ Subgroup.normalizer (V : Set G4)) (he1 : e ≠ 1)
    (he3 : e ^ 3 = 1) (hec : ∀ v ∈ V, e * v = v * e) : False := by
  classical
  have hzV : uElt 0 0 0 0 0 1 ∈ V := z0_mem hVU hV4 hUV
  have hz1 : uElt 0 0 0 0 0 1 ≠ 1 := by
    intro h
    have := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3) h
    simp [coe_uElt, uMat] at this
  obtain ⟨u, huV, hu1, huz, hVall⟩ := klein_elems hV4 hV2 hzV hz1
  obtain ⟨a, b, c, d, e', f, rfl⟩ := exists_uElt (hVU huV)
  have hzcomm : ∀ a' b' c' d' e'' f' : ZMod 2,
      uElt a' b' c' d' e'' f' * uElt 0 0 0 0 0 1 = uElt 0 0 0 0 0 1 * uElt a' b' c' d' e'' f' :=
    fun a' b' c' d' e'' f' => Subtype.ext (by
      simp only [coe_mul_uElt, coe_uElt]
      exact (zcomm_bits a' b' c' d' e'' f').symm)
  have hcj : ∀ t : G4, t ∈ U4 → uElt 0 0 0 0 0 1 * t = t * uElt 0 0 0 0 0 1 →
      t * uElt a b c d e' f * t⁻¹ ∈ V := fun t ht _ =>
    (Subgroup.mem_normalizer_iff.mp (hUV ht) _).mp huV
  have k1 := conj_cases hVall (hcj _ (uElt_mem 1 0 0 0 0 0) (hzcomm 1 0 0 0 0 0).symm) hu1 huz
    (hzcomm 1 0 0 0 0 0)
  have k2 := conj_cases hVall (hcj _ (uElt_mem 0 1 0 0 0 0) (hzcomm 0 1 0 0 0 0).symm) hu1 huz
    (hzcomm 0 1 0 0 0 0)
  have k3 := conj_cases hVall (hcj _ (uElt_mem 0 0 1 0 0 0) (hzcomm 0 0 1 0 0 0).symm) hu1 huz
    (hzcomm 0 0 1 0 0 0)
  have m1 : uMat a b c d e' f * uMat 1 0 0 0 0 0 = uMat 1 0 0 0 0 0 * uMat a b c d e' f ∨
      uMat 0 0 0 0 0 1 * uMat a b c d e' f * uMat 1 0 0 0 0 0 =
        uMat 1 0 0 0 0 0 * uMat a b c d e' f := by
    rcases k1 with h | h
    · left
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
    · right
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
  have m2 : uMat a b c d e' f * uMat 0 1 0 0 0 0 = uMat 0 1 0 0 0 0 * uMat a b c d e' f ∨
      uMat 0 0 0 0 0 1 * uMat a b c d e' f * uMat 0 1 0 0 0 0 =
        uMat 0 1 0 0 0 0 * uMat a b c d e' f := by
    rcases k2 with h | h
    · left
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
    · right
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
  have m3 : uMat a b c d e' f * uMat 0 0 1 0 0 0 = uMat 0 0 1 0 0 0 * uMat a b c d e' f ∨
      uMat 0 0 0 0 0 1 * uMat a b c d e' f * uMat 0 0 1 0 0 0 =
        uMat 0 0 1 0 0 0 * uMat a b c d e' f := by
    rcases k3 with h | h
    · left
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
    · right
      simpa [coe_mul_uElt, coe_uElt] using congrArg Subtype.val h
  have hb := shape1 a b c d e' f m1
  obtain ⟨ha, hc⟩ := shape2 a b c d e' f m2
  subst hb ha hc
  have hde : d ≠ 0 ∨ e' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) f with h0 | h1
    · exact hu1 (by rw [h0]; exact uElt_zero)
    · exact huz (by rw [h1])
  have ez := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hec _ hzV)
  have eu := congrArg (fun g : G4 => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) (hec _ huV)
  simp only [coe_mul_uElt, coe_uElt] at ez eu
  obtain ⟨h10, h20, h30, h21, h31, h32⟩ :=
    lower_bits (e : Matrix (Fin 4) (Fin 4) (ZMod 2)) d e' f hde ez eu
  have hup : ∀ i j : Fin 4, j < i → (e : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hij; decide)
        | simpa using h10
        | simpa using h20
        | simpa using h30
        | simpa using h21
        | simpa using h31
        | simpa using h32
  have hdet : (e : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := e.2
  rw [Matrix.det_of_isUpperTriangular (M := (e : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (fun i j hij => hup i j hij), Fin.prod_univ_four] at hdet
  obtain ⟨hd0, hd1, hd2, hd3⟩ := diag_bits _ _ _ _ hdet
  have heU : e ∈ U4 := ⟨hup, fun i => by fin_cases i <;> simpa using ‹_›⟩
  have hU2 : IsPGroup 2 ↥U4 := isSylow_U4.2.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU2) (⟨e, heU⟩ : ↥U4)
  have hdvd : 2 ^ k ∣ 3 := by
    rw [← hk]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext he3)
  have hk0 : 2 ^ k = 1 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
  rw [hk0, orderOf_eq_one_iff] at hk
  exact he1 (congrArg Subtype.val hk)

theorem not_clConfig_sl4 : ¬ ClConfig G4 := by
  intro h
  obtain ⟨V, e, hVU, hV4, hV2, hUV, he1, he3, hec⟩ := ClConfig.of_sylow isSylow_U4 h
  exact core_sl4 hVU hV4 hV2 hUV he1 he3 hec

end L4

theorem not_clConfig_of_psl4 {X : Type} [Group X] (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 4 2 1) :
    ¬ ClConfig X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let ψ : X ≃* G4 :=
    φ.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 4 K hK2)
  exact fun hc => not_clConfig_sl4 (hc.map ψ)

end CFSG.Quasithin.R3c12
