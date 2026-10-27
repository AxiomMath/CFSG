module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
import CFSG.GH74.KGroups.L3EpsBlockLin
import CFSG.LargeExtraspecial.S8CBFSL2
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.LargeExtraspecial.S8CBFCrit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.Sec11 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups


private lemma l02qj5a1_isMulCommutative_map_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (T : Subgroup H) :
    IsMulCommutative T ↔ IsMulCommutative (T.map e.symm.toMonoidHom) := by
  constructor
  · intro h
    haveI := h
    exact inferInstance
  · intro h
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.val_injective
    have h' : e.symm a * e.symm b = e.symm b * e.symm a :=
      congrArg Subtype.val
        (h.is_comm.comm (⟨e.symm a, ⟨a, a.2, rfl⟩⟩ : ↥(T.map e.symm.toMonoidHom))
          (⟨e.symm b, ⟨b, b.2, rfl⟩⟩ : ↥(T.map e.symm.toMonoidHom)))
    show (a : H) * (b : H) = (b : H) * (a : H)
    calc (a : H) * (b : H) = e (e.symm a * e.symm b) := by
          rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      _ = e (e.symm b * e.symm a) := by rw [h']
      _ = (b : H) * (a : H) := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]

private lemma l02qj5a1_quotient_two_abelian {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (h : ∀ P : Subgroup G, IsPGroup 2 P → IsMulCommutative P) :
    ∀ P' : Subgroup H, IsPGroup 2 P' → IsMulCommutative P' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P' hP'
  obtain ⟨S', hle⟩ := hP'.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (p := 2) (f := f) hf S'
  have hScoe : (S : Subgroup G).map f = (S' : Subgroup H) := by
    have := congrArg (fun X : Sylow 2 H => (X : Subgroup H)) hS
    simpa [Sylow.coe_mapSurjective] using this
  have hScomm : IsMulCommutative (S : Subgroup G) := h S S.isPGroup'
  haveI := hScomm
  have hmapcomm : IsMulCommutative ((S : Subgroup G).map f) := inferInstance
  rw [hScoe] at hmapcomm
  haveI : IsMulCommutative ↥(S' : Subgroup H) := hmapcomm
  have htop : IsMulCommutative ↥(S'.comap P'.subtype) :=
    Subgroup.comap_injective_isMulCommutative (S' : Subgroup H) (f := P'.subtype) P'.subtype_injective
  have htop_eq : S'.comap P'.subtype = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hle x.2
  rw [htop_eq] at htop
  rw [isMulCommutative_iff] at htop ⊢
  intro a b
  calc a * b = Subgroup.topEquiv (Subgroup.topEquiv.symm a * Subgroup.topEquiv.symm b) := by
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    _ = Subgroup.topEquiv (Subgroup.topEquiv.symm b * Subgroup.topEquiv.symm a) := by
        rw [htop (Subgroup.topEquiv.symm a) (Subgroup.topEquiv.symm b)]
    _ = b * a := by
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private def l02qj5a1_matA (E : Type) [Field E] : Matrix (Fin 3) (Fin 3) E :=
  !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private def l02qj5a1_matB (E : Type) [Field E] : Matrix (Fin 3) (Fin 3) E :=
  !![1, 0, 0; 0, 1, 1; 0, 0, 1]

private def l02qj5a1_uniA (E : Type) [Field E] : SpecialLinearGroup (Fin 3) E :=
  ⟨l02qj5a1_matA E, by simp [l02qj5a1_matA, Matrix.det_fin_three]⟩

private def l02qj5a1_uniB (E : Type) [Field E] : SpecialLinearGroup (Fin 3) E :=
  ⟨l02qj5a1_matB E, by simp [l02qj5a1_matB, Matrix.det_fin_three]⟩

private lemma l02qj5a1_matA_mul_matB_ne (E : Type) [Field E] :
    l02qj5a1_matA E * l02qj5a1_matB E ≠ l02qj5a1_matB E * l02qj5a1_matA E := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [l02qj5a1_matA, l02qj5a1_matB, Matrix.mul_apply, Fin.sum_univ_three] at h02

private lemma l02qj5a1_uniA_mul_uniB_ne (E : Type) [Field E] :
    l02qj5a1_uniA E * l02qj5a1_uniB E ≠ l02qj5a1_uniB E * l02qj5a1_uniA E := by
  intro h
  apply l02qj5a1_matA_mul_matB_ne E
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 3) E =>
    (M : Matrix (Fin 3) (Fin 3) E)) h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h'
  simpa [l02qj5a1_uniA, l02qj5a1_uniB] using h'

private lemma l02qj5a1_uniA_mem (E : Type) [Field E] :
    l02qj5a1_uniA E ∈ unitriangular 3 E := by
  rw [mem_unitriangular]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [l02qj5a1_uniA, l02qj5a1_matA]
  · intro i
    fin_cases i <;> simp [l02qj5a1_uniA, l02qj5a1_matA]

private lemma l02qj5a1_uniB_mem (E : Type) [Field E] :
    l02qj5a1_uniB E ∈ unitriangular 3 E := by
  rw [mem_unitriangular]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [l02qj5a1_uniB, l02qj5a1_matB]
  · intro i
    fin_cases i <;> simp [l02qj5a1_uniB, l02qj5a1_matB]

private lemma l02qj5a1_unitriangular_three_not_comm (E : Type) [Field E] :
    ¬ IsMulCommutative (unitriangular 3 E) := by
  intro h
  haveI := h
  let a : ↥(unitriangular 3 E) := ⟨l02qj5a1_uniA E, l02qj5a1_uniA_mem E⟩
  let b : ↥(unitriangular 3 E) := ⟨l02qj5a1_uniB E, l02qj5a1_uniB_mem E⟩
  have hcomm := mul_comm' a b
  exact l02qj5a1_uniA_mul_uniB_ne E (by
    simpa [a, b] using congrArg Subtype.val hcomm)

private lemma l02qj5a1_projUnitriangular_not_comm (E : Type) [Field E] :
    ¬ IsMulCommutative (projUnitriangular 3 E) := by
  intro h
  apply l02qj5a1_unitriangular_three_not_comm E
  haveI := h
  refine IsMulCommutative.of_comm fun a b => ?_
  apply Subtype.val_injective
  apply proj_injOn_unitriangular 3 (a * b).2 (b * a).2
  show proj 3 E (a.1 * b.1) = proj 3 E (b.1 * a.1)
  rw [map_mul, map_mul]
  exact congrArg Subtype.val
    (mul_comm' (⟨proj 3 E a.1, ⟨a.1, a.2, rfl⟩⟩ : projUnitriangular 3 E)
      (⟨proj 3 E b.1, ⟨b.1, b.2, rfl⟩⟩ : projUnitriangular 3 E))

private lemma l02qj5a1_projectiveSL_psl3_nonabelian_two (E : Type) [Field E] [Finite E] :
    ∃ T : Subgroup (projectiveSL 3 E), IsPGroup 2 T ∧ ¬ IsMulCommutative T := by
  by_cases h2 : CharP E 2
  ·
    haveI := h2
    refine ⟨projUnitriangular 3 E, ?_, l02qj5a1_projUnitriangular_not_comm E⟩
    obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := E) 2 (n := 3) (by norm_num)
    rw [← hS]
    exact S.isPGroup'
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk : ringChar E ≠ 2 := by
      intro h
      exact h2 (h ▸ ringChar.charP E)
    obtain ⟨-, -, hsyl⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.sl2_odd_field_involution_structure (k := E) hk
    let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) E) := default
    let φ : Matrix.SpecialLinearGroup (Fin 2) E →* projectiveSL 3 E := blockEmb
    refine ⟨(P : Subgroup _).map φ, IsPGroup.map P.isPGroup' φ, ?_⟩
    intro hcomm
    apply hsyl P
    haveI := hcomm
    have hcomap : IsMulCommutative
        (((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) E)).map φ).comap φ) :=
      Subgroup.comap_injective_isMulCommutative ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) E)).map φ)
        (f := φ) blockEmb_injective
    rw [Subgroup.comap_map_eq_self_of_injective blockEmb_injective
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) E))] at hcomap
    exact hcomap

private lemma l02qj5a1_psl3_nonabelian_two (E : Type) [Field E] [Finite E] :
    ∃ T : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin 3) E)), IsPGroup 2 T ∧
      ¬ IsMulCommutative T := by
  obtain ⟨T, hT2, hTna⟩ := l02qj5a1_projectiveSL_psl3_nonabelian_two E
  let e : LargeEvenProj (LargeEvenSLGroup (Fin 3) E) ≃* projectiveSL 3 E :=
    TypeA.recipeEquiv 3 E
  refine ⟨T.map e.symm.toMonoidHom, IsPGroup.map hT2 e.symm.toMonoidHom, ?_⟩
  intro hcomm
  exact hTna ((l02qj5a1_isMulCommutative_map_iff e T).mpr hcomm)

private lemma l02qj5a1_two_subgroup_of_S {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (_hσ : σ ^ 3 = 1) :
    ∀ P : Subgroup ↥(KS11Lie4Proof.d4ShortSL2 K σ.toRingHom), IsPGroup 2 P →
      IsMulCommutative P := by
  classical
  let L := orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer
  haveI : CharP L 2 := inferInstance
  let R := orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer
  have hSL2 : ∀ Q : Subgroup (SL2 L), IsPGroup 2 Q → IsMulCommutative Q := by
    intro Q hQ
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    exact CFSG.LargeExtraspecial.S8.sl2_comm_of_isPGroup Q hQ a.1 a.2 b.1 b.2
  let f : SL2 L →* ↥(R.range) := R.codRestrict R.range (fun g => ⟨g, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := y.2
    exact ⟨g, Subtype.ext hg⟩
  have hquot := l02qj5a1_quotient_two_abelian f hf hSL2
  let S := KS11Lie4Proof.d4ShortSL2 K σ.toRingHom
  let φ : ↥S →* ↥(R.range) :=
    { toFun := fun x => ⟨(x.1 : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).1, x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : (x.1 : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = y.1 := by
      apply Subtype.val_injective
      exact congrArg (fun z : ↥(R.range) => (z : ModGL TwistTag.D4.tag K)) hxy
    exact Subtype.ext h1
  intro P hP
  have hmap : IsMulCommutative (P.map φ) := hquot (P.map φ) (IsPGroup.map hP φ)
  refine IsMulCommutative.of_comm fun a b => ?_
  apply Subtype.val_injective
  apply hφinj
  have h' := hmap.is_comm.comm
    (⟨φ a.1, ⟨a.1, a.2, rfl⟩⟩ : ↥(P.map φ))
    (⟨φ b.1, ⟨b.1, b.2, rfl⟩⟩ : ↥(P.map φ))
  show φ (a.1 * b.1) = φ (b.1 * a.1)
  rw [map_mul, map_mul]
  exact congrArg Subtype.val h'

theorem kgLangT3_not_psl3_in_short {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hσ : σ ^ 3 = 1)
    (J : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hJS : J ≤ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (E : Type) [Field E] [Finite E]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSab : ∀ P : Subgroup ↥(KS11Lie4Proof.d4ShortSL2 K σ.toRingHom), IsPGroup 2 P →
      IsMulCommutative P := l02qj5a1_two_subgroup_of_S hσ
  have hJab : ∀ P : Subgroup ↥J, IsPGroup 2 P → IsMulCommutative P := by
    intro P hP
    let φ : ↥J →* ↥(KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :=
      { toFun := fun x => ⟨x.1, hJS x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hφinj : Function.Injective φ := by
      intro x y hxy
      have h1 : (x.1 : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = y.1 := by
        apply Subtype.val_injective
        exact congrArg (fun z : ↥(KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) => ((z : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K)) hxy
      exact Subtype.ext h1
    have hmap : IsMulCommutative (P.map φ) := hSab (P.map φ) (IsPGroup.map hP φ)
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.val_injective
    apply hφinj
    have h' := hmap.is_comm.comm
      (⟨φ a.1, ⟨a.1, a.2, rfl⟩⟩ : ↥(P.map φ))
      (⟨φ b.1, ⟨b.1, b.2, rfl⟩⟩ : ↥(P.map φ))
    show φ (a.1 * b.1) = φ (b.1 * a.1)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h'
  have hquot : ∀ P' : Subgroup (↥J ⧸ Subgroup.center ↥J), IsPGroup 2 P' → IsMulCommutative P' :=
    l02qj5a1_quotient_two_abelian (QuotientGroup.mk' (Subgroup.center ↥J))
      (QuotientGroup.mk'_surjective _) hJab
  obtain ⟨T, hT2, hTna⟩ := l02qj5a1_psl3_nonabelian_two E
  let T' : Subgroup (↥J ⧸ Subgroup.center ↥J) := T.map θ.symm.toMonoidHom
  have hT'2 : IsPGroup 2 T' := IsPGroup.map hT2 θ.symm.toMonoidHom
  have hT'comm : IsMulCommutative T' := hquot T' hT'2
  exact hTna ((l02qj5a1_isMulCommutative_map_iff θ T).mpr hT'comm)

end CFSG.StandardType
