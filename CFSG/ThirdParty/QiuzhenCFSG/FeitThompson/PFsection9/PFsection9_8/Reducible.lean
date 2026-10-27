module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Core

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public def quotientReducibleFamilyTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
        Fintype.card ι = p - 1 ∧
        (∀ i : ι,
          μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)) ∧
        ∀ χ : Section1.ClassFunction M,
          χ ∈ S →
            ¬ Section1.IsIrreducibleCharacterOnGroup χ →
              ∃ i : ι, μ i = χ


public theorem theorem_9_reducible_filter_card_of_transport_data_sec9
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {p : ℕ}
    {S : Finset (Section1.ClassFunction M)} :
    quotientReducibleFamilyTransportData_sec9 M p S →
        (reducibleCharacterFilter_sec9 M S).card = p - 1 := by
  classical
  intro hdata
  rcases hdata with ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, hall⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let R : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hRcard : R.card = Fintype.card ι := by
    simpa [R] using
      (Finset.card_image_of_injective (Finset.univ : Finset ι) hμinj)
  have hRmem :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ R ↔ χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ
    constructor
    · intro hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      exact hmem i
    · intro hχ
      rcases hall χ hχ.1 hχ.2 with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hReq : R = reducibleCharacterFilter_sec9 M S := by
    ext χ
    simpa [reducibleCharacterFilter_sec9] using hRmem χ
  rw [← hReq]
  exact hRcard.trans hcard


@[expose] public def nbRedMQuotientTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) [_hKnormal : (K.subgroupOf M).Normal]
    (_Wbar : Subgroup (M ⧸ K.subgroupOf M))
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
      Fintype.card ι = p - 1 ∧
      (∀ i : ι,
        μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)) ∧
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S →
          ¬ Section1.IsIrreducibleCharacterOnGroup χ →
            ∃ i : ι, μ i = χ

@[expose] public def nbRedMQuotientLowerTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) [_hKnormal : (K.subgroupOf M).Normal]
    (_Wbar : Subgroup (M ⧸ K.subgroupOf M))
    (p : ℕ)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∃ ι : Type u, ∃ instFintype : Fintype ι, ∃ instDecidableEq : DecidableEq ι,
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecidableEq
    ∃ μ : ι → Section1.ClassFunction M,
      Function.Injective μ ∧
      Fintype.card ι = p - 1 ∧
      ∀ i : ι,
        μ i ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup (μ i)

public theorem quotientReducibleFamilyTransportData_of_nbRedMQuotientTransportData_sec9
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G} [hKnormal : (K.subgroupOf M).Normal]
    {Wbar : Subgroup (M ⧸ K.subgroupOf M)}
    {p : ℕ}
    {S : Finset (Section1.ClassFunction M)} :
    nbRedMQuotientTransportData_sec9 M K Wbar p S →
      quotientReducibleFamilyTransportData_sec9 M p S := by
  intro hdata
  rcases hdata with
    ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, hall⟩
  refine ⟨ι, instFintype, instDecidableEq, ?_⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  exact ⟨μ, hμinj, hcard, hmem, hall⟩

public theorem le_normalizer_sup_of_le_normalizer_sec9
    {G : Type u} [Group G] (A B N : Subgroup G)
    (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hNB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hsup_closure :
        A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hxcl : x ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      simpa [hsup_closure] using hx
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun y _hy => n * y * n⁻¹ ∈ (A ⊔ B : Subgroup G)) ?_ ?_ ?_ ?_
      hxcl
    · intro y hy
      rcases hy with hyA | hyB
      · exact (le_sup_left : A ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNA hn) y).mp hyA)
      · exact (le_sup_right : B ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNB hn) y).mp hyB)
    · simp
    · intro y z _hy _hz hyP hzP
      simpa [mul_assoc] using (A ⊔ B).mul_mem hyP hzP
    · intro y _hy hyP
      simpa [mul_assoc] using (A ⊔ B).inv_mem hyP
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hforward_inv :
        ∀ y : G, y ∈ A ⊔ B → n⁻¹ * y * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G) := by
      intro y hy
      have hsup_closure :
          A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      have hycl : y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        simpa [hsup_closure] using hy
      refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
        (p := fun z _hz => n⁻¹ * z * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G))
        ?_ ?_ ?_ ?_ hycl
      · intro z hz
        rcases hz with hzA | hzB
        · exact (le_sup_left : A ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNA hninv) z).mp hzA)
        · exact (le_sup_right : B ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNB hninv) z).mp hzB)
      · simp
      · intro z w _hz _hw hzP hwP
        simpa [mul_assoc] using (A ⊔ B).mul_mem hzP hwP
      · intro z _hz hzP
        simpa [mul_assoc] using (A ⊔ B).inv_mem hzP
    have := hforward_inv (n * x * n⁻¹) hx
    simpa [mul_assoc] using this

public theorem conj_mem_sup_of_commutator_mem_left_sec9
    {G : Type u} [Group G]
    {A B : Subgroup G} {n b : G}
    (hb : b ∈ B) (hcomm : ⁅b, n⁆ ∈ A) :
    n * b * n⁻¹ ∈ A ⊔ B := by
  have hcomm_inv : ⁅b, n⁆⁻¹ ∈ A := A.inv_mem hcomm
  have heq : n * b * n⁻¹ = ⁅b, n⁆⁻¹ * b := by
    simp [commutatorElement_def, mul_assoc]
  rw [heq]
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hcomm_inv) (Subgroup.mem_sup_right hb)

public theorem le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    {G : Type u} [Group G]
    (A B N : Subgroup G)
    (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ n : G, n ∈ N → ∀ b : G, b ∈ B → ⁅b, n⁆ ∈ A) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hsup_closure :
        A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hxcl : x ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      simpa [hsup_closure] using hx
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun y _hy => n * y * n⁻¹ ∈ (A ⊔ B : Subgroup G)) ?_ ?_ ?_ ?_
      hxcl
    · intro y hy
      rcases hy with hyA | hyB
      · exact (le_sup_left : A ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hNA hn) y).mp hyA)
      · exact conj_mem_sup_of_commutator_mem_left_sec9 hyB (hcomm n hn y hyB)
    · simp
    · intro y z _hy _hz hyP hzP
      simpa [mul_assoc] using (A ⊔ B).mul_mem hyP hzP
    · intro y _hy hyP
      simpa [mul_assoc] using (A ⊔ B).inv_mem hyP
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hforward_inv :
        ∀ y : G, y ∈ A ⊔ B → n⁻¹ * y * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G) := by
      intro y hy
      have hsup_closure :
          A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      have hycl : y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        simpa [hsup_closure] using hy
      refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
        (p := fun z _hz => n⁻¹ * z * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G))
        ?_ ?_ ?_ ?_ hycl
      · intro z hz
        rcases hz with hzA | hzB
        · exact (le_sup_left : A ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hNA hninv) z).mp hzA)
        · exact conj_mem_sup_of_commutator_mem_left_sec9 hzB
            (hcomm n⁻¹ hninv z hzB)
      · simp
      · intro z w _hz _hw hzP hwP
        simpa [mul_assoc] using (A ⊔ B).mul_mem hzP hwP
      · intro z _hz hzP
        simpa [mul_assoc] using (A ⊔ B).inv_mem hzP
    have := hforward_inv (n * x * n⁻¹) hx
    simpa [mul_assoc] using this

public theorem quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
    {G : Type u} [Group G]
    {M MF U H0 C N : Subgroup G}
    (hNleM : N ≤ M)
    (hNnormU : N ≤ Subgroup.normalizer (U : Set G))
    (hNnormMF : N ≤ Subgroup.normalizer (MF : Set G))
    (hH0leM : H0 ≤ M)
    (hH0normalM : (H0.subgroupOf M).Normal)
    (hC : quotientCentralizerIn MF H0 U C) :
    N ≤ Subgroup.normalizer (C : Set G) := by
  have hforward :
      ∀ n : G, n ∈ N → ∀ x : G, x ∈ C → n * x * n⁻¹ ∈ C := by
    intro n hn x hxC
    have hxU : x ∈ U := hC.1 hxC
    have hconjU : n * x * n⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hNnormU hn) x).mp hxU
    rw [(hC.2 (n * x * n⁻¹) hconjU)]
    intro h hhMF
    have hninv_normMF : n⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem (hNnormMF hn)
    have hh' : n⁻¹ * h * n ∈ MF := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hninv_normMF h).mp hhMF
    have hcomm : ⁅x, n⁻¹ * h * n⁆ ∈ H0 :=
      (hC.2 x hxU).mp hxC (n⁻¹ * h * n) hh'
    let nM : M := ⟨n, hNleM hn⟩
    let cM : M := ⟨⁅x, n⁻¹ * h * n⁆, hH0leM hcomm⟩
    have hcM : cM ∈ H0.subgroupOf M := by
      simpa [cM, Subgroup.mem_subgroupOf] using hcomm
    have hconjM : nM * cM * nM⁻¹ ∈ H0.subgroupOf M :=
      hH0normalM.conj_mem cM hcM nM
    have hconjH0 : n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ ∈ H0 := by
      simpa [nM, cM, Subgroup.mem_subgroupOf] using hconjM
    have hcomm_eq :
        ⁅n * x * n⁻¹, h⁆ = n * ⁅x, n⁻¹ * h * n⁆ * n⁻¹ := by
      simp [commutatorElement_def]
      group
    rw [hcomm_eq]
    exact hconjH0
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward n hn x
  · intro hx
    have hninv : n⁻¹ ∈ N := N.inv_mem hn
    have hmem := hforward n⁻¹ hninv (n * x * n⁻¹) hx
    simpa [mul_assoc] using hmem

public theorem subgroupOf_subgroupOf_normal_of_le_normalizer_sec9
    {G : Type u} [Group G] {M D H : Subgroup G}
    (hHD : H ≤ D) (hDnormH : D ≤ Subgroup.normalizer (H : Set G)) :
    ((H.subgroupOf M).subgroupOf (D.subgroupOf M)).Normal := by
  have hHmDm : H.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHD hx
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHmDm).2 ?_
  intro d hdD
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hdG : ((d : M) : G) ∈ D := by
      simpa [Subgroup.mem_subgroupOf] using hdD
    have hxG : ((x : M) : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hconjG : ((d : M) : G) * ((x : M) : G) * ((d : M) : G)⁻¹ ∈ H :=
      ((Subgroup.mem_normalizer_iff.mp (hDnormH hdG) ((x : M) : G)).mp hxG)
    simpa [Subgroup.mem_subgroupOf] using hconjG
  · intro hx
    have hdG : ((d : M) : G) ∈ D := by
      simpa [Subgroup.mem_subgroupOf] using hdD
    have hconjG : ((d : M) : G) * ((x : M) : G) * ((d : M) : G)⁻¹ ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxG : ((x : M) : G) ∈ H :=
      ((Subgroup.mem_normalizer_iff.mp (hDnormH hdG) ((x : M) : G)).mpr hconjG)
    simpa [Subgroup.mem_subgroupOf] using hxG

public theorem normalizer_le_normalizer_commutator_self_sec9
    {G : Type u} [Group G] (C U : Subgroup G)
    (hU_norm_C : U ≤ Subgroup.normalizer (C : Set G)) :
    U ≤ Subgroup.normalizer ((⁅C, C⁆ : Subgroup G) : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← Subgroup.map_subtype_commutator C] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let φ : C ≃* C :=
      { toFun := fun c =>
          ⟨u * (c : G) * u⁻¹,
            ((Subgroup.mem_normalizer_iff.mp (hU_norm_C hu) (c : G)).mp c.property)⟩
        invFun := fun c =>
          ⟨u⁻¹ * (c : G) * (u⁻¹)⁻¹,
            ((Subgroup.mem_normalizer_iff.mp
              (hU_norm_C (U.inv_mem hu)) (c : G)).mp c.property)⟩
        left_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        right_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [mul_assoc] }
    refine ⟨φ y, ?_, ?_⟩
    · have hycomap : y ∈ (commutator C).comap φ.toMonoidHom := by
        exact (SetLike.ext_iff.mp
          ((inferInstance : (commutator C).Characteristic).fixed φ) y).mpr hy
      simpa [Subgroup.mem_comap] using hycomap
    · simpa [φ, hyx]
  · intro hx
    rw [← Subgroup.map_subtype_commutator C] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let φ : C ≃* C :=
      { toFun := fun c =>
          ⟨u⁻¹ * (c : G) * (u⁻¹)⁻¹,
            ((Subgroup.mem_normalizer_iff.mp
              (hU_norm_C (U.inv_mem hu)) (c : G)).mp c.property)⟩
        invFun := fun c =>
          ⟨u * (c : G) * u⁻¹,
            ((Subgroup.mem_normalizer_iff.mp (hU_norm_C hu) (c : G)).mp c.property)⟩
        left_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        right_inv := by
          intro c
          apply Subtype.ext
          simp [mul_assoc]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [mul_assoc] }
    refine ⟨φ y, ?_, ?_⟩
    · have hycomap : y ∈ (commutator C).comap φ.toMonoidHom := by
        exact (SetLike.ext_iff.mp
          ((inferInstance : (commutator C).Characteristic).fixed φ) y).mpr hy
      simpa [Subgroup.mem_comap] using hycomap
    · calc
        C.subtype (φ y) = u⁻¹ * C.subtype y * u := by simp [φ]
        _ = u⁻¹ * (u * x * u⁻¹) * u := by rw [hyx]
        _ = x := by group

public theorem pf4_piColumn_injective_of_xChar_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) := by
  classical
  have hresCol :
      ∀ j : J,
        Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) =
          (Fintype.card I : ℂ) • xChar j := by
    intro j
    ext t
    calc
      Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) t =
          ∑ i : I, piChar i j t := by
            simp [Section4Scratch.piColumn, Section1.subgroupRestriction]
      _ = ∑ _i : I, xChar j t := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Section1.subgroupRestriction] using congrFun (h45a.1 i j) t
      _ = (Fintype.card I : ℂ) * xChar j t := by
            simp [Finset.sum_const]
      _ = ((Fintype.card I : ℂ) • xChar j) t := by
            simp
  have hcardI_ne : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
  have hxInj : Function.Injective xChar :=
    Section4Scratch.xChar_injective_pf45 K piChar xChar h45a i0 j0 ω σ
      deltaSign hω h43b
  intro j k hEq
  have hsmul :
      (Fintype.card I : ℂ) • xChar j =
        (Fintype.card I : ℂ) • xChar k := by
    calc
      (Fintype.card I : ℂ) • xChar j =
          Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) :=
        (hresCol j).symm
      _ = Section1.subgroupRestriction K (Section4Scratch.piColumn piChar k) := by
        exact congrArg (Section1.subgroupRestriction K) hEq
      _ = (Fintype.card I : ℂ) • xChar k :=
        hresCol k
  have hxEq : xChar j = xChar k := by
    ext t
    have ht := congrFun hsmul t
    exact mul_left_cancel₀ hcardI_ne (by simpa using ht)
  exact hxInj hxEq

@[expose] public def nbRedMPF4QuotientColumnData_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (p : ℕ) : Prop :=
  ∃ I : Type u, ∃ J : Type u,
    ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
      ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
        letI : Fintype I := instFintypeI
        letI : Fintype J := instFintypeJ
        letI : DecidableEq I := instDecidableEqI
        letI : DecidableEq J := instDecidableEqJ
        ∃ i0 : I, ∃ j0 : J,
          ∃ ω : I → J → Section1.ClassFunction W,
            ∃ hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω,
              ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L,
                ∃ piChar : I → J → Section1.ClassFunction L,
                  ∃ deltaSign : J → ℂ,
                    ∃ xChar : J → Section1.ClassFunction K,
                      Section4.theorem_4_3_b_statement
                        W1 W2 W I J i0 j0 ω σ piChar deltaSign hω ∧
                      Section4.theorem_4_3_c_statement
                        W2 W I J piChar deltaSign ω ∧
                      Section4Scratch.theorem_4_5_a_statement K piChar xChar ∧
                      Section4Scratch.theorem_4_5_b_statement K piChar xChar ∧
                      deltaSign j0 = 1 ∧
                      piChar i0 j0 = Section1.principalCharacter L ∧
                      Function.Injective
                        (fun j : J => Section4Scratch.piColumn piChar j) ∧
                      (Finset.univ.erase j0).card = p - 1

public theorem theorem_9_nb_redM_quotient_notation_3_3_source_core_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L) :
    Section4.hypothesis_4_2_statement K W1 W2 W →
      ∃ I : Type u, ∃ J : Type u,
        ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
          ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
            letI : Fintype I := instFintypeI
            letI : Fintype J := instFintypeJ
            letI : DecidableEq I := instDecidableEqI
            letI : DecidableEq J := instDecidableEqJ
            ∃ i0 : I, ∃ j0 : J,
              ∃ ω : I → J → Section1.ClassFunction W,
                Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω := by
  intro h42
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (Section4.theorem_4_3_a K W1 W2 W h42).2
  exact Section3.exists_notation_3_3_of_hypothesis_3_1 h31

public theorem theorem_9_nb_redM_pf4_quotient_column_data_of_notation_sec9
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (p : ℕ) :
    Section4.hypothesis_4_2_statement K W1 W2 W →
      Nat.card W2 = p →
        (∃ I : Type u, ∃ J : Type u,
          ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
            ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
              letI : Fintype I := instFintypeI
              letI : Fintype J := instFintypeJ
              letI : DecidableEq I := instDecidableEqI
              letI : DecidableEq J := instDecidableEqJ
              ∃ i0 : I, ∃ j0 : J,
                ∃ ω : I → J → Section1.ClassFunction W,
                  Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) →
          nbRedMPF4QuotientColumnData_sec9 K W1 W2 W p := by
  classical
  intro h42 hW2card hnotation
  rcases hnotation with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases Section4.theorem_4_3 K W1 W2 W I J i0 j0 ω h42 hω with
    ⟨_h43a, σ, piChar, deltaSign, h43b, h43c, _h43d⟩
  rcases Section4Scratch.theorem_4_5 K W1 W2 W i0 j0 ω σ piChar deltaSign
      h42 hω h43b h43c with
    ⟨xChar, h45a, h45b⟩
  have h44 := Section4.proposition_4_4 K W1 W2 W I J i0 j0 ω σ
    piChar deltaSign h42 hω h43b h43c
  have hpiColumnInj :
      Function.Injective (fun j : J => Section4Scratch.piColumn piChar j) :=
    pf4_piColumn_injective_of_xChar_sec9
      (K := K) (W1 := W1) (W2 := W2) (W := W) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (piChar := piChar) (xChar := xChar)
      (deltaSign := deltaSign) hω h43b h45a
  have hJcard : Fintype.card J = p := by
    calc
      Fintype.card J = Nat.card W2 := hω.card_right
      _ = p := hW2card
  have hnonbaseCard : (Finset.univ.erase j0).card = p - 1 := by
    calc
      (Finset.univ.erase j0).card = Fintype.card J - 1 := by simp
      _ = p - 1 := by rw [hJcard]
  refine
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω, σ, piChar, deltaSign, xChar, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hnonbaseCard⟩
  · exact h43b
  · exact h43c
  · exact h45a
  · exact h45b
  · exact h44.2.1
  · exact h44.2.2
  · exact hpiColumnInj

public theorem pf4_exists_ne_one_mem_of_natCard_ne_one_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) (hK : Nat.card K ≠ 1) :
    ∃ x, x ∈ K ∧ x ≠ 1 := by
  by_contra hcontra
  have hforall : ∀ x : K, x = 1 := by
    intro x
    by_contra hx
    have hx' : (x : L) ≠ 1 := by
      intro hx1
      exact hx (Subtype.ext hx1)
    exact hcontra ⟨x, x.2, hx'⟩
  have hcard : Nat.card K = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨1, fun x => hforall x⟩
  exact hK hcard

public theorem pf4_w2_le_K_of_hypothesis_4_2_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
    hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases pf4_exists_ne_one_mem_of_natCard_ne_one_sec9 W1 hcard1 with
    ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

public theorem pf4_hypothesis_4_6_self_of_hypothesis_4_2_sec9
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    Section4Scratch.hypothesis_4_6_statement K W1 W2 W K
      ({x : L | x ∈ K ∧ x ≠ 1}) := by
  classical
  have h42' := h42
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hW1card, _hcyc2, _hW2card,
    _hcent, _hW1, hW2, _hW, _hodd⟩
  have hKnorm : K.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rcases hsemi.mul_surjective g trivial with ⟨k, hk, w, hw, hg⟩
    rw [hg]
    have hconjW : Section2.conjBy w n ∈ K := hsemi.right_normalizes_left w hw n hn
    have hconj : k * (w * n * w⁻¹) * k⁻¹ ∈ K := by
      exact K.mul_mem (K.mul_mem hk hconjW) (K.inv_mem hk)
    simpa [Section2.conjBy, mul_assoc] using hconj
  have hW2K : W2 ≤ K := pf4_w2_le_K_of_hypothesis_4_2_sec9 h42'
  refine ⟨⟨hsemi, _hHall, _hcyc1, _hW1card, _hcyc2, _hW2card,
    _hcent, _hW1, hW2, _hW, _hodd⟩, hKnorm, ?_, le_rfl, ?_, ?_⟩
  · exact hW2K
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
    exact ⟨(Subgroup.mem_inf.mp hxk.1).1, by simpa using hxk.2⟩
  · intro x hx
    exact hx

public theorem pf4_hypothesis_4_6_mf_quotient_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ)
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hKnormal : (K.subgroupOf M).Normal) :
    letI : (K.subgroupOf M).Normal := hKnormal
    let qM : M →* M ⧸ K.subgroupOf M :=
      QuotientGroup.mk' (K.subgroupOf M)
    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
      ((ambientDerivedSubgroup M).subgroupOf M).map qM
    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
      (W1.subgroupOf M).map qM
    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
      (W2.subgroupOf M).map qM
    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
      ((W1 ⊔ W2).subgroupOf M).map qM
    let Hbar : Subgroup (M ⧸ K.subgroupOf M) :=
      (MF.subgroupOf M).map qM
    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
      Section4Scratch.hypothesis_4_6_statement Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
  classical
  intro qM Kbar W1bar W2bar Wbar Hbar h42q
  have hMFnormalM : (MF.subgroupOf M).Normal := by
    rcases h92.mf.1 with ⟨_hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
    exact hMFnormalM
  have hHbarNormal : Hbar.Normal := by
    simpa [Hbar, qM] using
      (hMFnormalM.map qM (QuotientGroup.mk'_surjective (K.subgroupOf M)))
  have hW2MF : W2 ≤ MF := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2le.trans inf_le_left
  have hMFD : MF ≤ ambientDerivedSubgroup M :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW2barHbar : W2bar ≤ Hbar := by
    intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    refine ⟨y, ?_, hxy⟩
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hyW2
    simpa [Subgroup.mem_subgroupOf] using hW2MF hyW2G
  have hHbarKbar : Hbar ≤ Kbar := by
    intro x hx
    rcases hx with ⟨y, hyMF, hxy⟩
    refine ⟨y, ?_, hxy⟩
    have hyMFG : ((y : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hyMF
    simpa [Subgroup.mem_subgroupOf] using hMFD hyMFG
  refine ⟨h42q, hHbarNormal, hW2barHbar, hHbarKbar, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨_h, hxcentral⟩
    exact ⟨(Subgroup.mem_inf.mp hxcentral.1).1, by simpa using hxcentral.2⟩
  · intro x hx
    exact hx


public theorem quotientInflatedCharacter_irreducible_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.IsIrreducibleCharacterOnGroup
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) := by
  classical
  rcases hθbar with ⟨n, ρ, hρirr, hθeq⟩
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  refine ⟨n, ρ.comp qH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective ρ qH
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) H) hρirr
  · ext h
    simp [qH, hθeq, Representation.character]

public theorem quotientInflatedCharacter_subgroupInKernel_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    (θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))) :
    Section1.subgroupInKernel'
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))
      (Z.subgroupOf H) := by
  classical
  intro z
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  have hzq : qH z = 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' Z ((z : H) : L) = 1
    exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
  change θbar (qH z) = θbar (qH 1)
  rw [hzq]
  rfl

public theorem quotientInflatedCharacter_not_subgroupInKernel_of_map_sec9
    {L : Type u} [Group L] [Finite L]
    {H N Z : Subgroup L} [Z.Normal]
    (hHN : H ≤ N)
    {θbar : Section1.ClassFunction (N.map (QuotientGroup.mk' Z))}
    (hnot : ¬ Section1.subgroupInKernel' θbar
      ((H.map (QuotientGroup.mk' Z)).subgroupOf (N.map (QuotientGroup.mk' Z)))) :
    ¬ Section1.subgroupInKernel'
      (fun n : N => θbar (((QuotientGroup.mk' Z).subgroupMap N) n))
      (H.subgroupOf N) := by
  classical
  intro hker
  apply hnot
  intro a
  have haH : ((a : N.map (QuotientGroup.mk' Z)) : L ⧸ Z) ∈
      H.map (QuotientGroup.mk' Z) := by
    exact a.2
  rcases haH with ⟨h, hhH, hha⟩
  let n : N := ⟨h, hHN hhH⟩
  have hnH : n ∈ H.subgroupOf N := by
    simpa [n, Subgroup.mem_subgroupOf] using hhH
  have hq : ((QuotientGroup.mk' Z).subgroupMap N) n =
      (a : N.map (QuotientGroup.mk' Z)) := by
    ext
    exact hha
  calc
    θbar a = θbar (((QuotientGroup.mk' Z).subgroupMap N) n) := by rw [hq]
    _ = Section1.degree
        (fun n : N => θbar (((QuotientGroup.mk' Z).subgroupMap N) n)) :=
          hker ⟨n, hnH⟩
    _ = Section1.degree θbar := by simp [Section1.degree]

public theorem quotientInducedCF_eq_of_inducedCF_eq_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    {θ η : Section1.ClassFunction H}
    (h : Section1.inducedCF H θ = Section1.inducedCF H η) :
    Section1.quotientInducedCF H Z θ = Section1.quotientInducedCF H Z η := by
  classical
  ext q
  simp [Section1.quotientInducedCF, h]

public theorem quotientInducedCF_inflated_eq_inducedCF_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.quotientInducedCF H Z
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨n, ρ, _hρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin n → ℂ) := ρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hkerRep : Section1.subgroupInRepresentationKernel θrep (Z.subgroupOf H) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
      (Z.subgroupOf H)).mp hker
  have hthetaQuot_eq : Section1.quotientThetaCharacter H Z θrep = θbar := by
    ext y
    rcases Section1.quotientImageSubgroup_exists_preimage H Z y with ⟨h, hy⟩
    let hmem : ((h : L) : L ⧸ Z) ∈ Section1.quotientImageSubgroup H Z :=
      ⟨(h : L), h.2, rfl⟩
    have hy' : y = ⟨((h : L) : L ⧸ Z), hmem⟩ := by
      ext
      exact hy.symm
    rw [hy']
    calc
      Section1.quotientThetaCharacter H Z θrep ⟨((h : L) : L ⧸ Z), hmem⟩ =
          θrep.character h := by
            exact Section1.quotientThetaCharacter_mk H Z θrep hkerRep h hmem
      _ = θbar (qH h) := by rw [hθrep_char]
      _ = θbar ⟨((h : L) : L ⧸ Z), hmem⟩ := by rfl
  calc
    Section1.quotientInducedCF H Z
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) =
        Section1.quotientInducedCF H Z θrep.character := by
          rw [hθrep_char]
    _ = Section1.inducedCF (Section1.quotientImageSubgroup H Z)
          (Section1.quotientThetaCharacter H Z θrep) := by
          exact Section1.proposition_1_6_b_classFunction H Z hZH θrep hker
    _ = Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar := by
          simp [Section1.quotientImageSubgroup, hthetaQuot_eq]

public theorem quotientInflatedInducedCF_not_irreducible_of_quotient_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotRed : ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    ¬ Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  intro horig
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hindKer : Section1.subgroupInKernel'
      (Section1.inducedCF H θrep.character) Z :=
    (Section1.proposition_1_6_a H Z hZH θrep).mp hθker
  have hindKer' : Section1.subgroupInKernel'
      (Section1.inducedCF H (fun h : H => θbar (qH h))) Z := by
    simpa [hθrep_char] using hindKer
  rcases horig with ⟨n, ρ, hρirr, hρeq⟩
  have hρkerCF : Section1.subgroupInKernel' ρ.character Z := by
    simpa [← hρeq, qH] using hindKer'
  have hρkerRep : Section1.subgroupInRepresentationKernel ρ Z :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ Z).mp hρkerCF
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρq : Representation ℂ (L ⧸ Z) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ Z hρkerRep
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro g
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z)
    simpa [hcomp_eq] using hρirr
  have hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    refine ⟨n, ρq, hρqirr, ?_⟩
    symm
    ext y
    rcases QuotientGroup.mk'_surjective Z y with ⟨g, rfl⟩
    calc
      ρq.character (QuotientGroup.mk' Z g) = ρ.character g := by
        simpa [ρq, Representation.character] using
          congrArg (LinearMap.trace ℂ (Fin n → ℂ))
            (Section1.quotientRepresentationOfKernelSubgroup_mk ρ Z hρkerRep g)
      _ = Section1.inducedCF H (fun h : H => θbar (qH h)) g := by
        change ρ.character g =
          Section1.inducedCF H
            (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) g
        exact (congrFun hρeq g).symm
      _ = Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))
            (QuotientGroup.mk' Z g) := by
        rw [← hθrep_char]
        exact (Section1.quotientInducedCF_mk H Z hZH θrep
          ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
            (Z.subgroupOf H)).mp hθker) g).symm
  have hqeq := quotientInducedCF_inflated_eq_inducedCF_sec9
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar) := by
    simpa [qH, hqeq] using hquotIrr
  exact hquotRed hquotIrr'

public theorem quotientInflatedInducedCF_irreducible_of_quotient_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [H.Normal] [Z.Normal]
    (hZH : Z ≤ H)
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar)
    (hquotIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (H.map (QuotientGroup.mk' Z)) θbar)) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF H
        (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))) := by
  classical
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  rcases hθbar with ⟨m, θρ, hθρirr, hθeq⟩
  let θrep : Representation ℂ H (Fin m → ℂ) := θρ.comp qH
  have hθrep_char :
      θrep.character = fun h : H => θbar (qH h) := by
    ext h
    simp [θrep, qH, hθeq, Representation.character]
  have hθker : Section1.subgroupInKernel' θrep.character (Z.subgroupOf H) := by
    rw [hθrep_char]
    exact quotientInflatedCharacter_subgroupInKernel_sec9 θbar
  have hqeq := quotientInducedCF_inflated_eq_inducedCF_sec9
    (H := H) (Z := Z) hZH (θbar := θbar) ⟨m, θρ, hθρirr, hθeq⟩
  have hquotIrr' : Section1.IsIrreducibleCharacterOnGroup
      (Section1.quotientInducedCF H Z (fun h : H => θbar (qH h))) := by
    simpa [qH, hqeq] using hquotIrr
  rcases hquotIrr' with ⟨n, ρq, hρqirr, hρqeq⟩
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρorig : Representation ℂ L (Fin n → ℂ) := ρq.comp q
  refine ⟨n, ρorig, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective ρq q
      (QuotientGroup.mk'_surjective Z) hρqirr
  · ext g
    calc
      Section1.inducedCF H (fun h : H => θbar (qH h)) g =
          Section1.quotientInducedCF H Z (fun h : H => θbar (qH h)) (q g) := by
            rw [← hθrep_char]
            exact (Section1.quotientInducedCF_mk H Z hZH θrep
              ((Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel θrep
                (Z.subgroupOf H)).mp hθker) g).symm
      _ = ρq.character (q g) := by
            exact congrFun hρqeq (q g)
      _ = ρorig.character g := by
            simp [ρorig, q, Representation.character]

public theorem exists_quotient_character_of_subgroupInKernel_sec9
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (Z.subgroupOf H)) :
    ∃ θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z)),
      Section1.IsIrreducibleCharacterOnGroup θbar ∧
        θ = fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hkerRep : Section1.subgroupInRepresentationKernel ρ (Z.subgroupOf H) := by
    apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (Z.subgroupOf H)).mp
    simpa [hθeq] using hθker
  let θbarRep : Representation ℂ (Section1.quotientImageSubgroup H Z) (Fin n → ℂ) :=
    Section1.quotientThetaRepresentation H Z ρ hkerRep
  have hθbar_irr : Representation.IsIrreducible θbarRep := by
    let qH0 : H →* H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H)
    let ρqH : Representation ℂ (H ⧸ Z.subgroupOf H) (Fin n → ℂ) :=
      Section1.quotientRepresentationOfKernelSubgroup ρ (Z.subgroupOf H) hkerRep
    have hρqH_comp : ρqH.comp qH0 = ρ := by
      apply MonoidHom.ext
      intro h
      exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
        (Z.subgroupOf H) hkerRep h
    have hρqH_irr : Representation.IsIrreducible ρqH := by
      apply Section6.representation_isIrreducible_of_comp_surjective ρqH qH0
        (QuotientGroup.mk'_surjective (Z.subgroupOf H))
      simpa [hρqH_comp] using hρirr
    let e : H ⧸ Z.subgroupOf H ≃* Section1.quotientImageSubgroup H Z :=
      quotientSubgroupRangeEquiv H Z
    have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    change Representation.IsIrreducible (ρqH.comp e.symm.toMonoidHom)
    exact Section6.representation_isIrreducible_comp_surjective ρqH
      e.symm.toMonoidHom hsurj hρqH_irr
  let θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z)) := by
    simpa [Section1.quotientImageSubgroup] using θbarRep.character
  have hθbar_irr' : Section1.IsIrreducibleCharacterOnGroup θbar := by
    unfold Section1.IsIrreducibleCharacterOnGroup
    exact ⟨n, θbarRep, hθbar_irr, rfl⟩
  refine ⟨θbar, hθbar_irr', ?_⟩
  ext h
  let qH : H →* H.map (QuotientGroup.mk' Z) := (QuotientGroup.mk' Z).subgroupMap H
  let hmem : ((h : L) : L ⧸ Z) ∈ Section1.quotientImageSubgroup H Z :=
    ⟨(h : L), h.2, rfl⟩
  calc
    θ h = ρ.character h := by rw [hθeq]
    _ = θbarRep.character ⟨((h : L) : L ⧸ Z), hmem⟩ := by
          exact (Section1.quotientThetaRepresentation_character_mk H Z ρ hkerRep h hmem).symm
    _ = θbar (qH h) := by rfl

public theorem theorem_9_nb_redM_pf4_nonbase_not_MF_kernel_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ)
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    [hKnormal : (K.subgroupOf M).Normal]
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 j : J}
    {ω : I → J → Section1.ClassFunction
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    {σ : Section1.ClassFunction
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) →ₗ[ℂ]
        Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {piChar : I → J → Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {xChar : J → Section1.ClassFunction
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    {deltaSign : J → ℂ}
    (h42q : Section4.hypothesis_4_2_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))))
    (hω : Section3.notation_3_3_statement
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J i0 j0 ω σ piChar
      deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement
      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      (((W1 ⊔ W2).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) I J piChar deltaSign ω)
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (hj : j ∈ Finset.univ.erase j0) :
    ¬ Section1.subgroupInKernel'
      (fun h : (ambientDerivedSubgroup M).subgroupOf M =>
        xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
          ((ambientDerivedSubgroup M).subgroupOf M)) h))
      ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) := by
  classical
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  let Hbar : Subgroup (M ⧸ K.subgroupOf M) := (MF.subgroupOf M).map qM
  have hj_ne : j ≠ j0 := (Finset.mem_erase.mp hj).1
  have h46 :
      Section4Scratch.hypothesis_4_6_statement Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
    simpa [qM, Kbar, W1bar, W2bar, Wbar, Hbar, Nsub] using
      pf4_hypothesis_4_6_mf_quotient_sec9 M MF U W1 W2 K q h92
        (inferInstance : (K.subgroupOf M).Normal) h42q
  have h47 : Section4Scratch.theorem_4_7_statement Kbar Hbar
      ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) :=
    Section4Scratch.theorem_4_7 Kbar W1bar W2bar Wbar Hbar
      ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) h46
  have hnonkerBar :
      ¬ Section1.subgroupInKernel' (xChar j) (Hbar.subgroupOf Kbar) := by
    have hnonbase :
        Section4Scratch.theorem_4_7_nonbase_column_statement
          Kbar Hbar ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1})
          j0 piChar xChar := by
      exact Section4Scratch.theorem_4_7_nonbase_column
        Kbar W1bar W2bar Wbar Hbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1})
        i0 j0 ω σ piChar xChar deltaSign h46 h45a hω h43b h43c h47
    exact (hnonbase j hj_ne).1
  have hMFD : MF.subgroupOf M ≤ Nsub := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M :=
      MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92 hxMF
    simpa [Nsub, Subgroup.mem_subgroupOf] using hxD
  simpa [qM, Nsub, Kbar, Hbar] using
    quotientInflatedCharacter_not_subgroupInKernel_of_map_sec9
      (H := MF.subgroupOf M) (N := Nsub) (Z := K.subgroupOf M)
      hMFD hnonkerBar

public theorem pf4_reducible_kernelInducedFamily_member_is_nonbase_inflated_column_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF K : Subgroup G)
    [hKnormal : (K.subgroupOf M).Normal]
    (S : Finset (Section1.ClassFunction M))
    (hKD : K ≤ ambientDerivedSubgroup M)
    (hS : kernelInducedFamily M (ambientDerivedSubgroup M) MF K S)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {i0 : I} {j0 : J}
    {piChar : I → J → Section1.ClassFunction (M ⧸ K.subgroupOf M)}
    {xChar : J → Section1.ClassFunction
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M)))}
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement
      (((ambientDerivedSubgroup M).subgroupOf M).map
        (QuotientGroup.mk' (K.subgroupOf M))) piChar xChar)
    (hpiBase : piChar i0 j0 =
      Section1.principalCharacter (M ⧸ K.subgroupOf M)) :
    ∀ χ : Section1.ClassFunction M,
      χ ∈ S →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ →
          ∃ j : J, j ∈ Finset.univ.erase j0 ∧
            χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M)
              (fun h : (ambientDerivedSubgroup M).subgroupOf M =>
                xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                  ((ambientDerivedSubgroup M).subgroupOf M)) h)) := by
  classical
  intro χ hχS hχred
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  have hKN : K.subgroupOf M ≤ Nsub := by
    intro k hk
    change (k : G) ∈ ambientDerivedSubgroup M
    exact hKD hk
  have hNnormal : Nsub.Normal := by
    simpa [Nsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Nsub.Normal := hNnormal
  rcases hS with ⟨_hKNfam, _hMFNfam, hmemS⟩
  rcases (hmemS χ).mp hχS with ⟨θ, hθirr, hθnotMF, hθkerK, hχeq⟩
  rcases exists_quotient_character_of_subgroupInKernel_sec9
      (H := Nsub) (Z := K.subgroupOf M) hθirr hθkerK with
    ⟨θbar, hθbarirr, hθeq⟩
  have hθbar_mem : θbar ∈ Set.range xChar := by
    by_contra hθbar_not
    have hquotIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Kbar θbar) :=
      (h45b.1 θbar hθbarirr hθbar_not).1
    have horigIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Nsub
            (fun h : Nsub => θbar (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
              Nsub) h))) :=
      quotientInflatedInducedCF_irreducible_of_quotient_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN hθbarirr
        (by simpa [Kbar, Nsub, qM] using hquotIrr)
    have hχirr : Section1.IsIrreducibleCharacterOnGroup χ := by
      rw [hχeq, hθeq]
      simpa [Nsub, qM] using horigIrr
    exact hχred hχirr
  rcases hθbar_mem with ⟨j, hθbar_eq⟩
  have hj_ne : j ≠ j0 := by
    intro hj
    have hxbase : xChar j0 = Section1.principalCharacter Kbar := by
      rw [← h45a.1 i0 j0, hpiBase]
      ext y
      simp [Section1.subgroupRestriction, Section1.principalCharacter]
    have hθbar_principal : θbar = Section1.principalCharacter Kbar := by
      rw [← hθbar_eq, hj, hxbase]
    have hθMFker :
        Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf Nsub) := by
      rw [hθeq, hθbar_principal]
      intro m
      simp [Section1.degree, Section1.principalCharacter]
    exact hθnotMF hθMFker
  refine ⟨j, ?_, ?_⟩
  · simp [Finset.mem_erase, hj_ne]
  · calc
      χ = Section1.inducedCF Nsub θ := hχeq
      _ = Section1.inducedCF Nsub
          (fun h : Nsub =>
            θbar (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)) := by
            rw [hθeq]
      _ = Section1.inducedCF Nsub
          (fun h : Nsub =>
            xChar j (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)) := by
            rw [hθbar_eq]

public theorem theorem_9_nb_redM_pf4_column_lower_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientLowerTransportData_sec9 M K W2bar p S := by
  classical
  intro h92 _hH0MF _hpprime _hpData hKnormal hKD _hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q _hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  rcases hpf4 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ω, hω, σ, piChar, deltaSign, xChar, h43b, h43c, h45a,
      _h45b, _hdeltaBase, _hpiBase, hpiColumnInj, hnonbaseCard⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  let ι : Type u := {j : J // j ∈ Finset.univ.erase j0}
  letI : Fintype ι := inferInstance
  letI : DecidableEq ι := inferInstance
  let θ : ι → Section1.ClassFunction Nsub := fun j h =>
    xChar j.1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap Nsub) h)
  let μ : ι → Section1.ClassFunction M := fun j =>
    Section1.inducedCF Nsub (θ j)
  have hKN : K.subgroupOf M ≤ Nsub := by
    intro k hk
    change (k : G) ∈ ambientDerivedSubgroup M
    exact hKD hk
  have hNnormal : Nsub.Normal := by
    simpa [Nsub] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Nsub.Normal := hNnormal
  have h46 :
      Section4Scratch.hypothesis_4_6_statement
        Kbar W1bar W2bar Wbar Kbar
        ({x : M ⧸ K.subgroupOf M | x ∈ Kbar ∧ x ≠ 1}) := by
    exact pf4_hypothesis_4_6_self_of_hypothesis_4_2_sec9 h42q
  have hθirr : ∀ j : ι, Section1.IsIrreducibleCharacterOnGroup (θ j) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      quotientInflatedCharacter_irreducible_sec9
        (H := Nsub) (Z := K.subgroupOf M) (θbar := xChar j.1) (h45a.2.1 j.1)
  have hθker : ∀ j : ι,
      Section1.subgroupInKernel' (θ j) ((K.subgroupOf M).subgroupOf Nsub) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      quotientInflatedCharacter_subgroupInKernel_sec9
        (H := Nsub) (Z := K.subgroupOf M) (xChar j.1)
  have hθnonker : ∀ j : ι,
      ¬ Section1.subgroupInKernel' (θ j)
        ((MF.subgroupOf M).subgroupOf Nsub) := by
    intro j
    simpa [θ, Nsub, Kbar, qM] using
      theorem_9_nb_redM_pf4_nonbase_not_MF_kernel_source_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) (K := K)
        (q := q) h92 (i0 := i0) (j0 := j0) (j := j.1) (ω := ω) (σ := σ)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        h42q hω h43b h43c h45a j.2
  have hquotRed : ∀ j : ι,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Kbar (xChar j.1)) := by
    intro j hjirr
    have hpiRed :
        ¬ Section1.IsIrreducibleCharacterOnGroup
          (Section4Scratch.piColumn piChar j.1) :=
      Section5.piColumn_not_irreducible_pf53 h46 hω h43b j.1
    exact hpiRed (by simpa [← h45a.2.2 j.1] using hjirr)
  have hμred : ∀ j : ι, ¬ Section1.IsIrreducibleCharacterOnGroup (μ j) := by
    intro j
    simpa [μ, θ, Nsub, Kbar, qM] using
      quotientInflatedInducedCF_not_irreducible_of_quotient_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (h45a.2.1 j.1) (hquotRed j)
  rcases hS with ⟨_hKNfam, _hMFNfam, hmemS⟩
  have hμmem : ∀ j : ι, μ j ∈ S := by
    intro j
    rw [hmemS (μ j)]
    exact ⟨θ j, hθirr j, hθnonker j, hθker j, rfl⟩
  refine ⟨ι, inferInstance, inferInstance, μ, ?_, ?_, ?_⟩
  · intro j k hjk
    have hqeq :
        Section1.quotientInducedCF Nsub (K.subgroupOf M) (θ j) =
          Section1.quotientInducedCF Nsub (K.subgroupOf M) (θ k) :=
      quotientInducedCF_eq_of_inducedCF_eq_sec9
        (H := Nsub) (Z := K.subgroupOf M) (θ := θ j) (η := θ k) (by
          simpa [μ] using hjk)
    have hjeq :
        Section1.inducedCF Kbar (xChar j.1) =
          Section1.inducedCF Kbar (xChar k.1) := by
      have hjq := quotientInducedCF_inflated_eq_inducedCF_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (θbar := xChar j.1) (h45a.2.1 j.1)
      have hkq := quotientInducedCF_inflated_eq_inducedCF_sec9
        (H := Nsub) (Z := K.subgroupOf M) hKN (θbar := xChar k.1) (h45a.2.1 k.1)
      simpa [θ, Nsub, Kbar, qM, hjq, hkq] using hqeq
    have hcolumn :
        Section4Scratch.piColumn piChar j.1 =
          Section4Scratch.piColumn piChar k.1 := by
      calc
        Section4Scratch.piColumn piChar j.1 =
            Section1.inducedCF Kbar (xChar j.1) := (h45a.2.2 j.1).symm
        _ = Section1.inducedCF Kbar (xChar k.1) := hjeq
        _ = Section4Scratch.piColumn piChar k.1 := h45a.2.2 k.1
    exact Subtype.ext (hpiColumnInj hcolumn)
  · simpa [ι] using hnonbaseCard
  · intro j
    exact ⟨hμmem j, hμred j⟩

public theorem theorem_9_nb_redM_pf4_column_reducible_filter_card_le_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          (reducibleCharacterFilter_sec9 M S).card ≤ p - 1 := by
  classical
  intro _h92 _hH0MF _hpprime _hpData hKnormal hKD _hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro _h42q _hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Nsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) := Nsub.map qM
  rcases hpf4 with
    ⟨I, J, instFintypeI, instFintypeJ, _instDecidableEqI, instDecidableEqJ,
      i0, j0, _ω, _hω, _σ, piChar, _deltaSign, xChar, _h43b, _h43c, h45a,
      h45b, _hdeltaBase, hpiBase, _hpiColumnInj, hnonbaseCard⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq J := instDecidableEqJ
  let Red : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M S
  let ρ : Type u := {χ : Section1.ClassFunction M // χ ∈ Red}
  letI : Fintype ρ := Finset.Subtype.fintype Red
  let ι : Type u := {j : J // j ∈ Finset.univ.erase j0}
  letI : Fintype ι := Finset.Subtype.fintype (Finset.univ.erase j0)
  have hclass :
      ∀ χ : ρ, ∃ j : ι,
        (χ : Section1.ClassFunction M) =
          Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar j.1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := by
    intro χ
    have hχpair :
        (χ : Section1.ClassFunction M) ∈ S ∧
          ¬ Section1.IsIrreducibleCharacterOnGroup (χ : Section1.ClassFunction M) := by
      have hχRed : (χ : Section1.ClassFunction M) ∈ Red := χ.2
      have hχfilter :
          (χ : Section1.ClassFunction M) ∈ reducibleCharacterFilter_sec9 M S := by
        simp [Red] at hχRed ⊢
      exact Finset.mem_filter.mp hχfilter
    rcases pf4_reducible_kernelInducedFamily_member_is_nonbase_inflated_column_sec9
        M MF K S hKD hS
        (i0 := i0) (j0 := j0) (piChar := piChar) (xChar := xChar)
        h45a h45b hpiBase χ hχpair.1 hχpair.2 with
      ⟨j, hj, hχeq⟩
    exact ⟨⟨j, hj⟩, by simpa [Nsub, qM, Kbar] using hχeq⟩
  let f : ρ → ι := fun χ => Classical.choose (hclass χ)
  have hf : Function.Injective f := by
    intro χ ψ hχψ
    apply Subtype.ext
    have hχspec := Classical.choose_spec (hclass χ)
    have hψspec := Classical.choose_spec (hclass ψ)
    calc
      (χ : Section1.ClassFunction M) =
          Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar (f χ).1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := hχspec
      _ = Section1.inducedCF Nsub
            (fun h : Nsub =>
              xChar (f ψ).1 (((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap
                Nsub) h)) := by rw [hχψ]
      _ = (ψ : Section1.ClassFunction M) := hψspec.symm
  have hcardRedSubtype : Fintype.card ρ = Red.card :=
    Fintype.card_of_subtype Red (fun _ => Iff.rfl)
  have hcardNonbaseSubtype : Fintype.card ι = (Finset.univ.erase j0).card :=
    Fintype.card_of_subtype (Finset.univ.erase j0) (fun _ => Iff.rfl)
  calc
    (reducibleCharacterFilter_sec9 M S).card = Fintype.card ρ := by
      simpa [Red] using hcardRedSubtype.symm
    _ ≤ Fintype.card ι := Fintype.card_le_of_injective f hf
    _ = p - 1 := by
      rw [hcardNonbaseSubtype, hnonbaseCard]

public theorem theorem_9_nb_redM_pf4_column_reducible_subset_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          ∀ R : Finset (Section1.ClassFunction M),
                            R.card = p - 1 →
                              (∀ χ : Section1.ClassFunction M,
                                χ ∈ R →
                                  χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) →
                                ∀ χ : Section1.ClassFunction M,
                                  χ ∈ S →
                                    ¬ Section1.IsIrreducibleCharacterOnGroup χ →
                                      χ ∈ R := by
  classical
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4 R hRcard hRmem χ hχS hχred
  let Red : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M S
  have hRsubRed : R ⊆ Red := by
    intro ψ hψR
    have hψ := hRmem ψ hψR
    simpa [Red, reducibleCharacterFilter_sec9] using hψ
  have hRedCardLe : Red.card ≤ p - 1 := by
    simpa [Red] using
      theorem_9_nb_redM_pf4_column_reducible_filter_card_le_sec9
        M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
        hS h42q hW2bar_card hpf4
  have hRedCardLeR : Red.card ≤ R.card := by
    simpa [hRcard] using hRedCardLe
  have hR_eq_Red : R = Red :=
    Finset.eq_of_subset_of_card_le hRsubRed hRedCardLeR
  have hχRed : χ ∈ Red := by
    simp [Red, reducibleCharacterFilter_sec9, hχS, hχred]
  simpa [hR_eq_Red] using hχRed

public theorem theorem_9_nb_redM_pf4_column_exhaust_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientLowerTransportData_sec9 M K W2bar p S →
                            nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  classical
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4 hlower
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  rcases hlower with ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let R : Finset (Section1.ClassFunction M) := Finset.univ.image μ
  have hRcard : R.card = p - 1 := by
    calc
      R.card = Fintype.card ι := by
        simpa [R] using
          (Finset.card_image_of_injective (Finset.univ : Finset ι) hμinj)
      _ = p - 1 := hcard
  have hRmem :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ R →
          χ ∈ S ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨i, _hi, hχeq⟩
    simpa [hχeq.symm] using hmem i
  have hupper :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S →
          ¬ Section1.IsIrreducibleCharacterOnGroup χ →
            χ ∈ R :=
    theorem_9_nb_redM_pf4_column_reducible_subset_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4 R hRcard hRmem
  refine ⟨ι, instFintype, instDecidableEq, μ, hμinj, hcard, hmem, ?_⟩
  intro χ hχS hχred
  have hχR : χ ∈ R := hupper χ hχS hχred
  rcases Finset.mem_image.mp hχR with ⟨i, _hi, hχeq⟩
  exact ⟨i, hχeq⟩

public theorem theorem_9_nb_redM_pf4_column_transport_to_kernelInduced_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((ambientDerivedSubgroup M).subgroupOf M).map qM
                    let W1bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W1.subgroupOf M).map qM
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    let Wbar : Subgroup (M ⧸ K.subgroupOf M) :=
                      ((W1 ⊔ W2).subgroupOf M).map qM
                    Section4.hypothesis_4_2_statement Kbar W1bar W2bar Wbar →
                      Nat.card W2bar = p →
                        nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p →
                          nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  dsimp
  intro h42q hW2bar_card hpf4
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  have hlower : nbRedMQuotientLowerTransportData_sec9 M K W2bar p S :=
    theorem_9_nb_redM_pf4_column_lower_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4
  exact
    theorem_9_nb_redM_pf4_column_exhaust_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q hW2bar_card hpf4 hlower

public theorem theorem_9_nb_redM_pf4_quotient_character_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    Section4.hypothesis_4_2_statement
                      (((ambientDerivedSubgroup M).subgroupOf M).map
                        (QuotientGroup.mk' (K.subgroupOf M)))
                      ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                      ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                      (((W1 ⊔ W2).subgroupOf M).map
                        (QuotientGroup.mk' (K.subgroupOf M))) →
                      Nat.card
                        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p →
                        nbRedMQuotientTransportData_sec9 M K
                          ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
                          p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS h42q hW2bar_card
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let Kbar : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  let W1bar : Subgroup (M ⧸ K.subgroupOf M) := (W1.subgroupOf M).map qM
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  let Wbar : Subgroup (M ⧸ K.subgroupOf M) := ((W1 ⊔ W2).subgroupOf M).map qM
  have hpf4 : nbRedMPF4QuotientColumnData_sec9 Kbar W1bar W2bar Wbar p :=
    theorem_9_nb_redM_pf4_quotient_column_data_of_notation_sec9
      Kbar W1bar W2bar Wbar p h42q (by simpa [W2bar, qM] using hW2bar_card)
      (theorem_9_nb_redM_quotient_notation_3_3_source_core_sec9
        Kbar W1bar W2bar Wbar h42q)
  exact
    theorem_9_nb_redM_pf4_column_transport_to_kernelInduced_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf
      hS h42q (by simpa [W2bar, qM] using hW2bar_card) hpf4

public theorem theorem_9_nb_redM_primeTI_quotient_character_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    IsCyclic W2bar →
                      Nat.card W2bar ≠ 1 →
                      nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  change
    IsCyclic ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) →
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) ≠ 1 →
        nbRedMQuotientTransportData_sec9 M K
          ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) p S
  intro _hW2bar_cyclic _hW2bar_ne_one
  have h42q :
      Section4.hypothesis_4_2_statement
        (((ambientDerivedSubgroup M).subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M)))
        ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        (((W1 ⊔ W2).subgroupOf M).map
          (QuotientGroup.mk' (K.subgroupOf M))) :=
    theorem_9_nb_redM_M_mod_K_hypothesis_4_2_sec9
      M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  have hW2bar_card :
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p :=
    theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
      M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  exact
    theorem_9_nb_redM_pf4_quotient_character_transport_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS h42q hW2bar_card

public theorem theorem_9_nb_redM_quotient_character_transport_of_W2_card_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    Nat.card W2bar = p →
                      nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  change
    Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p →
      nbRedMQuotientTransportData_sec9 M K
        ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) p S
  intro hW2bar_card
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have hW2bar_cyclic : IsCyclic W2bar := by
    simpa [W2bar, qM] using
      theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
        M MF U W1 W2 H0 K q h92 hKnormal
  have hW2bar_ne_one : Nat.card W2bar ≠ 1 :=
    natCard_ne_one_of_eq_prime_sec9 (α := W2bar) hpprime hW2bar_card
  exact
    theorem_9_nb_redM_primeTI_quotient_character_transport_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS hW2bar_cyclic hW2bar_ne_one

public theorem theorem_9_nb_redM_quotient_transport_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    letI : (K.subgroupOf M).Normal := hKnormal
                    let qM : M →* M ⧸ K.subgroupOf M :=
                      QuotientGroup.mk' (K.subgroupOf M)
                    let W2bar : Subgroup (M ⧸ K.subgroupOf M) :=
                      (W2.subgroupOf M).map qM
                    nbRedMQuotientTransportData_sec9 M K W2bar p S := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have hW2bar_card : Nat.card W2bar = p := by
    simpa [W2bar, qM] using
      theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
        M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf
  exact
    theorem_9_nb_redM_quotient_character_transport_of_W2_card_source_core_sec9
      M MF U W1 W2 H0 K p q S h92 hH0MF hpprime hpData hKnormal hKD
      hKinf hS hW2bar_card

public theorem theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (K.subgroupOf M).Normal →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  kernelInducedFamily M (ambientDerivedSubgroup M) MF K S →
                    (reducibleCharacterFilter_sec9 M S).card = p - 1 := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  let W2bar : Subgroup (M ⧸ K.subgroupOf M) := (W2.subgroupOf M).map qM
  have htransport : nbRedMQuotientTransportData_sec9 M K W2bar p S :=
    theorem_9_nb_redM_quotient_transport_source_core_sec9 M MF U W1 W2 H0 K
      p q S h92 hH0MF hpprime hpData hKnormal hKD hKinf hS
  exact theorem_9_reducible_filter_card_of_transport_data_sec9
    (quotientReducibleFamilyTransportData_of_nbRedMQuotientTransportData_sec9
      (M := M) (K := K) (Wbar := W2bar) (p := p) (S := S) htransport)

public theorem theorem_9_H0C_le_ambientDerived_of_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          H0 ⊔ C ≤ ambientDerivedSubgroup M := by
  intro h92 hH0MF hC
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hH0D : H0 ≤ ambientDerivedSubgroup M :=
    hH0MF.trans (MF_le_ambientDerived_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92)
  have hCD : C ≤ ambientDerivedSubgroup M := hC.1.trans hUleD
  exact sup_le hH0D hCD

public theorem theorem_9_H0C_normal_M_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              ((H0 ⊔ C).subgroupOf M).Normal := by
  intro h92 hH0MF hC _hpprime hpData
  rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
  rcases hpDataCore with
    ⟨_hH0MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h92.mf.1 with ⟨hMFleM92, hMFnormalM, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, hW1normUInM, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hH0_le_M : H0 ≤ M := hH0MF.trans hMF_le_M
  have hC_le_M : C ≤ M := hC.1.trans (hUleD.trans hDleM)
  have hH0C_le_M : H0 ⊔ C ≤ M := sup_le hH0_le_M hC_le_M
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hH0C_le_M).2 ?_
  have hM_norm_H0 : M ≤ Subgroup.normalizer (H0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0_le_M).1 hH0_normal_M
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM92).1 hMFnormalM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hU_le_M : U ≤ M := hUleD.trans hDleM
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    hUleD.trans hD_norm_MF
  have hU_norm_C : U ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := U)
      hU_le_M Subgroup.le_normalizer hU_norm_MF hH0_le_M hH0_normal_M hC
  have hU_norm_H0C : U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C U
      (hU_le_M.trans hM_norm_H0) hU_norm_C
  have hMF_norm_H0C :
      MF ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9
    · exact hMF_le_M.trans hM_norm_H0
    · intro n hnMF b hbC
      exact (hC.2 b (hC.1 hbC)).mp hbC n hnMF
  have hMFU_norm_H0C :
      MF ⊔ U ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hMF_norm_H0C hU_norm_H0C
  have hD_norm_H0C :
      D ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) := by
    have hD_eq : D = MF ⊔ U := by
      dsimp [D]
      exact hcompDU.2.2.1
    simpa [hD_eq] using hMFU_norm_H0C
  have hW1_le_M : W1 ≤ M := hW1hall.1
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1_norm_C : W1 ≤ Subgroup.normalizer (C : Set G) :=
    quotientCentralizerIn_le_normalizer_of_le_normalizers_sec9
      (M := M) (MF := MF) (U := U) (H0 := H0) (N := W1)
      hW1_le_M hW1_norm_U (hW1_le_M.trans hM_norm_MF)
      hH0_le_M hH0_normal_M hC
  have hW1_norm_H0C :
      W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer_sec9 H0 C W1
      (hW1_le_M.trans hM_norm_H0) hW1_norm_C
  have hDW1_norm_H0C :
      D ⊔ W1 ≤ Subgroup.normalizer ((H0 ⊔ C : Subgroup G) : Set G) :=
    sup_le hD_norm_H0C hW1_norm_H0C
  have hM_eq : M = D ⊔ W1 := by
    dsimp [D]
    exact hcompMW1.2.2.1
  simpa [hM_eq] using hDW1_norm_H0C

public theorem theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              (H0 ⊔ C) ⊓ MF = H0 := by
  intro h92 hH0MF hC _hpprime hpData
  rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
  rcases hpDataCore with
    ⟨_hH0MF, hMFM, hH0normalM, _hH0normalMF, _hH0ltMF, _helem,
      _htypeIIIIV⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hFitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hH0M : H0 ≤ M := hH0MF.trans hMFM
  have hCM : C ≤ M :=
    hC.1.trans (hUleD.trans section12_ambientDerivedSubgroup_le)
  have hMFUdisj : Disjoint MF U := hcompDU.2.2.2
  apply le_antisymm
  · intro x hx
    let xM : M := ⟨x, hMFM hx.2⟩
    have hsubsup :
        (H0 ⊔ C).subgroupOf M = H0.subgroupOf M ⊔ C.subgroupOf M :=
      Subgroup.subgroupOf_sup hH0M hCM
    have hxSub : xM ∈ H0.subgroupOf M ⊔ C.subgroupOf M := by
      rw [← hsubsup]
      simpa [xM, Subgroup.mem_subgroupOf] using hx.1
    letI : (H0.subgroupOf M).Normal := hH0normalM
    rcases (Subgroup.mem_sup_of_normal_left
        (s := H0.subgroupOf M) (t := C.subgroupOf M) (x := xM)).1 hxSub with
      ⟨hM, hhH0M, cM, hcCM, hhcM⟩
    let h : G := hM
    let c : G := cM
    have hhH0 : h ∈ H0 := by
      simpa [h, Subgroup.mem_subgroupOf] using hhH0M
    have hcC : c ∈ C := by
      simpa [c, Subgroup.mem_subgroupOf] using hcCM
    have hhc : h * c = x := by
      simpa [h, c, xM] using congrArg Subtype.val hhcM
    have hx_eq : x = h * c := hhc.symm
    have hhMF : h ∈ MF := hH0MF hhH0
    have hcMF : c ∈ MF := by
      have hcalc : c = h⁻¹ * x := by
        rw [hx_eq]
        group
      rw [hcalc]
      exact MF.mul_mem (MF.inv_mem hhMF) hx.2
    have hcU : c ∈ U := hC.1 hcC
    have hcBot : c ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hcMF hcU
    have hc1 : c = 1 := by
      simpa using hcBot
    have hxH0 : x ∈ H0 := by
      rw [hx_eq, hc1, mul_one]
      exact hhH0
    exact hxH0
  · intro x hxH0
    exact ⟨Subgroup.mem_sup_left hxH0, hH0MF hxH0⟩

public theorem theorem_9_nb_redM_pair_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ)
    (SH0 SH0C : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
                kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
                  (reducibleCharacterFilter_sec9 M SH0).card = p - 1 ∧
                    (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 := by
  intro h92 hH0MF hC hpprime hpData hSH0 hSH0C
  have hH0normalM : (H0.subgroupOf M).Normal := by
    rcases hpData with ⟨_hp, _hp_eq, hpDataCore, _h96⟩
    rcases hpDataCore with
      ⟨_hH0MF, _hMFM, hH0normalM, _hH0normalMF, _hH0ltMF,
        _helem, _htypeIIIIV⟩
    exact hH0normalM
  have hH0D : H0 ≤ ambientDerivedSubgroup M :=
    hH0MF.trans (MF_le_ambientDerived_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92)
  have hH0infMF : H0 ⊓ MF = H0 := inf_eq_left.mpr hH0MF
  have hSH0card :
      (reducibleCharacterFilter_sec9 M SH0).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 H0 p q SH0 h92 hH0MF hpprime hpData
      hH0normalM hH0D hH0infMF hSH0
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0 :=
    theorem_9_H0C_inf_MF_eq_H0_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hSH0Ccard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  exact ⟨hSH0card, hSH0Ccard⟩


public theorem theorem_9_reducible_filter_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q : ℕ)
    (SH0 SH0C : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        quotientCentralizerIn MF H0 U C →
          Nat.Prime p →
            (∃ hp : Nat.Primes,
              hp.val = p ∧
                hoReductionData M MF U W2 H0 hp ∧
                  quotientChiefFactorData_9_6 M MF H0 W1 hp) →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
                kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
                  ∃ R0 RC : Finset (Section1.ClassFunction M),
                    R0.card = p - 1 ∧
                      RC.card = p - 1 ∧
                      (∀ χ : Section1.ClassFunction M,
                        χ ∈ R0 ↔
                          χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
  classical
  intro h92 hH0MF hC hpprime hpData hSH0 hSH0C
  let R0 : Finset (Section1.ClassFunction M) :=
    reducibleCharacterFilter_sec9 M SH0
  let RC : Finset (Section1.ClassFunction M) :=
    reducibleCharacterFilter_sec9 M SH0C
  rcases theorem_9_nb_redM_pair_count_source_core_sec9
      M MF U W1 W2 H0 C p q SH0 SH0C h92 hH0MF hC hpprime hpData hSH0 hSH0C with
    ⟨hR0card, hRCcard⟩
  refine ⟨R0, RC, ?_, ?_, ?_, ?_⟩
  · simpa [R0] using hR0card
  · simpa [RC] using hRCcard
  · intro χ
    simp [R0, reducibleCharacterFilter_sec9]
  · intro χ
    simp [RC, reducibleCharacterFilter_sec9]

public theorem classFunction_eq_of_irreducible_scalarProduct_ne_zero_sec9
    {L : Type u} [Group L] [Finite L]
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hinner : Section1.scalarProduct L φ ψ ≠ 0) :
    φ = ψ := by
  by_contra hne
  have hzero :
      Section1.scalarProduct L φ ψ = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne hφ hψ hne
  exact hinner hzero

public theorem inducedCF_eq_of_irreducible_constituent_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hIndψ : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K ψ))
    (hinner :
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K χ) ≠ 0) :
    χ = Section1.inducedCF K ψ := by
  have hχclass : Section1.IsClassFunction χ := by
    rcases hχ with ⟨_n, ρ, _hρirr, hχeq⟩
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hinnerInd :
      Section1.scalarProduct L (Section1.inducedCF K ψ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K ψ χ hχclass]
    exact hinner
  exact (classFunction_eq_of_irreducible_scalarProduct_ne_zero_sec9
    hIndψ hχ hinnerInd).symm

public theorem subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction K}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχker : Section1.subgroupInKernel' χ A)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  rcases hχirr with ⟨nχ, ρχ, _hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, hρθirr, hθeq⟩
  let ρχK : Representation ℂ K (Fin nχ → ℂ) := ρχ.comp K.subtype
  have hres :
      Section1.subgroupRestriction K χ = ρχK.character := by
    ext k
    simp [ρχK, Section1.subgroupRestriction, hχeq, Representation.character]
  have hχkerChar : Section1.subgroupInKernel' ρχ.character A := by
    simpa [hχeq] using hχker
  have hχkerRep : Section1.subgroupInRepresentationKernel ρχ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ A).mp hχkerChar
  have hχKkerRep :
      Section1.subgroupInRepresentationKernel ρχK (A.subgroupOf K) := by
    intro a
    change ρχ ((a : K) : L) = 1
    exact hχkerRep ⟨((a : K) : L), by
      exact a.property⟩
  have hinnerSwap :
      Section1.scalarProduct K (Section1.subgroupRestriction K χ) θ ≠ 0 :=
    (Section1.scalarProduct_ne_zero_swap θ
      (Section1.subgroupRestriction K χ)).1 hinner
  have hinnerRep :
      Section1.scalarProduct K ρχK.character ρθ.character ≠ 0 := by
    simpa [hθeq, hres] using hinnerSwap
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρθ ρχK]
      using hinnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρθ ρχK) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hθkerRep :
      Section1.subgroupInRepresentationKernel ρθ (A.subgroupOf K) := by
    letI : Representation.IsIrreducible ρθ := hρθirr
    have hf_inj : Function.Injective f := by
      rcases (Representation.IsIrreducible.injective_or_eq_zero
          (ρ := ρθ) (σ := ρχK) f) with hinj | hzero
      · exact hinj
      · exact (hf hzero).elim
    intro a
    apply LinearMap.ext
    intro v
    apply hf_inj
    calc
      f (ρθ (a : K) v) = ρχK (a : K) (f v) := by
        exact Representation.IntertwiningMap.isIntertwining ρθ ρχK f (a : K) v
      _ = f v := by
        rw [hχKkerRep a]
        simp
  have hθkerChar : Section1.subgroupInKernel' ρθ.character (A.subgroupOf K) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρθ (A.subgroupOf K)).mpr hθkerRep
  simpa [hθeq] using hθkerChar

public theorem constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction K}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotker : ¬ Section1.subgroupInKernel' χ A)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    ¬ Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  intro hθker
  rcases hχirr with ⟨nχ, ρχ, hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, _hρθirr, hθeq⟩
  let indρθ : Representation ℂ L (Representation.IndV K.subtype ρθ) :=
    Representation.ind K.subtype ρθ
  haveI : FiniteDimensional ℂ (Representation.IndV K.subtype ρθ) :=
    Theory.Representation.finiteDimensional_ind K ρθ
  have hIndCharKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρθ.character) A :=
    (Section1.proposition_1_6_a K A hAK ρθ).mp
      (by simpa [hθeq] using hθker)
  have hIndRepKer : Section1.subgroupInRepresentationKernel indρθ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      indρθ A).mp (by
        simpa [indρθ, Section1.inducedCF_eq_representation_character K ρθ]
          using hIndCharKer)
  have hχclass : Section1.IsClassFunction χ := by
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρχ) g x
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K θ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K θ χ hχclass]
    exact hinner
  have hIndInnerRep :
      Section1.scalarProduct L indρθ.character ρχ.character ≠ 0 := by
    simpa [indρθ, hχeq, hθeq,
      Section1.inducedCF_eq_representation_character K ρθ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρχ indρθ]
      using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hχRepKer : Section1.subgroupInRepresentationKernel ρχ A := by
    letI : Representation.IsIrreducible ρχ := hρχirr
    have hf_inj : Function.Injective f := by
      rcases (Representation.IsIrreducible.injective_or_eq_zero
          (ρ := ρχ) (σ := indρθ) f) with hinj | hzero
      · exact hinj
      · exact (hf hzero).elim
    intro a
    apply LinearMap.ext
    intro v
    apply hf_inj
    calc
      f (ρχ (a : L) v) = indρθ (a : L) (f v) := by
        exact Representation.IntertwiningMap.isIntertwining ρχ indρθ f (a : L) v
      _ = f v := by
        rw [hIndRepKer a]
        simp
  have hχkerChar : Section1.subgroupInKernel' ρχ.character A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ A).mpr hχRepKer
  exact hχnotker (by simpa [hχeq] using hχkerChar)

public theorem exists_irreducible_constituent_of_subgroupRestriction_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  letI : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  letI : Nontrivial φ.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Theory.Representation.RepMap φ.toRepresentation ρK := by
    refine Theory.Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using
        congrArg (fun f : Theory.Representation.RepMap φ.toRepresentation ρK => f v)
          hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ
          (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K χ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      Section1.standardizeRepresentation φ.toRepresentation, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible φ.toRepresentation hφirr
    · ext k
      symm
      exact Section1.standardizeRepresentation_character φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K χ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K χ)).2
        hinner_res'

public theorem exists_restriction_constituent_kernelD_sec9
    {L : Type u} [Group L] [Finite L]
    (K A B : Subgroup L) [K.Normal] [B.Normal] (hBK : B ≤ K)
    {χ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotB : ¬ Section1.subgroupInKernel' χ B)
    (hχkerA : Section1.subgroupInKernel' χ A) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 ∧
          ¬ Section1.subgroupInKernel' θ (B.subgroupOf K) ∧
            Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  rcases exists_irreducible_constituent_of_subgroupRestriction_sec9 K hχirr with
    ⟨θ, hθirr, hinner⟩
  have hθnotB :
      ¬ Section1.subgroupInKernel' θ (B.subgroupOf K) :=
    constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_sec9
      K B hBK hχirr hχnotB hθirr hinner
  have hθkerA : Section1.subgroupInKernel' θ (A.subgroupOf K) :=
    subgroupInKernel'_constituent_of_subgroupRestriction_kernel_sec9
      K A hχirr hχkerA hθirr hinner
  exact ⟨θ, hθirr, hinner, hθnotB, hθkerA⟩

public theorem theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := by
  intro hcase
  let D : Subgroup G := ambientDerivedSubgroup M
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.mf.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hMFD : MF ≤ D :=
    MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  let K : Subgroup M := MF.subgroupOf M
  let Dsub : Subgroup M := D.subgroupOf M
  have hKD : K ≤ Dsub := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [K, Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ D := hMFD hxMF
    simpa [Dsub, Subgroup.mem_subgroupOf] using hxD
  have hDsub_norm_K : Dsub ≤ Subgroup.normalizer (K : Set M) :=
    (show (⊤ : Subgroup M) ≤ Subgroup.normalizer (K : Set M) from
      Subgroup.le_normalizer_of_normal).trans' le_top
  have hKnormalD : (K.subgroupOf Dsub).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).2 hDsub_norm_K
  simpa [D, K, Dsub] using hKnormalD

public theorem theorem_9_8_exists_MF_restriction_constituent_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Section1.IsIrreducibleCharacterOnGroup θ →
        ¬ Section1.subgroupInKernel' θ
          ((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) →
        Section1.subgroupInKernel' θ
          ((H0.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) →
          ∃ ψ : Section1.ClassFunction
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)),
            Section1.IsIrreducibleCharacterOnGroup ψ ∧
              Section1.scalarProduct
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))
                ψ
                (Section1.subgroupRestriction
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 ∧
                ¬ Section1.subgroupInKernel' ψ
                  (((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M))) ∧
                  Section1.subgroupInKernel' ψ
                    (((H0.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M))) := by
  classical
  intro hcase hθirr hθnotMF hθkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let A : Subgroup (D.subgroupOf M) := (H0.subgroupOf M).subgroupOf (D.subgroupOf M)
  have hKnormal : K.Normal := by
    simpa [D, K] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : K.Normal := hKnormal
  rcases exists_restriction_constituent_kernelD_sec9
      (L := D.subgroupOf M) K A K le_rfl hθirr
      (by simpa [D, K] using hθnotMF)
      (by simpa [D, A] using hθkerH0) with
    ⟨ψ, hψirr, hinner, hψnot, hψker⟩
  exact ⟨ψ, hψirr, by simpa [D, K] using hinner,
    by simpa [D, K] using hψnot, by simpa [D, K, A] using hψker⟩

public theorem theorem_9_8_clifford_inertia_inducing_constituent_source_core_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {θ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hinner :
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K θ) ≠ 0) :
    ∃ η : Section1.ClassFunction (Section1.inertiaSubgroup K ψ),
      Section1.IsIrreducibleCharacterOnGroup η ∧
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF (Section1.inertiaSubgroup K ψ) η) ∧
        Section1.scalarProduct (Section1.inertiaSubgroup K ψ) η
          (Section1.subgroupRestriction (Section1.inertiaSubgroup K ψ) θ) ≠ 0 := by
  classical
  have hψclass : Section1.IsClassFunction ψ :=
    Section1.isCharacter_isClassFunction ψ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr)
  have hψbook : Section1.IsBookIrreducibleCharacter ψ :=
    Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hψirr
  let T : Subgroup L := Section1.inertiaSubgroup K ψ
  let Ksub : Subgroup T := K.subgroupOf T
  have hKleT : K ≤ T :=
    Section1.proposition_1_7_inertia_contains_H K ψ hψclass
  have hsubBook : Section1.IsBookIrreducibleCharacter
      (Section1.subgroupOfClassFunction (T := T) ψ) := by
    simpa [T] using
      Section1.isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia
        K ψ hψclass hψbook
  have hindChar : Section1.IsCharacter
      (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ)) :=
    Section1.isCharacter_inducedCF_of_isCharacter Ksub
      (Section1.subgroupOfClassFunction (T := T) ψ) hsubBook.1
  have hindNe :
      Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ) ≠ 0 := by
    intro hzero
    have hdeg_zero :
        Section1.degree
          (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ)) = 0 := by
      rw [hzero]
      rfl
    have hdeg_formula :=
      Section1.degree_inducedToSubgroup K T ψ
    have hindex_ne : ((Subgroup.index Ksub : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := Ksub))
    have hψdeg_ne : Section1.degree ψ ≠ 0 :=
      Section1.degree_ne_zero_of_isBookIrreducibleCharacter ψ hψbook
    have hprod_ne :
        (Subgroup.index Ksub : ℂ) * Section1.degree ψ ≠ 0 :=
      mul_ne_zero hindex_ne hψdeg_ne
    exact hprod_ne (hdeg_formula.symm.trans hdeg_zero)
  rcases Section1.exists_positive_irreducible_decomposition_of_character
      (Section1.inducedCF Ksub (Section1.subgroupOfClassFunction (T := T) ψ))
      hindChar hindNe with
    ⟨ι, hι, hιdec, e, ηfam, i0, hepos, hηbook, hηpair, hdecompT⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let χfam : ι → Section1.ClassFunction L :=
    fun i => Section1.inducedCF T (ηfam i)
  have hχdef : ∀ i : ι, χfam i = Section1.inducedCF T (ηfam i) := by
    intro i
    rfl
  rcases Section1.proposition_1_7_a K ψ hψclass hψbook e ηfam χfam
      hepos hηbook hηpair (by simpa [T, Ksub] using hdecompT) hχdef with
    ⟨_hχpair, hχbook, hdecompL⟩
  have hθclass : Section1.IsClassFunction θ :=
    Section1.isCharacter_isClassFunction θ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hweighted_inner :
      Section1.scalarProduct L
          (Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) χfam) θ ≠ 0 := by
    rw [← hdecompL]
    rw [Section1.scalarProduct_inducedCF_left K ψ θ hθclass]
    exact hinner
  have hsum_inner :
      (@Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
        (e i : ℂ) *
          Section1.scalarProduct T (ηfam i)
            (Section1.subgroupRestriction T θ)) ≠ 0 := by
    intro hzero
    apply hweighted_inner
    calc
      Section1.scalarProduct L
          (Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) χfam) θ =
          @Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
            (e i : ℂ) * Section1.scalarProduct L (χfam i) θ := by
            exact Section1.scalarProduct_weightedFamilySum_left
              (fun i : ι => (e i : ℂ)) χfam θ
      _ = @Finset.sum ι ℂ _ (@Finset.univ ι (Fintype.ofFinite ι)) fun i =>
            (e i : ℂ) *
            Section1.scalarProduct T (ηfam i)
              (Section1.subgroupRestriction T θ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hχdef i]
            rw [Section1.scalarProduct_inducedCF_left T (ηfam i) θ hθclass]
      _ = 0 := hzero
  have hex_inner :
      ∃ i : ι,
        Section1.scalarProduct T (ηfam i)
          (Section1.subgroupRestriction T θ) ≠ 0 := by
    by_contra hnone
    apply hsum_inner
    apply Finset.sum_eq_zero
    intro i _hi
    have hi : Section1.scalarProduct T (ηfam i)
        (Section1.subgroupRestriction T θ) = 0 := by
      by_contra hne
      exact hnone ⟨i, hne⟩
    rw [hi]
    simp
  rcases hex_inner with ⟨i, hi⟩
  exact ⟨ηfam i,
    Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ηfam i) (hηbook i),
    Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (χfam i) (hχbook i),
    by simpa [T] using hi⟩


@[expose] public def theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M U : Subgroup G) :
    ((U.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)) →* U where
  toFun x :=
    ⟨(((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
      have hxUM :
          ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ U.subgroupOf M :=
        Subgroup.mem_subgroupOf.mp x.property
      exact Subgroup.mem_subgroupOf.mp hxUM⟩
  map_one' := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

public theorem theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section2.IsInternalSemidirectProduct
          (⊤ : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
          ((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M))
          ((U.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) := by
  intro h92 hKnormal
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let W : Subgroup (D.subgroupOf M) := (U.subgroupOf M).subgroupOf (D.subgroupOf M)
  letI : K.Normal := by
    simpa [D, K] using hKnormal
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD', hUleD, hD_eq, hMFUdisj⟩
  have hMFleM : MF ≤ M := hMFleD.trans hDleM
  have hUleM : U ≤ M := hUleD.trans hDleM
  have hMFsubD : MF.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hMFleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hUsubD : U.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    exact hUleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hsupM :
      (MF.subgroupOf M) ⊔ (U.subgroupOf M) = D.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := M) hMFleM hUleM]
    simp [D, hD_eq]
  have hdisj : Disjoint K W := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxMFU : (((x : D.subgroupOf M) : M) : G) ∈ MF ⊓ U := by
        exact ⟨by
            simpa [D, K, Subgroup.mem_subgroupOf] using hx.1,
          by
            simpa [D, W, Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (((x : D.subgroupOf M) : M) : G) ∈ (⊥ : Subgroup G) := by
        exact hMFUdisj.le_bot hxMFU
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : K ⊔ W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF.subgroupOf M) (A' := U.subgroupOf M)
      (B := D.subgroupOf M) hMFsubD hUsubD]
    rw [hsupM]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  exact internalSemidirectProduct_top_of_normal_isComplement'_sec9
    (isComplement'_of_disjoint_sup_eq_top_of_normal K W hdisj hsupTop)

public theorem exists_component_not_le_ker_of_iSup_eq_top_sec9
    {Q : Type u} {A : Type w} [Group Q] [Group A]
    {ι : Sort v} (H : ι → Subgroup Q) (χ : Q →* A)
    (hSup : iSup H = ⊤) (hχ : χ ≠ 1) :
    ∃ i, ¬ H i ≤ χ.ker := by
  classical
  by_contra hnone
  apply hχ
  ext x
  have htop_le : (⊤ : Subgroup Q) ≤ χ.ker := by
    rw [← hSup]
    exact iSup_le fun i => by
      intro y hy
      by_contra hyker
      exact hnone ⟨i, fun hle => hyker (hle hy)⟩
  have hxker : x ∈ χ.ker := htop_le (Subgroup.mem_top x)
  simpa [MonoidHom.mem_ker] using hxker

public theorem injective_on_prime_card_subgroup_of_not_le_ker_sec9
    {Q : Type u} {A : Type w} [Group Q] [Finite Q] [Group A]
    (χ : Q →* A) {P : Subgroup Q} {p : ℕ}
    (hcard : Nat.card P = p) (hp : Nat.Prime p) (hP : ¬ P ≤ χ.ker) :
    Function.Injective fun x : P => χ (x : Q) := by
  classical
  let χP : P →* A := χ.comp P.subtype
  haveI : Fact (Nat.Prime (Nat.card P)) := ⟨by simpa [hcard] using hp⟩
  have hker_ne_top : χP.ker ≠ ⊤ := by
    intro htop
    apply hP
    intro y hy
    let yP : P := ⟨y, hy⟩
    have hykerP : yP ∈ χP.ker := by
      rw [htop]
      exact Subgroup.mem_top yP
    change χ y = 1
    simpa [χP, yP, MonoidHom.mem_ker] using hykerP
  have hker_bot : χP.ker = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card χP.ker with hbot | htop
    · exact hbot
    · exact False.elim (hker_ne_top htop)
  intro x y hxy
  have hdiv : x / y ∈ χP.ker := by
    change χ ((x / y : P) : Q) = 1
    simp [div_eq_mul_inv, hxy]
  have hbotmem : x / y ∈ (⊥ : Subgroup P) := by
    simpa [hker_bot] using hdiv
  have hdivone : x / y = 1 := by
    simpa using (Subgroup.mem_bot.mp hbotmem)
  exact div_eq_one.mp hdivone

@[expose] public noncomputable def pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.ClassFunction H :=
  fun h => θ ((Subgroup.subgroupOfEquivOfLe hHT).symm h)

public theorem subgroupOfClassFunction_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.subgroupOfClassFunction
        (T := T) (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) = θ := by
  ext h
  simp [pullbackClassFunctionOfSubgroupOfEquiv_sec9, Section1.subgroupOfClassFunction,
    Subgroup.subgroupOfEquivOfLe]

public theorem isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T)
    {θ : Section1.ClassFunction (H.subgroupOf T)}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let ρH : Representation ℂ H (Fin n → ℂ) := ρ.comp e.symm.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective
      ρ e.symm.toMonoidHom e.symm.surjective hρirr
  · ext h
    simp [ρH, e, pullbackClassFunctionOfSubgroupOfEquiv_sec9, hθeq,
      Representation.character, Subgroup.subgroupOfEquivOfLe]

public theorem degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9
    {G : Type u} [Group G] {H T : Subgroup G} (hHT : H ≤ T)
    (θ : Section1.ClassFunction (H.subgroupOf T)) :
    Section1.degree (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hHT θ) =
      Section1.degree θ := by
  change θ ((Subgroup.subgroupOfEquivOfLe hHT).symm 1) = θ 1
  congr 1

public theorem degree_eq_one_of_irreducible_kernel_quotient_commutative_sec9
    {G : Type u} [Group G] [Finite G]
    (H T : Subgroup G) [(H.subgroupOf T).Normal]
    {θ : Section1.ClassFunction T}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (H.subgroupOf T))
    (hcomm : IsMulCommutative (T ⧸ H.subgroupOf T)) :
    Section1.degree θ = 1 := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let q : T →* T ⧸ H.subgroupOf T := QuotientGroup.mk' (H.subgroupOf T)
  have hθkerρ : Section1.subgroupInKernel' ρ.character (H.subgroupOf T) := by
    simpa [hθeq] using hθker
  have hker : Section1.subgroupInRepresentationKernel ρ (H.subgroupOf T) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (H.subgroupOf T)).mp hθkerρ
  let ρq : Representation ℂ (T ⧸ H.subgroupOf T) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ (H.subgroupOf T) hker
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro t
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ
      (H.subgroupOf T) hker t
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective (H.subgroupOf T))
    simpa [hcomp_eq] using hρirr
  haveI : IsMulCommutative (T ⧸ H.subgroupOf T) := hcomm
  have hn : n = 1 := by
    haveI : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hθeq, Section1.degree_representation_character]
  simp [hn]

public theorem theorem_9_8_nonprincipal_MF_constituent_quotient_linear_character_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hMFleM : MF ≤ M)
    (hMFsubD : MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ¬ Section1.subgroupInKernel' ψ
          (((MF.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
        Section1.subgroupInKernel' ψ
          (((H0.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M))) →
          ∃ χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ,
            χ ≠ 1 ∧
              pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
                (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ) =
                Section1.quotientCharacterInflation H0 MF χ := by
  classical
  intro hcase hψirr hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let θM : Section1.ClassFunction (MF.subgroupOf M) :=
    pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
  let θ : Section1.ClassFunction MF :=
    pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
  have hθirr : Section1.IsIrreducibleCharacterOnGroup θ := by
    exact isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
      (isIrreducible_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD hψirr)
  have hθkerH0 : Section1.subgroupInKernel' θ (H0.subgroupOf MF) := by
    intro z
    have hzMF : ((z : MF) : G) ∈ MF := (z : MF).property
    have hzH0 : ((z : MF) : G) ∈ H0 := by
      exact (z : H0.subgroupOf MF).property
    let zM : M := ⟨(z : G), hMFleM hzMF⟩
    let zD : D.subgroupOf M := ⟨zM, by
      exact hMFsubD (by
        simp [zM, Subgroup.mem_subgroupOf])⟩
    let zK : K := ⟨zD, by
      change (zD : M) ∈ MF.subgroupOf M
      simp [zD, zM, Subgroup.mem_subgroupOf]⟩
    let zA :
        ((H0.subgroupOf M).subgroupOf (D.subgroupOf M)).subgroupOf K :=
      ⟨zK, by
        change (zK : D.subgroupOf M) ∈
          (H0.subgroupOf M).subgroupOf (D.subgroupOf M)
        change (zD : M) ∈ H0.subgroupOf M
        simpa [zD, zM, Subgroup.mem_subgroupOf] using hzH0⟩
    have hzψ := hψkerH0 zA
    have hdegθ :
        Section1.degree θ = Section1.degree ψ := by
      calc
        Section1.degree θ = Section1.degree θM := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
        _ = Section1.degree ψ := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
    calc
      θ z = ψ zK := by
        simp [θ, θM, zK, zD, zM, pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Subgroup.subgroupOfEquivOfLe]
      _ = Section1.degree ψ := hzψ
      _ = Section1.degree θ := hdegθ.symm
  have hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := by
    rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hpval, hpData⟩
    rcases hpData with
      ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, _hH0ltMF, hElem, _hrest⟩
    rcases hElem with ⟨hnormal, hbarElem⟩
    letI : (H0.subgroupOf MF).Normal := hnormal
    letI : IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := hbarElem
    infer_instance
  have hθdeg : Section1.degree θ = 1 :=
    degree_eq_one_of_irreducible_kernel_quotient_commutative_sec9
      H0 MF hθirr hθkerH0 hcomm
  rcases Section1.exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
      H0 MF hθirr hθkerH0 hθdeg with
    ⟨χ, hθχ⟩
  have hχne : χ ≠ 1 := by
    intro hχone
    apply hψnotMF
    intro z
    let zD : D.subgroupOf M := (z : K)
    let zM : M := zD
    let zMF : MF := ⟨(zM : G), by
      change zM ∈ MF.subgroupOf M
      exact (z : K).property⟩
    have hθtop : θ zMF = Section1.degree θ := by
      rw [hθχ, hχone]
      simp [Section1.quotientCharacterInflation, Section1.degree]
    have hdegθ :
        Section1.degree θ = Section1.degree ψ := by
      calc
        Section1.degree θ = Section1.degree θM := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM θM
        _ = Section1.degree ψ := by
          exact degree_pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ
    calc
      ψ (z : K) = θ zMF := by
        simp [θ, θM, zMF, zD, zM, pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Subgroup.subgroupOfEquivOfLe]
      _ = Section1.degree θ := hθtop
      _ = Section1.degree ψ := hdegθ
  exact ⟨χ, hχne, hθχ⟩

public theorem theorem_9_8_semidirect_index_eq_inf_complement_index_sec9
    {L : Type u} [Group L] [Finite L]
    (K W T : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    (hKT : K ≤ T) :
    T.index = ((W ⊓ T : Subgroup L).subgroupOf W).index := by
  classical
  have hcompTop : (K.subgroupOf (⊤ : Subgroup L)).IsComplement'
      (W.subgroupOf (⊤ : Subgroup L)) :=
    Section2.internalSemidirectProduct_isComplement hsemi
  have hcardL : Nat.card L = Nat.card K * Nat.card W := by
    have hmul := hcompTop.card_mul
    calc
      Nat.card L = Nat.card (⊤ : Subgroup L) := (Subgroup.card_top (G := L)).symm
      _ = Nat.card (K.subgroupOf (⊤ : Subgroup L)) *
            Nat.card (W.subgroupOf (⊤ : Subgroup L)) := hmul.symm
      _ = Nat.card K * Nat.card W := by
        rw [natCard_subgroupOf_eq K (⊤ : Subgroup L) le_top,
          natCard_subgroupOf_eq W (⊤ : Subgroup L) le_top]
  let WT : Subgroup L := W ⊓ T
  let WTsubT : Subgroup T := WT.subgroupOf T
  let WTsubW : Subgroup W := WT.subgroupOf W
  have hWT_le_T : WT ≤ T := by simp [WT]
  have hWT_le_W : WT ≤ W := by simp [WT]
  have hKsubT_comp : (K.subgroupOf T).IsComplement' WTsubT := by
    have hdisj : Disjoint (K.subgroupOf T) WTsubT := by
      rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        have hxInf : ((x : T) : L) ∈ K ⊓ W := by
          exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
            by simpa [WTsubT, WT, Subgroup.mem_subgroupOf] using hx.2.1⟩
        have hxBot : ((x : T) : L) ∈ (⊥ : Subgroup L) := by
          simpa [hsemi.inf_eq_bot] using hxInf
        ext
        simpa using hxBot
      · exact bot_le
    have hsupTop : K.subgroupOf T ⊔ WTsubT = ⊤ := by
      apply le_antisymm
      · exact le_top
      · intro x _hx
        have hxT : (x : L) ∈ T := x.property
        have hxTop : (x : L) ∈ (⊤ : Subgroup L) := by simp
        rcases hsemi.mul_surjective (x : L) hxTop with ⟨k, hkK, w, hwW, hxkw⟩
        have hkT : k ∈ T := hKT hkK
        have hkwT : k * w ∈ T := by
          rw [← hxkw]
          exact hxT
        have hwT : w ∈ T := by
          have hleft : k⁻¹ * (k * w) ∈ T := T.mul_mem (T.inv_mem hkT) hkwT
          simpa [mul_assoc] using hleft
        have hwWT : w ∈ WT := by
          simpa [WT] using (show w ∈ W ⊓ T from ⟨hwW, hwT⟩)
        let kT : T := ⟨k, hkT⟩
        let wT : T := ⟨w, hwT⟩
        have hkTmem : kT ∈ K.subgroupOf T := by
          simpa [kT, Subgroup.mem_subgroupOf] using hkK
        have hwTmem : wT ∈ WTsubT := by
          change ((wT : T) : L) ∈ WT
          simpa [wT] using hwWT
        have hx_eq : x = kT * wT := by
          ext
          simpa [kT, wT] using hxkw
        rw [hx_eq]
        exact Subgroup.mul_mem_sup hkTmem hwTmem
    letI : (K.subgroupOf T).Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : K.Normal) T
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (K.subgroupOf T) WTsubT hdisj hsupTop
  have hcardT : Nat.card T = Nat.card K * Nat.card WT := by
    have hmul := hKsubT_comp.card_mul
    calc
      Nat.card T = Nat.card (K.subgroupOf T) * Nat.card WTsubT := hmul.symm
      _ = Nat.card K * Nat.card WT := by
        rw [natCard_subgroupOf_eq K T hKT,
          natCard_subgroupOf_eq WT T hWT_le_T]
  have hTmul : Nat.card T * T.index = Nat.card L := Subgroup.card_mul_index T
  have hWsubmul : Nat.card WT * WTsubW.index = Nat.card W := by
    have hmul := Subgroup.card_mul_index (H := WTsubW)
    simpa [WTsubW, natCard_subgroupOf_eq WT W hWT_le_W] using hmul
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hcancel : Nat.card WT * T.index = Nat.card W := by
    apply Nat.mul_left_cancel hKpos
    calc
      Nat.card K * (Nat.card WT * T.index)
          = Nat.card T * T.index := by rw [hcardT, Nat.mul_assoc]
      _ = Nat.card L := hTmul
      _ = Nat.card K * Nat.card W := hcardL
  have hidx : T.index = WTsubW.index := by
    exact Nat.mul_left_cancel (Nat.card_pos (α := WT)) (by
      calc
        Nat.card WT * T.index = Nat.card W := hcancel
        _ = Nat.card WT * WTsubW.index := hWsubmul.symm)
  simpa [WT, WTsubW] using hidx

public theorem theorem_9_8_index_dvd_of_semidirect_factor_kernel_sec9
    {L : Type u} [Group L] [Finite L]
    {A : Type v} [Group A]
    (K W T : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    (hKT : K ≤ T)
    (f : W →* A) (a : ℕ)
    (hcard : Nat.card f.range = a)
    (hWTker : ((W ⊓ T : Subgroup L).subgroupOf W) ≤ f.ker) :
    a ∣ T.index := by
  have hTindex : T.index = ((W ⊓ T : Subgroup L).subgroupOf W).index :=
    theorem_9_8_semidirect_index_eq_inf_complement_index_sec9 K W T hsemi hKT
  have hfindex : f.ker.index = a := by
    rw [Subgroup.index_ker, hcard]
  exact hfindex ▸ (hTindex ▸ Subgroup.index_dvd_of_le hWTker)

public theorem
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (hKnormal :
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                      letI : ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                      (hMFleM : MF ≤ M) →
                      (hMFsubD :
                        MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M) →
                      (χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) →
                        (i : Fin q) →
                          ¬ H i ≤ χ.ker →
                            pullbackClassFunctionOfSubgroupOfEquiv_sec9
                              hMFleM
                              (pullbackClassFunctionOfSubgroupOfEquiv_sec9
                                hMFsubD ψ) =
                                Section1.quotientCharacterInflation H0 MF χ →
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    ∀ u : U,
                                      QuotientGroup.mk' (C.subgroupOf U) u =
                                        QuotientGroup.mk' (C.subgroupOf U)
                                          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) →
                                        quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
  classical
  intro hcase hnormalH0 H hcard _hnorm _hindep _hSup hfac
    hKnormal hMFleM hMFsubD χ i hiχ hψχ hnormalC x hxT u hu
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : ((MF.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
  letI : (C.subgroupOf U).Normal := hnormalC
  rcases hfac i with ⟨hnormalCfac, ρ, _hcyc, _hρcard, haction, hker⟩
  letI : (C.subgroupOf U).Normal := hnormalCfac
  have hχinj :
      Function.Injective fun y : H i => χ (y : MF ⧸ H0.subgroupOf MF) :=
    injective_on_prime_card_subgroup_of_not_le_ker_sec9 χ (hcard i)
      (case_9_7_a_p_prime_sec9 hcase) hiχ
  have hcoset_toU :
      QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) =
        QuotientGroup.mk' (C.subgroupOf U) u := hu.symm
  have hρ_eq :
      ρ (QuotientGroup.mk' (C.subgroupOf U) u) =
        ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) := by
    rw [hu]
  have hxKernel :
      ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) = 1 := by
    ext y
    rcases y with ⟨y, hyH⟩
    have hsubeq :
        (ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))
            ⟨y, hyH⟩ : H i) =
          (1 : MulAut (H i)) ⟨y, hyH⟩ := by
      apply hχinj
      change
        χ ((ρ (QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))
            ⟨y, hyH⟩ : H i) : MF ⧸ H0.subgroupOf MF) =
          χ ((1 : MulAut (H i)) ⟨y, hyH⟩ : H i)
      let xU : U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x
      revert hyH
      refine QuotientGroup.induction_on y ?_
      intro h hyH'
      rcases haction (QuotientGroup.mk' (C.subgroupOf U) xU) xU rfl with
        ⟨hconjMF, hρ_apply⟩
      let D : Subgroup G := ambientDerivedSubgroup M
      let K : Subgroup (D.subgroupOf M) :=
        (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
      let hM : M := ⟨(h : G), hMFleM h.property⟩
      let hD : D.subgroupOf M := ⟨hM, by
        exact hMFsubD (by
          simp [hM, Subgroup.mem_subgroupOf])⟩
      let hK : K := ⟨hD, by
        change (hD : M) ∈ MF.subgroupOf M
        simp [hD, hM, Subgroup.mem_subgroupOf]⟩
      let hConj : MF := ⟨(xU : G)⁻¹ * (h : G) * (xU : G), hconjMF h⟩
      let hConjM : M := ⟨(hConj : G), hMFleM hConj.property⟩
      let hConjD : D.subgroupOf M := ⟨hConjM, by
        exact hMFsubD (by
          simpa [hConjM, hConj, Subgroup.mem_subgroupOf] using hConj.property)⟩
      let hConjK : K := ⟨hConjD, by
        change (hConjD : M) ∈ MF.subgroupOf M
        simpa [hConjD, hConjM, hConj, Subgroup.mem_subgroupOf] using hConj.property⟩
      have hρ_val :
          ((ρ (QuotientGroup.mk' (C.subgroupOf U) xU))
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyH'⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF) hConj := by
        simpa [xU, hConj] using hρ_apply h hyH'
      have hxInvT :
          ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) ∈
            Section1.inertiaSubgroup K ψ := by
        exact (Section1.inertiaSubgroup K ψ).inv_mem hxT
      have hψ_conj : ψ hConjK = ψ hK := by
        have hxInvEq :
            Section1.conjugateOnNormal K ψ
                ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) = ψ :=
          by
            change
              Section1.conjugateOnNormal K ψ
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹) = ψ at hxInvT
            exact hxInvT
        have hraw := congrArg (fun θ => θ hK) hxInvEq
        have hsame :
            (⟨((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹ *
                  (hK : D.subgroupOf M) *
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹)⁻¹),
                hKnormal.conj_mem (hK : D.subgroupOf M) hK.property
                  ((x : (ambientDerivedSubgroup M).subgroupOf M)⁻¹)⟩ : K) =
              hConjK := by
          ext
          simp [D, hK, hD, hM, hConjK, hConjD, hConjM, hConj, xU,
            theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9, mul_assoc]
        change
          ψ (⟨((x : D.subgroupOf M)⁻¹) * (hK : D.subgroupOf M) *
                ((x : D.subgroupOf M)⁻¹)⁻¹,
              hKnormal.conj_mem (hK : D.subgroupOf M) hK.property
                ((x : D.subgroupOf M)⁻¹)⟩ : K) = ψ hK at hraw
        rw [hsame] at hraw
        exact hraw
      have hχ_h :
          ψ hK = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ) := by
        have heval := congrArg (fun θ => θ h) hψχ
        simpa [pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Section1.quotientCharacterInflation, Subgroup.subgroupOfEquivOfLe,
          hK, hD, hM] using heval
      have hχ_conj :
          ψ hConjK = (χ (QuotientGroup.mk' (H0.subgroupOf MF) hConj) : ℂ) := by
        have heval := congrArg (fun θ => θ hConj) hψχ
        simpa [pullbackClassFunctionOfSubgroupOfEquiv_sec9,
          Section1.quotientCharacterInflation, Subgroup.subgroupOfEquivOfLe,
          hConjK, hConjD, hConjM] using heval
      apply Units.ext
      calc
        (χ ((ρ (QuotientGroup.mk' (C.subgroupOf U) xU))
              ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyH'⟩ :
                MF ⧸ H0.subgroupOf MF) : ℂ)
            = (χ (QuotientGroup.mk' (H0.subgroupOf MF) hConj) : ℂ) := by
              rw [hρ_val]
        _ = ψ hConjK := hχ_conj.symm
        _ = ψ hK := hψ_conj
        _ = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ) := hχ_h
    exact congrArg Subtype.val hsubeq
  have huKernel : ρ (QuotientGroup.mk' (C.subgroupOf U) u) = 1 := by
    rw [hρ_eq, hxKernel]
  exact (hker (QuotientGroup.mk' (C.subgroupOf U) u)).mp huKernel u rfl


/-- Variant of
`theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_sec9`
for situations where the chosen component family is already fixed.  The
component-orbit package is not used by the centralizer calculation itself. -/
public theorem
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_noOrbit_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (hKnormal :
                      ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                      letI : ((MF.subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                      (χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ) →
                        (i : Fin q) →
                          ¬ H i ≤ χ.ker →
                            (∀ h :
                                (MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M),
                              ψ h =
                                (χ (QuotientGroup.mk' (H0.subgroupOf MF)
                                  ⟨(((h :
                                    (ambientDerivedSubgroup M).subgroupOf M) :
                                      M) : G), by
                                    have hh :
                                        ((h :
                                          (ambientDerivedSubgroup M).subgroupOf M) :
                                            M) ∈ MF.subgroupOf M := h.property
                                    simpa [Subgroup.mem_subgroupOf] using hh⟩) :
                                  ℂ)) →
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    quotientSubgroupCentralizedByElement MF H0 (H i)
                                      (((x :
                                        (ambientDerivedSubgroup M).subgroupOf M) :
                                          M) : G) := by
  classical
  intro hcase hnormalH0 H hcard hnorm hindep hSup hfac hKnormal
    χ i hiχ hψχ hnormalC x hxT
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : ((MF.subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
  letI : (C.subgroupOf U).Normal := hnormalC
  have hMFleM : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMFsubD :
      MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro y hy
    exact MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q
      hcase.1 (by simpa [Subgroup.mem_subgroupOf] using hy)
  have hψχ_core :
      pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFleM
        (pullbackClassFunctionOfSubgroupOfEquiv_sec9 hMFsubD ψ) =
        Section1.quotientCharacterInflation H0 MF χ := by
    ext h
    let hM : M := Subgroup.inclusion hMFleM h
    let hB :
        (MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M) :=
      ⟨Subgroup.inclusion hMFsubD ⟨hM, by
        change (hM : G) ∈ MF
        exact h.property⟩, by
          change ((Subgroup.inclusion hMFsubD ⟨hM, by
            change (hM : G) ∈ MF
            exact h.property⟩ :
              (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ MF.subgroupOf M
          change (hM : G) ∈ MF
          exact h.property⟩
    have hToMF :
        (Subgroup.subgroupOfEquivOfLe hMFleM)
            ((Subgroup.subgroupOfEquivOfLe hMFsubD) hB) = h := by
      apply Subtype.ext
      rfl
    change ψ hB = (χ (QuotientGroup.mk' (H0.subgroupOf MF) h) : ℂ)
    rw [← hToMF]
    exact hψχ hB
  let u : U := ⟨(((x :
      (ambientDerivedSubgroup M).subgroupOf M) : M) : G), by
    have hxUM :
        ((x : (ambientDerivedSubgroup M).subgroupOf M) : M) ∈ U.subgroupOf M :=
      Subgroup.mem_subgroupOf.mp x.property
    simpa [Subgroup.mem_subgroupOf] using hxUM⟩
  have hquot :
      QuotientGroup.mk' (C.subgroupOf U) u =
        QuotientGroup.mk' (C.subgroupOf U)
          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) := by
    rfl
  simpa [u] using
    theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
      M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep
      hSup hfac hKnormal hMFleM hMFsubD χ i hiχ hψχ_core
      hnormalC x hxT u hquot

public theorem
    theorem_9_8_nonprincipal_MF_constituent_component_centralized_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hnormalH0 : (H0.subgroupOf MF).Normal) →
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) →
          (∀ i, Nat.card (H i) = p) →
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
              iSupIndep H →
                iSup H = ⊤ →
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) →
                    (∃ hqpos : 0 < q,
                      ∀ i : Fin q,
                        ∃ w : W1,
                          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩)
                            (H i) (w : G)) →
                      (hKnormal :
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
                        letI : ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
                        Section1.IsIrreducibleCharacterOnGroup ψ →
                          ¬ Section1.subgroupInKernel' ψ
                            (((MF.subgroupOf M).subgroupOf
                              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                                ((MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M))) →
                          Section1.subgroupInKernel' ψ
                            (((H0.subgroupOf M).subgroupOf
                              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                                ((MF.subgroupOf M).subgroupOf
                                  ((ambientDerivedSubgroup M).subgroupOf M))) →
                            ∃ i : Fin q,
                              ∀ hnormalC : (C.subgroupOf U).Normal,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∀ x : (U.subgroupOf M).subgroupOf
                                    ((ambientDerivedSubgroup M).subgroupOf M),
                                  (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                                      Section1.inertiaSubgroup
                                        ((MF.subgroupOf M).subgroupOf
                                          ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                                    ∀ u : U,
                                      QuotientGroup.mk' (C.subgroupOf U) u =
                                        QuotientGroup.mk' (C.subgroupOf U)
                                          (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x) →
                                        quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
  classical
  intro hcase hnormalH0 H hcard hnorm hindep hSup hfac horbit hKnormal
    hψirr hψnotMF hψkerH0
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hMFleM : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMFsubD : MF.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    exact MF_le_ambientDerived_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1
      (by simpa [Subgroup.mem_subgroupOf] using hx)
  rcases theorem_9_8_nonprincipal_MF_constituent_quotient_linear_character_sec9
      M MF U W1 W2 H0 C p q a hMFleM hMFsubD ψ hcase hψirr hψnotMF
      hψkerH0 with
    ⟨χ, hχne, hψχ⟩
  rcases exists_component_not_le_ker_of_iSup_eq_top_sec9
      (Q := MF ⧸ H0.subgroupOf MF) (A := ℂˣ) H χ hSup hχne with
    ⟨i, hiχ⟩
  refine ⟨i, ?_⟩
  exact theorem_9_8_nonprincipal_MF_quotient_linear_component_centralized_source_core_sec9
    M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep hSup
    hfac hKnormal hMFleM hMFsubD χ i hiχ hψχ

public theorem theorem_9_8_nonprincipal_MF_constituent_component_factor_kernel_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ¬ Section1.subgroupInKernel' ψ
            (((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
          Section1.subgroupInKernel' ψ
            (((H0.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
            ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
              letI : (H0.subgroupOf MF).Normal := hnormalH0
              ∃ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                ∃ hnormalC : (C.subgroupOf U).Normal,
                  letI : (C.subgroupOf U).Normal := hnormalC
                  ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut Q,
                    Nat.card ρ.range = a ∧
                      ∀ x : (U.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M),
                        (x : (ambientDerivedSubgroup M).subgroupOf M) ∈
                            Section1.inertiaSubgroup
                              ((MF.subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) ψ →
                          ρ (QuotientGroup.mk' (C.subgroupOf U)
                            (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x)) = 1 := by
  intro hcase hKnormal hψirr hψnotMF hψkerH0
  rcases case_9_7_a_component_decomposition_sec9 hcase with
    ⟨hnormalH0, H, hcard, hnorm, hindep, hSup, hfac, horbit⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_8_nonprincipal_MF_constituent_component_centralized_source_core_sec9
        M MF U W1 W2 H0 C p q a ψ hcase hnormalH0 H hcard hnorm hindep
        hSup hfac horbit hKnormal hψirr hψnotMF hψkerH0 with
    ⟨i, hcentralized⟩
  rcases hfac i with ⟨hnormalC, ρ, _hcyc, hρcard, _haction, hker⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  refine ⟨hnormalH0, H i, hnormalC, ρ, hρcard, ?_⟩
  intro x hxT
  exact (hker (QuotientGroup.mk' (C.subgroupOf U)
      (theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U x))).mpr
    (by
      intro u hu
      exact hcentralized hnormalC x hxT u hu)

public theorem theorem_9_8_nonprincipal_MF_constituent_inertia_index_dvd_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (hKnormal :
        ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal) →
        letI : ((MF.subgroupOf M).subgroupOf
          ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hKnormal
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ¬ Section1.subgroupInKernel' ψ
            (((MF.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
          Section1.subgroupInKernel' ψ
            (((H0.subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))) →
            a ∣ (Section1.inertiaSubgroup
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) ψ).index := by
  classical
  intro hcase hKnormal hψirr hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let L : Type u := D.subgroupOf M
  let K : Subgroup L := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  let W : Subgroup L := (U.subgroupOf M).subgroupOf (D.subgroupOf M)
  let T : Subgroup L := Section1.inertiaSubgroup K ψ
  have hKnormal' : K.Normal := by
    simpa [D, L, K] using hKnormal
  letI : K.Normal := hKnormal'
  rcases theorem_9_8_nonprincipal_MF_constituent_component_factor_kernel_source_core_sec9
      M MF U W1 W2 H0 C p q a ψ hcase
      (by simpa [D, L, K] using hKnormal') hψirr hψnotMF hψkerH0 with
    ⟨hnormalH0, Q, hnormalC, ρ, hρcard, hρkerT⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  let toU : W →* U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U
  let f : W →* ρ.range :=
    ρ.rangeRestrict.comp ((QuotientGroup.mk' (C.subgroupOf U)).comp toU)
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q := hcase.1
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD, hUleD, _hD_eq, _hMFUdisj⟩
  have hUleM : U ≤ M := hUleD.trans hDleM
  have htoU_surj : Function.Surjective toU := by
    intro u0
    let uM : M := ⟨(u0 : G), hUleM u0.property⟩
    let uD : D.subgroupOf M :=
      ⟨uM, by
        simpa [D, Subgroup.mem_subgroupOf, uM] using hUleD u0.property⟩
    let uW : W :=
      ⟨uD, by
        change (uD : M) ∈ U.subgroupOf M
        simp [uD, uM, Subgroup.mem_subgroupOf]⟩
    exact ⟨uW, by
      ext
      rfl⟩
  have hfrange_top : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u0, rfl⟩
    rcases htoU_surj u0 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    ext
    simp [f, toU, hw]
  have hfrange_card : Nat.card f.range = a := by
    rw [hfrange_top]
    simpa using hρcard
  have hKT : K ≤ T :=
    Section1.proposition_1_7_inertia_contains_H K ψ
      (Section1.isCharacter_isClassFunction ψ
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr))
  have hWTker : ((W ⊓ T : Subgroup L).subgroupOf W) ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change ρ.rangeRestrict
        ((QuotientGroup.mk' (C.subgroupOf U)) (toU x)) = 1
    have hxT : (x : L) ∈ T := by
      exact hx.2
    have hρone : ρ ((QuotientGroup.mk' (C.subgroupOf U)) (toU x)) = 1 :=
      hρkerT x (by simpa [D, L, K, T] using hxT)
    exact Subtype.ext (by simpa using hρone)
  have hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W := by
    simpa [D, L, K, W] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q h92 hKnormal
  simpa [D, L, K, W, T] using
    theorem_9_8_index_dvd_of_semidirect_factor_kernel_sec9
      K W T hsemi hKT f a hfrange_card hWTker

public theorem theorem_9_8_nonprincipal_book_constituent_inertia_witness_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M))
    (ψ : Section1.ClassFunction
      ((MF.subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            Section1.IsIrreducibleCharacterOnGroup ψ →
              Section1.scalarProduct
                ((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M))
                ψ
                (Section1.subgroupRestriction
                  ((MF.subgroupOf M).subgroupOf
                    ((ambientDerivedSubgroup M).subgroupOf M)) θ) ≠ 0 →
              ¬ Section1.subgroupInKernel' ψ
                (((MF.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M))) →
              Section1.subgroupInKernel' ψ
                (((H0.subgroupOf M).subgroupOf
                  ((ambientDerivedSubgroup M).subgroupOf M)).subgroupOf
                    ((MF.subgroupOf M).subgroupOf
                      ((ambientDerivedSubgroup M).subgroupOf M))) →
                ∃ T : Subgroup ((ambientDerivedSubgroup M).subgroupOf M),
                  ∃ η : Section1.ClassFunction T,
                    Section1.IsIrreducibleCharacterOnGroup η ∧
                      Section1.IsIrreducibleCharacterOnGroup
                        (Section1.inducedCF T η) ∧
                      Section1.scalarProduct T η
                        (Section1.subgroupRestriction T θ) ≠ 0 ∧
                      a ∣ T.index := by
  intro hcase _hBarU _hUprime hθirr hψirr hψinner hψnotMF hψkerH0
  let D : Subgroup G := ambientDerivedSubgroup M
  let K : Subgroup (D.subgroupOf M) := (MF.subgroupOf M).subgroupOf (D.subgroupOf M)
  have hKnormal : K.Normal := by
    simpa [D, K] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : K.Normal := hKnormal
  let T : Subgroup (D.subgroupOf M) := Section1.inertiaSubgroup K ψ
  rcases theorem_9_8_clifford_inertia_inducing_constituent_source_core_sec9
      K hθirr hψirr (by simpa [D, K] using hψinner) with
    ⟨η, hηirr, hIndηirr, hηinner⟩
  have hindex : a ∣ T.index := by
    simpa [D, K, T] using
      theorem_9_8_nonprincipal_MF_constituent_inertia_index_dvd_source_core_sec9
        M MF U W1 W2 H0 C p q a ψ hcase
        (by simpa [D, K] using hKnormal) hψirr hψnotMF hψkerH0
  exact ⟨T, η, hηirr, hIndηirr, by simpa [D, K, T] using hηinner, hindex⟩

public theorem theorem_9_8_nonprincipal_book_constituent_inertia_divisibility_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              ∃ T : Subgroup ((ambientDerivedSubgroup M).subgroupOf M),
                ∃ η : Section1.ClassFunction T,
                  Section1.IsIrreducibleCharacterOnGroup η ∧
                    θ = Section1.inducedCF T η ∧
                      a ∣ T.index := by
  intro hcase hBarU hUprime hθirr hθnotMF hθkerH0
  rcases theorem_9_8_exists_MF_restriction_constituent_sec9
      M MF U W1 W2 H0 C p q a θ hcase hθirr hθnotMF hθkerH0 with
    ⟨ψ, hψirr, hψinner, hψnotMF, hψkerH0⟩
  rcases theorem_9_8_nonprincipal_book_constituent_inertia_witness_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ ψ hcase hBarU hUprime
      hθirr hψirr hψinner hψnotMF hψkerH0 with
    ⟨T, η, hηirr, hIndηirr, hηinner, hindex⟩
  exact ⟨T, η, hηirr,
    inducedCF_eq_of_irreducible_constituent_sec9 T hθirr hIndηirr hηinner,
    hindex⟩

public theorem theorem_9_8_witness_constituent_degree_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
              characterDegreeDivisibleBy a θ := by
  intro hcase hBarU hUprime hθirr hθnot hθker
  rcases theorem_9_8_nonprincipal_book_constituent_inertia_divisibility_data_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ hcase hBarU hUprime hθirr hθnot
      hθker with
    ⟨T, η, hηirr, hθeq, hindex⟩
  exact characterDegreeDivisibleBy_inducedCF_of_index_dvd_sec9 T a θ η
    hηirr hθeq hindex

public theorem theorem_9_8_degree_divisibility_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                  characterDegreeDivisibleBy a χ) ∧
                ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                  ∀ θ : Section1.ClassFunction
                      ((ambientDerivedSubgroup M).subgroupOf M),
                    Section1.IsIrreducibleCharacterOnGroup θ →
                      ¬ Section1.subgroupInKernel' θ
                        ((MF.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) →
                      Section1.subgroupInKernel' θ
                        ((H0.subgroupOf M).subgroupOf
                          ((ambientDerivedSubgroup M).subgroupOf M)) →
                      χ = Section1.inducedCF
                        ((ambientDerivedSubgroup M).subgroupOf M) θ →
                        characterDegreeDivisibleBy a θ := by
  intro hcase hBarU hUprime hSH0 _hSH0C _hSH0U
  have hwitness :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
        ∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
          Section1.IsIrreducibleCharacterOnGroup θ →
            ¬ Section1.subgroupInKernel' θ
              ((MF.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            Section1.subgroupInKernel' θ
              ((H0.subgroupOf M).subgroupOf
                ((ambientDerivedSubgroup M).subgroupOf M)) →
            χ = Section1.inducedCF
              ((ambientDerivedSubgroup M).subgroupOf M) θ →
              characterDegreeDivisibleBy a θ := by
    intro _χ _hχ θ hθirr hθnot hθker _hχeq
    exact theorem_9_8_witness_constituent_degree_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u θ hcase hBarU hUprime hθirr hθnot hθker
  constructor
  · intro χ hχ
    rcases hSH0 with ⟨_hH0le, _hMFle, hmem⟩
    rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
    exact characterDegreeDivisibleBy_inducedCF_of_constituent_sec9
      ((ambientDerivedSubgroup M).subgroupOf M) a χ θ
      (hwitness χ hχ θ hθirr hθnot hθker hχeq) hχeq
  · exact hwitness



end CFSG.Section9
