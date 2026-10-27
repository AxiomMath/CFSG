module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.E6.NativeTwoA2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Main

noncomputable section

abbrev e6Supp13 : Set (Fin Tag.E6.rank) := CFSG.RankThree.E6.support13

abbrev e6Supp56 : Set (Fin Tag.E6.rank) := CFSG.RankThree.E6.support56

@[expose] def e6FrameMoveWord : List (Fin Tag.E6.rank) :=
  [CFSG.RankThree.E6.e6Index 3, CFSG.RankThree.E6.e6Index 4, CFSG.RankThree.E6.e6Index 5,
    CFSG.RankThree.E6.e6Index 1, CFSG.RankThree.E6.e6Index 3, CFSG.RankThree.E6.e6Index 4,
    CFSG.RankThree.E6.e6Index 2, CFSG.RankThree.E6.e6Index 3, CFSG.RankThree.E6.e6Index 0,
    CFSG.RankThree.E6.e6Index 2, CFSG.RankThree.E6.e6Index 1, CFSG.RankThree.E6.e6Index 3]

theorem e6FrameMoveWord_smul_e0 :
    (coxeterSystem Tag.E6).wordProd e6FrameMoveWord •
        (Pi.single (CFSG.RankThree.E6.e6Index 0) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (CFSG.RankThree.E6.e6Index 5) 1 := by
  simp only [e6FrameMoveWord, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil,
    mul_smul, one_smul, simple_smul]
  decide +kernel

theorem e6FrameMoveWord_smul_e2 :
    (coxeterSystem Tag.E6).wordProd e6FrameMoveWord •
        (Pi.single (CFSG.RankThree.E6.e6Index 2) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (CFSG.RankThree.E6.e6Index 4) 1 := by
  simp only [e6FrameMoveWord, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil,
    mul_smul, one_smul, simple_smul]
  decide +kernel

@[expose] def e6FrameMoveElt (K : Type) [Field K] : ModGL Tag.E6 K :=
  (e6FrameMoveWord.map fun i => weylElt Tag.E6 K i 1).prod

@[expose] def e6FrameWeylElt (K : Type) [Field K] : ModGL Tag.E6 K :=
  CFSG.HardMathSupport.Lang.AnisoE6.nElt Tag.E6 K CFSG.HardMathSupport.Lang.AnisoE6.wWord

theorem e6FrameMoveElt_mem_adjointGroup (K : Type) [Field K] :
    e6FrameMoveElt K ∈ adjointGroup .E6 K := by
  unfold e6FrameMoveElt
  exact Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem e6FrameWeylElt_mem_adjointGroup (K : Type) [Field K] :
    e6FrameWeylElt K ∈ adjointGroup .E6 K := by
  unfold e6FrameWeylElt CFSG.HardMathSupport.Lang.AnisoE6.nElt
  exact Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

@[expose] def e6FrameMoveEltAdj (K : Type) [Field K] : adjointGroup .E6 K :=
  ⟨e6FrameMoveElt K, e6FrameMoveElt_mem_adjointGroup K⟩

@[expose] def e6FrameWeylEltAdj (K : Type) [Field K] : adjointGroup .E6 K :=
  ⟨e6FrameWeylElt K, e6FrameWeylElt_mem_adjointGroup K⟩

@[expose] def e6FrameSubgroupConjHom {G : Type*} [Group G] {H : Subgroup G} (g : H) : H →* H where
  toFun x := ⟨g * x * g⁻¹, H.mul_mem (H.mul_mem g.2 x.2) (H.inv_mem g.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by push_cast; group)

theorem e6FrameSubgroupConjHom_coe {G : Type*} [Group G] {H : Subgroup G} (g x : H) :
    ((e6FrameSubgroupConjHom g x : H) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
  rfl

theorem e6FrameSubgroupConjHom_injective {G : Type*} [Group G] {H : Subgroup G} (g : H) :
    Function.Injective (e6FrameSubgroupConjHom g) := by
  intro x y h
  have h' : (g : G) * (x : G) * (g : G)⁻¹ = (g : G) * (y : G) * (g : G)⁻¹ := by
    simpa only [e6FrameSubgroupConjHom_coe] using congrArg (fun z : H => (z : G)) h
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

theorem e6FrameSubgroupCommute_of_coe {G : Type*} [Group G] {H : Subgroup G} {a b : H}
    (h : Commute (a : G) (b : G)) : Commute a b :=
  (commute_iff_eq a b).2 (Subtype.ext h.eq)

theorem e6FrameConjMove_mem_support56 {K : Type} [Field K] [CharP K 2] {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K e6Supp13) :
    e6FrameMoveElt K * g * (e6FrameMoveElt K)⁻¹ ∈ subsystemGroup Tag.E6 K e6Supp56 := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hy
    · have hx : e6FrameMoveElt K * xUnit Tag.E6 K j c * (e6FrameMoveElt K)⁻¹ =
          pinnedX Tag.E6 K (((coxeterSystem Tag.E6).wordProd e6FrameMoveWord) •
            (Pi.single j 1)) c := by
        unfold e6FrameMoveElt
        rw [← pinnedX_single Tag.E6 K j c]
        exact CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo e6FrameMoveWord
          (isRoot_single Tag.E6 j) c
      rw [hx]
      rcases (CFSG.RankThree.E6.mem_support13 j).1 hj with rfl | rfl
      · rw [e6FrameMoveWord_smul_e0, pinnedX_single]
        exact Subgroup.subset_closure ⟨CFSG.RankThree.E6.e6Index 5,
          (CFSG.RankThree.E6.mem_support56 _).2 (Or.inr rfl), c, Or.inl rfl⟩
      · rw [e6FrameMoveWord_smul_e2, pinnedX_single]
        exact Subgroup.subset_closure ⟨CFSG.RankThree.E6.e6Index 4,
          (CFSG.RankThree.E6.mem_support56 _).2 (Or.inl rfl), c, Or.inl rfl⟩
    · have hy' : e6FrameMoveElt K * yUnit Tag.E6 K j c * (e6FrameMoveElt K)⁻¹ =
          pinnedX Tag.E6 K (((coxeterSystem Tag.E6).wordProd e6FrameMoveWord) •
            (-(Pi.single j 1))) c := by
        unfold e6FrameMoveElt
        rw [← pinnedX_neg_single Tag.E6 K j c]
        exact CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo e6FrameMoveWord
          (isRoot_neg_single Tag.E6 j) c
      rw [hy', smul_neg]
      rcases (CFSG.RankThree.E6.mem_support13 j).1 hj with rfl | rfl
      · rw [e6FrameMoveWord_smul_e0, pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨CFSG.RankThree.E6.e6Index 5,
          (CFSG.RankThree.E6.mem_support56 _).2 (Or.inr rfl), c, Or.inr rfl⟩
      · rw [e6FrameMoveWord_smul_e2, pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨CFSG.RankThree.E6.e6Index 4,
          (CFSG.RankThree.E6.mem_support56 _).2 (Or.inl rfl), c, Or.inr rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show e6FrameMoveElt K * (x * y) * (e6FrameMoveElt K)⁻¹ =
      (e6FrameMoveElt K * x * (e6FrameMoveElt K)⁻¹) *
        (e6FrameMoveElt K * y * (e6FrameMoveElt K)⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show e6FrameMoveElt K * x⁻¹ * (e6FrameMoveElt K)⁻¹ =
      (e6FrameMoveElt K * x * (e6FrameMoveElt K)⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem e6FrameConjWeyl_commutes_of_support {K : Type} [Field K] {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K e6Supp13) {A : Set (Fin Tag.E6.rank)}
    (hA : ∀ i ∈ A, i = CFSG.RankThree.E6.e6Index 0 ∨ i = CFSG.RankThree.E6.e6Index 2 ∨
      i = CFSG.RankThree.E6.e6Index 4 ∨ i = CFSG.RankThree.E6.e6Index 5)
    {h : ModGL Tag.E6 K} (hh : h ∈ subsystemGroup Tag.E6 K A) :
    Commute (e6FrameWeylElt K * b * (e6FrameWeylElt K)⁻¹) h := by
  unfold e6FrameWeylElt
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, d, rfl | rfl⟩ := hy
    · exact (CFSG.HardMathSupport.Lang.AnisoE6.commute_conj_support13 K hb i (hA i hi) d).1
    · exact (CFSG.HardMathSupport.Lang.AnisoE6.commute_conj_support13 K hb i (hA i hi) d).2
  | one => simp
  | mul y z _ _ hy hz => exact hy.mul_right hz
  | inv y _ hy => exact hy.inv_right

theorem e6FrameConjWeyl_commutes13 {K : Type} [Field K] {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K e6Supp13) {h : ModGL Tag.E6 K}
    (hh : h ∈ subsystemGroup Tag.E6 K e6Supp13) :
    Commute (e6FrameWeylElt K * b * (e6FrameWeylElt K)⁻¹) h :=
  e6FrameConjWeyl_commutes_of_support hb (A := e6Supp13)
    (fun i hi => by
      rcases (CFSG.RankThree.E6.mem_support13 i).1 hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)) hh

theorem e6FrameConjWeyl_commutes56 {K : Type} [Field K] {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K e6Supp13) {h : ModGL Tag.E6 K}
    (hh : h ∈ subsystemGroup Tag.E6 K e6Supp56) :
    Commute (e6FrameWeylElt K * b * (e6FrameWeylElt K)⁻¹) h :=
  e6FrameConjWeyl_commutes_of_support hb (A := e6Supp56)
    (fun i hi => by
      rcases (CFSG.RankThree.E6.mem_support56 i).1 hi with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))) hh

@[expose] def e6FrameRho0 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K :=
  (Subgroup.inclusion (CFSG.RankThree.Chevalley.subsystemGroup_le_adjointGroup_of_any
      (τ := Tag.E6) (L := K) e6Supp13)).comp
    (CFSG.RankThree.E6.a2Equiv₁ K).symm.toMonoidHom

@[expose] def e6FrameRho1 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K :=
  (e6FrameSubgroupConjHom (e6FrameMoveEltAdj K)).comp (e6FrameRho0 K)

@[expose] def e6FrameRho2 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K :=
  (e6FrameSubgroupConjHom (e6FrameWeylEltAdj K)).comp (e6FrameRho0 K)

theorem e6FrameRho1_coe (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((e6FrameRho1 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      e6FrameMoveElt K * ((e6FrameRho0 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) *
        (e6FrameMoveElt K)⁻¹ :=
  rfl

theorem e6FrameRho2_coe (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((e6FrameRho2 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      e6FrameWeylElt K * ((e6FrameRho0 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) *
        (e6FrameWeylElt K)⁻¹ :=
  rfl

theorem e6FrameRho0_mem13 (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((e6FrameRho0 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K e6Supp13 :=
  ((CFSG.RankThree.E6.a2Equiv₁ K).symm A).2

theorem e6FrameRho1_mem56 (K : Type) [Field K] [CharP K 2]
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((e6FrameRho1 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K e6Supp56 := by
  rw [e6FrameRho1_coe K A]
  exact e6FrameConjMove_mem_support56 (e6FrameRho0_mem13 K A)

theorem e6FrameRho0_injective (K : Type) [Field K] :
    Function.Injective (e6FrameRho0 K) := by
  intro A B h
  have hle : subsystemGroup Tag.E6 K e6Supp13 ≤ adjointGroup .E6 K :=
    CFSG.RankThree.Chevalley.subsystemGroup_le_adjointGroup_of_any (τ := Tag.E6) (L := K) e6Supp13
  exact (CFSG.RankThree.E6.a2Equiv₁ K).symm.injective (Subgroup.inclusion_injective hle h)

theorem e6FrameRho1_injective (K : Type) [Field K] :
    Function.Injective (e6FrameRho1 K) := by
  intro A B h
  exact e6FrameRho0_injective K
    (e6FrameSubgroupConjHom_injective (e6FrameMoveEltAdj K) h)

theorem e6FrameRho2_injective (K : Type) [Field K] :
    Function.Injective (e6FrameRho2 K) := by
  intro A B h
  exact e6FrameRho0_injective K
    (e6FrameSubgroupConjHom_injective (e6FrameWeylEltAdj K) h)

theorem e6FrameCommute01 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho0 K A) (e6FrameRho1 K B) :=
  e6FrameSubgroupCommute_of_coe (CFSG.RankThree.E6.commute_Q₁_Q₂ (e6FrameRho0_mem13 K A)
    (e6FrameRho1_mem56 K B))

theorem e6FrameCommute10 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho1 K A) (e6FrameRho0 K B) :=
  (e6FrameCommute01 K B A).symm

theorem e6FrameCommute02 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho0 K A) (e6FrameRho2 K B) := by
  apply e6FrameSubgroupCommute_of_coe
  rw [e6FrameRho2_coe K B]
  exact (e6FrameConjWeyl_commutes13 (e6FrameRho0_mem13 K B) (e6FrameRho0_mem13 K A)).symm

theorem e6FrameCommute20 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho2 K A) (e6FrameRho0 K B) :=
  (e6FrameCommute02 K B A).symm

theorem e6FrameCommute12 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho1 K A) (e6FrameRho2 K B) := by
  apply e6FrameSubgroupCommute_of_coe
  rw [e6FrameRho2_coe K B]
  exact (e6FrameConjWeyl_commutes56 (e6FrameRho0_mem13 K B) (e6FrameRho1_mem56 K A)).symm

theorem e6FrameCommute21 (K : Type) [Field K] [CharP K 2]
    (A B : Matrix.SpecialLinearGroup (Fin 3) K) :
    Commute (e6FrameRho2 K A) (e6FrameRho1 K B) :=
  (e6FrameCommute12 K B A).symm

theorem e6FrameConjWeyl_rho0 (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    e6FrameWeylEltAdj K * e6FrameRho0 K A * (e6FrameWeylEltAdj K)⁻¹ = e6FrameRho2 K A :=
  rfl

theorem e6FrameConjWeylInv_rho2 (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (e6FrameWeylEltAdj K)⁻¹ * e6FrameRho2 K A * e6FrameWeylEltAdj K = e6FrameRho0 K A := by
  apply Subtype.ext
  simp only [e6FrameRho2, MonoidHom.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    e6FrameSubgroupConjHom_coe]
  group

theorem e6FrameConjMoveInv_rho1 (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (e6FrameMoveEltAdj K)⁻¹ * e6FrameRho1 K A * e6FrameMoveEltAdj K = e6FrameRho0 K A := by
  apply Subtype.ext
  simp only [e6FrameRho1, MonoidHom.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    e6FrameSubgroupConjHom_coe]
  group

@[expose] def e6FrameRho (K : Type) [Field K] :
    Fin 3 → Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K :=
  Fin.cases (e6FrameRho0 K) (Fin.cases (e6FrameRho1 K) fun _ => e6FrameRho2 K)

@[simp] theorem e6FrameRho_zero (K : Type) [Field K] :
    e6FrameRho K 0 = e6FrameRho0 K := rfl

@[simp] theorem e6FrameRho_one (K : Type) [Field K] :
    e6FrameRho K 1 = e6FrameRho1 K := rfl

@[simp] theorem e6FrameRho_two (K : Type) [Field K] :
    e6FrameRho K 2 = e6FrameRho2 K := rfl

theorem exists_sl3_frame_E6 {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ ρ : Fin 3 → Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K,
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) ∧
      ∀ i, ∃ j, j ≠ i ∧ ∃ g : adjointGroup .E6 K, ∀ A, g * ρ i A * g⁻¹ = ρ j A := by
  refine ⟨e6FrameRho K, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [e6FrameRho_zero, e6FrameRho_one, e6FrameRho_two]
    · exact e6FrameRho0_injective K
    · exact e6FrameRho1_injective K
    · exact e6FrameRho2_injective K
  · intro i j hij A B
    fin_cases i <;> fin_cases j <;>
      simp only [e6FrameRho_zero, e6FrameRho_one, e6FrameRho_two]
    · exact absurd rfl hij
    · exact e6FrameCommute01 K A B
    · exact e6FrameCommute02 K A B
    · exact e6FrameCommute10 K A B
    · exact absurd rfl hij
    · exact e6FrameCommute12 K A B
    · exact e6FrameCommute20 K A B
    · exact e6FrameCommute21 K A B
    · exact absurd rfl hij
  · intro i
    fin_cases i <;> simp only [e6FrameRho_zero, e6FrameRho_one, e6FrameRho_two]
    · exact ⟨2, by decide, e6FrameWeylEltAdj K, fun A => e6FrameConjWeyl_rho0 K A⟩
    · exact ⟨0, by decide, (e6FrameMoveEltAdj K)⁻¹, fun A => e6FrameConjMoveInv_rho1 K A⟩
    · exact ⟨0, by decide, (e6FrameWeylEltAdj K)⁻¹, fun A => e6FrameConjWeylInv_rho2 K A⟩

end

end Main

end CFSG.StandardType

end
