module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofFusion
import CFSG.HardMathSupport.RichardWeiss.Proving.CarmichaelIso
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open CFSG.RankThree.PartOne.HNB Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.RichardWeiss.Proving

@[expose] def kMat : Fin 4 → Fin 2 → Matrix (Fin 3) (Fin 3) F25 := ![
  ![!![fe 1 0, fe 0 0, fe 0 0;
       fe 0 0, fe 4 0, fe 0 0;
       fe 0 0, fe 0 0, fe 4 0],
    !![fe 4 0, fe 0 0, fe 0 0;
       fe 0 0, fe 1 0, fe 0 0;
       fe 0 0, fe 0 0, fe 4 0]],
  ![!![fe 3 0, fe 3 3, fe 3 2;
       fe 3 2, fe 3 0, fe 3 3;
       fe 3 3, fe 3 2, fe 3 0],
    !![fe 3 0, fe 4 0, fe 4 0;
       fe 4 0, fe 3 0, fe 4 0;
       fe 4 0, fe 4 0, fe 3 0]],
  ![!![fe 3 0, fe 3 3, fe 4 0;
       fe 3 2, fe 3 0, fe 3 2;
       fe 4 0, fe 3 3, fe 3 0],
    !![fe 3 0, fe 4 0, fe 3 3;
       fe 4 0, fe 3 0, fe 3 3;
       fe 3 2, fe 3 2, fe 3 0]],
  ![!![fe 3 0, fe 4 0, fe 3 2;
       fe 4 0, fe 3 0, fe 3 2;
       fe 3 3, fe 3 3, fe 3 0],
    !![fe 3 0, fe 3 3, fe 3 3;
       fe 3 2, fe 3 0, fe 4 0;
       fe 3 2, fe 4 0, fe 3 0]]]

@[expose] def pairP : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

@[expose] def pairQ : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

@[expose] def kLet (r : Fin 6) : Fin 4 → Matrix (Fin 3) (Fin 3) F25 :=
  ![kMat (pairP r) 0, kMat (pairP r) 1, kMat (pairQ r) 0, kMat (pairQ r) 1]

@[expose] def aMat : Fin 6 → Fin 5 → Matrix (Fin 3) (Fin 3) F25 := ![
  ![!![fe 3 3, fe 2 0, fe 2 3;
       fe 4 1, fe 3 3, fe 4 0;
       fe 4 0, fe 2 3, fe 4 4],
    !![fe 4 0, fe 3 2, fe 1 1;
       fe 2 2, fe 2 0, fe 2 3;
       fe 1 4, fe 3 3, fe 4 0],
    !![fe 1 1, fe 1 0, fe 3 2;
       fe 2 2, fe 3 0, fe 2 3;
       fe 3 3, fe 1 0, fe 1 4],
    !![fe 1 1, fe 1 0, fe 3 2;
       fe 1 0, fe 1 4, fe 2 2;
       fe 3 2, fe 2 2, fe 3 0],
    !![fe 4 4, fe 1 0, fe 3 2;
       fe 3 2, fe 3 3, fe 2 0;
       fe 1 0, fe 4 1, fe 3 3]],
  ![!![fe 1 4, fe 3 2, fe 4 0;
       fe 4 0, fe 3 0, fe 3 3;
       fe 4 0, fe 4 0, fe 1 1],
    !![fe 4 0, fe 3 2, fe 1 4;
       fe 2 2, fe 2 0, fe 1 0;
       fe 1 1, fe 4 0, fe 4 0],
    !![fe 1 4, fe 4 0, fe 3 2;
       fe 4 0, fe 1 1, fe 4 0;
       fe 4 0, fe 3 3, fe 3 0],
    !![fe 4 4, fe 1 0, fe 1 0;
       fe 3 2, fe 3 3, fe 1 1;
       fe 3 2, fe 1 1, fe 3 3],
    !![fe 3 2, fe 1 1, fe 3 3;
       fe 3 0, fe 3 2, fe 3 2;
       fe 1 0, fe 2 3, fe 4 1]],
  ![!![fe 4 1, fe 2 3, fe 3 3;
       fe 3 2, fe 3 2, fe 4 4;
       fe 1 0, fe 2 0, fe 3 2],
    !![fe 0 0, fe 3 2, fe 0 0;
       fe 0 0, fe 0 0, fe 2 2;
       fe 4 0, fe 0 0, fe 0 0],
    !![fe 0 0, fe 0 0, fe 1 0;
       fe 2 2, fe 0 0, fe 0 0;
       fe 0 0, fe 2 3, fe 0 0],
    !![fe 4 4, fe 1 0, fe 3 3;
       fe 3 2, fe 3 3, fe 4 1;
       fe 2 2, fe 2 0, fe 3 3],
    !![fe 2 0, fe 2 2, fe 3 3;
       fe 3 2, fe 4 0, fe 2 0;
       fe 2 3, fe 2 0, fe 4 0]],
  ![!![fe 1 4, fe 4 1, fe 4 2;
       fe 0 4, fe 0 4, fe 0 0;
       fe 4 1, fe 1 4, fe 4 2],
    !![fe 1 4, fe 1 3, fe 4 1;
       fe 4 4, fe 0 4, fe 1 1;
       fe 4 2, fe 0 0, fe 4 2],
    !![fe 0 1, fe 0 0, fe 0 1;
       fe 3 0, fe 4 3, fe 2 0;
       fe 4 4, fe 0 4, fe 1 1],
    !![fe 0 4, fe 0 3, fe 3 2;
       fe 3 1, fe 0 2, fe 3 1;
       fe 3 2, fe 0 3, fe 0 4],
    !![fe 0 1, fe 1 1, fe 4 4;
       fe 0 0, fe 4 3, fe 4 3;
       fe 0 1, fe 4 4, fe 1 1]],
  ![!![fe 4 2, fe 0 2, fe 4 0;
       fe 0 2, fe 2 1, fe 3 4;
       fe 3 3, fe 2 4, fe 4 2],
    !![fe 1 3, fe 0 0, fe 4 3;
       fe 1 4, fe 1 2, fe 2 0;
       fe 4 1, fe 1 2, fe 3 0],
    !![fe 1 4, fe 4 4, fe 1 3;
       fe 1 2, fe 4 2, fe 0 0;
       fe 4 4, fe 3 0, fe 0 4],
    !![fe 0 4, fe 1 1, fe 2 0;
       fe 0 0, fe 4 2, fe 0 1;
       fe 4 3, fe 2 0, fe 1 4],
    !![fe 1 4, fe 1 2, fe 2 0;
       fe 4 4, fe 4 2, fe 1 4;
       fe 4 3, fe 0 0, fe 0 4]],
  ![!![fe 3 1, fe 3 4, fe 3 4;
       fe 3 4, fe 1 2, fe 4 0;
       fe 3 4, fe 4 0, fe 1 2],
    !![fe 0 1, fe 3 2, fe 3 4;
       fe 4 0, fe 0 1, fe 0 2;
       fe 0 2, fe 3 4, fe 0 3],
    !![fe 4 2, fe 2 4, fe 4 0;
       fe 3 4, fe 2 1, fe 2 4;
       fe 3 3, fe 3 4, fe 4 2],
    !![fe 3 2, fe 1 4, fe 3 3;
       fe 3 3, fe 3 3, fe 3 0;
       fe 1 1, fe 3 3, fe 4 0],
    !![fe 4 0, fe 3 2, fe 3 0;
       fe 1 4, fe 3 3, fe 3 2;
       fe 3 2, fe 1 1, fe 3 2]]]

@[expose] def aWord : Fin 6 → Fin 5 → List (Fin 4) := ![
  ![[0, 3, 2, 1, 0, 3, 2, 1],
    [3, 2, 1, 3, 2, 1],
    [3, 2, 1, 2, 1, 3],
    [3, 2, 1, 3, 1, 2],
    [1, 0, 3, 2, 0, 3, 2, 1]],
  ![[0, 3, 0, 2, 0, 3, 2, 0],
    [3, 2, 1, 3, 2, 1],
    [0, 2, 0, 3, 0, 3, 2, 0],
    [3, 2, 0, 3, 2, 0],
    [3, 2, 1, 0, 3, 2, 1, 0]],
  ![[1, 0, 2, 0, 2, 1],
    [2, 1, 0, 2, 0, 2, 1, 2],
    [2, 0, 2, 1, 0, 2, 1, 2, 0],
    [1, 0, 3, 2, 0, 3, 2, 1],
    [1, 0, 3, 0, 3, 1]],
  ![[3, 1, 3, 2, 1, 2],
    [1, 2, 1, 0, 2, 0],
    [1, 2, 0, 2, 1, 0],
    [1, 2, 1, 2],
    [3, 2, 1, 3, 1, 2]],
  ![[1, 0, 3, 1, 0, 3],
    [1, 0, 3, 0, 3, 1],
    [0, 3, 2, 1, 2, 1, 3, 0],
    [0, 2, 1, 3, 2, 1, 3, 0],
    [1, 0, 3, 1, 3, 0]],
  ![[3, 1, 0, 3, 1, 0],
    [3, 0, 3, 0],
    [3, 1, 3, 1],
    [0, 2, 0, 3, 2, 0, 3, 0],
    [0, 3, 2, 0, 2, 0, 3, 0]]]

@[expose] def aScal : Fin 6 → Fin 5 → F25 := ![
  ![fe 2 2, fe 1 0, fe 1 0, fe 2 3, fe 2 2],
  ![fe 2 3, fe 1 0, fe 2 3, fe 2 2, fe 2 3],
  ![fe 2 3, fe 2 3, fe 2 2, fe 2 2, fe 1 0],
  ![fe 2 3, fe 2 3, fe 2 2, fe 2 2, fe 2 2],
  ![fe 1 0, fe 1 0, fe 2 2, fe 1 0, fe 2 3],
  ![fe 2 2, fe 2 3, fe 1 0, fe 2 2, fe 1 0]]

@[expose] def kWord : Fin 6 → Fin 4 → List (Fin 5) := ![
  ![[4, 4, 0, 1, 1, 0],
    [1, 1, 0, 4, 4, 0],
    [1, 1, 3, 2, 1],
    [1, 1, 2, 3, 1]],
  ![[1, 1, 4, 3, 1],
    [3, 3, 4, 1, 3],
    [2, 0],
    [0, 2]],
  ![[1, 2, 2, 1],
    [1, 2],
    [3, 0, 4, 1, 3, 0],
    [1, 0, 4, 3, 1, 0]],
  ![[1, 1, 3, 2, 1],
    [1, 1, 2, 3, 1],
    [3, 3, 0, 4, 4, 0],
    [4, 4, 0, 3, 3, 0]],
  ![[0, 0, 4, 1, 0],
    [0, 0, 1, 4, 0],
    [2, 2, 0, 3, 3, 0],
    [2, 3, 3, 2, 0]],
  ![[0, 0, 2, 1, 0],
    [0, 0, 1, 2, 0],
    [3, 4],
    [3, 4, 4, 3]]]

@[expose] def kScal : Fin 6 → Fin 4 → F25 := ![
  ![fe 2 3, fe 2 3, fe 2 2, fe 2 2],
  ![fe 1 0, fe 2 2, fe 2 3, fe 2 3],
  ![fe 1 0, fe 1 0, fe 2 3, fe 1 0],
  ![fe 2 2, fe 2 2, fe 2 2, fe 2 2],
  ![fe 2 2, fe 2 2, fe 2 2, fe 2 2],
  ![fe 2 2, fe 2 2, fe 2 3, fe 2 2]]

@[expose] def sqScal : Fin 6 → Fin 5 → Fin 5 → F25 := ![
  ![![fe 1 0, fe 2 3, fe 1 0, fe 2 3, fe 2 2],
    ![fe 2 3, fe 1 0, fe 1 0, fe 2 2, fe 2 3],
    ![fe 1 0, fe 1 0, fe 1 0, fe 2 2, fe 2 2],
    ![fe 2 3, fe 2 2, fe 2 2, fe 1 0, fe 2 2],
    ![fe 2 2, fe 2 3, fe 2 2, fe 2 2, fe 1 0]],
  ![![fe 1 0, fe 1 0, fe 2 3, fe 1 0, fe 1 0],
    ![fe 1 0, fe 1 0, fe 2 3, fe 2 3, fe 2 2],
    ![fe 2 3, fe 2 3, fe 1 0, fe 1 0, fe 2 2],
    ![fe 1 0, fe 2 3, fe 1 0, fe 1 0, fe 1 0],
    ![fe 1 0, fe 2 2, fe 2 2, fe 1 0, fe 1 0]],
  ![![fe 1 0, fe 2 3, fe 1 0, fe 1 0, fe 2 2],
    ![fe 2 3, fe 1 0, fe 1 0, fe 2 3, fe 2 3],
    ![fe 1 0, fe 1 0, fe 1 0, fe 2 3, fe 2 2],
    ![fe 1 0, fe 2 3, fe 2 3, fe 1 0, fe 2 3],
    ![fe 2 2, fe 2 3, fe 2 2, fe 2 3, fe 1 0]],
  ![![fe 1 0, fe 2 2, fe 2 2, fe 1 0, fe 1 0],
    ![fe 2 2, fe 1 0, fe 1 0, fe 1 0, fe 2 2],
    ![fe 2 2, fe 1 0, fe 1 0, fe 2 2, fe 1 0],
    ![fe 1 0, fe 1 0, fe 2 2, fe 1 0, fe 2 2],
    ![fe 1 0, fe 2 2, fe 1 0, fe 2 2, fe 1 0]],
  ![![fe 1 0, fe 1 0, fe 2 2, fe 2 2, fe 2 2],
    ![fe 1 0, fe 1 0, fe 1 0, fe 2 3, fe 2 2],
    ![fe 2 2, fe 1 0, fe 1 0, fe 2 3, fe 1 0],
    ![fe 2 2, fe 2 3, fe 2 3, fe 1 0, fe 2 2],
    ![fe 2 2, fe 2 2, fe 1 0, fe 2 2, fe 1 0]],
  ![![fe 1 0, fe 1 0, fe 2 3, fe 2 3, fe 2 2],
    ![fe 1 0, fe 1 0, fe 2 2, fe 1 0, fe 2 2],
    ![fe 2 3, fe 2 2, fe 1 0, fe 2 2, fe 2 2],
    ![fe 2 3, fe 1 0, fe 2 2, fe 1 0, fe 2 3],
    ![fe 2 2, fe 2 2, fe 2 2, fe 2 3, fe 1 0]]]

@[expose] def repA : Fin 4 → Fin 3 := ![1, 0, 1, 1]

@[expose] def repB : Fin 4 → Fin 3 := ![0, 1, 1, 2]

theorem kMat_facts : ∀ p i, det3 (kMat p i) = 1 ∧
    ((kMat p i).map (· ^ (5 ^ 1)))ᵀ * kMat p i = 1 := by
  decide +kernel

theorem aMat_facts : ∀ r i, det3 (aMat r i) = 1 ∧
    ((aMat r i).map (· ^ (5 ^ 1)))ᵀ * aMat r i = 1 ∧ aMat r i ^ 3 = 1 := by
  decide +kernel

theorem aMat_sq : ∀ r i j, i ≠ j → (aMat r i * aMat r j) ^ 2 = sqScal r i j • 1 := by
  decide +kernel

theorem aMat_ne_smul : ∀ r (c : F25), aMat r 0 ≠ c • 1 := by
  decide +kernel

theorem aMat_word : ∀ r i, aMat r i = aScal r i • ((aWord r i).map (kLet r)).prod := by
  decide +kernel

theorem kLet_word : ∀ r j, kLet r j = kScal r j • ((kWord r j).map (aMat r)).prod := by
  decide +kernel

theorem kMat_mul_uMat : ∀ p i,
    kMat p i * uMat (repA p) (repB p) = uMat (repA p) (repB p) * kMat 0 i := by
  decide +kernel

@[expose] noncomputable def kSU (p : Fin 4) (i : Fin 2) : SU5 :=
  mkSU (kMat p i) (by rw [det_eq_det3]; exact (kMat_facts p i).1) (kMat_facts p i).2

noncomputable abbrev kPU (p : Fin 4) (i : Fin 2) : PU5 := (kSU p i : PU5)

@[expose] noncomputable def kY (p : Fin 4) : Subgroup PU5 :=
  Subgroup.closure {kPU p 0, kPU p 1}

@[expose] noncomputable def aSU (r : Fin 6) (i : Fin 5) : SU5 :=
  mkSU (aMat r i) (by rw [det_eq_det3]; exact (aMat_facts r i).1) (aMat_facts r i).2.1

noncomputable abbrev aPU (r : Fin 6) (i : Fin 5) : PU5 := (aSU r i : PU5)

theorem repA_repB_ne (p : Fin 4) : (repA p, repB p) ≠ (0, 0) := by
  revert p
  decide +kernel

private noncomputable def matHom : SU5 →* Matrix (Fin 3) (Fin 3) F25 :=
  (Units.coeHom (M := Matrix (Fin 3) (Fin 3) F25)).comp SU5.subtype

private theorem matHom_eq_coe (g : SU5) :
    matHom g = ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := rfl

private theorem matHom_aSU (r : Fin 6) (i : Fin 5) : matHom (aSU r i) = aMat r i := by
  simp only [matHom_eq_coe, aSU, coe_mkSU]

theorem aPU_pow_three (r : Fin 6) (i : Fin 5) : aPU r i ^ 3 = 1 := by
  have h1 : aSU r i ^ 3 = 1 := by
    apply SU5_ext
    rw [← matHom_eq_coe, ← matHom_eq_coe, map_pow, matHom_aSU]
    rw [show matHom (1 : SU5) = 1 from rfl]
    exact (aMat_facts r i).2.2
  have h2 : aPU r i ^ 3 = ((1 : SU5) : PU5) := by
    rw [← QuotientGroup.mk_pow, h1]
  rw [h2, QuotientGroup.mk_one]

theorem aPU_mul_pow_two (r : Fin 6) {i j : Fin 5} (hij : i ≠ j) :
    (aPU r i * aPU r j) ^ 2 = 1 := by
  have h1 : (((aSU r i * aSU r j) ^ 2 : SU5) : PU5) = ((1 : SU5) : PU5) := by
    refine mk_eq_mk_of_smul (g := (aSU r i * aSU r j) ^ 2) (k := 1)
      (c := sqScal r i j) ?_
    rw [← matHom_eq_coe, ← matHom_eq_coe, map_pow, map_mul, matHom_aSU, matHom_aSU]
    rw [show matHom (1 : SU5) = 1 from rfl]
    exact aMat_sq r i j hij
  have h2 : (aPU r i * aPU r j) ^ 2 = ((1 : SU5) : PU5) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, h1]
  rw [h2, QuotientGroup.mk_one]

theorem aPU_ne_one (r : Fin 6) : aPU r 0 ≠ 1 := by
  refine mk_ne_one_of (g := aSU r 0) fun c => ?_
  rw [← matHom_eq_coe, matHom_aSU]
  exact aMat_ne_smul r c

private theorem kSU_eq_conj (p : Fin 4) (i : Fin 2) :
    kSU p i = uSU (repA p) (repB p) (repA_repB_ne p) * kSU 0 i *
      (uSU (repA p) (repB p) (repA_repB_ne p))⁻¹ := by
  have h : kSU p i * uSU (repA p) (repB p) (repA_repB_ne p) =
      uSU (repA p) (repB p) (repA_repB_ne p) * kSU 0 i := by
    apply SU5_ext
    simp only [coe_mul, kSU, uSU, coe_mkSU]
    exact kMat_mul_uMat p i
  rw [← h]
  group

theorem kPU_eq_conj (p : Fin 4) (i : Fin 2) :
    kPU p i = uPU (repA p) (repB p) (repA_repB_ne p) * kPU 0 i *
      (uPU (repA p) (repB p) (repA_repB_ne p))⁻¹ := by
  have h := congrArg (fun g : SU5 => (g : PU5)) (kSU_eq_conj p i)
  simpa only [kPU, uPU, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h

theorem kY_eq_map (p : Fin 4) :
    kY p = (kY 0).map (MulAut.conj (uPU (repA p) (repB p) (repA_repB_ne p))).toMonoidHom := by
  have h : ∀ i : Fin 2,
      (MulAut.conj (uPU (repA p) (repB p) (repA_repB_ne p))).toMonoidHom (kPU 0 i) =
        kPU p i := fun i => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, kPU_eq_conj p i]
  simp only [kY, MonoidHom.map_closure, Set.image_pair, h 0, h 1]

private noncomputable def kLetSU (r : Fin 6) : Fin 4 → SU5 :=
  ![kSU (pairP r) 0, kSU (pairP r) 1, kSU (pairQ r) 0, kSU (pairQ r) 1]

private theorem matHom_kLetSU (r : Fin 6) (j : Fin 4) : matHom (kLetSU r j) = kLet r j := by
  fin_cases j <;> rfl

private theorem coe_prod_mem {T : Subgroup PU5} (l : List SU5)
    (h : ∀ x ∈ l, (x : PU5) ∈ T) : ((l.prod : SU5) : PU5) ∈ T := by
  induction l with
  | nil => simpa using T.one_mem
  | cons a l ih =>
    rw [List.prod_cons, QuotientGroup.mk_mul]
    exact T.mul_mem (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private theorem aPU_eq_word (r : Fin 6) (i : Fin 5) :
    aPU r i = ((((aWord r i).map (kLetSU r)).prod : SU5) : PU5) := by
  have hword : matHom (((aWord r i).map (kLetSU r)).prod) =
      ((aWord r i).map (kLet r)).prod := by
    rw [MonoidHom.map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun j _ => matHom_kLetSU r j)
  refine mk_eq_mk_of_smul (g := aSU r i) (k := ((aWord r i).map (kLetSU r)).prod)
    (c := aScal r i) ?_
  rw [← matHom_eq_coe, ← matHom_eq_coe, matHom_aSU, hword, ← aMat_word r i]

private theorem mem_kY (p : Fin 4) (i : Fin 2) : kPU p i ∈ kY p := by
  simp only [kY]
  exact Subgroup.subset_closure (by fin_cases i <;> simp)

private theorem kLetSU_mem (r : Fin 6) (j : Fin 4) :
    ((kLetSU r j : SU5) : PU5) ∈ kY (pairP r) ⊔ kY (pairQ r) := by
  fin_cases j
  · exact Subgroup.mem_sup_left (mem_kY (pairP r) 0)
  · exact Subgroup.mem_sup_left (mem_kY (pairP r) 1)
  · exact Subgroup.mem_sup_right (mem_kY (pairQ r) 0)
  · exact Subgroup.mem_sup_right (mem_kY (pairQ r) 1)

theorem aPU_mem (r : Fin 6) (i : Fin 5) : aPU r i ∈ kY (pairP r) ⊔ kY (pairQ r) := by
  rw [aPU_eq_word]
  refine coe_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact kLetSU_mem r j

private theorem kLetSU_mem_closure (r : Fin 6) (j : Fin 4) :
    ((kLetSU r j : SU5) : PU5) ∈ Subgroup.closure (Set.range (aPU r)) := by
  have hword : matHom (((kWord r j).map (aSU r)).prod) =
      ((kWord r j).map (aMat r)).prod := by
    rw [MonoidHom.map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => matHom_aSU r i)
  have h : matHom (kLetSU r j) =
      kScal r j • matHom (((kWord r j).map (aSU r)).prod) := by
    rw [matHom_kLetSU, hword, kLet_word]
  have heq : ((kLetSU r j : SU5) : PU5) =
      ((((kWord r j).map (aSU r)).prod : SU5) : PU5) :=
    mk_eq_mk_of_smul (g := kLetSU r j) (k := ((kWord r j).map (aSU r)).prod)
      (c := kScal r j) (by
        rw [← matHom_eq_coe, ← matHom_eq_coe]
        exact h)
  rw [heq]
  refine coe_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self i)

theorem closure_range_aPU (r : Fin 6) :
    Subgroup.closure (Set.range (aPU r)) = kY (pairP r) ⊔ kY (pairQ r) := by
  refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) (sup_le ?_ ?_)
  · rintro _ ⟨i, rfl⟩
    exact aPU_mem r i
  · simp only [kY]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl)
    · exact kLetSU_mem_closure r 0
    · exact kLetSU_mem_closure r 1
  · simp only [kY]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl)
    · exact kLetSU_mem_closure r 2
    · exact kLetSU_mem_closure r 3

theorem nonempty_mulEquiv_pair (r : Fin 6) :
    Nonempty (↥(kY (pairP r) ⊔ kY (pairQ r)) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_altThreeCycle_eq 5 (aPU r) (aPU_pow_three r)
    fun i j hij => aPU_mul_pow_two r hij
  have hcomp : ψ ∘ altThreeCycle = aPU r := funext hψ
  have hrange : ψ.range = Subgroup.closure (Set.range (aPU r)) := by
    rw [MonoidHom.range_eq_map, ← closure_altThreeCycle (n := 5), MonoidHom.map_closure,
      ← Set.range_comp, hcomp]
  have hT : ψ.range = kY (pairP r) ⊔ kY (pairQ r) := hrange.trans (closure_range_aPU r)
  have hnt : Nontrivial ↥ψ.range := by
    refine ⟨⟨aPU r 0, MonoidHom.mem_range.mpr ⟨altThreeCycle 0, hψ 0⟩⟩, 1, fun h => ?_⟩
    exact aPU_ne_one r (by simpa using congrArg Subtype.val h)
  have hsurj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hinj : Function.Injective ψ.rangeRestrict :=
    injective_of_surjective_alt (α := Fin 7) (by rw [Nat.card_fin]; norm_num)
      ψ.rangeRestrict hsurj
  exact ⟨(MulEquiv.subgroupCongr hT).symm.trans
    (MulEquiv.ofBijective ψ.rangeRestrict ⟨hinj, hsurj⟩).symm⟩

private theorem exists_pair_eq_or {p q : Fin 4} (hpq : p ≠ q) :
    (∃ r : Fin 6, pairP r = p ∧ pairQ r = q) ∨
      (∃ r : Fin 6, pairP r = q ∧ pairQ r = p) := by
  revert p q
  decide +kernel

theorem nonempty_mulEquiv_kY_sup {p q : Fin 4} (hpq : p ≠ q) :
    Nonempty (↥(kY p ⊔ kY q) ≃* alternatingGroup (Fin 7)) := by
  rcases exists_pair_eq_or hpq with ⟨r, hp, hq⟩ | ⟨r, hp, hq⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_pair r
    exact ⟨(MulEquiv.subgroupCongr (by rw [hp, hq])).symm.trans e⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_pair r
    exact ⟨(MulEquiv.subgroupCongr (by rw [hp, hq, sup_comm])).symm.trans e⟩

theorem not_isPGroup_kY_sup {p q : Fin 4} (hpq : p ≠ q) : ¬ IsPGroup 2 ↥(kY p ⊔ kY q) := by
  intro h
  obtain ⟨e⟩ := nonempty_mulEquiv_kY_sup hpq
  have hcard : Nat.card ↥(kY p ⊔ kY q) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  rw [hcard] at hn
  have h5 : (5 : ℕ) ∣ 2 ^ n := dvd_trans (by norm_num : (5 : ℕ) ∣ 2520) hn
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)

end CFSG.RankThree.PartTwo.Sec16.Res3U35
