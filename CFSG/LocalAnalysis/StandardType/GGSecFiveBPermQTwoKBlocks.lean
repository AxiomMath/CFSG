module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoFrameDefs
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType

namespace QTwoBlocks

open Polynomial Matrix CoordSL SLNS CFSG.RankThree.CALinearPlane
open scoped commutatorElement

section Entries

variable {F : Type} [Field F] {m e s d : ℕ} (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d)

@[expose] def NsTriv (k : Fin s → ℕ) (x : (Fin e × Fin s) ⊕ Fin d) : Prop :=
  ∀ a i, x = Sum.inl (a, i) → k i = 0

omit [Field F] in
theorem nsTriv_of_mem_fixS {S : Finset (Fin s)} {k : Fin s → ℕ} (hk : ∀ i ∈ S, k i = 0)
    {p : Fin m} (hp : p ∈ fixS ε Sᶜ) : NsTriv k (ε p) := by
  intro a i hai
  rw [mem_fixS, hai] at hp
  simp only [inT, Sum.elim_inl, Finset.mem_compl, not_not] at hp
  exact hk i hp

omit [Field F] in
theorem nsTriv_of_not_mem_fixS {S : Finset (Fin s)} {k : Fin s → ℕ} (hk : ∀ i, i ∉ S → k i = 0)
    {p : Fin m} (hp : p ∉ fixS ε Sᶜ) : NsTriv k (ε p) := by
  intro a i hai
  rw [mem_fixS, hai, not_not] at hp
  simp only [inT, Sum.elim_inl, Finset.mem_compl] at hp
  exact hk i hp

omit [Field F] in
theorem exists_inl_of_not_mem_fixS {S : Finset (Fin s)} {p : Fin m} (hp : p ∉ fixS ε Sᶜ) :
    ∃ a i, ε p = Sum.inl (a, i) ∧ i ∉ S := by
  rw [mem_fixS, not_not] at hp
  rcases hε : ε p with ⟨a, i⟩ | j
  · rw [hε] at hp
    simp only [inT, Sum.elim_inl, Finset.mem_compl] at hp
    exact ⟨a, i, rfl, hp⟩
  · rw [hε] at hp
    simp [inT] at hp

theorem nsCore_apply_of_triv {C : Matrix (Fin e) (Fin e) F} {k : Fin s → ℕ}
    {x : (Fin e × Fin s) ⊕ Fin d} (hx : NsTriv k x) (y : (Fin e × Fin s) ⊕ Fin d) :
    nsCore C k x y = (1 : Matrix _ _ F) x y ∧ nsCore C k y x = (1 : Matrix _ _ F) y x := by
  classical
  rcases x with ⟨a, i⟩ | j <;> rcases y with ⟨b, i'⟩ | j'
  · by_cases hii : i = i'
    · subst hii
      rw [nsCore, fromBlocks_apply₁₁, fromBlocks_apply₁₁, blockDiagonal_apply_eq,
        blockDiagonal_apply_eq, hx a i rfl, pow_zero, one_apply, one_apply, one_apply, one_apply]
      constructor
      · by_cases hab : a = b
        · subst hab
          simp
        · rw [if_neg hab, if_neg (fun h => hab (by simpa using h))]
      · by_cases hab : b = a
        · subst hab
          simp
        · rw [if_neg hab, if_neg (fun h => hab (by simpa using h))]
    · rw [nsCore, fromBlocks_apply₁₁, fromBlocks_apply₁₁, blockDiagonal_apply_ne _ _ _ hii,
        blockDiagonal_apply_ne _ _ _ (Ne.symm hii), one_apply, one_apply,
        if_neg (fun h => hii (by simp at h; exact h.2)),
        if_neg (fun h => hii (by simp at h; exact h.2.symm))]
      exact ⟨rfl, rfl⟩
  · simp [nsCore]
  · simp [nsCore]
  · rw [nsCore, fromBlocks_apply₂₂, fromBlocks_apply₂₂, one_apply, one_apply, one_apply, one_apply]
    constructor
    · by_cases hjj : j = j'
      · subst hjj
        simp
      · rw [if_neg hjj, if_neg (fun h => hjj (by simpa using h))]
    · by_cases hjj : j' = j
      · subst hjj
        simp
      · rw [if_neg hjj, if_neg (fun h => hjj (by simpa using h))]

theorem nsMat_apply_of_left {C : Matrix (Fin e) (Fin e) F} {k : Fin s → ℕ} {p : Fin m}
    (hp : NsTriv k (ε p)) (q : Fin m) :
    nsMat ε C k p q = (1 : Matrix (Fin m) (Fin m) F) p q := by
  classical
  rw [nsMat, submatrix_apply, (nsCore_apply_of_triv hp (ε q)).1, one_apply, one_apply]
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [if_neg (fun h => hpq (ε.injective h)), if_neg hpq]

theorem nsMat_apply_of_right {C : Matrix (Fin e) (Fin e) F} {k : Fin s → ℕ} {q : Fin m}
    (hq : NsTriv k (ε q)) (p : Fin m) :
    nsMat ε C k p q = (1 : Matrix (Fin m) (Fin m) F) p q := by
  classical
  rw [nsMat, submatrix_apply, (nsCore_apply_of_triv hq (ε p)).2, one_apply, one_apply]
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [if_neg (fun h => hpq (ε.injective h)), if_neg hpq]

theorem commute_of_standard {J : Finset (Fin m)} {A X : Matrix (Fin m) (Fin m) F}
    (hA : ∀ p q, (p ∈ J ∨ q ∈ J) → A p q = (1 : Matrix (Fin m) (Fin m) F) p q)
    (hX : ∀ p q, (p ∉ J ∨ q ∉ J) → X p q = (1 : Matrix (Fin m) (Fin m) F) p q) :
    A * X = X * A := by
  classical
  ext p q
  by_cases hp : p ∈ J
  · have h1 : (A * X) p q = ((1 : Matrix (Fin m) (Fin m) F) * X) p q := by
      simp only [mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [hA p l (Or.inl hp)]
    rw [h1, Matrix.one_mul]
    by_cases hq : q ∈ J
    · have h2 : (X * A) p q = (X * (1 : Matrix (Fin m) (Fin m) F)) p q := by
        simp only [mul_apply]
        exact Finset.sum_congr rfl fun l _ => by rw [hA l q (Or.inr hq)]
      rw [h2, Matrix.mul_one]
    · have h2 : (X * A) p q = 0 := by
        simp only [mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l ∈ J
        · rw [hA l q (Or.inl hl), one_apply, if_neg (fun h : l = q => hq (h ▸ hl)), mul_zero]
        · rw [hX p l (Or.inr hl), one_apply, if_neg (fun h : p = l => hl (h ▸ hp)), zero_mul]
      rw [h2, hX p q (Or.inr hq), one_apply, if_neg (fun h : p = q => hq (h ▸ hp))]
  · have h1 : (A * X) p q = (A * (1 : Matrix (Fin m) (Fin m) F)) p q := by
      simp only [mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ∈ J
      · rw [hA p l (Or.inr hl), one_apply, if_neg (fun h : p = l => hp (h ▸ hl)), zero_mul,
          zero_mul]
      · rw [hX l q (Or.inl hl)]
    have h2 : (X * A) p q = ((1 : Matrix (Fin m) (Fin m) F) * A) p q := by
      simp only [mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [hX p l (Or.inl hp)]
    rw [h1, h2, Matrix.mul_one, Matrix.one_mul]

variable {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)

theorem nsSL_mem_coordBlockSL {S : Finset (Fin s)} {k : Fin s → ℕ} (hk : ∀ i, i ∉ S → k i = 0) :
    nsSL ε hC k ∈ coordBlockSL F (fixS ε Sᶜ) := by
  rw [mem_coordBlockSL_iff]
  intro p q hpq
  rw [← one_apply]
  rcases hpq with hp | hq
  · exact nsMat_apply_of_left ε (nsTriv_of_not_mem_fixS ε hk hp) q
  · exact nsMat_apply_of_right ε (nsTriv_of_not_mem_fixS ε hk hq) p

theorem nsSL_commute_of_mem_coordBlockSL {S : Finset (Fin s)} {k : Fin s → ℕ}
    (hk : ∀ i ∈ S, k i = 0) {x : SpecialLinearGroup (Fin m) F}
    (hx : x ∈ coordBlockSL F (fixS ε Sᶜ)) : nsSL ε hC k * x = x * nsSL ε hC k := by
  rw [mem_coordBlockSL_iff] at hx
  apply Subtype.ext
  show nsMat ε C k * (x : Matrix (Fin m) (Fin m) F) = (x : Matrix (Fin m) (Fin m) F) * nsMat ε C k
  refine commute_of_standard (J := fixS ε Sᶜ) ?_ ?_
  · intro p q hpq
    rcases hpq with hp | hq
    · exact nsMat_apply_of_left ε (nsTriv_of_mem_fixS ε hk hp) q
    · exact nsMat_apply_of_right ε (nsTriv_of_mem_fixS ε hk hq) p
  · intro p q hpq
    rw [hx p q hpq, one_apply]

end Entries

section Commutator

variable {F : Type} [Field F] [Finite F] {g : F[X]} [Fact (Irreducible g)] {m s d : ℕ}
  (ε : Fin m ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin d) (hC : (rootMat g).det = 1)

omit [Finite F] in
private theorem aligned_single {hζ : AdjoinRoot.root g ^ 3 = 1} (k : Fin s) :
    Aligned hζ (Pi.single k (1 : ZMod 3)) := by
  intro i j hj u _ hij
  have hjk : j = k := by
    by_contra h
    exact hj (Pi.single_eq_of_ne h 1)
  subst hjk
  by_cases hik : i = j
  · rw [hik]
  · exfalso
    rw [Pi.single_eq_of_ne hik, Pi.single_eq_same, mul_one] at hij
    exact u.ne_zero hij.symm

omit [Field F] [Finite F] [Fact (Irreducible g)] in
private theorem kT_singleton_eq (k : Fin s) :
    kT {k} = fun i => ((Pi.single k (1 : ZMod 3) : Fin s → ZMod 3) i).val := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp only [kT, Finset.mem_singleton, if_true, Pi.single_eq_same]
    rfl
  · simp [kT, hik]

theorem frameForm_block_of_comm (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    {u : SpecialLinearGroup (Fin m) F} {k : Fin s}
    (hu : Commute (nsSL ε hC (kT {k})) u) :
    (∀ z : AdjoinRoot g, frameForm g ε (u : Matrix (Fin m) (Fin m) F) (Pi.single k z, 0) =
      (Pi.single k (z * (frameForm g ε (u : Matrix (Fin m) (Fin m) F) (Pi.single k 1, 0)).1 k),
        0)) ∧
    (∀ x : (Fin s → AdjoinRoot g) × (Fin d → F), x.1 k = 0 →
      (frameForm g ε (u : Matrix (Fin m) (Fin m) F) x).1 k = 0) := by
  set β : Fin s → ZMod 3 := Pi.single k 1 with hβdef
  have hβ : kT {k} = fun i => (β i).val := kT_singleton_eq k
  have hζ : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  have hu' : u * nsSL ε hC (fun i => (β i).val) = nsSL ε hC (fun i => (β i).val) * u := by
    rw [← hβ]
    exact hu.eq.symm
  obtain ⟨hφ, -, -⟩ := frameForm_comm_of_mem hu'
  have hβk : β k ≠ 0 := by
    rw [hβdef, Pi.single_eq_same]
    exact one_ne_zero
  refine ⟨fun z => ?_, fun x hx => ?_⟩
  · rw [apply_single_of_comm hprim (hζ := hζ) (aligned_single k) hφ hβk z]
    refine Prod.ext (funext fun i => ?_) rfl
    by_cases hik : i = k
    · subst hik
      simp
    · simp [Pi.single_eq_of_ne hik]
  · have hfix : torusAct g (fun i => (β i).val) x = x := by
      refine (torusAct_eq_self_iff hprim).mpr fun i hi => ?_
      have hik : i = k := by
        by_contra h
        exact hi (by rw [hβdef, Pi.single_eq_of_ne h])
      rw [hik]
      exact hx
    have h2 := hφ x
    rw [hfix] at h2
    exact (torusAct_eq_self_iff hprim).mp h2.symm k hβk

theorem commutator_mem_coordBlockSL (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    {S : Finset (Fin s)} {x y : SpecialLinearGroup (Fin m) F}
    (hx : ∀ k, k ∉ S → Commute (nsSL ε hC (kT {k})) x)
    (hy : ∀ k, k ∉ S → Commute (nsSL ε hC (kT {k})) y) :
    ⁅x, y⁆ ∈ coordBlockSL F (fixS ε Sᶜ) := by
  classical
  set φ : SpecialLinearGroup (Fin m) F →
      (((Fin s → AdjoinRoot g) × (Fin d → F)) →ₗ[F] ((Fin s → AdjoinRoot g) × (Fin d → F))) :=
    fun u => frameForm g ε (u : Matrix (Fin m) (Fin m) F) with hφdef
  have hφmul : ∀ u v, φ (u * v) = φ u ∘ₗ φ v := fun u v => by
    show frameForm g ε ((u * v : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, frameForm_mul]
  have hφone : φ 1 = LinearMap.id := by
    show frameForm g ε ((1 : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) = _
    rw [Matrix.SpecialLinearGroup.coe_one, frameForm_one]
  have hcomm : ∀ u ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)),
      ∀ k, k ∉ S → Commute (nsSL ε hC (kT {k})) u := by
    intro u hu k hk
    rcases hu with rfl | rfl | rfl | rfl
    · exact hx k hk
    · exact hy k hk
    · exact (hx k hk).inv_right
    · exact (hy k hk).inv_right
  set lam : SpecialLinearGroup (Fin m) F → Fin s → AdjoinRoot g :=
    fun u k => (φ u (Pi.single k 1, 0)).1 k with hlam
  have hblk : ∀ u ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)), ∀ k, k ∉ S →
      ∀ z, φ u (Pi.single k z, 0) = (Pi.single k (z * lam u k), 0) :=
    fun u hu k hk z => (frameForm_block_of_comm ε hC hprim (hcomm u hu k hk)).1 z
  have hpres : ∀ u ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)), ∀ k, k ∉ S →
      ∀ v : (Fin s → AdjoinRoot g) × (Fin d → F), v.1 k = 0 → (φ u v).1 k = 0 :=
    fun u hu k hk v hv => (frameForm_block_of_comm ε hC hprim (hcomm u hu k hk)).2 v hv
  have hinv : ∀ u, u ∈ ({x, y} : Set (SpecialLinearGroup (Fin m) F)) → ∀ k, k ∉ S →
      lam u⁻¹ k * lam u k = 1 := by
    intro u hu k hk
    have hu4 : u ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) := by
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hu4' : u⁻¹ ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) := by
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    have h1 := congrArg (fun ψ => ψ (Pi.single k 1, 0)) (hφmul u u⁻¹)
    simp only [mul_inv_cancel, hφone, LinearMap.id_apply, LinearMap.comp_apply] at h1
    rw [hblk u⁻¹ hu4' k hk 1, hblk u hu4 k hk, one_mul] at h1
    have h2 := congrFun (congrArg Prod.fst h1) k
    simpa using h2.symm
  have hx4 : x ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) := Or.inl rfl
  have hy4 : y ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) := Or.inr (Or.inl rfl)
  have hxi4 : x⁻¹ ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) :=
    Or.inr (Or.inr (Or.inl rfl))
  have hyi4 : y⁻¹ ∈ ({x, y, x⁻¹, y⁻¹} : Set (SpecialLinearGroup (Fin m) F)) :=
    Or.inr (Or.inr (Or.inr rfl))
  have hc : φ ⁅x, y⁆ = φ x ∘ₗ φ y ∘ₗ φ x⁻¹ ∘ₗ φ y⁻¹ := by
    rw [commutatorElement_def, hφmul, hφmul, hφmul, LinearMap.comp_assoc, LinearMap.comp_assoc]
  have hfixblk : ∀ k, k ∉ S → ∀ z, φ ⁅x, y⁆ (Pi.single k z, 0) = (Pi.single k z, 0) := by
    intro k hk z
    rw [hc]
    simp only [LinearMap.comp_apply]
    rw [hblk _ hyi4 k hk, hblk _ hxi4 k hk, hblk _ hy4 k hk, hblk _ hx4 k hk]
    have h1 := hinv x (Or.inl rfl) k hk
    have h2 := hinv y (Or.inr rfl) k hk
    congr 2
    calc z * lam y⁻¹ k * lam x⁻¹ k * lam y k * lam x k
        = z * (lam y⁻¹ k * lam y k) * (lam x⁻¹ k * lam x k) := by ring
      _ = z := by rw [h1, h2, mul_one, mul_one]
  have hpresc : ∀ k, k ∉ S → ∀ v : (Fin s → AdjoinRoot g) × (Fin d → F), v.1 k = 0 →
      (φ ⁅x, y⁆ v).1 k = 0 := by
    intro k hk v hv
    rw [hc]
    simp only [LinearMap.comp_apply]
    exact hpres _ hx4 k hk _ (hpres _ hy4 k hk _ (hpres _ hxi4 k hk _ (hpres _ hyi4 k hk _ hv)))
  rw [mem_coordBlockSL_iff]
  intro p q hpq
  have hcol : ∀ v, ((⁅x, y⁆ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ frameCoords g ε v =
      frameCoords g ε (φ ⁅x, y⁆ v) := fun v => (frameCoords_frameForm g ε _ v).symm
  have hentry : ((⁅x, y⁆ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) p q =
      (((⁅x, y⁆ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ Pi.single q 1) p := by
    rw [Matrix.mulVec_single_one]
    rfl
  rcases hεq : ε q with ⟨a, i⟩ | j
  · have hq : Pi.single q (1 : F) = frameCoords g ε (Pi.single i ((rootPB g).basis a), 0) := by
      rw [frameCoords_single_basis, ← hεq, Equiv.symm_apply_apply]
    by_cases hi : i ∈ S
    ·
      have hp : p ∉ fixS ε Sᶜ := by
        rcases hpq with hp | hq'
        · exact hp
        · exfalso
          apply hq'
          rw [mem_fixS, hεq]
          simp [inT, hi]
      obtain ⟨a', k', hεp, hk'⟩ := exists_inl_of_not_mem_fixS ε hp
      rw [hentry, hq, hcol, frameCoords_apply, hεp]
      have hk'i : k' ≠ i := fun h => hk' (h ▸ hi)
      have hv : ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g),
          (0 : Fin d → F)).1 k' = 0 :=
        Pi.single_eq_of_ne hk'i _
      simp only [Sum.elim_inl]
      rw [hpresc k' hk' _ hv, map_zero, Finsupp.zero_apply,
        if_neg (fun h => by rw [h, hεq] at hεp; simp at hεp; exact hk'i hεp.2.symm)]
    · rw [hentry, hq, hcol, hfixblk i hi, ← hq, Pi.single_apply]
  ·
    have hp : p ∉ fixS ε Sᶜ := by
      rcases hpq with hp | hq'
      · exact hp
      · exfalso
        apply hq'
        rw [mem_fixS, hεq]
        simp [inT]
    obtain ⟨a', k', hεp, hk'⟩ := exists_inl_of_not_mem_fixS ε hp
    have hq : Pi.single q (1 : F) = frameCoords g ε (0, Pi.single j 1) := by
      funext y'
      rw [frameCoords_apply]
      rcases hy' : ε y' with ⟨a'', i''⟩ | j''
      · have hne : y' ≠ q := fun h => by rw [h, hεq] at hy'; simp at hy'
        simp [Pi.single_eq_of_ne hne]
      · simp only [Sum.elim_inr]
        by_cases hjj : j'' = j
        · subst hjj
          have hyq : y' = q := ε.injective (hy'.trans hεq.symm)
          subst hyq
          simp
        · have hne : y' ≠ q := fun h => by
            rw [h, hεq] at hy'
            exact hjj (by simpa using hy'.symm)
          rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hjj]
    rw [hentry, hq, hcol, frameCoords_apply, hεp]
    simp only [Sum.elim_inl]
    rw [hpresc k' hk' _ rfl, map_zero, Finsupp.zero_apply,
      if_neg (fun h => by rw [h, hεq] at hεp; simp at hεp)]

end Commutator

section Simple

private theorem commutator_top_normal {X : Type*} [Group X] (A : Subgroup X) :
    (⁅(⊤ : Subgroup X), A⁆).Normal := by
  constructor
  intro x hx c
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, h, hh, rfl⟩ := hz
    have e : c * ⁅a, h⁆ * c⁻¹ = ⁅c * a, h⁆ * ⁅c, h⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c * a, trivial, h, hh, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨c, trivial, h, hh, rfl⟩))
  | one => simp
  | mul z w _ _ hz hw =>
    have e : c * (z * w) * c⁻¹ = (c * z * c⁻¹) * (c * w * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hz hw
  | inv z _ hz =>
    have e : c * z⁻¹ * c⁻¹ = (c * z * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hz

theorem commutator_zpowers_eq_top {c : ℕ} (hc : 3 ≤ c) {z : SpecialLinearGroup (Fin c) (ZMod 2)}
    (hz : z ≠ 1) : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin c) (ZMod 2))), Subgroup.zpowers z⁆ = ⊤ := by
  have := CFSG.RankThree.PartTwo.Sec4.RonanK429F.isSimpleGroup_SL_zmod_two hc
  have := commutator_top_normal (Subgroup.zpowers z)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (⁅(⊤ : Subgroup (SpecialLinearGroup (Fin c) (ZMod 2))), Subgroup.zpowers z⁆) with h | h
  · exfalso
    apply hz
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin c) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top u)) z
        (Subgroup.mem_zpowers z)).symm
    rw [LineL2.center_eq_bot_two (Nat.card_zmod 2), Subgroup.mem_bot] at hzc
    exact hzc
  · exact h

end Simple

end QTwoBlocks

open Polynomial Matrix QTwoBlocks CFSG.RankThree.CALinearPlane Multiplicative
open scoped commutatorElement MatrixGroups

namespace GGSecFiveBPermQTwoKFrame

variable {G : Type} [Group G] {Bs K : Subgroup G} {n r m d : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin (r + 2) ≃ Fin n}
  {g : (ZMod 2)[X]} [Fact (Irreducible g)]
  {ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
  {hC : (CoordSL.rootMat g).det = 1} {hCp : CoordSL.rootMat g ^ 3 = 1} {κ : SL(m, ZMod 2) →* G}

theorem frameHom_ofAdd (t : Fin (r + 1) → ZMod 3) :
    CoordSL.frameHom κ 1 ε hC hCp (ofAdd t) = κ (SLNS.nsSL ε hC fun i => (t i).val) := by
  rw [CoordSL.frameHom_apply, one_mul, inv_one, mul_one]

theorem coords_toAdd (b : ↥Bs) (k : Fin (r + 1)) :
    toAdd (ggSecFiveBPermQTwoCoords eta π b) k = toAdd (eta b (π k.succ)) := rfl

theorem coords_mul (b c : ↥Bs) :
    ggSecFiveBPermQTwoCoords eta π (b * c) =
      ggSecFiveBPermQTwoCoords eta π b * ggSecFiveBPermQTwoCoords eta π c := by
  apply toAdd.injective
  funext k
  simp only [ggSecFiveBPermQTwoCoords, toAdd_ofAdd, toAdd_mul, map_mul, Pi.mul_apply,
    Pi.add_apply]

theorem coords_inv (b : ↥Bs) :
    ggSecFiveBPermQTwoCoords eta π b⁻¹ = (ggSecFiveBPermQTwoCoords eta π b)⁻¹ := by
  apply toAdd.injective
  funext k
  show toAdd (eta b⁻¹ (π k.succ)) = -toAdd (eta b (π k.succ))
  rw [map_inv, Pi.inv_apply, toAdd_inv]

theorem frameHom_single (k : Fin (r + 1)) :
    CoordSL.frameHom κ 1 ε hC hCp (ofAdd (Pi.single k 1)) = κ (SLNS.nsSL ε hC (SLNS.kT {k})) := by
  rw [frameHom_ofAdd, kT_singleton_eq]

theorem mem_coordZeroOn_iff {S : Finset (Fin (r + 1))} (b : ↥Bs) :
    (b : G) ∈ ggBsCoordZeroOn Bs eta ((fun k => π k.succ) '' (S : Set (Fin (r + 1)))) ↔
      ∀ k ∈ S, toAdd (ggSecFiveBPermQTwoCoords eta π b) k = 0 := by
  rw [mem_ggBsCoordZeroOn]
  constructor
  · rintro ⟨hb, h⟩ k hk
    have h1 : eta b (π k.succ) = 1 := h (π k.succ) ⟨k, hk, rfl⟩
    rw [coords_toAdd, h1, toAdd_one]
  · intro h
    refine ⟨b.2, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    have h1 := h k hk
    rw [coords_toAdd] at h1
    exact toAdd.injective (h1.trans toAdd_one.symm)


variable (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
include hF

theorem eq_one_of_central {z : G} (hz : z ∈ K) (hc : ∀ x ∈ K, z * x = x * z) : z = 1 := by
  rw [← hF.2.1] at hz
  obtain ⟨w, rfl⟩ := hz
  have hw : w ∈ Subgroup.center SL(m, ZMod 2) := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply hF.1
    rw [map_mul, map_mul]
    exact (hc (κ u) (hF.2.1 ▸ ⟨u, rfl⟩)).symm
  rw [LineL2.center_eq_bot_two (Nat.card_zmod 2), Subgroup.mem_bot] at hw
  rw [hw, map_one]

theorem frameHom_injective : Function.Injective (CoordSL.frameHom κ 1 ε hC hCp) := by
  have hp3 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hnsplit : ¬ 3 ∣ Nat.card (ZMod 2) - 1 := by
    rw [Nat.card_zmod]
    decide
  refine CoordSL.frameHom_injective κ 1 ε hC hCp ?_ (CoordSL.rootPB_dim_pos g)
    fun j hj c => CoordSL.isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hF.2.2.1 j hj c
  intro u hu
  rw [hF.1 (hu.trans (map_one κ).symm)]
  exact Subgroup.one_mem _

theorem frameHom_mem_K (t : Multiplicative (Fin (r + 1) → ZMod 3)) :
    CoordSL.frameHom κ 1 ε hC hCp t ∈ K := by
  rw [← ofAdd_toAdd t, frameHom_ofAdd, ← hF.2.1]
  exact ⟨_, rfl⟩

theorem eq_of_conj_eq {t t' : Multiplicative (Fin (r + 1) → ZMod 3)}
    (h : ∀ u, CoordSL.frameHom κ 1 ε hC hCp t * κ u * (CoordSL.frameHom κ 1 ε hC hCp t)⁻¹ =
      CoordSL.frameHom κ 1 ε hC hCp t' * κ u * (CoordSL.frameHom κ 1 ε hC hCp t')⁻¹) :
    t = t' := by
  set ι := CoordSL.frameHom κ 1 ε hC hCp
  have hz : (ι t')⁻¹ * ι t = 1 := by
    refine hF.eq_one_of_central (K.mul_mem (K.inv_mem (hF.frameHom_mem_K t'))
      (hF.frameHom_mem_K t)) fun x hx => ?_
    rw [← hF.2.1] at hx
    obtain ⟨u, rfl⟩ := hx
    calc (ι t')⁻¹ * ι t * κ u = (ι t')⁻¹ * (ι t * κ u * (ι t)⁻¹) * ι t := by group
      _ = (ι t')⁻¹ * (ι t' * κ u * (ι t')⁻¹) * ι t := by rw [h u]
      _ = κ u * ((ι t')⁻¹ * ι t) := by group
  exact hF.frameHom_injective (inv_mul_eq_one.mp hz).symm

theorem frameHom_mem_Bs (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (t : Multiplicative (Fin (r + 1) → ZMod 3)) : CoordSL.frameHom κ 1 ε hC hCp t ∈ Bs := by
  set ι := CoordSL.frameHom κ 1 ε hC hCp
  refine hBs _ ?_ (CoordSL.frameHom_pow_p κ 1 ε hC hCp t)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 := hF.2.2.2 ⟨b, hb⟩ (SLNS.nsSL ε hC fun i => (toAdd t i).val)
  rw [← frameHom_ofAdd (hCp := hCp), ofAdd_toAdd] at h1
  have hcomm : ι (ggSecFiveBPermQTwoCoords eta π ⟨b, hb⟩) * ι t =
      ι t * ι (ggSecFiveBPermQTwoCoords eta π ⟨b, hb⟩) := by
    rw [← map_mul, ← map_mul, mul_comm]
  calc b * ι t = (b * ι t * b⁻¹) * b := by group
    _ = ι t * b := by
      rw [show b * ι t * b⁻¹ = ι t from by
        rw [show (b : G) = ((⟨b, hb⟩ : ↥Bs) : G) from rfl, h1, hcomm, mul_inv_cancel_right]]

theorem coords_frameHom (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (t : Multiplicative (Fin (r + 1) → ZMod 3)) :
    ggSecFiveBPermQTwoCoords eta π ⟨_, hF.frameHom_mem_Bs hBs t⟩ = t := by
  refine hF.eq_of_conj_eq fun u => ?_
  exact (hF.2.2.2 ⟨_, hF.frameHom_mem_Bs hBs t⟩ u).symm

theorem coords_eq_one_of_commute {b : ↥Bs} (hb : ∀ x ∈ K, (b : G) * x = x * b) :
    ggSecFiveBPermQTwoCoords eta π b = 1 := by
  refine hF.eq_of_conj_eq fun u => ?_
  rw [← hF.2.2.2 b u, map_one, one_mul, inv_one, mul_one]
  have hu : κ u ∈ K := hF.2.1 ▸ ⟨u, rfl⟩
  rw [hb _ hu, mul_inv_cancel_right]


theorem block_le_centralizer_coordZeroOn (S : Finset (Fin (r + 1))) :
    (coordBlockSL (ZMod 2) (SLNS.fixS ε Sᶜ)).map κ ≤
      Subgroup.centralizer (ggBsCoordZeroOn Bs eta
        ((fun k => π k.succ) '' (S : Set (Fin (r + 1)))) : Set G) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhB : h ∈ Bs := ggBsCoordZeroOn_le _ _ _ hh
  have hcoord := (mem_coordZeroOn_iff ⟨h, hhB⟩).mp hh
  have h1 := hF.2.2.2 ⟨h, hhB⟩ u
  rw [← ofAdd_toAdd (ggSecFiveBPermQTwoCoords eta π ⟨h, hhB⟩), frameHom_ofAdd,
    ← map_inv, ← map_mul, ← map_mul,
    nsSL_commute_of_mem_coordBlockSL ε hC (fun k hk => by rw [hcoord k hk, ZMod.val_zero]) hu,
    mul_inv_cancel_right] at h1
  calc h * κ u = (h * κ u * h⁻¹) * h := by group
    _ = κ u * h := by rw [show h * κ u * h⁻¹ = κ u from h1]

theorem blockComm [Finite G]
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs) {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {S : Finset (Fin (r + 1))} (hS0 : S.Nonempty) (hS : S ≠ Finset.univ)
    (h3 : 3 ≤ (SLNS.fixS ε Sᶜ).card) :
    ggBlockComm Bs eta ((fun k => π k.succ) '' (S : Set (Fin (r + 1)))) =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε Sᶜ)).map κ := by
  classical
  set H := ggBsCoordZeroOn Bs eta ((fun k => π k.succ) '' (S : Set (Fin (r + 1)))) with hHdef
  set J := SLNS.fixS ε Sᶜ with hJ
  set R := (coordBlockSL (ZMod 2) J).map κ with hRdef
  set ι := CoordSL.frameHom κ 1 ε hC hCp with hιdef
  have hp3 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3 :=
    CoordSL.root_isPrimitiveRoot Nat.prime_three hp3 hF.2.2.1
  have hιB : ∀ t, ι t ∈ Bs := hF.frameHom_mem_Bs hBs
  have hιcoords : ∀ t, ggSecFiveBPermQTwoCoords eta π ⟨ι t, hιB t⟩ = t :=
    hF.coords_frameHom hBs
  have hκK : ∀ u, κ u ∈ K := fun u => hF.2.1 ▸ ⟨u, rfl⟩
  have hsingH : ∀ k, k ∉ S → ι (ofAdd (Pi.single k 1)) ∈ H := by
    intro k hk
    rw [show ι (ofAdd (Pi.single k 1)) = ((⟨_, hιB _⟩ : ↥Bs) : G) from rfl, mem_coordZeroOn_iff,
      hιcoords]
    intro k' hk'
    rw [toAdd_ofAdd, Pi.single_eq_of_ne (fun h : k' = k => hk (h ▸ hk'))]
  have hRC : R ≤ Subgroup.centralizer (H : Set G) :=
    hF.block_le_centralizer_coordZeroOn S
  have hRW : R ≤ ⁅R, Bs ⊓ R⁆ := by
    obtain ⟨k₁, hk₁⟩ := hS0
    have hz₀ : SLNS.nsSL ε hC (SLNS.kT {k₁}) ∈ coordBlockSL (ZMod 2) J :=
      nsSL_mem_coordBlockSL ε hC fun i hi => by
        simp only [SLNS.kT, Finset.mem_singleton]
        rw [if_neg (fun h : i = k₁ => hi (h ▸ hk₁))]
    rw [← range_blockSLOn] at hz₀
    obtain ⟨z, hz⟩ := hz₀
    have hzne : z ≠ 1 := by
      intro h1
      have h2 : ι (ofAdd (Pi.single k₁ 1)) = 1 := by
        rw [hιdef, frameHom_single, ← hz, h1, map_one, map_one]
      have h3' := hF.frameHom_injective (h2.trans (map_one _).symm)
      have h4 := congrFun (congrArg toAdd h3') k₁
      simp at h4
    set φ := κ.comp (blockSLOn (ZMod 2) J) with hφ
    have hRφ : R = φ.range := by
      rw [hRdef, ← range_blockSLOn, hφ, MonoidHom.range_comp]
    have hφz : φ z = ι (ofAdd (Pi.single k₁ 1)) := by
      rw [hφ, MonoidHom.comp_apply, hz, hιdef, frameHom_single]
    have htop := commutator_zpowers_eq_top h3 hzne
    have hzW : φ z ∈ Bs ⊓ R := ⟨hφz ▸ hιB _, hRφ ▸ ⟨z, rfl⟩⟩
    calc R = (⊤ : Subgroup (SL(J.card, ZMod 2))).map φ := by rw [hRφ, MonoidHom.range_eq_map]
      _ = (⁅(⊤ : Subgroup (SL(J.card, ZMod 2))), Subgroup.zpowers z⁆).map φ := by rw [htop]
      _ = ⁅(⊤ : Subgroup (SL(J.card, ZMod 2))).map φ, (Subgroup.zpowers z).map φ⁆ :=
          Subgroup.map_commutator _ _ _
      _ ≤ ⁅R, Bs ⊓ R⁆ := by
          refine Subgroup.commutator_mono (by rw [hRφ, MonoidHom.range_eq_map]) ?_
          rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
          exact hzW
  refine ggCommutator_centralizer_eq_of_mul (E := Bs) (H := H) (W := Bs ⊓ R)
    (N := ⁅K ⊓ Subgroup.centralizer (H : Set G), K ⊓ Subgroup.centralizer (H : Set G)⁆) (R := R)
    ?_ inf_le_left ?_ ?_ ?_ hRC hRW
  ·
    intro e he
    set b : ↥Bs := ⟨e, he⟩
    set tS : Fin (r + 1) → ZMod 3 :=
      fun k => if k ∈ S then toAdd (ggSecFiveBPermQTwoCoords eta π b) k else 0 with htS
    set w := ι (ofAdd tS) with hw
    have hwR : w ∈ R := by
      rw [hw, hιdef, frameHom_ofAdd]
      refine ⟨_, nsSL_mem_coordBlockSL ε hC fun i hi => ?_, rfl⟩
      simp only [htS, if_neg hi, ZMod.val_zero]
    have hhB : e * w⁻¹ ∈ Bs := Bs.mul_mem he (Bs.inv_mem (hιB _))
    refine ⟨e * w⁻¹, ?_, w, ⟨hιB _, hwR⟩, by group⟩
    rw [show e * w⁻¹ = ((b * (⟨w, hιB _⟩ : ↥Bs)⁻¹ : ↥Bs) : G) from rfl, mem_coordZeroOn_iff,
      coords_mul, coords_inv, hιcoords]
    intro k hk
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply, htS, if_pos hk]
    exact add_neg_cancel _
  ·
    intro c hc
    have hyH : y ∈ H := by
      rw [show y = ((⟨y, hyB⟩ : ↥Bs) : G) from rfl, mem_coordZeroOn_iff,
        hF.coords_eq_one_of_commute fun x hx => ?_]
      · intro k _
        rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hx)).symm
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∉ S := by
      by_contra h
      exact hS (Finset.eq_univ_iff_forall.mpr fun k => by
        by_contra hk
        exact h ⟨k, hk⟩)
    set r₀ := ι (ofAdd (Pi.single k₀ 1)) with hr₀
    have hr₀K : r₀ ∈ K := hF.frameHom_mem_K _
    have hr₀nc : r₀ ∉ Subgroup.centralizer (K : Set G) := by
      intro h
      have h1 : r₀ = 1 := hF.eq_one_of_central hr₀K fun x hx =>
        (Subgroup.mem_centralizer_iff.mp h x hx).symm
      have h2 := hF.frameHom_injective (h1.trans (map_one _).symm)
      have h3' := congrFun (congrArg toAdd h2) k₀
      simp at h3'
    have hcy : c ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc y hyH).symm
    have hcK : c ∈ Subgroup.normalizer (K : Set G) :=
      ggMem_normalizer_of_component (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hr₀K hr₀nc
        (Subgroup.le_normalizer hcy) (Subgroup.mem_centralizer_iff.mp hc r₀ (hsingH k₀ hk₀)).symm
    have hcA : c ∈ Subgroup.normalizer
        ((K ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hcK, Subgroup.le_normalizer hc⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcA ⊢
    rw [Subgroup.map_commutator, hcA]
  ·
    intro x hx
    have hRA : R ≤ K ⊓ Subgroup.centralizer (H : Set G) := fun z hz =>
      ⟨by obtain ⟨u, -, rfl⟩ := hz; exact hκK u, hRC hz⟩
    exact Subgroup.commutator_mono hRA (le_trans inf_le_right hRA) (hRW hx.2)
  ·
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨u, rfl⟩ : a ∈ κ.range := hF.2.1 ▸ ha.1
    obtain ⟨v, rfl⟩ : b ∈ κ.range := hF.2.1 ▸ hb.1
    have hcomm : ∀ x, κ x ∈ Subgroup.centralizer (H : Set G) → ∀ k, k ∉ S →
        Commute (SLNS.nsSL ε hC (SLNS.kT {k})) x := by
      intro x hx k hk
      apply hF.1
      rw [map_mul, map_mul, ← frameHom_single (hCp := hCp)]
      exact (Subgroup.mem_centralizer_iff.mp hx _ (hsingH k hk))
    rw [← map_commutatorElement]
    exact ⟨_, commutator_mem_coordBlockSL ε hC hprim (hcomm u ha.2) (hcomm v hb.2), rfl⟩

end GGSecFiveBPermQTwoKFrame

end CFSG.StandardType

end
