module

public import CFSG.RankThree.PartOne.KLR.A1Twist
public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4
public import CFSG.RankThree.PartOne.KE.SuzukiDescentSp
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.PartOne.KF4.B2Surj
public import CFSG.RankThree.PartOne.KLR.RadMap

public noncomputable section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.Lattice
open Matrix

section B2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

abbrev B2Q (L : Type) [Field L] : Subgroup (ModGL ReeTag.F4.tag L) :=
  subsystemGroup ReeTag.F4.tag L f4B2Support

omit [CharP L 2] in
theorem B2Q_eq_rootSpan :
    B2Q L = rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) :=
  subsystemGroup_eq_rootSpan f4B2Support

omit [CharP L 2] in
theorem B2Q_le_adjointGroup : B2Q L ≤ adjointGroup ReeTag.F4.tag L := by
  rw [B2Q_eq_rootSpan]
  exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _

omit [CharP L 2] in
theorem IsReeFrob.fext_yUnit {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a F)
    (j : Fin ReeTag.F4.tag.rank) (c : L) :
    Fext F (yUnit ReeTag.F4.tag L j c) =
      yUnit ReeTag.F4.tag L (ReeTag.F4.perm j) (c ^ ReeTag.F4.relationExponent a j) := by
  rw [Fext_of_mem F (yUnit_mem_adjointGroup j c)]
  exact congrArg Subtype.val (hF j c).2

theorem perm_f4Index_one :
    ReeTag.F4.perm (f4Index 1 : Fin ReeTag.F4.tag.rank) = f4Index 2 := Fin.ext rfl

theorem perm_f4Index_two :
    ReeTag.F4.perm (f4Index 2 : Fin ReeTag.F4.tag.rank) = f4Index 1 := Fin.ext rfl

omit [CharP L 2] in
theorem fext_mem_B2Q {g : ModGL ReeTag.F4.tag L} (hg : g ∈ B2Q L) : Fext D.F g ∈ B2Q L := by
  have hg' : g ∈ Subgroup.closure {g : ModGL ReeTag.F4.tag L |
      ∃ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support ∧ ∃ c : L,
        g = xUnit ReeTag.F4.tag L i c ∨ g = yUnit ReeTag.F4.tag L i c} := hg
  have key := twistMap_mem_of_closure (F := D.F) (n := (1 : ModGL ReeTag.F4.tag L))
    (s := {g : ModGL ReeTag.F4.tag L | ∃ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support ∧
      ∃ c : L, g = xUnit ReeTag.F4.tag L i c ∨ g = yUnit ReeTag.F4.tag L i c})
    (T := B2Q L) ?_ ?_ hg'
  · simpa [twistMap] using key.1
  · rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c
  · have hperm : ∀ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support →
        ReeTag.F4.perm i ∈ f4B2Support := by
      intro i hi
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [perm_f4Index_one]
        exact (mem_f4B2Support _).2 (Or.inr rfl)
      · rw [perm_f4Index_two]
        exact (mem_f4B2Support _).2 (Or.inl rfl)
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · show twistMap D.F 1 (xUnit ReeTag.F4.tag L i c) ∈ B2Q L
      unfold twistMap
      rw [D.isFrob.fext_xUnit]
      simp only [one_mul, inv_one, mul_one]
      exact xUnit_mem_subsystemGroup (hperm i hi) _
    · show twistMap D.F 1 (yUnit ReeTag.F4.tag L i c) ∈ B2Q L
      unfold twistMap
      rw [D.isFrob.fext_yUnit]
      simp only [one_mul, inv_one, mul_one]
      exact yUnit_mem_subsystemGroup (hperm i hi) _

omit [CharP L 2] [Algebra K L] in
theorem minorMap_x2 (c : L) :
    minorMap (1 + Matrix.single 1 2 c : Matrix (Fin 4) (Fin 4) L) =
      1 + (Matrix.single 0 1 c + Matrix.single 2 3 c) := by
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

omit [CharP L 2] [Algebra K L] in
theorem minorMap_x3 (c : L) :
    minorMap (1 + (Matrix.single 0 1 c + Matrix.single 2 3 c) : Matrix (Fin 4) (Fin 4) L) =
      1 + Matrix.single 1 2 (c ^ 2) := by
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, sq]

omit [CharP L 2] [Algebra K L] in
theorem minorMap_y2 (c : L) :
    minorMap (1 + Matrix.single 2 1 c : Matrix (Fin 4) (Fin 4) L) =
      1 + (Matrix.single 1 0 c + Matrix.single 3 2 c) := by
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

omit [CharP L 2] [Algebra K L] in
theorem minorMap_y3 (c : L) :
    minorMap (1 + (Matrix.single 1 0 c + Matrix.single 3 2 c) : Matrix (Fin 4) (Fin 4) L) =
      1 + Matrix.single 2 1 (c ^ 2) := by
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, sq]

omit [CharP L 2] [Algebra K L] in
theorem map_pow_x2 (c : L) (k : ℕ) (hk : k ≠ 0) :
    (1 + Matrix.single 1 2 c : Matrix (Fin 4) (Fin 4) L).map (fun x => x ^ k) =
      1 + Matrix.single 1 2 (c ^ k) := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [Matrix.map_apply, zero_pow hk]

omit [CharP L 2] [Algebra K L] in
theorem map_pow_x3 (c : L) (k : ℕ) (hk : k ≠ 0) :
    (1 + (Matrix.single 0 1 c + Matrix.single 2 3 c) : Matrix (Fin 4) (Fin 4) L).map
      (fun x => x ^ k) = 1 + (Matrix.single 0 1 (c ^ k) + Matrix.single 2 3 (c ^ k)) := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [Matrix.map_apply, zero_pow hk]

omit [CharP L 2] [Algebra K L] in
theorem map_pow_y2 (c : L) (k : ℕ) (hk : k ≠ 0) :
    (1 + Matrix.single 2 1 c : Matrix (Fin 4) (Fin 4) L).map (fun x => x ^ k) =
      1 + Matrix.single 2 1 (c ^ k) := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [Matrix.map_apply, zero_pow hk]

omit [CharP L 2] [Algebra K L] in
theorem map_pow_y3 (c : L) (k : ℕ) (hk : k ≠ 0) :
    (1 + (Matrix.single 1 0 c + Matrix.single 3 2 c) : Matrix (Fin 4) (Fin 4) L).map
      (fun x => x ^ k) = 1 + (Matrix.single 1 0 (c ^ k) + Matrix.single 3 2 (c ^ k)) := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [Matrix.map_apply, zero_pow hk]

omit [CharP L 2] in
@[expose] noncomputable def B2Ftilde : B2Q L →* B2Q L where
  toFun x := ⟨Fext D.F (x : ModGL ReeTag.F4.tag L), fext_mem_B2Q D x.2⟩
  map_one' := Subtype.ext (Fext_one D.F)
  map_mul' x y := Subtype.ext (Fext_mul D.F (B2Q_le_adjointGroup x.2) (B2Q_le_adjointGroup y.2))

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
@[expose] noncomputable def B2eQ (L : Type) [Field L] [CharP L 2] : B2Q L ≃* antiSp L :=
  (f4B2Equiv L).trans (MulEquiv.subgroupCongr f4SpGroup_eq_antiSp)

abbrev b2i1 : Fin ReeTag.F4.tag.rank := f4Index 1

abbrev b2i2 : Fin ReeTag.F4.tag.rank := f4Index 2

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
abbrev b2Mat (g : ModGL ReeTag.F4.tag L) : Matrix (Fin 4) (Fin 4) L := f4B2_data.Mat g

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem b2Mat_x2 (c : L) :
    b2Mat (xUnit ReeTag.F4.tag L b2i1 c) = 1 + Matrix.single 1 2 c := f4B2_Mat_x2 c

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem b2Mat_y2 (c : L) :
    b2Mat (yUnit ReeTag.F4.tag L b2i1 c) = 1 + Matrix.single 2 1 c := f4B2_Mat_y2 c

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem b2Mat_x3 (c : L) :
    b2Mat (xUnit ReeTag.F4.tag L b2i2 c) =
      1 + (Matrix.single 0 1 c + Matrix.single 2 3 c) := f4B2_Mat_x3 c

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem b2Mat_y3 (c : L) :
    b2Mat (yUnit ReeTag.F4.tag L b2i2 c) =
      1 + (Matrix.single 1 0 c + Matrix.single 3 2 c) := f4B2_Mat_y3 c

section Compat

variable {S₀ : MulAut (antiSp L)}
  (hS₀ : ∀ g : antiSp L, glMat (S₀ g : GL (Fin 4) L) =
    (minorMap (glMat (g : GL (Fin 4) L))).map (fun x => x ^ 2 ^ a))
include hS₀

theorem B2_gen_x2 (c : L) (hg : xUnit ReeTag.F4.tag L b2i1 c ∈ B2Q L) :
    B2eQ L (B2Ftilde D ⟨_, hg⟩) = S₀ (B2eQ L ⟨_, hg⟩) := by
  apply antiSp_ext
  rw [hS₀]
  change b2Mat (Fext D.F (xUnit ReeTag.F4.tag L b2i1 c)) =
    (minorMap (b2Mat (xUnit ReeTag.F4.tag L b2i1 c))).map _
  rw [D.isFrob.fext_xUnit, perm_f4Index_one, relExp_long a _ (by decide), b2Mat_x3,
    b2Mat_x2, minorMap_x2, map_pow_x3 _ _ (pow_ne_zero _ two_ne_zero)]

theorem B2_gen_y2 (c : L) (hg : yUnit ReeTag.F4.tag L b2i1 c ∈ B2Q L) :
    B2eQ L (B2Ftilde D ⟨_, hg⟩) = S₀ (B2eQ L ⟨_, hg⟩) := by
  apply antiSp_ext
  rw [hS₀]
  change b2Mat (Fext D.F (yUnit ReeTag.F4.tag L b2i1 c)) =
    (minorMap (b2Mat (yUnit ReeTag.F4.tag L b2i1 c))).map _
  rw [D.isFrob.fext_yUnit, perm_f4Index_one, relExp_long a _ (by decide), b2Mat_y3,
    b2Mat_y2, minorMap_y2, map_pow_y3 _ _ (pow_ne_zero _ two_ne_zero)]

theorem B2_gen_x3 (c : L) (hg : xUnit ReeTag.F4.tag L b2i2 c ∈ B2Q L) :
    B2eQ L (B2Ftilde D ⟨_, hg⟩) = S₀ (B2eQ L ⟨_, hg⟩) := by
  apply antiSp_ext
  rw [hS₀]
  change b2Mat (Fext D.F (xUnit ReeTag.F4.tag L b2i2 c)) =
    (minorMap (b2Mat (xUnit ReeTag.F4.tag L b2i2 c))).map _
  rw [D.isFrob.fext_xUnit, perm_f4Index_two, relExp_short a _ (by decide), b2Mat_x2,
    b2Mat_x3, minorMap_x3, map_pow_x2 _ _ (pow_ne_zero _ two_ne_zero), ← pow_mul, ← pow_succ']

theorem B2_gen_y3 (c : L) (hg : yUnit ReeTag.F4.tag L b2i2 c ∈ B2Q L) :
    B2eQ L (B2Ftilde D ⟨_, hg⟩) = S₀ (B2eQ L ⟨_, hg⟩) := by
  apply antiSp_ext
  rw [hS₀]
  change b2Mat (Fext D.F (yUnit ReeTag.F4.tag L b2i2 c)) =
    (minorMap (b2Mat (yUnit ReeTag.F4.tag L b2i2 c))).map _
  rw [D.isFrob.fext_yUnit, perm_f4Index_two, relExp_short a _ (by decide), b2Mat_y2,
    b2Mat_y3, minorMap_y3, map_pow_y2 _ _ (pow_ne_zero _ two_ne_zero), ← pow_mul, ← pow_succ']

theorem B2eQ_Ftilde (x : B2Q L) : B2eQ L (B2Ftilde D x) = S₀ (B2eQ L x) := by
  obtain ⟨g, hg0⟩ := x
  have main : ∀ g : ModGL ReeTag.F4.tag L, g ∈ B2Q L → ∀ hg : g ∈ B2Q L,
      B2eQ L (B2Ftilde D ⟨g, hg⟩) = S₀ (B2eQ L ⟨g, hg⟩) := by
    intro g hg0
    have hg' : g ∈ Subgroup.closure {g : ModGL ReeTag.F4.tag L |
        ∃ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support ∧ ∃ c : L,
          g = xUnit ReeTag.F4.tag L i c ∨ g = yUnit ReeTag.F4.tag L i c} := hg0
    induction hg' using Subgroup.closure_induction with
    | mem y hy =>
      intro hg
      obtain ⟨i, hi, c, rfl | rfl⟩ := hy
      · rcases (mem_f4B2Support i).1 hi with rfl | rfl
        · exact B2_gen_x2 D hS₀ c hg
        · exact B2_gen_x3 D hS₀ c hg
      · rcases (mem_f4B2Support i).1 hi with rfl | rfl
        · exact B2_gen_y2 D hS₀ c hg
        · exact B2_gen_y3 D hS₀ c hg
    | one =>
      intro hg
      have h1 : (⟨1, hg⟩ : B2Q L) = 1 := rfl
      rw [h1, map_one, map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hg
      have hy' : y ∈ B2Q L := hy
      have hz' : z ∈ B2Q L := hz
      have h1 : (⟨y * z, hg⟩ : B2Q L) = ⟨y, hy'⟩ * ⟨z, hz'⟩ := rfl
      rw [h1, map_mul, map_mul, map_mul, map_mul, ihy hy' hy', ihz hz' hz']
    | inv y hy ihy =>
      intro hg
      have hy' : y ∈ B2Q L := hy
      have h1 : (⟨y⁻¹, hg⟩ : B2Q L) = (⟨y, hy'⟩ : B2Q L)⁻¹ := rfl
      rw [h1, map_inv, map_inv, map_inv, map_inv, ihy hy' hy']
  exact main g hg0 hg0

end Compat

section Eps

def b2Words : List (List (Fin ReeTag.F4.tag.rank)) :=
  [[], [b2i1], [b2i2], [b2i1, b2i2], [b2i2, b2i1], [b2i1, b2i2, b2i1], [b2i2, b2i1, b2i2],
    [b2i1, b2i2, b2i1, b2i2]]

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem b2Words_letters : ∀ ω ∈ b2Words, ∀ k ∈ ω, k = b2i1 ∨ k = b2i2 := by
  decide

theorem b2_table : ∀ β₁ ∈ rootFinset ReeTag.F4.tag, ∀ β₂ ∈ rootFinset ReeTag.F4.tag,
    (∀ k, k ≠ b2i1 → k ≠ b2i2 → β₁ k = 0) → (∀ k, k ≠ b2i1 → k ≠ b2i2 → β₂ k = 0) →
    ReeTag.F4.quadForm β₁ = 4 → ReeTag.F4.quadForm β₂ = 2 →
    CFSG.LieType.Steinberg.Adjoint.iform β₁ β₂ = CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) (Pi.single b2i2 1) →
    ∃ ω ∈ b2Words, wordMat ReeTag.F4.tag ω *ᵥ (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        β₁ ∧ wordMat ReeTag.F4.tag ω *ᵥ (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) = β₂ := by
  decide +kernel

theorem b2_exists_eps {w' : WeylGroup ReeTag.F4.tag}
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    ∃ ω ∈ b2Words,
      (coxeterSystem ReeTag.F4.tag).wordProd ω •
          (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        w' • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) ∧
      (coxeterSystem ReeTag.F4.tag).wordProd ω •
          (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        w' • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
  have hr1 : IsRoot ReeTag.F4.tag (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ _
  have hr2 : IsRoot ReeTag.F4.tag (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ _
  have hm1 : (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈
      parabolicRoots ReeTag.F4.tag f4B2Support := by
    refine ⟨hr1, fun k hk => ?_⟩
    have hk' : k ≠ b2i1 := fun h => hk ((mem_f4B2Support _).2 (Or.inl h))
    exact Pi.single_eq_of_ne hk' _
  have hm2 : (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈
      parabolicRoots ReeTag.F4.tag f4B2Support := by
    refine ⟨hr2, fun k hk => ?_⟩
    have hk' : k ≠ b2i2 := fun h => hk ((mem_f4B2Support _).2 (Or.inr h))
    exact Pi.single_eq_of_ne hk' _
  have h1 : w' • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      w' • ReeTag.F4.dualRoot (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rw [ReeTag.dualRoot_single, perm_f4Index_two]
  have h2 : w' • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      w' • ReeTag.F4.dualRoot (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    rw [ReeTag.dualRoot_single, perm_f4Index_one]
  have hβ1 := hstab _ hm2
  have hβ2 := hstab _ hm1
  rw [← h1] at hβ1
  rw [← h2] at hβ2
  have hq1 : ReeTag.F4.quadForm (w' • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 4 := by
    rw [quadForm_smul]
    exact (ReeTag.F4_quadForm_single b2i1).trans (by decide)
  have hq2 : ReeTag.F4.quadForm (w' • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ)) = 2 := by
    rw [quadForm_smul]
    exact (ReeTag.F4_quadForm_single b2i2).trans (by decide)
  have hi : CFSG.LieType.Steinberg.Adjoint.iform
      (w' • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ))
      (w' • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      CFSG.LieType.Steinberg.Adjoint.iform (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ)
        (Pi.single b2i2 1) := iform_smul w' _ _
  obtain ⟨ω, hω, e1, e2⟩ := b2_table _ (mem_rootFinset.2 hβ1.1) _ (mem_rootFinset.2 hβ2.1)
    (fun k hk1 hk2 => hβ1.2 k fun hk => ((mem_f4B2Support k).1 hk).elim hk1 hk2)
    (fun k hk1 hk2 => hβ2.2 k fun hk => ((mem_f4B2Support k).1 hk).elim hk1 hk2) hq1 hq2 hi
  refine ⟨ω, hω, ?_, ?_⟩
  · rw [wordProd_smul_eq_wordMat_mulVec, e1]
  · rw [wordProd_smul_eq_wordMat_mulVec, e2]

omit [Finite K] [CharP K ReeTag.F4.prime] [Algebra K L] [CharP L 2] in
theorem twistMap_eq_of_closure {F : MulAut (adjointGroup ReeTag.F4.tag L)}
    {n₁ n₂ : ModGL ReeTag.F4.tag L} {s : Set (ModGL ReeTag.F4.tag L)}
    (hs : s ⊆ adjointGroup ReeTag.F4.tag L)
    (h : ∀ g ∈ s, twistMap F n₁ g = twistMap F n₂ g) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ Subgroup.closure s) :
    twistMap F n₁ g = twistMap F n₂ g ∧ g ∈ adjointGroup ReeTag.F4.tag L := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨h x hx, hs hx⟩
  | one => exact ⟨by rw [twistMap_one, twistMap_one], one_mem _⟩
  | mul x y _ _ hx hy =>
    refine ⟨?_, mul_mem hx.2 hy.2⟩
    rw [twistMap_mul n₁ hx.2 hy.2, twistMap_mul n₂ hx.2 hy.2, hx.1, hy.1]
  | inv x _ hx =>
    refine ⟨?_, inv_mem hx.2⟩
    rw [twistMap_inv n₁ hx.2, twistMap_inv n₂ hx.2, hx.1]

theorem twist_eq_on_B2Q {n' : ModGL ReeTag.F4.tag L} {w' ε : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hε1 : ε • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      w' • (Pi.single b2i1 1 : Fin ReeTag.F4.tag.rank → ℤ))
    (hε2 : ε • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      w' • (Pi.single b2i2 1 : Fin ReeTag.F4.tag.rank → ℤ))
    {g : ModGL ReeTag.F4.tag L} (hg : g ∈ B2Q L) :
    twistMap D.F n' g = twistMap D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L ε) g := by
  have hg' : g ∈ Subgroup.closure {g : ModGL ReeTag.F4.tag L |
      ∃ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support ∧ ∃ c : L,
        g = xUnit ReeTag.F4.tag L i c ∨ g = yUnit ReeTag.F4.tag L i c} := hg
  refine (twistMap_eq_of_closure (F := D.F) ?_ ?_ hg').1
  · rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c
  · have hm := permAct_canonicalRep (L := L) ε
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      unfold twistMap
      rw [D.isFrob.twist_pinnedX hperm (isRoot_single _ i),
        D.isFrob.twist_pinnedX hm (isRoot_single _ i), ReeTag.dualRoot_single]
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [perm_f4Index_one, ← hε2]
      · rw [perm_f4Index_two, ← hε1]
    · rw [← pinnedX_neg_single]
      unfold twistMap
      rw [D.isFrob.twist_pinnedX hperm (IsRoot.neg (isRoot_single _ i)),
        D.isFrob.twist_pinnedX hm (IsRoot.neg (isRoot_single _ i)),
        dualRoot_neg (isRoot_single _ i), ReeTag.dualRoot_single, smul_neg, smul_neg]
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [perm_f4Index_one, ← hε2]
      · rw [perm_f4Index_two, ← hε1]

omit [CharP L 2] in
theorem wordProd_mem_parabolicWeylGroup_b2 {ω : List (Fin ReeTag.F4.tag.rank)}
    (hω : ∀ k ∈ ω, k = b2i1 ∨ k = b2i2) :
    (coxeterSystem ReeTag.F4.tag).wordProd ω ∈ parabolicWeylGroup ReeTag.F4.tag f4B2Support := by
  rw [CoxeterSystem.wordProd]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨k, (mem_f4B2Support k).2 (hω k hk), rfl⟩

end Eps

section Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {L : Type} [Field L] [Algebra K L]
  [CharP L 2] {a : ℕ}

theorem fixed_S0_iff_mem_range (hK : Nat.card K = 2 ^ (2 * a + 1)) {S₀ : MulAut (antiSp L)}
    (hS₀ : ∀ g : antiSp L, glMat (S₀ g : GL (Fin 4) L) =
      (minorMap (glMat (g : GL (Fin 4) L))).map (fun x => x ^ 2 ^ a)) (A : antiSp L) :
    S₀ A = A ↔ A ∈ (szEmbed hK (algebraMap K L)).range := by
  constructor
  · intro hA
    obtain ⟨h1, h2⟩ := fixed_of_S0_pow hS₀ (m := 0) (a := a) (by omega) (by simpa using hA)
    have hf : ∀ x : L, x ^ 2 ^ (2 * a + 1) = x → x ∈ Set.range (algebraMap K L) := fun x hx =>
      CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K) (by rw [hK]; exact hx)
    exact mem_range_szEmbed hK (algebraMap K L) hf h1 h2
  · rintro ⟨g, rfl⟩
    apply antiSp_ext
    rw [hS₀, glMat_szEmbed]
    have hρ : minorMap (glMat (g : GL (Fin 4) K)) =
        (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ (a + 1)) :=
      (mem_suzukiGroup_iff_minorMap hK ⟨(g : GL (Fin 4) K), suzukiGroup_le_antiSp hK g.2⟩).1 g.2
    rw [minorMap_map_hom, hρ, Matrix.map_map, Matrix.map_map]
    ext i j
    simp only [Function.comp_apply, Matrix.map_apply]
    have hq : ∀ x : K, x ^ 2 ^ (2 * a + 1) = x := fun x => by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    rw [← map_pow, ← pow_mul, ← pow_add, show a + 1 + a = 2 * a + 1 by omega, hq]

end Fix

section Main

theorem noSolvableRadical_B2 [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    NoSolvableRadical (B2Q L ⊓ twistedFixed D.F n') := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨ω, hω, hε1, hε2⟩ := b2_exists_eps hstab
  have hεW := wordProd_mem_parabolicWeylGroup_b2 (b2Words_letters ω hω)
  set ε := (coxeterSystem ReeTag.F4.tag).wordProd ω with hε
  set m := canonicalRep (coxeterSystem ReeTag.F4.tag) L ε with hm
  have hmQ : m ∈ B2Q L := canonicalRep_mem_subsystemGroup hεW
  have heq : ∀ g ∈ B2Q L, twistMap D.F n' g = twistMap D.F m g := fun g hg =>
    twist_eq_on_B2Q D hperm hε1 hε2 hg
  obtain ⟨S₀, hS₀, hLang⟩ := antiSp_lang_aut L a
  let mQ : B2Q L := ⟨m, hmQ⟩
  let M : antiSp L := B2eQ L mQ
  obtain ⟨h, hh⟩ := hLang M
  let Fm : B2Q L →* B2Q L := (MulAut.conj mQ).toMonoidHom.comp (B2Ftilde D)
  have hFm : ∀ x, B2eQ L (Fm x) = M * S₀ (B2eQ L x) * M⁻¹ := by
    intro x
    show B2eQ L (mQ * B2Ftilde D x * mQ⁻¹) = _
    rw [map_mul, map_mul, map_inv, B2eQ_Ftilde D hS₀]
  let P' : Subgroup (ModGL ReeTag.F4.tag L) := B2Q L ⊓ twistedFixed D.F n'
  let P'₀ : Subgroup (B2Q L) := P'.subgroupOf (B2Q L)
  have hP'₀ : ∀ x : B2Q L, x ∈ P'₀ ↔ Fm x = x := by
    intro x
    have hxad := B2Q_le_adjointGroup x.2
    show (x : ModGL ReeTag.F4.tag L) ∈ P' ↔ _
    constructor
    · rintro ⟨-, -, hfix⟩
      refine Subtype.ext ?_
      show m * Fext D.F x * m⁻¹ = x
      have : twistMap D.F n' x = x := hfix
      rw [heq x x.2] at this
      exact this
    · intro hFx
      refine ⟨x.2, hxad, ?_⟩
      have h1 : m * Fext D.F x * m⁻¹ = x := congrArg Subtype.val hFx
      show twistMap D.F n' x = x
      rw [heq x x.2]
      exact h1
  have hP'eq : P'₀.map (B2Q L).subtype = P' :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  let Y₁ : Subgroup (antiSp L) := P'₀.map (B2eQ L).toMonoidHom
  have hY₁ : ∀ A : antiSp L, A ∈ Y₁ ↔ M * S₀ A * M⁻¹ = A := by
    intro A
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hP'₀ x).1 hx
      have h2 := hFm x
      rw [h1] at h2
      exact h2.symm
    · intro hA
      refine ⟨(B2eQ L).symm A, (hP'₀ _).2 ?_, by simp⟩
      apply (B2eQ L).injective
      rw [hFm, MulEquiv.apply_symm_apply]
      exact hA
  have hY₂ : ∀ A : antiSp L, A ∈ Y₁.map (MulAut.conj h).toMonoidHom ↔ S₀ A = A := by
    intro A
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hB' := (hY₁ B).1 hB
      rw [hh] at hB'
      show S₀ (h * B * h⁻¹) = h * B * h⁻¹
      rw [map_mul, map_mul, map_inv]
      calc S₀ h * S₀ B * (S₀ h)⁻¹ = h * (h⁻¹ * S₀ h * S₀ B * (h⁻¹ * S₀ h)⁻¹) * h⁻¹ := by group
        _ = h * B * h⁻¹ := by rw [hB']
    · intro hA
      refine ⟨h⁻¹ * A * h, (hY₁ _).2 ?_, ?_⟩
      · rw [hh, map_mul, map_mul, map_inv, hA]
        group
      · show h * (h⁻¹ * A * h) * h⁻¹ = A
        group
  have hrange : Y₁.map (MulAut.conj h).toMonoidHom = (szEmbed hK (algebraMap K L)).range := by
    ext A
    rw [hY₂, fixed_S0_iff_mem_range hK hS₀]
  obtain ⟨-, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  have hns : ¬ Group.IsSolvable (suzukiGroup a K) := Group.IsPerfect.not_isSolvable _
  have h1 : NoSolvableRadical (szEmbed hK (algebraMap K L)).range :=
    noSolvableRadical_range hns _ (szEmbed_injective hK _)
  rw [← hrange] at h1
  have h2 : NoSolvableRadical Y₁ :=
    noSolvableRadical_of_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective h1
  have h3 : NoSolvableRadical P'₀ :=
    noSolvableRadical_of_map (B2eQ L).toMonoidHom (B2eQ L).injective h2
  have h4 := noSolvableRadical_map (B2Q L).subtype (B2Q L).subtype_injective h3
  rw [hP'eq] at h4
  exact h4

end Main

end B2

end CFSG.RankThree.PartOne.KLR
