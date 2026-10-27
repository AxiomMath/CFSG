module

public import CFSG.Quasithin.Background.G2UCodes
public import CFSG.Quasithin.Background.G2URoots

public section

namespace CFSG.Quasithin.G2U

open CFSG.Blueprint.Chevalley

variable (R : Type*) [CommRing R]

@[expose] def ind (a x : Label .G2) : R :=
  if a = x then 1 else 0

@[expose] def rv (β : Fin Tag.G2.rank → ℤ) : Label .G2 → R
  | .inl _ => 0
  | .inr α => if α.1 = β then 1 else 0

@[expose] def colX (i : Fin Tag.G2.rank) (c : R) : Label .G2 → Label .G2 → R
  | .inl j, x => ind R (.inl j) x + ((Tag.G2.cartan j i).natAbs : R) * c * rv R (Pi.single i 1) x
  | .inr α, x =>
    if α.1 = Pi.single i 1 then ind R (.inr α) x
    else if α.1 = -Pi.single i 1 then
      ind R (.inr α) x + c * ind R (.inl i) x + c ^ 2 * rv R (Pi.single i 1) x
    else ∑ k ∈ Finset.range (su i α.1 + 1),
      ((sd i α.1 + k).choose k : R) * c ^ k * rv R (α.1 + (k : ℤ) • Pi.single i 1) x

@[expose] def colY (i : Fin Tag.G2.rank) (c : R) : Label .G2 → Label .G2 → R
  | .inl j, x => ind R (.inl j) x + ((Tag.G2.cartan j i).natAbs : R) * c * rv R (-Pi.single i 1) x
  | .inr α, x =>
    if α.1 = -Pi.single i 1 then ind R (.inr α) x
    else if α.1 = Pi.single i 1 then
      ind R (.inr α) x + c * ind R (.inl i) x + c ^ 2 * rv R (-Pi.single i 1) x
    else ∑ k ∈ Finset.range (sd i α.1 + 1),
      ((su i α.1 + k).choose k : R) * c ^ k * rv R (α.1 - (k : ℤ) • Pi.single i 1) x

variable {R}

theorem rootVec_apply (β : Fin Tag.G2.rank → ℤ) (x : Label .G2) :
    rootVec .G2 R β x = rv R β x := by
  rcases x with j | ⟨α, hα⟩
  · simp only [rootVec, rv]
    split_ifs <;> simp
  · simp only [rootVec, rv]
    split_ifs with h1 h2 h2
    · subst h2
      simp
    · rw [Finsupp.single_apply, ite_eq_right_iff]
      intro h
      exact absurd (by cases h; rfl) h2
    · subst h2
      exact absurd hα h1
    · simp

theorem xOp_single_apply (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    xOp .G2 R i c (Finsupp.single b 1) x = colX R i c b x := by
  rw [xOp, Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [colX, ind, hVec, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, rootVec_apply, mul_assoc]
  · simp only [colX]
    by_cases h1 : α = Pi.single i 1
    · simp [h1, ind, Finsupp.single_apply]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : α = -Pi.single i 1
      · rw [ite_eq_left h2, ite_eq_left h2]
        simp only [ind, hVec, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
          rootVec_apply, smul_eq_mul]
      · rw [ite_eq_right h2, ite_eq_right h2, Finsupp.finsetSum_apply, stringUp_eq hα,
          stringDown_eq hα]
        simp only [Finsupp.smul_apply, rootVec_apply, smul_eq_mul]

theorem yOp_single_apply (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    yOp .G2 R i c (Finsupp.single b 1) x = colY R i c b x := by
  rw [yOp, Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [colY, ind, hVec, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, rootVec_apply, mul_assoc]
  · simp only [colY]
    by_cases h1 : α = -Pi.single i 1
    · simp [h1, ind, Finsupp.single_apply]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : α = Pi.single i 1
      · rw [ite_eq_left h2, ite_eq_left h2]
        simp only [ind, hVec, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
          rootVec_apply, smul_eq_mul]
      · rw [ite_eq_right h2, ite_eq_right h2, Finsupp.finsetSum_apply, stringUp_eq hα,
          stringDown_eq hα]
        simp only [Finsupp.smul_apply, rootVec_apply, smul_eq_mul]

variable {S : Type*} [CommRing S] (σ : R →+* S)

theorem map_ind (a x : Label .G2) : σ (ind R a x) = ind S a x := by
  simp only [ind]
  split_ifs <;> simp

theorem map_rv (β : Fin Tag.G2.rank → ℤ) (x : Label .G2) : σ (rv R β x) = rv S β x := by
  rcases x with j | α
  · simp [rv]
  · simp only [rv]
    split_ifs <;> simp

theorem map_colX (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    σ (colX R i c b x) = colX S i (σ c) b x := by
  rcases b with j | α
  · simp [colX, map_ind, map_rv]
  · simp only [colX]
    split_ifs <;> simp [map_ind, map_rv]

theorem map_colY (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    σ (colY R i c b x) = colY S i (σ c) b x := by
  rcases b with j | α
  · simp [colY, map_ind, map_rv]
  · simp only [colY]
    split_ifs <;> simp [map_ind, map_rv]

variable (R) in
@[expose] def XMat (i : Fin Tag.G2.rank) (c : R) : Matrix (Fin 14) (Fin 14) R :=
  Matrix.of fun a b => colX R i c (lab b) (lab a)

variable (R) in
@[expose] def YMat (i : Fin Tag.G2.rank) (c : R) : Matrix (Fin 14) (Fin 14) R :=
  Matrix.of fun a b => colY R i c (lab b) (lab a)

theorem map_XMat (i : Fin Tag.G2.rank) (c : R) : (XMat R i c).map σ = XMat S i (σ c) := by
  ext a b
  simp [XMat, map_colX]

theorem map_YMat (i : Fin Tag.G2.rank) (c : R) : (YMat R i c).map σ = YMat S i (σ c) := by
  ext a b
  simp [YMat, map_colY]

@[expose] def g0c : List ℕ :=
  [3, 2, 4, 24, 16, 416, 320, 128, 256, 1536, 1024, 2048, 12288, 8192]

@[expose] def g1c : List ℕ :=
  [1, 46, 36, 40, 592, 32, 64, 640, 7424, 512, 5120, 6144, 4096, 8192]

@[expose] def g2c : List ℕ :=
  [1, 3, 4, 8, 24, 32, 96, 128, 416, 512, 1536, 2048, 4096, 12288]

@[expose] def g3c : List ℕ :=
  [1, 2, 6, 10, 16, 46, 64, 144, 256, 592, 1280, 2304, 7424, 8192]

theorem XMat_zero_one : XMat (ZMod 2) (ix 0) 1 = dec2 g0c := by
  decide +kernel

theorem XMat_one_one : XMat (ZMod 2) (ix 1) 1 = dec2 g1c := by
  decide +kernel

theorem YMat_zero_one : YMat (ZMod 2) (ix 0) 1 = dec2 g2c := by
  decide +kernel

theorem YMat_one_one : YMat (ZMod 2) (ix 1) 1 = dec2 g3c := by
  decide +kernel

theorem XMat_zero : ∀ i : Fin Tag.G2.rank, XMat (ZMod 2) i 0 = 1 := by
  decide +kernel

theorem YMat_zero : ∀ i : Fin Tag.G2.rank, YMat (ZMod 2) i 0 = 1 := by
  decide +kernel

end CFSG.Quasithin.G2U
