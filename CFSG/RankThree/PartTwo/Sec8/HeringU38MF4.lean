module

public import CFSG.GH74.KGroups.FieldGF

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG.GH74.KGroups

abbrev F := GF4

@[expose] def ωF : F := GF4.ofNat' 2

@[expose] def ω2F : F := GF4.ofNat' 3

@[expose] def cj (x : F) : F := x * x

structure V3 where
  x : F
  y : F
  z : F

@[expose] def V3.toProd (v : V3) : F × F × F := (v.x, v.y, v.z)

theorem V3.toProd_injective : Function.Injective V3.toProd := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [V3.toProd, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

instance : DecidableEq V3 := fun u v =>
  decidable_of_iff (u.toProd = v.toProd) V3.toProd_injective.eq_iff

structure Mat3 where
  a00 : F
  a01 : F
  a02 : F
  a10 : F
  a11 : F
  a12 : F
  a20 : F
  a21 : F
  a22 : F

instance : DecidableEq Mat3 := fun A B =>
  decidable_of_iff (A.a00 = B.a00 ∧ A.a01 = B.a01 ∧ A.a02 = B.a02 ∧ A.a10 = B.a10 ∧
    A.a11 = B.a11 ∧ A.a12 = B.a12 ∧ A.a20 = B.a20 ∧ A.a21 = B.a21 ∧ A.a22 = B.a22)
    ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ => by
      cases A; cases B; simp_all,
      fun h => by subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

namespace Mat3

@[expose] def mul (A B : Mat3) : Mat3 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20,
   A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
   A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
   A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20,
   A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
   A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
   A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20,
   A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
   A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

@[expose] def one : Mat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def cjT (A : Mat3) : Mat3 :=
  ⟨cj A.a00, cj A.a10, cj A.a20, cj A.a01, cj A.a11, cj A.a21, cj A.a02, cj A.a12, cj A.a22⟩

@[expose] def smul (c : F) (A : Mat3) : Mat3 :=
  ⟨c * A.a00, c * A.a01, c * A.a02, c * A.a10, c * A.a11, c * A.a12, c * A.a20, c * A.a21,
    c * A.a22⟩

@[expose] def diag (a b c : F) : Mat3 := ⟨a, 0, 0, 0, b, 0, 0, 0, c⟩

@[expose] def mv (A : Mat3) (v : V3) : V3 :=
  ⟨A.a00 * v.x + A.a01 * v.y + A.a02 * v.z, A.a10 * v.x + A.a11 * v.y + A.a12 * v.z,
    A.a20 * v.x + A.a21 * v.y + A.a22 * v.z⟩

@[expose] def det (A : Mat3) : F :=
  A.a00 * (A.a11 * A.a22 - A.a12 * A.a21) - A.a01 * (A.a10 * A.a22 - A.a12 * A.a20) +
    A.a02 * (A.a10 * A.a21 - A.a11 * A.a20)

@[expose] def ofCols (u v w : V3) : Mat3 :=
  ⟨u.x, v.x, w.x, u.y, v.y, w.y, u.z, v.z, w.z⟩

@[expose] def pow (A : Mat3) : ℕ → Mat3
  | 0 => one
  | n + 1 => mul (pow A n) A

instance : Mul Mat3 := ⟨mul⟩
instance : One Mat3 := ⟨one⟩

instance : Pow Mat3 ℕ := ⟨pow⟩

@[expose] def commGen (D t : Mat3) : Mat3 := t * (D * t * cjT D).cjT

end Mat3

@[expose] def dotc (u v : V3) : F := cj u.x * v.x + cj u.y * v.y + cj u.z * v.z

@[expose] def IsU (A : Mat3) : Prop := A.cjT * A = 1

instance (A : Mat3) : Decidable (IsU A) := by unfold IsU; infer_instance

@[expose] def allF : List F := [0, 1, ωF, ω2F]

@[expose] def allV : List V3 :=
  allF.flatMap fun a => allF.flatMap fun b => allF.map fun c => ⟨a, b, c⟩

theorem mem_allF (a : F) : a ∈ allF := by revert a; decide +kernel

theorem mem_allV (v : V3) : v ∈ allV := by
  obtain ⟨a, b, c⟩ := v
  have ha := mem_allF a
  have hb := mem_allF b
  have hc := mem_allF c
  simp only [allV, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

@[expose] def RegF (B : Mat3) : Prop :=
  ∃ u ∈ allV, (Mat3.ofCols u (B.mv u) (B.mv (B.mv u))).det ≠ 0

instance (B : Mat3) : Decidable (RegF B) := by unfold RegF; infer_instance

@[expose] def perm3 (p q r : Fin 3) : Mat3 :=
  let e : Fin 3 → V3 := fun i =>
    ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0⟩
  Mat3.ofCols (e p) (e q) (e r)

@[expose] def fourier : Mat3 := ⟨1, 1, 1, ωF, ω2F, 1, ω2F, ωF, 1⟩

@[expose] def cands : List Mat3 :=
  1 :: perm3 0 2 1 :: perm3 2 1 0 ::
    (allF.filter (· ≠ 0)).flatMap fun a => (allF.filter (· ≠ 0)).flatMap fun b =>
      (allF.filter (· ≠ 0)).map fun c => Mat3.diag a b c * fourier

@[expose] def ClassGoal (B : Mat3) : Prop :=
  (∃ c ∈ allF, c ≠ 0 ∧ B * B * B = Mat3.smul c 1) → (∀ a ∈ allF, B ≠ Mat3.smul a 1) →
    RegF B ∨ ∃ H ∈ cands, ∃ l ∈ allF, ∃ m ∈ allF, l ≠ 0 ∧ m ≠ 0 ∧ l ≠ m ∧
      B * H = H * Mat3.diag l l m

instance (B : Mat3) : Decidable (ClassGoal B) := by unfold ClassGoal; infer_instance

theorem classify_cols :
    ∀ c0 ∈ allV, dotc c0 c0 = 1 → ∀ c1 ∈ allV, dotc c1 c1 = 1 → dotc c0 c1 = 0 →
      ∀ c2 ∈ allV, dotc c2 c2 = 1 → dotc c0 c2 = 0 → dotc c1 c2 = 0 →
        ClassGoal (Mat3.ofCols c0 c1 c2) := by decide +kernel

theorem IsU.cols {B : Mat3} (hB : IsU B) :
    dotc ⟨B.a00, B.a10, B.a20⟩ ⟨B.a00, B.a10, B.a20⟩ = 1 ∧
    dotc ⟨B.a01, B.a11, B.a21⟩ ⟨B.a01, B.a11, B.a21⟩ = 1 ∧
    dotc ⟨B.a02, B.a12, B.a22⟩ ⟨B.a02, B.a12, B.a22⟩ = 1 ∧
    dotc ⟨B.a00, B.a10, B.a20⟩ ⟨B.a01, B.a11, B.a21⟩ = 0 ∧
    dotc ⟨B.a00, B.a10, B.a20⟩ ⟨B.a02, B.a12, B.a22⟩ = 0 ∧
    dotc ⟨B.a01, B.a11, B.a21⟩ ⟨B.a02, B.a12, B.a22⟩ = 0 := by
  have h00 := congrArg Mat3.a00 hB
  have h11 := congrArg Mat3.a11 hB
  have h22 := congrArg Mat3.a22 hB
  have h01 := congrArg Mat3.a01 hB
  have h02 := congrArg Mat3.a02 hB
  have h12 := congrArg Mat3.a12 hB
  exact ⟨h00, h11, h22, h01, h02, h12⟩

theorem classify {B : Mat3} (hB : IsU B) : ClassGoal B := by
  obtain ⟨h0, h1, h2, h01, h02, h12⟩ := hB.cols
  have hB' : B = Mat3.ofCols ⟨B.a00, B.a10, B.a20⟩ ⟨B.a01, B.a11, B.a21⟩
      ⟨B.a02, B.a12, B.a22⟩ := rfl
  rw [hB']
  exact classify_cols _ (mem_allV _) h0 _ (mem_allV _) h1 h01 _ (mem_allV _) h2 h02 h12

theorem cands_unitary : ∀ H ∈ cands, IsU H := by decide +kernel

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
