module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveCentral
public import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Spinor
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

theorem fiveForm_castSucc_self {k : ℕ} {ε : Bool} (i : Fin k) :
    fiveForm k ε (Pi.single i.castSucc 1) (Pi.single i.castSucc 1) = 1 := by
  rw [fiveForm_single, if_neg i.castSucc_lt_last.ne, Pi.single_eq_same, mul_one]

theorem fiveForm_castSucc_castSucc {k : ℕ} {ε : Bool} {i j : Fin k} (hij : i ≠ j) :
    fiveForm k ε (Pi.single i.castSucc 1) (Pi.single j.castSucc 1) = 0 := by
  rw [fiveForm_single, Pi.single_eq_of_ne' (fun h => hij (Fin.castSucc_injective k h)),
    mul_zero]

theorem fiveForm_castSucc_last {k : ℕ} {ε : Bool} (i : Fin k) :
    fiveForm k ε (Pi.single i.castSucc 1) (Pi.single (Fin.last k) 1) = 0 := by
  rw [fiveForm_single, if_pos rfl, Pi.single_eq_of_ne' i.castSucc_lt_last.ne, mul_zero]

theorem fiveForm_last_castSucc {k : ℕ} {ε : Bool} (i : Fin k) :
    fiveForm k ε (Pi.single (Fin.last k) 1) (Pi.single i.castSucc 1) = 0 := by
  rw [fiveForm_comm, fiveForm_castSucc_last i]

theorem fiveReflOf_mulVec_self {k : ℕ} {ε : Bool} {u : Fin (k + 1) → ZMod 5}
    (hu : fiveForm k ε u u ≠ 0) :
    (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u = -u := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [fiveReflOf_mulVec]
  have hcoe : 2 * fiveForm k ε u u * (fiveForm k ε u u)⁻¹ = 2 := by
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
  rw [hcoe]
  module

theorem fiveReflOf_mulVec_eq_self_of_orthogonal {k : ℕ} {ε : Bool}
    {x y : Fin (k + 1) → ZMod 5} (h : fiveForm k ε y x = 0) :
    (fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y = y := by
  rw [fiveReflOf_mulVec, h]
  simp

theorem fiveReflOf_commute_of_orthogonal {k : ℕ} {ε π : Bool}
    {u v : Fin (k + 1) → ZMod 5} (hu : fiveForm k ε u u ≠ 0)
    (hπu : IsSquare (fiveForm k ε u u) ↔ π = true) (huv : fiveForm k ε u v = 0) :
    Commute (fiveReflOf k ε u) (fiveReflOf k ε v) := by
  have hmem_u : fiveReflOf k ε u ∈ fiveReflections k ε π := fiveReflOf_mem hu hπu
  have hvu : fiveForm k ε v u = 0 := by rw [fiveForm_comm]; exact huv
  have hru_v : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v = v :=
    fiveReflOf_mulVec_eq_self_of_orthogonal hvu
  have hconj := conj_fiveReflOf (fiveForm_mulVec_of_mem (Subgroup.subset_closure hmem_u)) v
  rw [hru_v] at hconj
  show fiveReflOf k ε u * fiveReflOf k ε v = fiveReflOf k ε v * fiveReflOf k ε u
  have h2 := congrArg (fun x => x * fiveReflOf k ε u) hconj
  rwa [mul_assoc, inv_mul_cancel, mul_one] at h2

theorem exists_commuting_fiveReflections_notMem_center {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ∃ ra rb : fiveReflectionGroup k ε π,
      (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
      (rb : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ∧
      Commute ra rb ∧ ra ≠ rb ∧ ra * rb ∉ Subgroup.center (fiveReflectionGroup k ε π) := by
  have hk0 : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  have hk3 : 3 < k := by omega
  let i0 : Fin k := ⟨0, hk0⟩
  let i1 : Fin k := ⟨1, hk1⟩
  let i2 : Fin k := ⟨2, hk2⟩
  let i3 : Fin k := ⟨3, hk3⟩
  have h01 : i0 ≠ i1 := by
    intro h; have h' := congrArg Fin.val h; simp only [i0, i1] at h'; omega
  have h01c : i0.castSucc ≠ i1.castSucc := fun h => h01 (Fin.castSucc_injective k h)
  have h02 : i0 ≠ i2 := by
    intro h; have h' := congrArg Fin.val h; simp only [i0, i2] at h'; omega
  have h03 : i0 ≠ i3 := by
    intro h; have h' := congrArg Fin.val h; simp only [i0, i3] at h'; omega
  have h12 : i1 ≠ i2 := by
    intro h; have h' := congrArg Fin.val h; simp only [i1, i2] at h'; omega
  have h13 : i1 ≠ i3 := by
    intro h; have h' := congrArg Fin.val h; simp only [i1, i3] at h'; omega
  have h23 : i2 ≠ i3 := by
    intro h; have h' := congrArg Fin.val h; simp only [i2, i3] at h'; omega
  cases π
  ·
    let u : Fin (k + 1) → ZMod 5 := Pi.single i0.castSucc 1 + Pi.single i1.castSucc 1
    let v : Fin (k + 1) → ZMod 5 := Pi.single i2.castSucc 1 + Pi.single i3.castSucc 1
    let w : Fin (k + 1) → ZMod 5 := Pi.single (Fin.last k) 1
    have hu_norm : fiveForm k ε u u = 2 := by
      dsimp only [u]
      rw [fiveForm_add_right, fiveForm_add_left, fiveForm_add_left,
        fiveForm_castSucc_self i0, fiveForm_castSucc_castSucc h01.symm,
        fiveForm_castSucc_castSucc h01, fiveForm_castSucc_self i1]
      decide
    have hv_norm : fiveForm k ε v v = 2 := by
      dsimp only [v]
      rw [fiveForm_add_right, fiveForm_add_left, fiveForm_add_left,
        fiveForm_castSucc_self i2, fiveForm_castSucc_castSucc h23.symm,
        fiveForm_castSucc_castSucc h23, fiveForm_castSucc_self i3]
      decide
    have hu_ne : fiveForm k ε u u ≠ 0 := by rw [hu_norm]; decide
    have hv_ne : fiveForm k ε v v ≠ 0 := by rw [hv_norm]; decide
    have huv : fiveForm k ε u v = 0 := by
      dsimp only [u, v]
      rw [fiveForm_add_right, fiveForm_add_left, fiveForm_add_left,
        fiveForm_castSucc_castSucc h02, fiveForm_castSucc_castSucc h03,
        fiveForm_castSucc_castSucc h12, fiveForm_castSucc_castSucc h13]
      decide
    have hwu : fiveForm k ε w u = 0 := by
      dsimp only [w, u]
      rw [fiveForm_add_right, fiveForm_last_castSucc i0, fiveForm_last_castSucc i1, add_zero]
    have hwv : fiveForm k ε w v = 0 := by
      dsimp only [w, v]
      rw [fiveForm_add_right, fiveForm_last_castSucc i2, fiveForm_last_castSucc i3, add_zero]
    have hπu : IsSquare (fiveForm k ε u u) ↔ false = true := by rw [hu_norm]; decide
    have hπv : IsSquare (fiveForm k ε v v) ↔ false = true := by rw [hv_norm]; decide
    have hmem_u : fiveReflOf k ε u ∈ fiveReflections k ε false := fiveReflOf_mem hu_ne hπu
    have hmem_v : fiveReflOf k ε v ∈ fiveReflections k ε false := fiveReflOf_mem hv_ne hπv
    have hcomm : Commute (fiveReflOf k ε u) (fiveReflOf k ε v) :=
      fiveReflOf_commute_of_orthogonal hu_ne hπu huv
    have hru : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u = -u :=
      fiveReflOf_mulVec_self hu_ne
    have hrv_u : (fiveReflOf k ε v : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u = u :=
      fiveReflOf_mulVec_eq_self_of_orthogonal huv
    have hrv_w : (fiveReflOf k ε v : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w :=
      fiveReflOf_mulVec_eq_self_of_orthogonal hwv
    have hru_w : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w :=
      fiveReflOf_mulVec_eq_self_of_orthogonal hwu
    have hu0 : u i0.castSucc = 1 := by
      dsimp only [u]
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01c, add_zero]
    have hneg_u : (-u : Fin (k + 1) → ZMod 5) ≠ u := by
      intro h
      have h0 := congrFun h i0.castSucc
      rw [Pi.neg_apply, hu0] at h0
      exact absurd h0 (by decide)
    have hwlast : w (Fin.last k) = 1 := by dsimp only [w]; exact Pi.single_eq_same _ _
    have hneg_w : (-w : Fin (k + 1) → ZMod 5) ≠ w := by
      intro h
      have h0 := congrFun h (Fin.last k)
      rw [Pi.neg_apply, hwlast] at h0
      exact absurd h0 (by decide)
    have hne_uv : fiveReflOf k ε u ≠ fiveReflOf k ε v := by
      intro h
      have h_u := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u) h
      rw [hru, hrv_u] at h_u
      exact hneg_u h_u
    let ra : fiveReflectionGroup k ε false :=
      ⟨fiveReflOf k ε u, Subgroup.subset_closure hmem_u⟩
    let rb : fiveReflectionGroup k ε false :=
      ⟨fiveReflOf k ε v, Subgroup.subset_closure hmem_v⟩
    refine ⟨ra, rb, hmem_u, hmem_v, ?_, ?_, ?_⟩
    · rw [Commute]; exact Subtype.ext hcomm
    · intro h; exact hne_uv (congrArg Subtype.val h)
    · intro hz
      rcases (mem_center_fiveReflectionGroup_iff hk ε false _).mp hz with h1 | h1
      · have h1' : (fiveReflOf k ε u * fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) = 1 := by
          simpa using h1
        have hu_eq := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u) h1'
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hrv_u, hru,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at hu_eq
        exact hneg_u hu_eq
      · have h1' : (fiveReflOf k ε u * fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
          simpa using h1
        have hw_eq := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) h1'
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hrv_w, hru_w] at hw_eq
        have hneg1 : (((-1 : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) = -w := by
          rw [Units.coe_neg_one, Matrix.neg_mulVec, Matrix.one_mulVec] <;> rfl
        rw [hneg1] at hw_eq
        exact hneg_w hw_eq.symm
  ·
    let u : Fin (k + 1) → ZMod 5 := Pi.single i0.castSucc 1
    let v : Fin (k + 1) → ZMod 5 := Pi.single i1.castSucc 1
    let w : Fin (k + 1) → ZMod 5 := Pi.single (Fin.last k) 1
    have hu_norm : fiveForm k ε u u = 1 := by
      dsimp only [u]; exact fiveForm_castSucc_self i0
    have hv_norm : fiveForm k ε v v = 1 := by
      dsimp only [v]; exact fiveForm_castSucc_self i1
    have hu_ne : fiveForm k ε u u ≠ 0 := by rw [hu_norm]; decide
    have hv_ne : fiveForm k ε v v ≠ 0 := by rw [hv_norm]; decide
    have huv : fiveForm k ε u v = 0 := by
      dsimp only [u, v]; exact fiveForm_castSucc_castSucc h01
    have hwu : fiveForm k ε w u = 0 := by
      dsimp only [w, u]; exact fiveForm_last_castSucc i0
    have hwv : fiveForm k ε w v = 0 := by
      dsimp only [w, v]; exact fiveForm_last_castSucc i1
    have hπu : IsSquare (fiveForm k ε u u) ↔ true = true := by rw [hu_norm]; simp
    have hπv : IsSquare (fiveForm k ε v v) ↔ true = true := by rw [hv_norm]; simp
    have hmem_u : fiveReflOf k ε u ∈ fiveReflections k ε true := fiveReflOf_mem hu_ne hπu
    have hmem_v : fiveReflOf k ε v ∈ fiveReflections k ε true := fiveReflOf_mem hv_ne hπv
    have hcomm : Commute (fiveReflOf k ε u) (fiveReflOf k ε v) :=
      fiveReflOf_commute_of_orthogonal hu_ne hπu huv
    have hru : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u = -u :=
      fiveReflOf_mulVec_self hu_ne
    have hrv_u : (fiveReflOf k ε v : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u = u :=
      fiveReflOf_mulVec_eq_self_of_orthogonal huv
    have hrv_w : (fiveReflOf k ε v : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w :=
      fiveReflOf_mulVec_eq_self_of_orthogonal hwv
    have hru_w : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w = w :=
      fiveReflOf_mulVec_eq_self_of_orthogonal hwu
    have hu0 : u i0.castSucc = 1 := by
      dsimp only [u]; exact Pi.single_eq_same _ _
    have hneg_u : (-u : Fin (k + 1) → ZMod 5) ≠ u := by
      intro h
      have h0 := congrFun h i0.castSucc
      rw [Pi.neg_apply, hu0] at h0
      exact absurd h0 (by decide)
    have hwlast : w (Fin.last k) = 1 := by dsimp only [w]; exact Pi.single_eq_same _ _
    have hneg_w : (-w : Fin (k + 1) → ZMod 5) ≠ w := by
      intro h
      have h0 := congrFun h (Fin.last k)
      rw [Pi.neg_apply, hwlast] at h0
      exact absurd h0 (by decide)
    have hne_uv : fiveReflOf k ε u ≠ fiveReflOf k ε v := by
      intro h
      have h_u := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u) h
      rw [hru, hrv_u] at h_u
      exact hneg_u h_u
    let ra : fiveReflectionGroup k ε true :=
      ⟨fiveReflOf k ε u, Subgroup.subset_closure hmem_u⟩
    let rb : fiveReflectionGroup k ε true :=
      ⟨fiveReflOf k ε v, Subgroup.subset_closure hmem_v⟩
    refine ⟨ra, rb, hmem_u, hmem_v, ?_, ?_, ?_⟩
    · rw [Commute]; exact Subtype.ext hcomm
    · intro h; exact hne_uv (congrArg Subtype.val h)
    · intro hz
      rcases (mem_center_fiveReflectionGroup_iff hk ε true _).mp hz with h1 | h1
      · have h1' : (fiveReflOf k ε u * fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) = 1 := by
          simpa using h1
        have hu_eq := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u) h1'
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hrv_u, hru,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at hu_eq
        exact hneg_u hu_eq
      · have h1' : (fiveReflOf k ε u * fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
          simpa using h1
        have hw_eq := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) h1'
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hrv_w, hru_w] at hw_eq
        have hneg1 : (((-1 : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) = -w := by
          rw [Units.coe_neg_one, Matrix.neg_mulVec, Matrix.one_mulVec] <;> rfl
        rw [hneg1] at hw_eq
        exact hneg_w hw_eq.symm

theorem index_commutator_fiveReflectionGroup {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    (commutator (fiveReflectionGroup k ε π)).index = 2 := by
  obtain ⟨ra, rb, hra, hrb, hcomm, hne, _hnotmem⟩ :=
    exists_commuting_fiveReflections_notMem_center hk ε π
  set t : Abelianization (fiveReflectionGroup k ε π) := Abelianization.of ra with ht
  have hra2 : ra * ra = 1 := by
    obtain ⟨x, -, -, hrx⟩ := exists_eq_fiveReflOf hra
    apply Subtype.ext
    show (ra : GL (Fin (k + 1)) (ZMod 5)) * (ra : GL (Fin (k + 1)) (ZMod 5)) = 1
    rw [hrx]
    exact Units.ext (fiveReflMatrix_mul_self k ε x)
  have ht2 : t * t = 1 := by
    rw [ht]
    rw [← map_mul, hra2, map_one]
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hgen : ∀ g (hg : g ∈ fiveReflections k ε π),
      Abelianization.of (⟨g, Subgroup.subset_closure hg⟩ : fiveReflectionGroup k ε π) = t := by
    intro g hg
    obtain ⟨c, hc, hconj⟩ := isConj_of_mem_fiveReflections hk ε π hg hra
    have hconjR : (⟨c, hc⟩ : fiveReflectionGroup k ε π) *
        (⟨g, Subgroup.subset_closure hg⟩ : fiveReflectionGroup k ε π) *
        (⟨c, hc⟩ : fiveReflectionGroup k ε π)⁻¹ = ra := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hconj
    rw [ht, ← hconjR, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hmem : ∀ b : fiveReflectionGroup k ε π,
      Abelianization.of b = 1 ∨ Abelianization.of b = t := by
    intro b
    refine Subgroup.closure_induction
      (p := fun g (hg : g ∈ Subgroup.closure (fiveReflections k ε π)) =>
        Abelianization.of (⟨g, hg⟩ : fiveReflectionGroup k ε π) = 1 ∨
          Abelianization.of (⟨g, hg⟩ : fiveReflectionGroup k ε π) = t)
      ?_ ?_ ?_ ?_ b.2
    · intro g hg
      exact Or.inr (hgen g hg)
    · left
      change Abelianization.of (1 : fiveReflectionGroup k ε π) = 1
      exact map_one _
    · intro x y hx hy ihx ihy
      have hmul : Abelianization.of
            (⟨x * y, mul_mem hx hy⟩ : fiveReflectionGroup k ε π) =
          Abelianization.of (⟨x, hx⟩ : fiveReflectionGroup k ε π) *
            Abelianization.of (⟨y, hy⟩ : fiveReflectionGroup k ε π) := by
        rw [← map_mul]
        exact congrArg Abelianization.of (Subtype.ext rfl)
      rw [hmul]
      rcases ihx with hx1 | hx1 <;> rcases ihy with hy1 | hy1
      · left; rw [hx1, hy1, one_mul]
      · right; rw [hx1, hy1, one_mul]
      · right; rw [hx1, hy1, mul_one]
      · left; rw [hx1, hy1, ht2]
    · intro x hx ihx
      have hinv : Abelianization.of
            (⟨x⁻¹, inv_mem hx⟩ : fiveReflectionGroup k ε π) =
          (Abelianization.of (⟨x, hx⟩ : fiveReflectionGroup k ε π))⁻¹ := by
        rw [← map_inv]
        exact congrArg Abelianization.of (Subtype.ext rfl)
      rw [hinv]
      rcases ihx with hx1 | hx1
      · left; rw [hx1, inv_one]
      · right; rw [hx1, ht_inv]
  apply (Subgroup.index_eq_two_iff_exists_notMem_and
    (H := commutator (fiveReflectionGroup k ε π))).mpr
  refine ⟨ra, ?_, fun b => ?_⟩
  · intro hmem'
    obtain ⟨x, hx, -, hrx⟩ := exists_eq_fiveReflOf hra
    have hdet : Matrix.GeneralLinearGroup.det (ra : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
      rw [hrx]
      exact det_fiveReflOf hx
    have h1 : Matrix.GeneralLinearGroup.det (ra : GL (Fin (k + 1)) (ZMod 5)) = 1 := by
      have := Abelianization.commutator_subset_ker
        (Matrix.GeneralLinearGroup.det.comp
          (fiveReflectionGroup k ε π).subtype :
            fiveReflectionGroup k ε π →* (ZMod 5)ˣ) hmem'
      simpa using this
    rw [hdet] at h1
    exact absurd h1 (by decide)
  · have hba : (b * ra ∈ commutator (fiveReflectionGroup k ε π)) ↔
        Abelianization.of (b * ra) = 1 := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    have hb : (b ∈ commutator (fiveReflectionGroup k ε π)) ↔
        Abelianization.of b = 1 := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    rw [hba, hb, map_mul]
    rcases hmem b with hb1 | hbt
    · right; exact hb1
    · left; rw [hbt, ← ht]; exact ht2

theorem det_fiveReflection {k : ℕ} {ε π : Bool} {r : fiveReflectionGroup k ε π}
    (hr : (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    Matrix.GeneralLinearGroup.det (r : GL (Fin (k + 1)) (ZMod 5)) = -1 := by
  obtain ⟨x, hx, -, hrx⟩ := exists_eq_fiveReflOf hr
  rw [hrx]
  exact det_fiveReflOf hx

theorem fiveReflection_mul_self {k : ℕ} {ε π : Bool} {r : fiveReflectionGroup k ε π}
    (hr : (r : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) : r * r = 1 := by
  obtain ⟨x, -, -, hrx⟩ := exists_eq_fiveReflOf hr
  apply Subtype.ext
  show (r : GL (Fin (k + 1)) (ZMod 5)) * (r : GL (Fin (k + 1)) (ZMod 5)) = 1
  rw [hrx]
  exact Units.ext (fiveReflMatrix_mul_self k ε x)

theorem det_neg_one_five (k : ℕ) :
    Matrix.GeneralLinearGroup.det (-1 : GL (Fin (k + 1)) (ZMod 5)) =
      (-1 : (ZMod 5)ˣ) ^ (k + 1) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one,
    Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
  rfl

theorem commutator_subset_ker_det_fiveReflection {k : ℕ} (ε π : Bool) :
    commutator (fiveReflectionGroup k ε π) ≤
      (Matrix.GeneralLinearGroup.det.comp (fiveReflectionGroup k ε π).subtype).ker :=
  Abelianization.commutator_subset_ker _

theorem center_fiveReflectionGroup_eq_bot {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (hneg : (-1 : GL (Fin (k + 1)) (ZMod 5)) ∉ fiveReflectionGroup k ε π) :
    Subgroup.center (fiveReflectionGroup k ε π) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rcases (mem_center_fiveReflectionGroup_iff hk ε π g).mp hg with h | h
  · exact Subtype.ext h
  · exact absurd (h ▸ g.2) hneg

end CFSG.OddTranspositions.PartThree
