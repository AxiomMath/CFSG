module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofMono
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix
open scoped commutatorElement

theorem eq_of_eq_mul_commute {Q H : Type*} [Group Q] [Group H] (hQ : Group.IsPerfect Q)
    (f g : Q →* H) (w : Q → H) (hw : ∀ x, f x = g x * w x)
    (hwc : ∀ x y, w x * g y = g y * w x) (hww : ∀ x y, w x * w y = w y * w x) (x : Q) :
    f x = g x := by
  have hle : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ MonoidHom.eqLocus f g := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    change f ⁅a, b⁆ = g ⁅a, b⁆
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hw a, hw b,
      map_mul, map_mul, map_mul, map_inv, map_inv]
    have e2 : w a * g b = g b * w a := hwc a b
    have e3 : w a * w b = w b * w a := hww a b
    have e5 : w b * (g a)⁻¹ = (g a)⁻¹ * w b := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hwc b a, mul_assoc, mul_inv_cancel, mul_one]
    calc g a * w a * (g b * w b) * (g a * w a)⁻¹ * (g b * w b)⁻¹
        = g a * (w a * g b) * w b * (w a)⁻¹ * (g a)⁻¹ * (w b)⁻¹ * (g b)⁻¹ := by group
      _ = g a * (g b * w a) * w b * (w a)⁻¹ * (g a)⁻¹ * (w b)⁻¹ * (g b)⁻¹ := by rw [e2]
      _ = g a * g b * ((w a * w b) * (w a)⁻¹) * (g a)⁻¹ * (w b)⁻¹ * (g b)⁻¹ := by group
      _ = g a * g b * ((w b * w a) * (w a)⁻¹) * (g a)⁻¹ * (w b)⁻¹ * (g b)⁻¹ := by rw [e3]
      _ = g a * g b * (w b * (g a)⁻¹) * (w b)⁻¹ * (g b)⁻¹ := by group
      _ = g a * g b * ((g a)⁻¹ * w b) * (w b)⁻¹ * (g b)⁻¹ := by rw [e5]
      _ = g a * g b * (g a)⁻¹ * (g b)⁻¹ := by group
  have htop : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = (⊤ : Subgroup Q) := by
    rw [← commutator_def]
    exact @Group.IsPerfect.commutator_eq_top Q _ hQ
  rw [htop] at hle
  exact hle (Subgroup.mem_top x)

section Aut

variable {M : Type*} [Group M]

theorem mulAut_mul_coe {X : Subgroup M} {α β : MulAut X} {u v : M}
    (hα : ∀ m : X, ((α m : X) : M) = u * m * u⁻¹) (hβ : ∀ m : X, ((β m : X) : M) = v * m * v⁻¹)
    (m : X) : (((α * β) m : X) : M) = (u * v) * m * (u * v)⁻¹ := by
  rw [MulAut.mul_apply, hα, hβ]
  group

theorem mulAut_pow_coe {X : Subgroup M} {α : MulAut X} {u : M}
    (hα : ∀ m : X, ((α m : X) : M) = u * m * u⁻¹) (n : ℕ) (m : X) :
    (((α ^ n) m : X) : M) = u ^ n * m * (u ^ n)⁻¹ := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ]
    group

end Aut

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isQuasisimple_slPi_two (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : IsQuasisimple (slPi π 2 (p ^ f) K) := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  cases π
  · have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
    have : CharP K p := hK.unitary.charP
    have hq' : p ^ f % 3 = 2 := hq
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := p) (f := f) hcard
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := f) hcard
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 _ le_rfl
        (Or.inr (by rw [hF]; omega)) (Or.inr (by rw [hF]; omega)))
  · have hcard : Nat.card K = p ^ f := hK.card
    have hq' : p ^ f % 3 = 1 := hq
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (statedSLEquiv 2 K).symm
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
        (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega)))

@[expose] def diagTwo (μ : Kˣ) : GL (Fin 2) K :=
  ⟨diagonal ![(μ : K), ((μ⁻¹ : Kˣ) : K)], diagonal ![((μ⁻¹ : Kˣ) : K), (μ : K)],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem coe_diagTwo (μ : Kˣ) :
    ((diagTwo μ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![(μ : K), ((μ⁻¹ : Kˣ) : K)] :=
  rfl

@[expose] def wTwo : GL (Fin 2) K :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_wTwo : ((wTwo : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
  rfl

@[expose] def tTwo (x : K) : GL (Fin 2) K :=
  ⟨!![x, -1; 1, 0], !![0, 1; -1, x],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_tTwo (x : K) : ((tTwo x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x, -1; 1, 0] :=
  rfl

theorem diagTwo_mem_slPi (hK : PiField π p f K) {μ : Kˣ}
    (hμ : π = false → (μ : K) ^ (p ^ f + 1) = 1) : diagTwo μ ∈ slPi π 2 (p ^ f) K := by
  have hdet : ((diagTwo μ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [coe_diagTwo, det_diagonal, Fin.prod_univ_two]
    simp
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have h1 := hμ rfl
    have h2 : ((μ⁻¹ : Kˣ) : K) ^ (p ^ f + 1) = 1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, h1, inv_one]
    rw [coe_diagTwo, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, h.bar_apply]
      rw [← pow_succ, h1]
    · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one, h.bar_apply]
      rw [← pow_succ, h2]
  · rw [mem_slPi_true]
    exact hdet

theorem wTwo_mem_slPi (hK : PiField π p f K) : (wTwo : GL (Fin 2) K) ∈ slPi π 2 (p ^ f) K := by
  have hdet : ((wTwo : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [coe_wTwo, det_fin_two_of]
    ring
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_wTwo]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mem_slPi_true]
    exact hdet

theorem tTwo_mem_slPi_true (x : K) : tTwo x ∈ slPi true 2 (p ^ f) K := by
  rw [mem_slPi_true, coe_tTwo, det_fin_two_of]
  ring


theorem det_eq_one_of_mem_slPi (hK : PiField π p f K) {n : ℕ} {B : GL (Fin n) K}
    (hB : B ∈ slPi π n (p ^ f) K) : GeneralLinearGroup.det B = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h' => by subst h'; exact hK.unitary
  have := ((mem_slPi_iff hπ).mp hB).2
  exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, this, Units.val_one])

@[expose] noncomputable def blockConj (hK : PiField π p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) : slPi π 2 (p ^ f) K →* slPi π 3 (p ^ f) K where
  toFun B := ⟨h * blockHom (B : GL (Fin 2) K) * h⁻¹,
    conj_mem_slPi (fun h' => by subst h'; exact hK.unitary) hh
      (blockHom_mem_slPi hK (slPi_le_glPi (fun h' => by subst h'; exact hK.unitary) B.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' B B' := Subtype.ext (by
    simp only [Subgroup.coe_mul, map_mul]
    group)

theorem coe_blockConj (hK : PiField π p f K) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K)
    (B : slPi π 2 (p ^ f) K) :
    ((blockConj hK hh B : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      h * blockHom (B : GL (Fin 2) K) * h⁻¹ :=
  rfl

@[expose] noncomputable def blockProj (hK : PiField π p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) : slPi π 2 (p ^ f) K →* projImage (slPi π 3 (p ^ f) K) :=
  (projOf (slPi π 3 (p ^ f) K)).comp (blockConj hK hh)

theorem coe_blockProj (hK : PiField π p f K) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K)
    (B : slPi π 2 (p ^ f) K) :
    ((blockProj hK hh B : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (h * blockHom (B : GL (Fin 2) K) * h⁻¹) :=
  rfl

theorem blockProj_injective (hK : PiField π p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) : Function.Injective (blockProj hK hh) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have h1 := congrArg (fun x : projImage (slPi π 3 (p ^ f) K) =>
    (x : ProjGenLinGroup (Fin 3) K)) hB
  simp only [coe_blockProj, Subgroup.coe_one] at h1
  have h2 := conj_mem_statedScalars_iff.mp (mk_eq_one_iff_mem_statedScalars.mp h1)
  exact Subtype.ext (eq_one_of_blockHom_mem_statedScalars (det_eq_one_of_mem_slPi hK B.2) h2)

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
