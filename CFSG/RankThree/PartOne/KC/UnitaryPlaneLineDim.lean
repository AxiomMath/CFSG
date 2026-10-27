module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneDecomposition
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Type*} [Group P] [Fintype P] {p : ℕ}
  (ρ : P →* LinearMap.GeneralLinearGroup K V)

@[expose] def decompFamily (B : V →ₛₗ[σ] V →ₗ[K] K) (p : ℕ) :
    Option {L : Subgroup P // Nat.card L = p} → Submodule K V
  | none => fixedSpace ρ ⊤
  | some L => lineSpace ρ B L.1

omit [FiniteDimensional K V] in
theorem orth_decompFamily (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {i j : Option {L : Subgroup P // Nat.card L = p}} (hij : i ≠ j) {u w : V}
    (hu : u ∈ decompFamily ρ B p i) (hw : w ∈ decompFamily ρ B p j) : B u w = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some M => exact (orth_top_line ρ hB hu hw).1
  | some L =>
    cases j with
    | none => exact (orth_top_line ρ hB hw hu).2
    | some M =>
      have hne : L.1 ≠ M.1 := fun h => hij (by rw [Subtype.ext h])
      exact orth_line_line ρ hP hpK hρ hB hBl L.2 M.2 hne hu hw

omit [FiniteDimensional K V] in
theorem nondeg_decompFamily (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (i : Option {L : Subgroup P // Nat.card L = p}) :
    (B.domRestrict₁₂ (decompFamily ρ B p i) (decompFamily ρ B p i)).SeparatingLeft := by
  cases i with
  | none => exact separatingLeft_fixedTop ρ hP hpK hρ hB hBl
  | some L => exact separatingLeft_lineSpace ρ hP hpK hρ hB hBl L.2

open scoped _root_.Classical in
omit [FiniteDimensional K V] in
theorem isInternal_decompFamily (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    DirectSum.IsInternal (decompFamily ρ B p) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro v hvi hv
    have hle : (⨆ j, ⨆ (_ : j ≠ i), decompFamily ρ B p j) ≤
        (decompFamily ρ B p i).orthogonalBilin B := by
      refine iSup₂_le fun j hj w hw u hu => ?_
      exact orth_decompFamily ρ hP hpK hρ hB hBl (Ne.symm hj) hu hw
    have hv' := hle hv
    rw [Submodule.mem_orthogonalBilin] at hv'
    have hsep := nondeg_decompFamily ρ hP hpK hρ hB hBl i
    have := hsep ⟨v, hvi⟩ (fun y => by
      have h1 : B (y : V) v = 0 := hv' y y.2
      show B v (y : V) = 0
      rw [← (LinearMap.isSymm_def.mp hB) (y : V) v, h1, map_zero])
    exact congrArg Subtype.val this
  · rw [eq_top_iff]
    intro v _
    have h := sup_eq_top ρ hP hpK hρ hB hBl
    have hv : v ∈ fixedSpace ρ ⊤ ⊔ ⨆ L ∈ lines p P, lineSpace ρ B L := by rw [h]; trivial
    rw [Submodule.mem_sup] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    refine Submodule.add_mem _ (Submodule.mem_iSup_of_mem none ha) ?_
    have : (⨆ L ∈ lines p P, lineSpace ρ B L) ≤ ⨆ i, decompFamily ρ B p i := by
      refine iSup₂_le fun L hL => ?_
      exact le_iSup (decompFamily ρ B p) (some ⟨L, mem_lines.mp hL⟩)
    exact this hb

theorem finrank_eq_sum (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    Module.finrank K V = Module.finrank K (fixedSpace ρ ⊤) +
      ∑ L ∈ lines p P, Module.finrank K (lineSpace ρ B L) := by
  classical
  have hint := isInternal_decompFamily ρ hP hpK hρ hB hBl
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap (decompFamily ρ B p)) hint).finrank_eq
  rw [Module.finrank_directSum] at e
  rw [← e, Fintype.sum_option]
  congr 1
  rw [Finset.sum_subtype (lines p P) (fun L => mem_lines)]
  rfl


omit [FiniteDimensional K V] in
theorem fixedTop_inf_lineSpace (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (L : Subgroup P) : fixedSpace ρ ⊤ ⊓ lineSpace ρ B L = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv0, hvL⟩
  have hv' := hvL.2
  have h := separatingLeft_fixedTop ρ hP hpK hρ hB hBl ⟨v, hv0⟩ (fun y => by
    have h1 : B (y : V) v = 0 := hv' y y.2
    show B v (y : V) = 0
    rw [← (LinearMap.isSymm_def.mp hB) (y : V) v, h1, map_zero])
  exact (Submodule.mem_bot K).mpr (congrArg Subtype.val h)

omit [Fintype P] [FiniteDimensional K V] in
theorem exists_ne_one_mem (hp : p.Prime) {L : Subgroup P} (hL : Nat.card L = p) :
    ∃ x ∈ L, x ≠ 1 := by
  by_contra hall
  have hall' : ∀ x ∈ L, x = 1 := fun x hx => by
    by_contra hx1
    exact hall ⟨x, hx, hx1⟩
  have h1 : Nat.card L = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hall' a a.2).trans (hall' b b.2).symm)⟩, ⟨1⟩⟩
  rw [hL] at h1
  exact hp.one_lt.ne' h1

theorem dvd_finrank_lineSpace (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft) {e : ℕ}
    (hcop : Nat.Coprime e p)
    (hdim : ∀ x : P, x ≠ 1 →
      e ∣ Module.finrank K V - Module.finrank K (LinearMap.ker (act ρ x - 1)))
    {L : Subgroup P} (hL : L ∈ lines p P) : e ∣ Module.finrank K (lineSpace ρ B L) := by
  classical
  set S := ∑ M ∈ lines p P, Module.finrank K (lineSpace ρ B M) with hS
  set D0 := Module.finrank K (fixedSpace ρ ⊤) with hD0
  have hn := finrank_eq_sum ρ hP hpK hρ hB hBl
  have hle : ∀ M ∈ lines p P, Module.finrank K (lineSpace ρ B M) ≤ S := fun M hM =>
    Finset.single_le_sum (f := fun M => Module.finrank K (lineSpace ρ B M))
      (fun _ _ => Nat.zero_le _) hM
  have hline : ∀ M ∈ lines p P, e ∣ S - Module.finrank K (lineSpace ρ B M) := by
    intro M hM
    obtain ⟨x, hxM, hx1⟩ := exists_ne_one_mem hP.prime (mem_lines.mp hM)
    have h1 := hdim x hx1
    rw [ker_act_sub_one_eq ρ hP hpK hρ hB hBl (mem_lines.mp hM) hxM hx1] at h1
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ ⊤) (lineSpace ρ B M)
    rw [fixedTop_inf_lineSpace ρ hP hpK hρ hB hBl M, finrank_bot, add_zero] at h2
    rw [h2] at h1
    have h3 : Module.finrank K V - (D0 + Module.finrank K (lineSpace ρ B M)) =
        S - Module.finrank K (lineSpace ρ B M) := by omega
    rwa [h3] at h1
  have hsum : e ∣ ∑ M ∈ lines p P, (S - Module.finrank K (lineSpace ρ B M)) :=
    Finset.dvd_sum hline
  have hsum2 : ∑ M ∈ lines p P, (S - Module.finrank K (lineSpace ρ B M)) = p * S := by
    rw [Finset.sum_tsub_distrib _ hle, Finset.sum_const, hP.card_lines, smul_eq_mul, ← hS,
      Nat.succ_mul, Nat.add_sub_cancel, mul_comm]
  rw [hsum2] at hsum
  have hS' : e ∣ S := hcop.dvd_of_dvd_mul_left hsum
  have := Nat.dvd_sub hS' (hline L hL)
  rwa [Nat.sub_sub_self (hle L hL)] at this

end CFSG.RankThree.PartOne.KCUnitaryPlane
