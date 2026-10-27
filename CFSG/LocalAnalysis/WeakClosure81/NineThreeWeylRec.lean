module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFrame
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeEight
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonClass

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Cox
open Subgroup
open scoped Pointwise commutatorElement symmDiff

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def weylD4Refl : Set ↥weylD4 :=
  {σ | ∃ (i j : Fin 4) (b : Bool), i ≠ j ∧ (σ : Equiv.Perm (Fin 4 × Bool)) =
    Equiv.swap (i, false) (j, b) * Equiv.swap (i, true) (j, !b)}

private theorem nine3_star3T_labelled {Q : Type*} [Group Q] [Finite Q] {Δ : Set Q}
    (h : Star3T.IsTT Δ) (hS : Star3T.IsStar Δ) {d a : Q} (hd : d ∈ Δ) (ha : a ∈ Δ)
    (hc : ¬ Star3T.Conn Δ d a) (hk : (Star3T.cent Δ d).ncard = 4)
    (hcard : 16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent Δ d)))
    {M : CoxeterMatrix (Fin 4)} (hM : ∀ i j, M.M i j = MD4 i j) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) :
    ∃ e : W ≃* Q, ∀ x, x ∈ Δ ↔ ∃ w : W, x = e (w * cs.simple 0 * w⁻¹) := by
  have hpl := Star3T.isPlane_of_not_conn hd ha hc
  have hcl : ∀ u ∈ Star3T.cent Δ d, ∀ v ∈ Star3T.cent Δ d, u * v = v * u := fun u hu v hv =>
    h.isClique_cent hS hd ha hc hu hv
  have hbr : ∀ x ∈ Star3T.cent Δ d, x * a * x = a * x * a := fun x hx =>
    h.braid hx.1 ha (Star3T.noncomm_of_mem_cent hpl hx)
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp (by omega : 2 < (Star3T.cent Δ d).ncard)
  have hz : x₁ * (x₂ * (x₃ * a * x₃) * x₂) * x₁ ∈ Star3T.cent Δ (d * a * d) := by
    have hpl' : Star3T.IsPlane Δ d (d * a * d) a := h.isPlane_rot hpl
    have u3 : x₃ * a * x₃ ∈ Star3T.cent Δ (d * a * d) :=
      h.cent_conj_mem hS hpl h₃ (Star3T.self_mem_cent ha)
    have u2 : x₂ * (x₃ * a * x₃) * x₂ ∈ Star3T.cent Δ a :=
      h.cent_conj_mem hS hpl' h₂ u3
    exact h.cent_conj_mem hS hpl h₁ u2
  have himg := h.cent_eq_image hS (h.isPlane_swap hpl)
  rw [himg] at hz
  obtain ⟨x₄, h₄, hx₄⟩ := hz
  have hx₄' : a * x₄ * a = (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) := by
    have := hx₄
    simp only at this
    rw [this]
    simp only [mul_assoc]
  have c12 : x₁ * x₂ = x₂ * x₁ := hcl _ h₁ _ h₂
  have c13 : x₁ * x₃ = x₃ * x₁ := hcl _ h₁ _ h₃
  have c23 : x₂ * x₃ = x₃ * x₂ := hcl _ h₂ _ h₃
  have n1 : x₄ ≠ x₁ := fun e => by
    rw [e] at hx₄'
    exact h23 (Star3T.eq_of_conj_eq h h₁.1 h₂.1 h₃.1 (hbr _ h₁) (hbr _ h₂) (hbr _ h₃) hx₄')
  have n2 : x₄ ≠ x₂ := fun e => by
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₂ * x₁ * x₃ := by rw [c12]
    have e2 : x₃ * x₂ * x₁ = x₃ * x₁ * x₂ := by
      calc x₃ * x₂ * x₁ = x₃ * (x₂ * x₁) := mul_assoc _ _ _
        _ = x₃ * (x₁ * x₂) := by rw [← c12]
        _ = x₃ * x₁ * x₂ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h13 (Star3T.eq_of_conj_eq h h₂.1 h₁.1 h₃.1 (hbr _ h₂) (hbr _ h₁) (hbr _ h₃) hx₄')
  have n3 : x₄ ≠ x₃ := fun e => by
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₃ * x₁ * x₂ := by
      calc x₁ * x₂ * x₃ = x₁ * (x₂ * x₃) := mul_assoc _ _ _
        _ = x₁ * (x₃ * x₂) := by rw [c23]
        _ = x₁ * x₃ * x₂ := (mul_assoc _ _ _).symm
        _ = x₃ * x₁ * x₂ := by rw [c13]
    have e2 : x₃ * x₂ * x₁ = x₂ * x₁ * x₃ := by
      calc x₃ * x₂ * x₁ = x₂ * x₃ * x₁ := by rw [← c23]
        _ = x₂ * (x₃ * x₁) := mul_assoc _ _ _
        _ = x₂ * (x₁ * x₃) := by rw [← c13]
        _ = x₂ * x₁ * x₃ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h12 (Star3T.eq_of_conj_eq h h₃.1 h₁.1 h₂.1 (hbr _ h₃) (hbr _ h₁) (hbr _ h₂) hx₄')
  have hcent : Star3T.cent Δ d = {x₁, x₂, x₃, x₄} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    · have hn : ({x₁, x₂, x₃, x₄} : Set Q).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [h12, h13, n1.symm]),
          Set.ncard_insert_of_notMem (by simp [h23, n2.symm]), Set.ncard_pair n3.symm]
      omega
  let f : Fin 4 → Q := ![x₁, a, x₂, x₃]
  have hsq : ∀ i, f i * f i = 1 := by
    intro i
    fin_cases i
    · exact h.mul_self x₁ h₁.1
    · exact h.mul_self a ha
    · exact h.mul_self x₂ h₂.1
    · exact h.mul_self x₃ h₃.1
  have hcomm : ∀ i j, MD4 i j = 2 → f i * f j = f j * f i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact c12 | exact c12.symm | exact c13 | exact c13.symm
        | exact c23 | exact c23.symm
  have hbraid : ∀ i j, MD4 i j = 3 → f i * f j * f i = f j * f i * f j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact hbr _ h₁ | exact (hbr _ h₁).symm | exact hbr _ h₂
        | exact (hbr _ h₂).symm | exact hbr _ h₃ | exact (hbr _ h₃).symm
  have hR : IsRel M.M f := IsRel.of_eq hM ⟨hsq, hcomm, hbraid⟩
  have hlift : M.IsLiftable f :=
    hR.isLiftable (fun i j => by rw [hM]; fin_cases i <;> fin_cases j <;> decide)
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have hmem : ∀ i, f i ∈ Subgroup.closure (Set.range f) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    have m1 := hmem 0
    have ma := hmem 1
    have m2 := hmem 2
    have m3 := hmem 3
    have hp : (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) ∈ Subgroup.closure (Set.range f) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m2) m3) ma)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ m3 m2) m1)
    have haa := h.mul_self a ha
    have hx4 : x₄ ∈ Subgroup.closure (Set.range f) := by
      have e : x₄ = a * ((x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁)) * a := by
        rw [← hx₄']
        calc x₄ = (a * a) * x₄ * (a * a) := by rw [haa, one_mul, mul_one]
          _ = a * (a * x₄ * a) * a := by simp only [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ma hp) ma
    rw [eq_top_iff, ← h.closure_insert_cent_eq_top hS hpl, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ma
    · rw [hcent] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact m1
      · exact m2
      · exact m3
      · exact hx4
  obtain ⟨hfin, hW⟩ := finite_card_D4 hM cs
  have : Finite W := hfin
  have hQ : 192 ≤ Nat.card Q := by
    have h1 := h.natCard_eq_three_mul hS hpl
    have hle : Nat.card (Subgroup.closure (Star3T.cent Δ d)) ≤
        Nat.card (Subgroup.centralizer ({d} : Set Q)) :=
      Subgroup.card_le_of_le ((Subgroup.closure_le _).mpr (Star3T.IsTT.cent_subset_centralizer d))
    have : (Star3T.cent Δ d).ncard = 4 := hk
    rw [this] at h1
    omega
  obtain ⟨e, he⟩ := exists_mulEquiv_of_card_le cs f hlift hgen (by omega)
  refine ⟨e, ?_⟩
  intro x
  constructor
  · intro hx
    have hx1a : ¬ Star3T.Conn Δ x₁ a :=
      fun hcon => hc ((Star3T.conn_of_mem_cent hd h₁).trans hcon)
    obtain ⟨g, hg⟩ := h.exists_conj_of_not_conn h₁.1 ha hx1a x hx
    refine ⟨e.symm g, ?_⟩
    rw [hg, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, he 0]
    rfl
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact h.conj_mem' (by rw [he 0]; exact h₁.1) _

private def nine3PermRef (i j : Fin 4) (b : Bool) : Equiv.Perm (Fin 4 × Bool) :=
  Equiv.swap (i, false) (j, b) * Equiv.swap (i, true) (j, !b)

private def nine3Ref : Fin 12 → Equiv.Perm (Fin 4 × Bool)
  | 0 => nine3PermRef 0 1 false
  | 1 => nine3PermRef 0 1 true
  | 2 => nine3PermRef 0 2 false
  | 3 => nine3PermRef 0 2 true
  | 4 => nine3PermRef 0 3 false
  | 5 => nine3PermRef 0 3 true
  | 6 => nine3PermRef 1 2 false
  | 7 => nine3PermRef 1 2 true
  | 8 => nine3PermRef 1 3 false
  | 9 => nine3PermRef 1 3 true
  | 10 => nine3PermRef 2 3 false
  | 11 => nine3PermRef 2 3 true

private def nine3RefSet : Set (Equiv.Perm (Fin 4 × Bool)) := Set.range nine3Ref

private def nine3WeylGens : Set (Equiv.Perm (Fin 4 × Bool)) :=
  {s | ∃ (i j : Fin 4) (b : Bool), i ≠ j ∧ s = nine3PermRef i j b}

private theorem nine3WeylGens_range : nine3WeylGens = nine3RefSet := by
  ext s
  constructor
  · rintro ⟨i, j, b, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> fin_cases b <;> (try exact absurd rfl hij) <;>
      (unfold nine3RefSet; simp only [Set.mem_range]; decide +kernel)
  · rintro ⟨n, rfl⟩
    fin_cases n <;> (unfold nine3WeylGens; decide +kernel)

private theorem nine3_weylD4_eq : weylD4 = Subgroup.closure nine3RefSet := by
  change Subgroup.closure nine3WeylGens = Subgroup.closure nine3RefSet
  rw [nine3WeylGens_range]

private def nine3D (n : Fin 12) : ↥weylD4 :=
  ⟨nine3Ref n, by rw [nine3_weylD4_eq]; exact Subgroup.subset_closure ⟨n, rfl⟩⟩

private theorem nine3_mem_weylD4Refl_range (d : ↥weylD4) :
    d ∈ weylD4Refl ↔ d ∈ Set.range nine3D := by
  change (d : Equiv.Perm (Fin 4 × Bool)) ∈ nine3WeylGens ↔ d ∈ Set.range nine3D
  rw [nine3WeylGens_range]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn]
    rfl

private theorem nine3Ref_conj : ∀ i j : Fin 12,
    nine3Ref i * nine3Ref j * (nine3Ref i)⁻¹ ∈ nine3RefSet := by
  unfold nine3RefSet
  decide +kernel

private theorem nine3Ref_comm_or_cube : ∀ i j : Fin 12,
    nine3Ref i * nine3Ref j = nine3Ref j * nine3Ref i ∨
      (nine3Ref i * nine3Ref j) ^ 3 = 1 := by
  decide +kernel

private theorem nine3Ref_isStar : ∀ i j k : Fin 12,
    nine3Ref i * nine3Ref j ≠ nine3Ref j * nine3Ref i →
      (nine3Ref k * nine3Ref i = nine3Ref i * nine3Ref k ∨
        nine3Ref k * nine3Ref j = nine3Ref j * nine3Ref k ∨
        nine3Ref k * (nine3Ref i * nine3Ref j * nine3Ref i) =
          (nine3Ref i * nine3Ref j * nine3Ref i) * nine3Ref k) := by
  decide +kernel

private theorem nine3D_sq : ∀ d ∈ Set.range nine3D, d * d = 1 := by
  rintro d ⟨n, rfl⟩
  apply Subtype.ext
  change nine3Ref n * nine3Ref n = 1
  fin_cases n <;> decide +kernel

private theorem nine3D_ne_one : ∀ d ∈ Set.range nine3D, d ≠ 1 := by
  rintro d ⟨n, rfl⟩ h
  have h' : nine3Ref n = 1 := congrArg Subtype.val h
  fin_cases n <;> exact absurd h' (by decide +kernel)

private theorem nine3D_conj : ∀ d ∈ Set.range nine3D, ∀ g : ↥weylD4,
    g * d * g⁻¹ ∈ Set.range nine3D := by
  have hgen_fwd : ∀ a ∈ nine3RefSet, ∀ b ∈ nine3RefSet, a * b * a⁻¹ ∈ nine3RefSet := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact nine3Ref_conj i j
  have hgen : ∀ a ∈ nine3RefSet, ∀ d, d ∈ nine3RefSet ↔ a * d * a⁻¹ ∈ nine3RefSet := by
    rintro a ⟨i, rfl⟩ d
    constructor
    · intro hd; exact hgen_fwd (nine3Ref i) ⟨i, rfl⟩ d hd
    · intro h
      have hsq : nine3Ref i * nine3Ref i = 1 := by fin_cases i <;> decide +kernel
      have hgi : (nine3Ref i)⁻¹ = nine3Ref i := inv_eq_of_mul_eq_one_left hsq
      have hd : d = nine3Ref i * (nine3Ref i * d * nine3Ref i) * nine3Ref i := by
        calc d = (nine3Ref i * nine3Ref i) * d * (nine3Ref i * nine3Ref i) := by
              rw [hsq, one_mul, mul_one]
          _ = nine3Ref i * (nine3Ref i * d * nine3Ref i) * nine3Ref i := by
              simp only [mul_assoc]
      rw [hd]
      have h' : nine3Ref i * (nine3Ref i * d * (nine3Ref i)⁻¹) * (nine3Ref i)⁻¹ ∈ nine3RefSet :=
        hgen_fwd (nine3Ref i) ⟨i, rfl⟩ (nine3Ref i * d * (nine3Ref i)⁻¹) h
      rwa [hgi] at h'
  have hmem : ∀ u ∈ weylD4, ∀ d, d ∈ nine3RefSet ↔ u * d * u⁻¹ ∈ nine3RefSet := by
    intro u hu
    rw [nine3_weylD4_eq] at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => intro d; simp
    | mul x y hx hy ihx ihy =>
        intro d
        rw [show (x * y) * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ by group]
        exact (ihy d).trans (ihx (y * d * y⁻¹))
    | inv x hx ihx =>
        intro d
        have h := ihx (x⁻¹ * d * x)
        rw [show x * (x⁻¹ * d * x) * x⁻¹ = d by group] at h
        rw [show x⁻¹ * d * (x⁻¹)⁻¹ = x⁻¹ * d * x by group]
        exact h.symm
  rintro d ⟨n, rfl⟩ g
  have h : (g : Equiv.Perm _) * nine3Ref n * (g : Equiv.Perm _)⁻¹ ∈ nine3RefSet :=
    (hmem (g : Equiv.Perm _) g.2 (nine3Ref n)).mp ⟨n, rfl⟩
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  apply Subtype.ext
  show nine3Ref m = (g : Equiv.Perm _) * nine3Ref n * (g : Equiv.Perm _)⁻¹
  exact hm

private theorem nine3D_comm_or_cube : ∀ a ∈ Set.range nine3D, ∀ b ∈ Set.range nine3D,
    a * b = b * a ∨ (a * b) ^ 3 = 1 := by
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
  rcases nine3Ref_comm_or_cube i j with h | h
  · left; apply Subtype.ext
    change nine3Ref i * nine3Ref j = nine3Ref j * nine3Ref i
    exact h
  · right; apply Subtype.ext
    change (nine3Ref i * nine3Ref j) ^ 3 = 1
    exact h

private theorem nine3_range_eq_preimage : Set.range nine3D =
    ((↑) : ↥weylD4 → Equiv.Perm (Fin 4 × Bool)) ⁻¹' nine3WeylGens := by
  ext s
  exact (nine3_mem_weylD4Refl_range s).symm

private theorem nine3_closure_range_top : Subgroup.closure (Set.range nine3D) = ⊤ := by
  rw [nine3_range_eq_preimage]
  exact Subgroup.closure_closure_coe_preimage

private theorem nine3_weylD4Refl_isTT : Star3T.IsTT (Set.range nine3D) where
  mul_self := nine3D_sq
  ne_one := nine3D_ne_one
  conj_mem := nine3D_conj
  closure_eq_top := nine3_closure_range_top
  comm_or_cube := nine3D_comm_or_cube

private theorem nine3_weylD4Refl_isStar : Star3T.IsStar (Set.range nine3D) := by
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hnab c ⟨k, rfl⟩
  have hnab' : nine3Ref i * nine3Ref j ≠ nine3Ref j * nine3Ref i := by
    intro h
    exact hnab (Subtype.ext (by change nine3Ref i * nine3Ref j = nine3Ref j * nine3Ref i; exact h))
  rcases nine3Ref_isStar i j k hnab' with h | h | h
  · left; apply Subtype.ext; change nine3Ref k * nine3Ref i = nine3Ref i * nine3Ref k; exact h
  · right; left; apply Subtype.ext
    change nine3Ref k * nine3Ref j = nine3Ref j * nine3Ref k; exact h
  · right; right; apply Subtype.ext
    change nine3Ref k * (nine3Ref i * nine3Ref j * nine3Ref i) =
      (nine3Ref i * nine3Ref j * nine3Ref i) * nine3Ref k
    exact h

private theorem nine3_comm_idx : ∀ n : Fin 12,
    nine3Ref n * nine3Ref 0 = nine3Ref 0 * nine3Ref n ↔
      (n = 0 ∨ n = 1 ∨ n = 10 ∨ n = 11) := by
  decide +kernel

private theorem nine3_cent_range : Star3T.cent (Set.range nine3D) (nine3D 0) =
    ({nine3D 0, nine3D 1, nine3D 10, nine3D 11} : Set ↥weylD4) := by
  ext y
  constructor
  · rintro ⟨hy, hcomm⟩
    obtain ⟨n, rfl⟩ := hy
    have hcomm' : nine3Ref n * nine3Ref 0 = nine3Ref 0 * nine3Ref n := by
      have := congrArg Subtype.val hcomm
      change nine3Ref n * nine3Ref 0 = nine3Ref 0 * nine3Ref n at this
      exact this
    rcases (nine3_comm_idx n).mp hcomm' with rfl | rfl | rfl | rfl
    · simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨⟨0, rfl⟩, rfl⟩
    · refine ⟨⟨1, rfl⟩, ?_⟩
      apply Subtype.ext; change nine3Ref 1 * nine3Ref 0 = nine3Ref 0 * nine3Ref 1
      decide +kernel
    · refine ⟨⟨10, rfl⟩, ?_⟩
      apply Subtype.ext; change nine3Ref 10 * nine3Ref 0 = nine3Ref 0 * nine3Ref 10
      decide +kernel
    · refine ⟨⟨11, rfl⟩, ?_⟩
      apply Subtype.ext; change nine3Ref 11 * nine3Ref 0 = nine3Ref 0 * nine3Ref 11
      decide +kernel

private theorem nine3_cent_ncard : (Star3T.cent (Set.range nine3D) (nine3D 0)).ncard = 4 := by
  rw [nine3_cent_range]
  rw [Set.ncard_insert_of_notMem (by decide +kernel),
      Set.ncard_insert_of_notMem (by decide +kernel),
      Set.ncard_insert_of_notMem (by decide +kernel)]
  simp

private theorem nine3_comm_trans : ∀ m n : Fin 12,
    nine3Ref 0 * nine3Ref m = nine3Ref m * nine3Ref 0 →
      nine3Ref m * nine3Ref n = nine3Ref n * nine3Ref m →
        nine3Ref 0 * nine3Ref n = nine3Ref n * nine3Ref 0 := by
  decide +kernel

private theorem nine3_conn_cent : ∀ y, Star3T.Conn (Set.range nine3D) (nine3D 0) y →
    y ∈ Star3T.cent (Set.range nine3D) (nine3D 0) := by
  intro y hy
  induction hy with
  | refl => exact ⟨⟨0, rfl⟩, rfl⟩
  | @tail b c _ hbc ih =>
      change b ∈ Set.range nine3D ∧ c ∈ Set.range nine3D ∧ b * c = c * b at hbc
      obtain ⟨hb, hc, hcomm⟩ := hbc
      obtain ⟨m, rfl⟩ := hb
      obtain ⟨n, rfl⟩ := hc
      obtain ⟨-, ihm⟩ := ih
      have ihm' : nine3Ref 0 * nine3Ref m = nine3Ref m * nine3Ref 0 := by
        have := congrArg Subtype.val ihm
        change nine3Ref m * nine3Ref 0 = nine3Ref 0 * nine3Ref m at this
        exact this.symm
      have hcomm' : nine3Ref m * nine3Ref n = nine3Ref n * nine3Ref m := by
        have := congrArg Subtype.val hcomm
        change nine3Ref m * nine3Ref n = nine3Ref n * nine3Ref m at this
        exact this
      refine ⟨⟨n, rfl⟩, ?_⟩
      apply Subtype.ext
      exact (nine3_comm_trans m n ihm' hcomm').symm

private theorem nine3_not_conn : ¬ Star3T.Conn (Set.range nine3D) (nine3D 0) (nine3D 2) := by
  intro h
  obtain ⟨-, hc⟩ := nine3_conn_cent (nine3D 2) h
  have hc' : nine3Ref 2 * nine3Ref 0 = nine3Ref 0 * nine3Ref 2 := by
    have := congrArg Subtype.val hc
    change nine3Ref 2 * nine3Ref 0 = nine3Ref 0 * nine3Ref 2 at this
    exact this
  exact (by decide +kernel : nine3Ref 2 * nine3Ref 0 ≠ nine3Ref 0 * nine3Ref 2) hc'

private def nine3Quad (e : Fin 4 → Bool) : ↥weylD4 :=
  nine3D 0 ^ (if e 0 then 1 else 0) * nine3D 1 ^ (if e 1 then 1 else 0) *
    nine3D 10 ^ (if e 2 then 1 else 0) * nine3D 11 ^ (if e 3 then 1 else 0)

private theorem nine3Quad_inj : Function.Injective nine3Quad := by
  decide +kernel

private theorem nine3Quad_mem (e : Fin 4 → Bool) :
    nine3Quad e ∈ Subgroup.closure (Star3T.cent (Set.range nine3D) (nine3D 0)) := by
  rw [nine3_cent_range]
  have h0 : nine3D 0 ∈ Subgroup.closure ({nine3D 0, nine3D 1, nine3D 10, nine3D 11} :
      Set ↥weylD4) := Subgroup.subset_closure (by simp)
  have h1 : nine3D 1 ∈ Subgroup.closure ({nine3D 0, nine3D 1, nine3D 10, nine3D 11} :
      Set ↥weylD4) := Subgroup.subset_closure (by simp)
  have h10 : nine3D 10 ∈ Subgroup.closure ({nine3D 0, nine3D 1, nine3D 10, nine3D 11} :
      Set ↥weylD4) := Subgroup.subset_closure (by simp)
  have h11 : nine3D 11 ∈ Subgroup.closure ({nine3D 0, nine3D 1, nine3D 10, nine3D 11} :
      Set ↥weylD4) := Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ h0 _) (Subgroup.pow_mem _ h1 _))
    (Subgroup.pow_mem _ h10 _)) (Subgroup.pow_mem _ h11 _)

private theorem nine3_closure_card :
    16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent (Set.range nine3D) (nine3D 0))) := by
  let f : (Fin 4 → Bool) →
      ↥(Subgroup.closure (Star3T.cent (Set.range nine3D) (nine3D 0))) :=
    fun e => ⟨nine3Quad e, nine3Quad_mem e⟩
  have hf : Function.Injective f := fun e e' h => nine3Quad_inj (Subtype.ext_iff.mp h)
  have h1 : Nat.card (Fin 4 → Bool) ≤
      Nat.card ↥(Subgroup.closure (Star3T.cent (Set.range nine3D) (nine3D 0))) :=
    Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Fin 4 → Bool) = 16 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun]
  omega

theorem nine3_weylD4_recognition {D : Set Γ} (hTT : Star3T.IsTT D) (hS : Star3T.IsStar D)
    {d a : Γ} (hd : d ∈ D) (ha : a ∈ D) (hc : ¬ Star3T.Conn D d a)
    (hk : (Star3T.cent D d).ncard = 4)
    (hcard : 16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent D d))) :
    ∃ e : Γ ≃* ↥weylD4, ∀ x, x ∈ D ↔ e x ∈ weylD4Refl := by
  have hM4 : ∀ i j, coxeterD4.M i j = MD4 i j := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨e₁, he₁⟩ :=
    nine3_star3T_labelled hTT hS hd ha hc hk hcard hM4 coxeterD4.toCoxeterSystem
  obtain ⟨e₂, he₂⟩ :=
    nine3_star3T_labelled nine3_weylD4Refl_isTT nine3_weylD4Refl_isStar
      (⟨0, rfl⟩ : nine3D 0 ∈ Set.range nine3D)
      (⟨2, rfl⟩ : nine3D 2 ∈ Set.range nine3D)
      nine3_not_conn nine3_cent_ncard nine3_closure_card hM4 coxeterD4.toCoxeterSystem
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro x
  rw [nine3_mem_weylD4Refl_range, he₂, he₁]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [hw, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hw' : e₂ (e₁.symm x) = e₂ (w * coxeterD4.toCoxeterSystem.simple 0 * w⁻¹) := by
      simpa only [MulEquiv.trans_apply] using hw
    have h : e₁.symm x = w * coxeterD4.toCoxeterSystem.simple 0 * w⁻¹ := e₂.injective hw'
    calc x = e₁ (e₁.symm x) := (MulEquiv.apply_symm_apply e₁ x).symm
      _ = e₁ (w * coxeterD4.toCoxeterSystem.simple 0 * w⁻¹) := by rw [h]

theorem nine3OddFrame_four_equiv {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 4 π D) (hi : Nine3FibreIndep 3 π D) :
    ∃ e : Γ ≃* ↥weylD4, ∀ x, x ∈ D ↔ e x ∈ weylD4Refl := by
  obtain ⟨d, hd, a, ha, hda⟩ := nine3OddFrame_exists_ne h (by norm_num : 0 < 4)
  have hTT : Star3T.IsTT D := nine3OddFrame_isTT h
  have hS : Star3T.IsStar D := nine3OddFrame_isStar h
  have hnc : ¬ Star3T.Conn D d a := nine3OddFrame_not_conn h hd ha hda
  have hk : (Star3T.cent D d).ncard = 4 := by
    rw [nine3OddFrame_ncard_cent h hd]
  have hcard : 16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent D d)) := by
    classical
    obtain ⟨c, hc⟩ := h.refl d hd
    have hsub : nine3FibreSet π D c ⊆ Star3T.cent D d := by
      rintro e ⟨heD, heπ⟩
      exact ⟨heD, h.comm e heD d hd (heπ.trans hc.symm)⟩
    have hle : (Star3T.cent D d).ncard ≤ (nine3FibreSet π D c).ncard := by
      have h4 : (nine3FibreSet π D c).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact h.card c
      rw [hk, h4]
    have hcent : Star3T.cent D d = nine3FibreSet π D c :=
      (Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)).symm
    rw [hcent]
    let F : Set Γ := nine3FibreSet π D c
    let E : Subgroup Γ := Subgroup.closure F
    have hcomm : F.Pairwise Commute := by
      intro u hu v hv _
      exact h.comm u hu.1 v hv.1 (hu.2.trans hv.2.symm)
    haveI : Finite ↥F := Finite.of_injective (Subtype.val : ↥F → Γ) Subtype.val_injective
    haveI : Fintype ↥F := Fintype.ofFinite ↥F
    letI : CommGroup E := Subgroup.closureCommGroupOfComm hcomm
    let φ : ↥F → E := fun d => ⟨(d : Γ), Subgroup.subset_closure d.2⟩
    have hφ_sq : ∀ d : ↥F, φ d * φ d = 1 := by
      intro d
      apply Subtype.ext
      simpa [φ] using h.sq d.1 d.2.1
    have hφ_sq' : ∀ d : ↥F, φ d ^ 2 = 1 := fun d => by rw [pow_two]; exact hφ_sq d
    have hclosure : Subgroup.closure (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F)) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : (x : Γ) ∈
          (Subgroup.closure (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F))).map E.subtype := by
        rw [MonoidHom.map_closure]
        have himg : E.subtype '' (φ '' (↑(Finset.univ : Finset ↥F) : Set ↥F)) = F := by
          ext y; constructor
          · rintro ⟨z, ⟨i, -, rfl⟩, rfl⟩
            exact i.2
          · intro hy
            exact ⟨φ ⟨y, hy⟩, ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩, rfl⟩
        rw [himg]
        exact x.2
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    have hinj : Set.InjOn (fun S : Finset ↥F => ∏ d ∈ S, φ d)
        ((Finset.univ : Finset ↥F).powerset : Set (Finset ↥F)) := by
      intro S _ T _ hST
      have hST' : (∏ d ∈ S, φ d) = ∏ d ∈ T, φ d := hST
      by_contra hne
      have hrel : ∏ d ∈ S ∆ T, φ d = 1 := by
        have hsd := TauCeti.prod_sdiff_union_sdiff φ (S := S) (D := T) (fun i _ => hφ_sq' i)
        rw [Finset.symmDiff_def, hsd, hST']
        rw [← sq, ← Finset.prod_pow]
        exact Finset.prod_eq_one (fun i _ => hφ_sq' i)
      have hne' : (S ∆ T).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        exact hne (Finset.symmDiff_eq_empty.mp hemp)
      set l : List Γ := (S ∆ T).toList.map (fun d : ↥F => (d : Γ)) with hl
      have hl_nodup : l.Nodup := by
        rw [hl]
        exact List.Nodup.map (fun _ _ hab => Subtype.ext hab) (S ∆ T).nodup_toList
      have hl_ne : l ≠ [] := by
        rw [hl]
        intro hnil
        exact Finset.nonempty_iff_ne_empty.mp hne'
          (Finset.toList_eq_nil.mp (List.map_eq_nil_iff.mp hnil))
      have hl_mem : ∀ d ∈ l, d ∈ D ∧ π d = zmodRefl 3 c := by
        intro d hd
        rw [hl] at hd
        obtain ⟨d', _, rfl⟩ := List.mem_map.mp hd
        exact d'.2
      have hl_prod : l.prod = 1 := by
        rw [hl]
        have h1 := List.prod_map_hom (S ∆ T).toList φ E.subtype
        rw [show (fun d : ↥F => (d : Γ)) = (E.subtype ∘ φ) from rfl, h1,
          Finset.prod_map_toList, hrel, map_one]
      exact hi c l hl_nodup hl_ne hl_mem hl_prod
    have hcardE : Nat.card E = 16 := by
      have htau := TauCeti.natCard_closure_image_eq_two_pow (s := Finset.univ) (f := φ)
        (fun i _ => hφ_sq' i) hinj
      rw [hclosure, Subgroup.card_top] at htau
      rw [htau, Finset.card_univ, ← Nat.card_eq_fintype_card]
      have h4 : Nat.card ↥F = 4 := h.card c
      rw [h4]
      norm_num
    change 16 ≤ Nat.card ↥E
    rw [hcardE]
  exact nine3_weylD4_recognition hTT hS hd ha hnc hk hcard

end CFSG.LocalAnalysis.WeakClosure81
