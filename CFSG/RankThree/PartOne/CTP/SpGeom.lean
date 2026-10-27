module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Eig

variable {K : Type} [Field K]

@[expose] noncomputable def eig (g : StatedSp 2 K) (l : K) : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  Module.End.eigenspace (Matrix.mulVecLin (mat 2 K g)) l

theorem mem_eig {g : StatedSp 2 K} {l : K} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ eig g l ↔ mat 2 K g *ᵥ v = l • v := by
  simp [eig]

theorem form_eig_eq_zero {g : StatedSp 2 K} {l m : K} (hlm : l * m ≠ 1)
    {u v : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ eig g l) (hv : v ∈ eig g m) : form u v = 0 := by
  have h := form_mulVec g u v
  rw [mem_eig.mp hu, mem_eig.mp hv, form_smul_left, form_smul_right, ← mul_assoc] at h
  have h2 : (l * m - 1) * form u v = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hlm)

theorem form_eig_self_eq_zero [CharP K 2] {g : StatedSp 2 K} {l : K} (hl : l ≠ 1)
    {u v : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ eig g l) (hv : v ∈ eig g l) : form u v = 0 := by
  refine form_eig_eq_zero (fun h => hl ?_) hu hv
  have h2 : (l + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h3 : l + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
  rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]

theorem eq_zero_of_form_eq_zero {v : Fin 2 ⊕ Fin 2 → K} (h : ∀ w, form v w = 0) : v = 0 := by
  funext b
  have := h (Pi.single (par b) 1)
  rw [form_single_right, par_par] at this
  have hs : sgn K b ≠ 0 := sgn_ne_zero b
  exact (mul_eq_zero.mp this).resolve_right hs

theorem form_neg_right (u v : Fin 2 ⊕ Fin 2 → K) : form u (-v) = -form u v := by
  have h := form_smul_right u v (-1 : K)
  rwa [neg_one_smul, neg_one_mul] at h

end Eig

section Orth

variable {K : Type} [Field K]

@[expose] noncomputable def formBil : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) :=
  Matrix.toBilin' (Matrix.J (Fin 2) K)

theorem formBil_apply (u v : Fin 2 ⊕ Fin 2 → K) : formBil u v = -form u v :=
  toBilin'_J_apply u v

@[expose] noncomputable def orth (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  formBil.orthogonal S

theorem mem_orth {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ orth S ↔ ∀ s ∈ S, form v s = 0 := by
  unfold orth
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun s _ => ?_
  rw [formBil_apply, neg_eq_zero, form_antisymm, neg_eq_zero]

theorem finrank_orth_add (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Module.finrank K (orth S) + Module.finrank K S = 4 := by
  have h := LinearMap.BilinForm.finrank_orthogonal
    (B := (formBil : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K))) nondegenerate_toBilin'_J S
  have h4 : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  have h5 : Module.finrank K S ≤ 4 := h4 ▸ Submodule.finrank_le S
  unfold orth
  omega

end Orth

section Decomp

variable {K : Type} [Field K]

@[expose] noncomputable def actHom (K : Type) [Field K] :
    StatedSp 2 K →* Module.End K (Fin 2 ⊕ Fin 2 → K) where
  toFun g := Matrix.mulVecLin (mat 2 K g)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem perfect_fix_of_line {H : Type*} [Group H] [Group.IsPerfect H] {V : Type*}
    [AddCommGroup V] [Module K V] (ρ : H →* Module.End K V) {v : V} (hv : v ≠ 0)
    (hline : ∀ h, ∃ c : K, ρ h v = c • v) : ∀ h, ρ h v = v := by
  choose c hc using hline
  have hcmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    have e : (c (g * h)) • v = (c g * c h) • v := by
      rw [← hc (g * h), map_mul, Module.End.mul_apply, hc h, map_smul, hc g, smul_smul, mul_comm]
    exact smul_left_injective K hv e
  have hc1 : c 1 = 1 := by
    have e : (c 1) • v = (1 : K) • v := by
      rw [← hc 1, map_one, Module.End.one_apply, one_smul]
    exact smul_left_injective K hv e
  let χ : H →* K :=
    { toFun := c
      map_one' := hc1
      map_mul' := hcmul }
  have hsub : ∀ g : H, c g = 1 := by
    intro g
    have hsub : Subsingleton χ.toHomUnits.range := by
      have : Group.IsPerfect χ.toHomUnits.range := Group.IsPerfect.range χ.toHomUnits
      infer_instance
    have h1 : (⟨χ.toHomUnits g, ⟨g, rfl⟩⟩ : χ.toHomUnits.range) = 1 := Subsingleton.elim _ _
    have h2 : χ.toHomUnits g = 1 := congrArg Subtype.val h1
    have h3 := congrArg Units.val h2
    simpa [χ] using h3
  intro g
  rw [hc g, hsub g, one_smul]

@[expose] noncomputable def mov (g : StatedSp 2 K) : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  ⨆ (l : K) (_ : l ≠ 1), eig g l

theorem eig_le_mov {g : StatedSp 2 K} {l : K} (hl : l ≠ 1) : eig g l ≤ mov g :=
  le_iSup₂_of_le l hl le_rfl

theorem iSup_eig_eq_top {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) : ⨆ l, eig g l = ⊤ := by
  have hf : (Matrix.mulVecLin (mat 2 K g) : Module.End K (Fin 2 ⊕ Fin 2 → K)) ^ p = 1 := by
    have h := congrArg (actHom K) hg
    rwa [map_pow, map_one] at h
  exact CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ hf

theorem isCompl_eig_one_mov {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) : IsCompl (eig g 1) (mov g) := by
  have hind : iSupIndep (fun l : K => eig g l) := Module.End.eigenspaces_iSupIndep _
  refine ⟨hind 1, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← iSup_eig_eq_top hζ hg, iSup_split_single _ (1 : K)]
  exact le_rfl

theorem mov_le_orth_eig_one (g : StatedSp 2 K) : mov g ≤ orth (eig g 1) := by
  refine iSup₂_le fun l hl v hv => ?_
  rw [mem_orth]
  intro s hs
  exact form_eig_eq_zero (by simpa using hl) hv hs

theorem form_eq_zero_comm {u v : Fin 2 ⊕ Fin 2 → K} (h : form u v = 0) : form v u = 0 := by
  rw [form_antisymm, h, neg_zero]

theorem eig_one_le_orth_mov (g : StatedSp 2 K) : eig g 1 ≤ orth (mov g) := by
  intro u hu
  rw [mem_orth]
  intro v hv
  exact form_eq_zero_comm (mem_orth.mp (mov_le_orth_eig_one g hv) u hu)

theorem eq_zero_of_form_sup {S T : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h : S ⊔ T = ⊤)
    {v : Fin 2 ⊕ Fin 2 → K} (hS : ∀ s ∈ S, form v s = 0) (hT : ∀ t ∈ T, form v t = 0) :
    v = 0 := by
  refine eq_zero_of_form_eq_zero fun w => ?_
  have hw : w ∈ S ⊔ T := by rw [h]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
  rw [form_add_right, hS s hs, hT t ht, add_zero]

theorem eig_one_nondeg {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) {u : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ eig g 1)
    (h : ∀ w ∈ eig g 1, form u w = 0) : u = 0 :=
  eq_zero_of_form_sup (isCompl_eig_one_mov hζ hg).sup_eq_top h fun t ht =>
    mem_orth.mp (eig_one_le_orth_mov g hu) t ht

theorem mov_nondeg {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) {u : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ mov g)
    (h : ∀ w ∈ mov g, form u w = 0) : u = 0 :=
  eq_zero_of_form_sup (isCompl_eig_one_mov hζ hg).sup_eq_top
    (fun s hs => mem_orth.mp (mov_le_orth_eig_one g hu) s hs) h

theorem finrank_eig_one_add_mov {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) :
    Module.finrank K (eig g 1) + Module.finrank K (mov g) = 4 := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_eig_one_mov hζ hg)
  simpa using h

theorem finrank_ne_one_of_nondeg {S : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hS : ∀ u ∈ S, (∀ w ∈ S, form u w = 0) → u = 0) : Module.finrank K S ≠ 1 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h
  apply hv0
  apply Subtype.ext
  refine hS v v.2 fun w hw => ?_
  obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
  have : w = c • (v : Fin 2 ⊕ Fin 2 → K) := (congrArg Subtype.val hc).symm
  rw [this, form_smul_right, form_self, mul_zero]

end Decomp

end CFSG.RankThree.PartOne.CTP
