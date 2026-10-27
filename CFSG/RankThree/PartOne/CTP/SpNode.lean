module

public import CFSG.RankThree.PartOne.CTP.SpGeom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K]

section PlaneGroup

theorem card_planeGroup {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW : IsHyperbolicPlane W) :
    Nat.card (planeGroup W) = Nat.card SL(2, K) := by
  obtain ⟨u, w, huw, rfl⟩ := hW
  obtain ⟨c, hcu, hcw⟩ := exists_sp_apply_eq (m := 1) u w huw
  rw [← hcu, ← hcw, planeGroup_span_conj]
  have h0 : planeGroup (Submodule.span K {(Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K),
      Pi.single (Sum.inr 0) 1}) = (longBlock K 2 0).range := by
    rw [range_longBlock]
    exact (planeGroup_stdPlane (K := K) (n := 2) 0).trans (longRootSp2_eq_suppGroup 0)
  rw [h0, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact (Nat.card_congr
    (MonoidHom.ofInjective (longBlock_injective (K := K) (n := 2) 0)).toEquiv).symm

end PlaneGroup

section Node

variable [Finite K] [CharP K 2]

@[expose] def fixSub (A : Subgroup (StatedSp 2 K)) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | ∀ a ∈ A, mat 2 K a *ᵥ v = v}
  add_mem' := by
    intro v w hv hw a ha
    rw [Matrix.mulVec_add, hv a ha, hw a ha]
  zero_mem' := by
    intro a _
    simp
  smul_mem' := by
    intro c v hv a ha
    rw [Matrix.mulVec_smul, hv a ha]

omit [Finite K] [CharP K 2] in
theorem mem_fixSub {A : Subgroup (StatedSp 2 K)} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ fixSub A ↔ ∀ a ∈ A, mat 2 K a *ᵥ v = v := Iff.rfl

omit [Finite K] [CharP K 2] in
theorem mulVec_mem_eig {g a : StatedSp 2 K} (hc : a * g = g * a) {l : K}
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ eig g l) : mat 2 K a *ᵥ v ∈ eig g l := by
  rw [mem_eig] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← map_mul, ← hc, map_mul, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

omit [Finite K] [CharP K 2] in
theorem two_le_finrank_eig_of_moved {g : StatedSp 2 K} (A : Subgroup (StatedSp 2 K))
    [Group.IsPerfect A] (hc : ∀ a ∈ A, a * g = g * a) {l : K} {a : StatedSp 2 K} (ha : a ∈ A)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ eig g l) (hmov : mat 2 K a *ᵥ v ≠ v) :
    2 ≤ Module.finrank K (eig g l) := by
  by_contra hlt
  have hv0 : v ≠ 0 := fun h => hmov (by rw [h]; simp)
  have hpos : 0 < Module.finrank K (eig g l) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have h1 : Module.finrank K (eig g l) = 1 := by omega
  have hline : ∀ b : A, ∃ c : K, ((actHom K).comp A.subtype) b v = c • v := by
    intro b
    have hb : mat 2 K (b : StatedSp 2 K) *ᵥ v ∈ eig g l := mulVec_mem_eig (hc b b.2) hv
    obtain ⟨c, hcv⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : eig g l)
      (fun h => hv0 (congrArg Subtype.val h))).mp h1 ⟨_, hb⟩
    exact ⟨c, (congrArg Subtype.val hcv).symm⟩
  have := perfect_fix_of_line ((actHom K).comp A.subtype) hv0 hline ⟨a, ha⟩
  exact hmov this

omit [Finite K] in
theorem finrank_eig_le_two {g : StatedSp 2 K} {l : K} (hl : l ≠ 1) :
    Module.finrank K (eig g l) ≤ 2 := by
  have hle : eig g l ≤ orth (eig g l) := fun v hv =>
    mem_orth.mpr fun w hw => form_eig_self_eq_zero hl hv hw
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_orth_add (eig g l)
  omega

omit [Finite K] in
theorem eig_eq_orth_of_finrank_two {g : StatedSp 2 K} {l : K} (hl : l ≠ 1)
    (h2 : Module.finrank K (eig g l) = 2) : eig g l = orth (eig g l) := by
  have hle : eig g l ≤ orth (eig g l) := fun v hv =>
    mem_orth.mpr fun w hw => form_eig_self_eq_zero hl hv hw
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have := finrank_orth_add (eig g l)
  omega

omit [Finite K] [CharP K 2] in
theorem finrank_eig_one_cases {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    Module.finrank K (eig g 1) = 2 ∨ Module.finrank K (eig g 1) = 0 := by
  have h1 := finrank_eig_one_add_mov hζ hg
  have hd1 : Module.finrank K (eig g 1) ≠ 1 :=
    finrank_ne_one_of_nondeg fun u hu h => eig_one_nondeg hζ hg hu h
  have he1 : Module.finrank K (mov g) ≠ 1 :=
    finrank_ne_one_of_nondeg fun u hu h => mov_nondeg hζ hg hu h
  have hd4 : Module.finrank K (eig g 1) ≠ 4 := by
    intro h4
    apply hg1
    have htop : eig g 1 = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4]; simp)
    have hmat : mat 2 K g = 1 := by
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      have hv : v ∈ eig g 1 := by rw [htop]; exact Submodule.mem_top
      rw [mem_eig.mp hv, one_smul, Matrix.one_mulVec]
    exact mat_injective (by rw [hmat, map_one])
  omega

omit [Finite K] in
theorem mov_le_fixSub {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1)
    (hd : Module.finrank K (eig g 1) = 2) (A : Subgroup (StatedSp 2 K)) [Group.IsPerfect A]
    (hc : ∀ a ∈ A, a * g = g * a) : mov g ≤ fixSub A := by
  have hmovdim : Module.finrank K (mov g) = 2 := by
    have := finrank_eig_one_add_mov hζ hg
    omega
  refine iSup₂_le fun l hl v hv => ?_
  refine mem_fixSub.mpr fun a ha => ?_
  by_contra hmov
  have h2 := two_le_finrank_eig_of_moved A hc ha hv hmov
  have h3 := finrank_eig_le_two (g := g) hl
  have heq : eig g l = mov g :=
    Submodule.eq_of_le_of_finrank_eq (eig_le_mov hl) (by omega)
  have hmovne : mov g ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hmovdim
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmovne
  apply hu0
  refine mov_nondeg hζ hg hu fun w hw => ?_
  rw [← heq] at hu hw
  exact form_eig_self_eq_zero hl hu hw

theorem sp_node_long {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1)
    (hd : Module.finrank K (eig g 1) = 2) (A : Subgroup (StatedSp 2 K)) [Group.IsPerfect A]
    (hcard : Nat.card A = Nat.card SL(2, K)) (hc : ∀ a ∈ A, a * g = g * a) :
    IsHyperbolicPlane (eig g 1) ∧ orth (eig g 1) = mov g ∧ A = planeGroup (eig g 1) := by
  have hyp : IsHyperbolicPlane (eig g 1) :=
    isHyperbolicPlane_iff.mpr ⟨hd, fun v hv h => eig_one_nondeg hζ hg hv h⟩
  have hmovdim : Module.finrank K (mov g) = 2 := by
    have := finrank_eig_one_add_mov hζ hg
    omega
  have horth : orth (eig g 1) = mov g := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq (mov_le_orth_eig_one g) ?_
    have := finrank_orth_add (eig g 1)
    omega
  refine ⟨hyp, horth, ?_⟩
  have hle : A ≤ planeGroup (eig g 1) := by
    intro a ha v hv
    have hv' : v ∈ orth (eig g 1) := mem_orth.mpr hv
    rw [horth] at hv'
    exact mem_fixSub.mp (mov_le_fixSub hζ hg hd A hc hv') a ha
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_planeGroup hyp, hcard])

omit [Finite K] in
theorem sp_node_short {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) (hd : Module.finrank K (eig g 1) = 0)
    (A : Subgroup (StatedSp 2 K)) [Group.IsPerfect A] (hA1 : A ≠ ⊥)
    (hc : ∀ a ∈ A, a * g = g * a) :
    ∃ l : K, l ≠ 1 ∧ l ≠ 0 ∧ Module.finrank K (eig g l) = 2 ∧
      Module.finrank K (eig g l⁻¹) = 2 ∧
      IsCompl (eig g l) (eig g l⁻¹) ∧ ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig g μ = ⊥ := by
  have hind : iSupIndep (fun μ : K => eig g μ) := Module.End.eigenspaces_iSupIndep _
  have hbot : eig g 1 = ⊥ := Submodule.finrank_eq_zero.mp hd
  have hmov : mov g = ⊤ := by
    have h := (isCompl_eig_one_mov hζ hg).codisjoint
    rw [codisjoint_iff, hbot, bot_sup_eq] at h
    exact h
  obtain ⟨l, hl, a, ha, v, hv, hmv⟩ : ∃ l : K, l ≠ 1 ∧ ∃ a ∈ A, ∃ v ∈ eig g l,
      mat 2 K a *ᵥ v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hA1
    have hle : mov g ≤ fixSub A := iSup₂_le fun l hl v hv =>
      mem_fixSub.mpr fun a ha => hcon l hl a ha v hv
    rw [hmov, top_le_iff] at hle
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hmat : mat 2 K a = 1 := by
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      have hv : v ∈ fixSub A := by rw [hle]; exact Submodule.mem_top
      rw [mem_fixSub.mp hv a ha, Matrix.one_mulVec]
    exact mat_injective (by rw [hmat, map_one])
  have h2 := two_le_finrank_eig_of_moved A hc ha hv hmv
  have h3 := finrank_eig_le_two (g := g) hl
  have hl2 : Module.finrank K (eig g l) = 2 := by omega
  have hLorth := eig_eq_orth_of_finrank_two hl hl2
  have hl0 : l ≠ 0 := by
    rintro rfl
    have h0 : mat 2 K g *ᵥ v = 0 := by rw [mem_eig.mp hv, zero_smul]
    have hv0 : v = 0 := by
      have := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h0
      simpa [Matrix.mulVec_mulVec, ← map_mul] using this
    apply hmv
    rw [hv0]
    simp
  have hlinv : l ≠ l⁻¹ := by
    intro h
    apply hl
    have hll : l * l = 1 := by
      field_simp at h
      linear_combination h
    have h2' : (l + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, sq, hll, one_pow, CharTwo.add_self_eq_zero]
    have h3' : l + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2'
    rw [eq_neg_of_add_eq_zero_left h3', CharTwo.neg_eq]
  have hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig g μ = ⊥ := by
    intro μ hμl hμi
    have hml : μ * l ≠ 1 := by
      intro h
      exact hμi (eq_inv_of_mul_eq_one_left h)
    have hle : eig g μ ≤ eig g l := by
      rw [hLorth]
      intro u hu
      exact mem_orth.mpr fun w hw => form_eig_eq_zero hml hu hw
    have hdis : Disjoint (eig g μ) (eig g l) := hind.pairwiseDisjoint hμl
    exact (Submodule.disjoint_def.mp hdis |> fun h => eq_bot_iff.mpr fun u hu =>
      by simpa using h u hu (hle hu))
  have hsup : eig g l ⊔ eig g l⁻¹ = ⊤ := by
    rw [eq_top_iff, ← iSup_eig_eq_top hζ hg]
    refine iSup_le fun μ => ?_
    by_cases h1 : μ = l
    · rw [h1]; exact le_sup_left
    by_cases h2 : μ = l⁻¹
    · rw [h2]; exact le_sup_right
    · rw [hzero μ h1 h2]; exact bot_le
  have hcompl : IsCompl (eig g l) (eig g l⁻¹) :=
    ⟨hind.pairwiseDisjoint hlinv, codisjoint_iff.mpr hsup⟩
  have hd2 := Submodule.finrank_add_eq_of_isCompl hcompl
  refine ⟨l, hl, hl0, hl2, ?_, hcompl, hzero⟩
  have : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  omega

theorem sp_node {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) (hg1 : g ≠ 1) (A : Subgroup (StatedSp 2 K))
    [Group.IsPerfect A] (hA1 : A ≠ ⊥) (hcard : Nat.card A = Nat.card SL(2, K))
    (hc : ∀ a ∈ A, a * g = g * a) :
    (IsHyperbolicPlane (eig g 1) ∧ orth (eig g 1) = mov g ∧ A = planeGroup (eig g 1)) ∨
      ∃ l : K, l ≠ 1 ∧ l ≠ 0 ∧ Module.finrank K (eig g l) = 2 ∧
        Module.finrank K (eig g l⁻¹) = 2 ∧
        IsCompl (eig g l) (eig g l⁻¹) ∧ ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig g μ = ⊥ := by
  rcases finrank_eig_one_cases hζ hg hg1 with hd | hd
  · exact Or.inl (sp_node_long hζ hg hd A hcard hc)
  · exact Or.inr (sp_node_short hζ hg hd A hA1 hc)

end Node

end CFSG.RankThree.PartOne.CTP
