module

public import CFSG.Quasithin.MS93.MSPBasic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

omit [Field F] in
theorem ext4 {u v : V4 F} (h0 : u (.inl 0) = v (.inl 0)) (h1 : u (.inl 1) = v (.inl 1))
    (h2 : u (.inr 0) = v (.inr 0)) (h3 : u (.inr 1) = v (.inr 1)) : u = v := by
  funext i
  rcases i with i | i <;> fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem exists_eq_span_of_isPoint {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ x : V4 F, x ≠ 0 ∧ p = F ∙ x := by
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp hp
  have hv : (v : V4 F) ≠ 0 := fun h => hv0 (Subtype.ext h)
  exact ⟨v, hv, eq_span_singleton_of_mem_of_finrank_eq_one hp v.2 hv⟩

theorem isPoint_span {x : V4 F} (hx : x ≠ 0) : IsPoint (F ∙ x) :=
  finrank_span_singleton hx

theorem commSp_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) : commSp (xPoint p) = p := by
  refine le_antisymm (commSp_fixer_perp_le p) ?_
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  obtain ⟨y, hy⟩ := exists_form_eq_one hx
  rw [Submodule.span_singleton_le_iff_mem]
  have h := sub_mem_commSp (transv_mem_xPoint x 1) y
  rwa [transv_mulVec, hy, mul_one, one_smul, add_sub_cancel_left] at h

theorem fixSp_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) : fixSp (xPoint p) = perp p := by
  refine le_antisymm (fun v hv => ?_) (le_fixer_iff.1 le_rfl)
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  have h := hv _ (transv_mem_xPoint x 1)
  rw [transv_mulVec, add_eq_left, one_mul, smul_eq_zero] at h
  exact mem_perp_span.2 (h.resolve_right hx)

theorem xPoint_map_conj (g : Sp4 F) (p : Submodule F (V4 F)) :
    (xPoint p).map (MulAut.conj g).toMonoidHom = xPoint (p.map (mulVecLin (mat g))) := by
  rw [fixer_map_conj]
  change fixer _ = fixer (perp _)
  rw [perp_map]

abbrev e₁ (F : Type) [Field F] : V4 F := Pi.single (.inl 0) 1

abbrev e₂ (F : Type) [Field F] : V4 F := Pi.single (.inl 1) 1

abbrev f₁ (F : Type) [Field F] : V4 F := Pi.single (.inr 0) 1

abbrev f₂ (F : Type) [Field F] : V4 F := Pi.single (.inr 1) 1

theorem e₁_ne_zero : e₁ F ≠ 0 := fun h => by simpa using congrFun h (.inl 0)

theorem pt₀_eq_span : pt₀ F = F ∙ e₁ F := by
  ext v
  rw [mem_pt₀, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨v (.inl 0), funext fun i => ?_⟩
    rcases i with i | i <;> fin_cases i <;> simp [h1, h2, h3]
  · rintro ⟨a, rfl⟩
    simp

theorem isPoint_pt₀ : IsPoint (pt₀ F) := by
  rw [pt₀_eq_span]
  exact isPoint_span e₁_ne_zero

theorem isLine_ln₀ : IsLine (ln₀ F) := by
  refine ⟨?_, fun x hx y hy => ?_⟩
  · exact (SymplecticHigher.unitriangular_invariant_isotropic_subspaces (r := 2) (K := F)).2.2.1.1
      2 le_rfl
  · rw [form_apply, (mem_ln₀.1 hx).1, (mem_ln₀.1 hx).2, (mem_ln₀.1 hy).1, (mem_ln₀.1 hy).2]
    ring

theorem card_sylS [Finite F] : Nat.card (sylS F) = Nat.card F ^ 4 := by
  rw [card_unipotent]
  norm_num

theorem exists_sylow_sylS [Finite F] [CharP F 2] :
    ∃ T : Sylow 2 (Sp4 F), (T : Subgroup (Sp4 F)) = sylS F :=
  exists_sylow_unipotent 2 2

theorem isPGroup_sylS [Finite F] [CharP F 2] : IsPGroup 2 (sylS F) := by
  obtain ⟨T, hT⟩ := exists_sylow_sylS (F := F)
  rw [← hT]
  exact T.isPGroup'

theorem sylS_le_borel : sylS F ≤ borel F := unipotent_le_borelSubgroup

theorem borel_eq_inf : borel F = P₁ F ⊓ P₂ F := by
  ext g
  rw [mem_borelSubgroup, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨h 2 (by norm_num) le_rfl, h 1 le_rfl (by norm_num)⟩
  · rintro ⟨h2, h1⟩ i hi1 hi2
    interval_cases i
    · exact h1
    · exact h2

theorem borel_le_P₁ : borel F ≤ P₁ F := by
  rw [borel_eq_inf]
  exact inf_le_left

theorem borel_le_P₂ : borel F ≤ P₂ F := by
  rw [borel_eq_inf]
  exact inf_le_right

theorem sylS_le_P₁ : sylS F ≤ P₁ F := sylS_le_borel.trans borel_le_P₁

theorem sylS_le_P₂ : sylS F ≤ P₂ F := sylS_le_borel.trans borel_le_P₂

theorem normalizer_sylS : Subgroup.normalizer (sylS F : Set (Sp4 F)) = borel F :=
  SymplecticHigher.normalizer_unipotent

theorem mulVec_blockMat_unitri (a : F) (C : Matrix (Fin 2) (Fin 2) F) (v : V4 F) :
    (blockMat (unitri a) C *ᵥ v) (.inl 0) = v (.inl 0) + a * v (.inl 1) +
        (C 0 0 + a * C 1 0) * v (.inr 0) + (C 0 1 + a * C 1 1) * v (.inr 1) ∧
      (blockMat (unitri a) C *ᵥ v) (.inl 1) = v (.inl 1) + C 1 0 * v (.inr 0) +
        C 1 1 * v (.inr 1) ∧
      (blockMat (unitri a) C *ᵥ v) (.inr 0) = v (.inr 0) ∧
      (blockMat (unitri a) C *ᵥ v) (.inr 1) = -a * v (.inr 0) + v (.inr 1) := by
  rw [blockMat, inv_unitri, fromBlocks_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, mulVec, dotProduct,
    Fin.sum_univ_two, unitri, Matrix.mul_apply, transpose_apply, Function.comp_apply, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Matrix.zero_apply]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem exists_of_mem_sylS {g : Sp4 F} (hg : g ∈ sylS F) :
    ∃ (a : F) (C : Matrix (Fin 2) (Fin 2) F), Cᵀ = C ∧ mat g = blockMat (unitri a) C := by
  obtain ⟨A, C, hA, hC, hg⟩ := mem_unipotent.1 hg
  refine ⟨A 0 1, C, hC, ?_⟩
  change ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [hg, ← eq_unitri_of_isUnitriangular hA]

theorem mem_sylS_of {g : Sp4 F} {a : F} {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (hg : mat g = blockMat (unitri a) C) : g ∈ sylS F :=
  mem_unipotent.2 ⟨unitri a, C, isUnitriangular_unitri a, hC, hg⟩

theorem mat_tau {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    mat (tau hC) = blockMat (unitri 0) C := by
  rw [mat, coe_tau, blockMat, unitri_zero, Matrix.one_mul, inv_one, transpose_one]

theorem mat_lam (a : F) : mat (lam a) = blockMat (unitri a) 0 := by
  rw [mat, coe_lam, blockMat, Matrix.mul_zero, inv_unitri]

theorem tau_mem_Q₁ {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) : tau hC ∈ Q₁ F := by
  intro v hv
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri 0 C v
  rw [mat_tau]
  funext i
  rcases i with i | i <;> fin_cases i
  · simp [e0, h0, h1]
  · simp [e1, h0, h1]
  · simp [e2]
  · simp [e3, h0]

theorem Q₁_eq_radical : Q₁ F = radical F := by
  refine le_antisymm (fun g hg => ?_) ?_
  · have hcol : ∀ j : Fin 2, mat g *ᵥ Pi.single (.inl j) 1 = Pi.single (.inl j) 1 := fun j =>
      hg _ (mem_ln₀.2 ⟨by simp, by simp⟩)
    have hent : ∀ (i : Fin 2 ⊕ Fin 2) (j : Fin 2),
        mat g i (.inl j) = (Pi.single (.inl j) (1 : F) : V4 F) i := fun i j => by
      rw [← hcol j, mulVec_single_one]
      rfl
    have h21 : (mat g).toBlocks₂₁ = 0 := by
      ext i j
      rw [toBlocks₂₁, of_apply, hent]
      simp
    have h11 : (mat g).toBlocks₁₁ = 1 := by
      ext i j
      rw [toBlocks₁₁, of_apply, hent, one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    obtain ⟨-, C, hC, hgC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
    refine ⟨C, hC, mat_injective ?_⟩
    change ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
    rw [hgC]
    change blockMat (mat g).toBlocks₁₁ C = _
    rw [h11, mat_tau, unitri_zero]
  · rintro _ ⟨C, hC, rfl⟩
    exact tau_mem_Q₁ hC

theorem card_Q₁ [Finite F] : Nat.card (Q₁ F) = Nat.card F ^ 3 := by
  rw [Q₁_eq_radical, card_radical]

theorem Q₁_le_sylS : Q₁ F ≤ sylS F := by
  rw [Q₁_eq_radical]
  exact radical_le_unipotent

theorem Q₁_le_P₁ : Q₁ F ≤ P₁ F := fixer_le_stab _

theorem P₁_le_normalizer_Q₁ : P₁ F ≤ Subgroup.normalizer (Q₁ F : Set (Sp4 F)) :=
  stab_le_normalizer_fixer _

theorem Q₁_comm {x y : Sp4 F} (hx : x ∈ Q₁ F) (hy : y ∈ Q₁ F) : x * y = y * x := by
  rw [Q₁_eq_radical] at hx hy
  obtain ⟨C, hC, rfl⟩ := hx
  obtain ⟨E, hE, rfl⟩ := hy
  exact tau_comm hC hE

theorem Q₁_sq [CharP F 2] {x : Sp4 F} (hx : x ∈ Q₁ F) : x ^ 2 = 1 := by
  rw [Q₁_eq_radical] at hx
  obtain ⟨C, hC, rfl⟩ := hx
  rw [sq, tau_mul_tau]
  apply mat_injective
  rw [mat_tau, mat_one, show C + C = 0 from by ext i j; exact CharTwo.add_self_eq_zero _,
    unitri_zero, blockMat_one]

theorem mulVec_tau_sym2 (b c d : F) (v : V4 F) :
    (mat (tau (sym2_transpose b c d)) *ᵥ v) (.inl 0) = v (.inl 0) + b * v (.inr 0) +
        c * v (.inr 1) ∧
      (mat (tau (sym2_transpose b c d)) *ᵥ v) (.inl 1) = v (.inl 1) + c * v (.inr 0) +
        d * v (.inr 1) ∧
      (mat (tau (sym2_transpose b c d)) *ᵥ v) (.inr 0) = v (.inr 0) ∧
      (mat (tau (sym2_transpose b c d)) *ᵥ v) (.inr 1) = v (.inr 1) := by
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri 0 (sym2 b c d) v
  rw [mat_tau, e0, e1, e2, e3]
  simp [sym2]

theorem mulVec_lam (a : F) (v : V4 F) :
    (mat (lam a) *ᵥ v) (.inl 0) = v (.inl 0) + a * v (.inl 1) ∧
      (mat (lam a) *ᵥ v) (.inl 1) = v (.inl 1) ∧ (mat (lam a) *ᵥ v) (.inr 0) = v (.inr 0) ∧
      (mat (lam a) *ᵥ v) (.inr 1) = -a * v (.inr 0) + v (.inr 1) := by
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri a 0 v
  rw [mat_lam, e0, e1, e2, e3]
  simp

theorem fixSp_Q₁ : fixSp (Q₁ F) = ln₀ F := by
  refine le_antisymm (fun v hv => mem_ln₀.2 ⟨?_, ?_⟩) (le_fixer_iff.1 le_rfl)
  · have h := congrFun (hv _ (tau_mem_Q₁ (sym2_transpose (1 : F) 0 0))) (.inl 0)
    rw [(mulVec_tau_sym2 1 0 0 v).1] at h
    simpa using h
  · have h := congrFun (hv _ (tau_mem_Q₁ (sym2_transpose (0 : F) 0 1))) (.inl 1)
    rw [(mulVec_tau_sym2 0 0 1 v).2.1] at h
    simpa using h

theorem commSp_Q₁ : commSp (Q₁ F) = ln₀ F := by
  refine le_antisymm (commSp_qLine_le isLine_ln₀) fun v hv => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  have k0 := sub_mem_commSp (tau_mem_Q₁ (sym2_transpose (v (.inl 0)) 0 (v (.inl 1)))) (f₁ F + f₂ F)
  convert k0 using 1
  funext i
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 (v (.inl 0)) 0 (v (.inl 1)) (f₁ F + f₂ F)
  rcases i with i | i <;> fin_cases i
  · simp [e0]
  · simp [e1]
  · simp [e2, h0]
  · simp [e3, h1]

theorem commSp_Q₁_le_fixSp : commSp (Q₁ F) ≤ fixSp (Q₁ F) := by
  rw [commSp_Q₁, fixSp_Q₁]

theorem finrank_fixSp_Q₁ : Module.finrank F (fixSp (Q₁ F)) = 2 := by
  rw [fixSp_Q₁]
  exact isLine_ln₀.1

theorem card_fixSp_Q₁ [Finite F] : Nat.card (fixSp (Q₁ F)) = Nat.card F ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_fixSp_Q₁]

theorem mat_apply_eq (g : Sp4 F) (i j : Fin 2 ⊕ Fin 2) :
    mat g i j = (mat g *ᵥ Pi.single j 1) i := by
  rw [mulVec_single_one]
  rfl

theorem lam_mem_sylS (a : F) : lam a ∈ sylS F := lam_mem_unipotent a

theorem entry_of_mem_sylS {g : Sp4 F} {a : F} {C : Matrix (Fin 2) (Fin 2) F}
    (hg : mat g = blockMat (unitri a) C) : mat g (.inl 1) (.inr 1) = C 1 1 := by
  rw [mat_apply_eq, hg, (mulVec_blockMat_unitri a C _).2.1]
  simp

theorem mem_Q₂_iff {g : Sp4 F} : g ∈ Q₂ F ↔ g ∈ sylS F ∧ mat g (.inl 1) (.inr 1) = 0 := by
  constructor
  · intro hg
    have he₁ : mat g *ᵥ e₁ F = e₁ F :=
      hg.1 _ (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
    have he₂ : mat g *ᵥ e₂ F - e₂ F ∈ pt₀ F := hg.2 _ (mem_perp_pt₀.2 (by simp))
    have hf₂ : mat g *ᵥ f₂ F - f₂ F ∈ pt₀ F := hg.2 _ (mem_perp_pt₀.2 (by simp))
    obtain ⟨a1, a2, a3⟩ := mem_pt₀.1 he₂
    obtain ⟨b1, -, -⟩ := mem_pt₀.1 hf₂
    simp only [Pi.sub_apply] at a1 a2 a3 b1
    have hc0 : ∀ i, mat g i (.inl 0) = e₁ F i := fun i => by rw [mat_apply_eq, he₁]
    have hc1 : ∀ i, mat g i (.inl 1) = (mat g *ᵥ e₂ F) i := fun i => mat_apply_eq g i _
    have h21 : (mat g).toBlocks₂₁ = 0 := by
      ext i j
      rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
      revert i
      revert j
      rw [Fin.forall_fin_two]
      refine ⟨fun i => by rw [hc0]; simp, ?_⟩
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · rw [hc1]
        simpa using a2
      · rw [hc1]
        simpa using a3
    obtain ⟨hdet, C, hC, hgC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
    have hA : IsUnitriangular (mat g).toBlocks₁₁ := by
      have h00 : (mat g).toBlocks₁₁ 0 0 = 1 := by rw [toBlocks₁₁, of_apply, hc0]; simp
      have h10 : (mat g).toBlocks₁₁ 1 0 = 0 := by rw [toBlocks₁₁, of_apply, hc0]; simp
      have h11 : (mat g).toBlocks₁₁ 1 1 = 1 := by
        rw [toBlocks₁₁, of_apply, hc1]
        simpa [sub_eq_zero] using a1
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact h10
      · revert i
        rw [Fin.forall_fin_two]
        exact ⟨h00, h11⟩
    refine ⟨mem_unipotent.2 ⟨_, C, hA, hC, hgC⟩, ?_⟩
    rw [mat_apply_eq]
    simpa [sub_eq_zero] using b1
  · rintro ⟨hS, h0⟩
    obtain ⟨a, C, hC, hg⟩ := exists_of_mem_sylS hS
    have hC11 : C 1 1 = 0 := by rw [← entry_of_mem_sylS hg, h0]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := mem_pt₀.1 hv
      obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri a C v
      rw [hg]
      funext i
      rcases i with i | i <;> fin_cases i
      · simp [e0, h1, h2, h3]
      · simp [e1, h1, h2, h3]
      · simp [e2]
      · simp [e3, h2, h3]
    · have h2 := mem_perp_pt₀.1 hv
      obtain ⟨-, e1, e2, e3⟩ := mulVec_blockMat_unitri a C v
      refine mem_pt₀.2 ⟨?_, ?_, ?_⟩ <;> rw [Pi.sub_apply, hg]
      · rw [e1, h2, hC11]
        ring
      · rw [e2, sub_self]
      · rw [e3, h2]
        ring

theorem Q₂_le_sylS : Q₂ F ≤ sylS F := fun _ hg => (mem_Q₂_iff.1 hg).1

theorem Q₂_le_P₂ : Q₂ F ≤ P₂ F := (qPoint_le_fixer _).trans (fixer_le_stab _)

theorem P₂_le_normalizer_Q₂ : P₂ F ≤ Subgroup.normalizer (Q₂ F : Set (Sp4 F)) :=
  stab_le_normalizer_qPoint _

theorem lam_mem_Q₂ (a : F) : lam a ∈ Q₂ F := by
  refine mem_Q₂_iff.2 ⟨lam_mem_sylS a, ?_⟩
  rw [mat_apply_eq, (mulVec_lam a _).2.1]
  simp

theorem tau_sym2_mem_Q₂ (b c : F) : tau (sym2_transpose b c 0) ∈ Q₂ F := by
  refine mem_Q₂_iff.2 ⟨tau_mem_unipotent _, ?_⟩
  rw [mat_apply_eq, (mulVec_tau_sym2 b c 0 _).2.1]
  simp

@[expose] def entryHom : sylS F →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (mat (g : Sp4 F) (.inl 1) (.inr 1))
  map_one' := by simp [mat_one]
  map_mul' g h := by
    obtain ⟨a, C, hC, hg⟩ := exists_of_mem_sylS g.2
    obtain ⟨b, E, hE, hh⟩ := exists_of_mem_sylS h.2
    rw [← ofAdd_add, mat_apply_eq, Subgroup.coe_mul, mat_mul_mulVec, entry_of_mem_sylS hg,
      entry_of_mem_sylS hh, hg]
    obtain ⟨-, e1, -⟩ := mulVec_blockMat_unitri a C (mat (h : Sp4 F) *ᵥ Pi.single (.inr 1) 1)
    rw [e1, ← mat_apply_eq, entry_of_mem_sylS hh, hh]
    obtain ⟨-, -, f2, f3⟩ := mulVec_blockMat_unitri b E (Pi.single (.inr 1) 1)
    rw [f2, f3]
    simp [add_comm]

theorem entryHom_apply (g : sylS F) :
    entryHom g = Multiplicative.ofAdd (mat (g : Sp4 F) (.inl 1) (.inr 1)) := rfl

theorem ker_entryHom : (entryHom (F := F)).ker = (Q₂ F).subgroupOf (sylS F) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Q₂_iff, entryHom_apply]
  simp [g.2]

theorem entryHom_surjective : Function.Surjective (entryHom (F := F)) := by
  intro d
  refine ⟨⟨tau (sym2_transpose 0 0 (Multiplicative.toAdd d)), tau_mem_unipotent _⟩, ?_⟩
  rw [entryHom_apply, mat_apply_eq, (mulVec_tau_sym2 0 0 _ _).2.1]
  simp

theorem card_Q₂ [Finite F] : Nat.card (Q₂ F) = Nat.card F ^ 3 := by
  have h := (entryHom (F := F)).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ entryHom_surjective).toEquiv,
    ker_entryHom, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q₂_le_sylS).toEquiv,
    card_sylS] at h
  have hq : 0 < Nat.card F := Nat.card_pos
  have hM : Nat.card (Multiplicative F) = Nat.card F := rfl
  rw [hM] at h
  have : Nat.card F ^ 4 = Nat.card F * Nat.card F ^ 3 := by ring
  rw [this] at h
  exact (Nat.eq_of_mul_eq_mul_left hq h).symm

theorem Q₁_sup_Q₂ : Q₁ F ⊔ Q₂ F = sylS F := by
  refine le_antisymm (sup_le Q₁_le_sylS Q₂_le_sylS) fun g hg => ?_
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hg
  exact Subgroup.mul_mem_sup (tau_mem_Q₁ hC) (lam_mem_Q₂ a)

theorem card_Q₁_inf_Q₂ [Finite F] : Nat.card ↥(Q₁ F ⊓ Q₂ F) = Nat.card F ^ 2 := by
  let φ : F × F → ↥(Q₁ F ⊓ Q₂ F) := fun x =>
    ⟨tau (sym2_transpose x.1 x.2 0), tau_mem_Q₁ _, tau_sym2_mem_Q₂ x.1 x.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have h := tau_injective _ _ (congrArg Subtype.val hxy)
      have h0 := congrFun₂ h 0 0
      have h1 := congrFun₂ h 0 1
      simp only [sym2, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one] at h0 h1
      exact Prod.ext h0 h1
    · have hg1 : (g : Sp4 F) ∈ radical F := by
        rw [← Q₁_eq_radical]
        exact (Subgroup.mem_inf.1 g.2).1
      have hg2 : (g : Sp4 F) ∈ Q₂ F := (Subgroup.mem_inf.1 g.2).2
      obtain ⟨C, hC, hgC⟩ := hg1
      have h11 : C 1 1 = 0 := by
        rw [← entry_of_mem_sylS (mat_tau hC), ← hgC]
        exact (mem_Q₂_iff.1 hg2).2
      refine ⟨(C 0 0, C 0 1), Subtype.ext ?_⟩
      change tau _ = (g : Sp4 F)
      rw [hgC]
      refine tau_congr _ _ ?_
      conv_rhs => rw [eq_sym2 hC]
      rw [h11]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod]
  ring

theorem fixSp_Q₂ : fixSp (Q₂ F) = pt₀ F := by
  refine le_antisymm (fun v hv => mem_pt₀.2 ⟨?_, ?_, ?_⟩)
    (le_fixer_iff.1 (qPoint_le_fixer _))
  · have h := congrFun (hv _ (lam_mem_Q₂ 1)) (.inl 0)
    rw [(mulVec_lam 1 v).1] at h
    simpa using h
  · have h := congrFun (hv _ (tau_sym2_mem_Q₂ 1 0)) (.inl 0)
    rw [(mulVec_tau_sym2 1 0 0 v).1] at h
    simpa using h
  · have h := congrFun (hv _ (tau_sym2_mem_Q₂ 0 1)) (.inl 0)
    rw [(mulVec_tau_sym2 0 1 0 v).1] at h
    simpa using h

theorem commSp_Q₂ : commSp (Q₂ F) = perp (pt₀ F) := by
  refine le_antisymm (commSp_le_iff.2 fun g hg v =>
    sub_mem_perp_of_mem_fixer (qPoint_le_fixer _ hg) v) fun v hv => ?_
  have h0 := mem_perp_pt₀.1 hv
  have k0 := sub_mem_commSp (tau_sym2_mem_Q₂ (v (.inl 0)) (v (.inl 1))) (f₁ F)
  have k1 := sub_mem_commSp (lam_mem_Q₂ (-v (.inr 1))) (f₁ F)
  convert add_mem k0 k1 using 1
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 (v (.inl 0)) (v (.inl 1)) 0 (f₁ F)
  obtain ⟨l0, l1, l2, l3⟩ := mulVec_lam (-v (.inr 1)) (f₁ F)
  refine ext4 ?_ ?_ ?_ ?_ <;> simp only [Pi.add_apply, Pi.sub_apply]
  · rw [e0, l0]
    simp
  · rw [e1, l1]
    simp
  · rw [e2, l2]
    simp [h0]
  · rw [e3, l3]
    simp

theorem not_commSp_Q₂_le_fixSp : ¬ commSp (Q₂ F) ≤ fixSp (Q₂ F) := by
  rw [commSp_Q₂, fixSp_Q₂]
  intro h
  have := (mem_pt₀.1 (h (mem_perp_pt₀.2 (show e₂ F (.inr 0) = 0 by simp)))).1
  simp at this

theorem finrank_fixSp_Q₂ : Module.finrank F (fixSp (Q₂ F)) = 1 := by
  rw [fixSp_Q₂]
  exact isPoint_pt₀

theorem transv_e₁ (c : F) : transv (e₁ F) c = tau (sym2_transpose c 0 0) := by
  refine ext_mulVec fun v => ?_
  funext i
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 c 0 0 v
  have hB : form F (e₁ F) v = v (.inr 0) := pairedSympForm_single_inl 0 v
  rw [transv_mulVec, hB]
  rcases i with i | i <;> fin_cases i
  · simp [e0]
  · simp [e1]
  · simp [e2]
  · simp [e3]

theorem mem_X₂_iff {g : Sp4 F} : g ∈ X₂ F ↔ ∃ c : F, transv (e₁ F) c = g := by
  rw [show X₂ F = xPoint (F ∙ e₁ F) by rw [← pt₀_eq_span]]
  exact mem_xPoint_span e₁_ne_zero

theorem X₂_le_Q₁ : X₂ F ≤ Q₁ F := fun g hg => by
  obtain ⟨c, rfl⟩ := mem_X₂_iff.1 hg
  rw [transv_e₁]
  exact tau_mem_Q₁ _

theorem X₂_le_Q₂ : X₂ F ≤ Q₂ F := fun g hg => by
  obtain ⟨c, rfl⟩ := mem_X₂_iff.1 hg
  rw [transv_e₁]
  exact tau_sym2_mem_Q₂ c 0

theorem card_X₂ [Finite F] : Nat.card (X₂ F) = Nat.card F := by
  have hφ : Function.Bijective fun c : F =>
      (⟨transv (e₁ F) c, mem_X₂_iff.2 ⟨c, rfl⟩⟩ : X₂ F) :=
    ⟨fun c d h => transv_injective e₁_ne_zero (congrArg Subtype.val h), fun g => by
      obtain ⟨c, hc⟩ := mem_X₂_iff.1 g.2
      exact ⟨c, Subtype.ext hc⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hφ)).symm

theorem commSp_X₂ : commSp (X₂ F) = pt₀ F := commSp_xPoint isPoint_pt₀

theorem fixSp_X₂ : fixSp (X₂ F) = perp (pt₀ F) := fixSp_xPoint isPoint_pt₀

theorem P₂_le_normalizer_X₂ : P₂ F ≤ Subgroup.normalizer (X₂ F : Set (Sp4 F)) :=
  stab_le_normalizer_xPoint _

end CFSG.Quasithin.MS93.MSP
