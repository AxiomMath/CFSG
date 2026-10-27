module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Checks
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric
public import CFSG.GH74.KGroups.PSL2
public import CFSG.GroupTheory.PGL2Basic
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7

open CFSG.QuasithinUnique.A6Facts CFSG.GorensteinWalter CFSG.Quasithin Matrix

@[expose] def enum7 : Fin 7 → ZMod 7 := fun k => (k.val : ZMod 7)

theorem enum7_bij : Function.Bijective enum7 := by decide

noncomputable def ptE : Fin 8 ≃ Projectivization (ZMod 7) (Fin 2 → ZMod 7) :=
  CFSG.GH74.KGroups.PSL2.ptEquiv enum7 enum7_bij

noncomputable def rho : PGL2 (ZMod 7) →* Equiv.Perm (Fin 8) :=
  (Equiv.permCongrHom ptE.symm).toMonoidHom.comp
    (MulAction.toPermHom (PGL2 (ZMod 7)) (Projectivization (ZMod 7) (Fin 2 → ZMod 7)))

theorem ptE_rho (g : PGL2 (ZMod 7)) (i : Fin 8) : ptE (rho g i) = g • ptE i := by
  simp [rho, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem rho_mk (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) (hM : M.det ≠ 0) (σ : Equiv.Perm (Fin 8))
    (h : ∀ i : Fin 8, ∃ c : ZMod 7, c • (M *ᵥ CFSG.GH74.KGroups.PSL2.vecP enum7 i) =
      CFSG.GH74.KGroups.PSL2.vecP enum7 (σ i)) :
    rho (ProjGenLinGroup.mk (GeneralLinearGroup.mkOfDetNeZero M hM)) = σ := by
  ext1 i
  apply ptE.injective
  rw [ptE_rho]
  symm
  change CFSG.GH74.KGroups.PSL2.pt enum7 (σ i) =
    ProjGenLinGroup.mk (GeneralLinearGroup.mkOfDetNeZero M hM) • CFSG.GH74.KGroups.PSL2.pt enum7 i
  unfold CFSG.GH74.KGroups.PSL2.pt
  rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff']
  simp only [Units.smul_def, Matrix.smul_eq_mulVec]
  exact h i

@[expose] def g1 : Equiv.Perm (Fin 8) where
  toFun := ![1, 2, 3, 4, 5, 6, 0, 7]
  invFun := ![6, 0, 1, 2, 3, 4, 5, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def g2 : Equiv.Perm (Fin 8) where
  toFun := ![7, 1, 4, 5, 2, 3, 6, 0]
  invFun := ![7, 1, 4, 5, 2, 3, 6, 0]
  left_inv := by decide
  right_inv := by decide

theorem gens_code : [g1, g2].map (codeN 8) = gGenC := by decide

@[expose] def mat1 : Matrix (Fin 2) (Fin 2) (ZMod 7) := !![1, 0; 1, 1]

@[expose] def mat2 : Matrix (Fin 2) (Fin 2) (ZMod 7) := !![0, 1; 1, 0]

theorem mat1_det : mat1.det ≠ 0 := by
  rw [mat1, Matrix.det_fin_two_of]
  decide

theorem mat2_det : mat2.det ≠ 0 := by
  rw [mat2, Matrix.det_fin_two_of]
  decide

theorem act1 : ∀ i : Fin 8, ∃ c : ZMod 7, c • (mat1 *ᵥ CFSG.GH74.KGroups.PSL2.vecP enum7 i) =
    CFSG.GH74.KGroups.PSL2.vecP enum7 (g1 i) := by
  decide +kernel

theorem act2 : ∀ i : Fin 8, ∃ c : ZMod 7, c • (mat2 *ᵥ CFSG.GH74.KGroups.PSL2.vecP enum7 i) =
    CFSG.GH74.KGroups.PSL2.vecP enum7 (g2 i) := by
  decide +kernel

@[expose] def G0 : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure {g | g ∈ [g1, g2]}

theorem g_build' : gLit = Core.buildCodes (List.range 8) gGenC gTree := g_build

theorem g_tbl' :
    Core.tblCheckC (List.range 8) gGenC (Core.buildCodes (List.range 8) gGenC gTree) gTbl = true := by
  rw [← g_build']
  exact g_tbl

theorem mem_G0_iff (σ : Equiv.Perm (Fin 8)) : σ ∈ G0 ↔ codeN 8 σ ∈ gLit := by
  rw [g_build']
  exact (mem_closure_iff_of_tblN gens_code g_tbl').1 σ

theorem exists_mem_G0 {c : List ℕ} (hc : c ∈ gLit) : ∃ σ ∈ G0, codeN 8 σ = c := by
  rw [g_build'] at hc
  exact (mem_closure_iff_of_tblN gens_code g_tbl').2 c hc

theorem card_G0 : Nat.card G0 = 336 := by
  have hnd : (Core.buildCodes (List.range 8) gGenC gTree).Nodup := g_build' ▸ g_nodup
  rw [G0, card_closure_eq_of_tblN gens_code g_tbl' hnd, ← g_build', g_length]

theorem card_pgl2_zmod7 : Nat.card (PGL2 (ZMod 7)) = 336 := by
  rw [pgl2_card_formula, Nat.card_zmod]
  norm_num

theorem G0_le_range : G0 ≤ rho.range := by
  rw [G0, Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl
  · exact ⟨_, rho_mk mat1 mat1_det g1 act1⟩
  · exact ⟨_, rho_mk mat2 mat2_det g2 act2⟩

theorem rho_range : rho.range = G0 := by
  refine (Subgroup.eq_of_le_of_card_ge G0_le_range ?_).symm
  rw [card_G0, ← card_pgl2_zmod7]
  exact Nat.card_le_card_of_surjective _ rho.rangeRestrict_surjective

theorem rho_injective : Function.Injective rho := by
  have hb := rho.rangeRestrict_surjective.bijective_of_nat_card_le
    (by rw [rho_range, card_G0, card_pgl2_zmod7])
  intro a b hab
  exact hb.1 (Subtype.ext hab)

theorem nonempty_equiv_pgl2_zmod {X : Type} [Group X] (h : CFSG.Quasithin.F6.IsPGL2 7 X) :
    Nonempty (X ≃* PGL2 (ZMod 7)) := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let σ : ZMod 7 ≃+* K := ZMod.ringEquivOfPrime K (by norm_num) hc
  let e₂ : GL (Fin 2) K ⧸ CFSG.Open.StatedScalars (Fin 2) K ≃* PGL2 K :=
    QuotientGroup.quotientMulEquivOfEq (M := CFSG.Open.StatedScalars (Fin 2) K)
      (N := Subgroup.center (GL (Fin 2) K))
      (by rw [CFSG.Open.StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar])
  exact ⟨e.trans (e₂.trans (pgl2RingEquiv σ.symm))⟩

structure IsF7Emb {X : Type} [Group X] (φ : X →* Equiv.Perm (Fin 8)) : Prop where
  inj : Function.Injective φ
  mem : ∀ x, codeN 8 (φ x) ∈ gLit
  surj : ∀ c ∈ gLit, ∃ x, codeN 8 (φ x) = c

structure IsF7Model {X : Type} [Group X] (φ : X →* Equiv.Perm (Fin 8)) (Tb : Subgroup X) : Prop
    extends IsF7Emb φ where
  memT : ∀ x, x ∈ Tb ↔ codeN 8 (φ x) ∈ tLit

section Codes

variable {X : Type} [Group X] {φ : X →* Equiv.Perm (Fin 8)}

theorem code_mul (x y : X) :
    codeN 8 (φ (x * y)) = Core.cmul (codeN 8 (φ x)) (codeN 8 (φ y)) := by
  rw [map_mul, codeN_mul]

theorem code_one : codeN 8 (φ 1) = cid := by
  rw [map_one, codeN_one]
  rfl

theorem IsF7Emb.code_inj (h : IsF7Emb φ) {x y : X} (hxy : codeN 8 (φ x) = codeN 8 (φ y)) :
    x = y :=
  h.inj (codeN_injective hxy)

theorem IsF7Emb.eq_one (h : IsF7Emb φ) {x : X} (hx : codeN 8 (φ x) = cid) : x = 1 :=
  h.code_inj (by rw [hx, code_one])

theorem IsF7Emb.card_eq (h : IsF7Emb φ) {H : Subgroup X} {l : List (List ℕ)}
    (hH : ∀ x, x ∈ H ↔ codeN 8 (φ x) ∈ l) (hl : ∀ c ∈ l, c ∈ gLit) (hnd : l.Nodup) :
    Nat.card H = l.length := by
  classical
  let f : H → l.toFinset := fun x => ⟨codeN 8 (φ x), List.mem_toFinset.2 ((hH x).1 x.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (h.code_inj (congrArg Subtype.val hxy)),
      fun ⟨c, hc⟩ => ?_⟩
    have hc' := List.mem_toFinset.1 hc
    obtain ⟨x, rfl⟩ := h.surj c (hl c hc')
    exact ⟨⟨x, (hH x).2 hc'⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

@[expose] def subL [Finite X] (φ : X →* Equiv.Perm (Fin 8)) (l : List (List ℕ)) (h1 : cid ∈ l)
    (hm : ∀ c ∈ l, ∀ d ∈ l, Core.cmul c d ∈ l) : Subgroup X where
  carrier := {x | codeN 8 (φ x) ∈ l}
  one_mem' := by
    change codeN 8 (φ 1) ∈ l
    rw [code_one]
    exact h1
  mul_mem' := by
    intro a b ha hb
    change codeN 8 (φ (a * b)) ∈ l
    rw [code_mul]
    exact hm _ ha _ hb
  inv_mem' := by
    intro a ha
    have hpow : ∀ n : ℕ, codeN 8 (φ (a ^ n)) ∈ l := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero, code_one]
        exact h1
      | succ n ih =>
        rw [pow_succ, code_mul]
        exact hm _ ih _ ha
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
    change codeN 8 (φ a⁻¹) ∈ l
    rw [← hn]
    exact hpow n

theorem mem_subL [Finite X] {l : List (List ℕ)} {h1 : cid ∈ l}
    {hm : ∀ c ∈ l, ∀ d ∈ l, Core.cmul c d ∈ l} {x : X} :
    x ∈ subL φ l h1 hm ↔ codeN 8 (φ x) ∈ l :=
  Iff.rfl

end Codes

theorem exists_model {X : Type} [Group X] [Finite X] (hX : CFSG.Quasithin.F6.IsPGL2 7 X)
    {Tb : Subgroup X} (hTb : IsSylowIn 2 Tb ⊤) : ∃ φ : X →* Equiv.Perm (Fin 8), IsF7Model φ Tb := by
  obtain ⟨ψ⟩ := nonempty_equiv_pgl2_zmod hX
  set φ₀ : X →* Equiv.Perm (Fin 8) := rho.comp ψ.toMonoidHom with hφ₀
  have hemb : IsF7Emb φ₀ := by
    refine ⟨rho_injective.comp ψ.injective, fun x => ?_, fun c hc => ?_⟩
    · exact (mem_G0_iff _).1 (rho_range ▸ ⟨ψ x, rfl⟩)
    · obtain ⟨σ, hσ, rfl⟩ := exists_mem_G0 hc
      rw [← rho_range] at hσ
      obtain ⟨g, rfl⟩ := hσ
      exact ⟨ψ.symm g, by simp [φ₀]⟩
  set T' := subL φ₀ tLit t_one t_mul with hT'
  have hT'card : Nat.card T' = 16 := by
    rw [hemb.card_eq (fun x => mem_subL) t_sub t_nodup, t_length]
  have hX336 : Nat.card X = 336 := CFSG.GroupTheory.card_of_isPGL2_seven hX
  have hT'p : IsPGroup 2 T' := IsPGroup.of_card (n := 4) (by rw [hT'card]; norm_num)
  have hT'i : T'.index = 21 := by
    have := T'.index_mul_card
    rw [hT'card, hX336] at this
    omega
  have hTbi : ¬ 2 ∣ Tb.index := by
    have := hTb.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  let S' : Sylow 2 X := hT'p.toSylow (by rw [hT'i]; decide)
  let Sb : Sylow 2 X := hTb.isPGroup.toSylow hTbi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' Sb
  have hmemTb : ∀ x, x ∈ Tb ↔ g⁻¹ * x * g ∈ T' := by
    intro x
    have hx : x ∈ Tb ↔ x ∈ ((g • S' : Sylow 2 X) : Subgroup X) := by rw [hg]; rfl
    rw [hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [S', MulAut.smul_def]
  refine ⟨φ₀.comp (MulAut.conj g⁻¹).toMonoidHom, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · exact hemb.inj.comp (MulAut.conj g⁻¹).injective
  · intro x
    exact hemb.mem _
  · intro c hc
    obtain ⟨x, rfl⟩ := hemb.surj c hc
    refine ⟨g * x * g⁻¹, ?_⟩
    simp [mul_assoc]
  · intro x
    rw [hmemTb x]
    simp [T', mem_subL]

end CFSG.LocalAnalysis.WeakClosure81.NFF7
