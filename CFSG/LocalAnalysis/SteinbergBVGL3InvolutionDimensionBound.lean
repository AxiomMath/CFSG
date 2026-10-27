module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModulesFlag
public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.SteinbergBV

open Module Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim

namespace ThreeInvolutions

@[expose] def t01 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def t12 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def t20 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

@[expose] def t02 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

@[expose] def t10 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

@[expose] def t21 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 0, 1, 1]

@[expose] def pMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def pMatInv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def invGL (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : M * M = 1) :
    GL (Fin 3) (ZMod 2) :=
  ⟨M, M, h, h⟩

@[expose] def pGL : GL (Fin 3) (ZMod 2) :=
  ⟨pMat, pMatInv, by decide, by decide⟩

abbrev T01 : GL (Fin 3) (ZMod 2) := invGL t01 (by decide)

abbrev T12 : GL (Fin 3) (ZMod 2) := invGL t12 (by decide)

abbrev T20 : GL (Fin 3) (ZMod 2) := invGL t20 (by decide)

theorem pGL_conj_T01 : pGL * T01 * pGL⁻¹ = T12 :=
  Units.ext <| by
    change pMat * t01 * pMatInv = t12
    decide

theorem pGL_conj_T12 : pGL * T12 * pGL⁻¹ = T20 :=
  Units.ext <| by
    change pMat * t12 * pMatInv = t20
    decide

theorem closure_tGL_eq_top :
    Subgroup.closure ({T01, T12, T20} : Set (GL (Fin 3) (ZMod 2))) = ⊤ := by
  set H := Subgroup.closure ({T01, T12, T20} : Set (GL (Fin 3) (ZMod 2))) with hH
  have h01 : T01 ∈ H := Subgroup.subset_closure (by simp)
  have h12 : T12 ∈ H := Subgroup.subset_closure (by simp)
  have h20 : T20 ∈ H := Subgroup.subset_closure (by simp)
  have h02 : invGL t02 (by decide) ∈ H := by
    have h : invGL t02 (by decide) = T01 * T12 * T01⁻¹ * T12⁻¹ :=
      Units.ext <| by
        change t02 = t01 * t12 * t01 * t12
        decide
    rw [h]
    exact mul_mem (mul_mem (mul_mem h01 h12) (inv_mem h01)) (inv_mem h12)
  have h10 : invGL t10 (by decide) ∈ H := by
    have h : invGL t10 (by decide) = T12 * T20 * T12⁻¹ * T20⁻¹ :=
      Units.ext <| by
        change t10 = t12 * t20 * t12 * t20
        decide
    rw [h]
    exact mul_mem (mul_mem (mul_mem h12 h20) (inv_mem h12)) (inv_mem h20)
  have h21 : invGL t21 (by decide) ∈ H := by
    have h : invGL t21 (by decide) = T20 * T01 * T20⁻¹ * T01⁻¹ :=
      Units.ext <| by
        change t21 = t20 * t01 * t20 * t01
        decide
    rw [h]
    exact mul_mem (mul_mem (mul_mem h20 h01) (inv_mem h20)) (inv_mem h01)
  have htr : ∀ t : TransvectionStruct (Fin 3) (ZMod 2),
      ∃ U ∈ H, (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) = t.toMatrix := by
    rintro ⟨i, j, hij, c⟩
    obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
    · exact ⟨1, one_mem _, by
        change (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = transvection i j 0
        rw [transvection_zero]⟩
    · change ∃ U ∈ H, (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) = transvection i j 1
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ⟨T01, h01, by decide⟩
      · exact ⟨invGL t02 (by decide), h02, by decide⟩
      · exact ⟨invGL t10 (by decide), h10, by decide⟩
      · exact absurd rfl hij
      · exact ⟨T12, h12, by decide⟩
      · exact ⟨T20, h20, by decide⟩
      · exact ⟨invGL t21 (by decide), h21, by decide⟩
      · exact absurd rfl hij
  have hlist : ∀ L : List (TransvectionStruct (Fin 3) (ZMod 2)),
      ∃ U ∈ H, (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, one_mem _, rfl⟩
    | cons t L ih =>
      obtain ⟨U, hU, hUe⟩ := htr t
      obtain ⟨U', hU', hU'e⟩ := ih
      exact ⟨U * U', mul_mem hU hU', by rw [Units.val_mul, hUe, hU'e, List.map_cons,
        List.prod_cons]⟩
  refine eq_top_iff.2 fun A _ => ?_
  obtain ⟨L, d, hd, h⟩ := CFSG.LinearGroups.row_addition_diagonalization A
  have hd1 : diagonal d = 1 := by
    have hd' : d = fun _ => 1 := funext fun i => by
      have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact key _ (hd i)
    rw [hd', diagonal_one]
  obtain ⟨U, hU, hUe⟩ := hlist L
  have hUA : U * A = 1 := Units.ext (by rw [Units.val_mul, hUe, h, hd1, Units.val_one])
  rw [eq_inv_of_mul_eq_one_right hUA]
  exact inv_mem hU

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_basis_toGL_eq_t01 (hV : finrank (ZMod 2) V = 3) {a : V ≃ₗ[ZMod 2] V}
    (ha : a * a = 1) (ha1 : a ≠ 1) : ∃ β : Basis (Fin 3) (ZMod 2) V, toGL β a = T01 := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have haa : ∀ x, a (a x) = x := fun x => by
    have h := DFunLike.congr_fun ha x
    rw [LinearEquiv.mul_apply] at h
    exact h
  set N : V →ₗ[ZMod 2] V := (a : V →ₗ[ZMod 2] V) - LinearMap.id with hN
  have hNx : ∀ x, N x = a x - x := fun x => rfl
  have hNN : ∀ x, N (N x) = 0 := fun x => by
    rw [hNx, hNx, map_sub, haa, show x - a x - (a x - x) = (x + x) - (a x + a x) by abel, h2,
      h2, sub_self]
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact ha1 (LinearEquiv.ext hcon)
  set u := N v with hu
  have hu0 : u ≠ 0 := by
    rw [hu, hNx]
    exact sub_ne_zero.2 hv
  have hNu : N u = 0 := hNN v
  have hrk := LinearMap.finrank_range_add_finrank_ker N
  rw [hV] at hrk
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨x, rfl⟩
    exact hNN x
  have hpos : 0 < finrank (ZMod 2) (LinearMap.range N) := by
    refine Nat.pos_of_ne_zero fun h0 => hu0 ?_
    rw [Submodule.finrank_eq_zero] at h0
    have : u ∈ LinearMap.range N := ⟨v, rfl⟩
    rwa [h0, Submodule.mem_bot] at this
  have hmono := Submodule.finrank_mono hle
  have hker2 : finrank (ZMod 2) (LinearMap.ker N) = 2 := by omega
  have hspan : Submodule.span (ZMod 2) {u} < LinearMap.ker N := by
    refine lt_of_le_of_ne ?_ fun h => ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hNu
    · have := finrank_span_singleton (K := ZMod 2) hu0
      rw [h, hker2] at this
      omega
  obtain ⟨w, hwker, hwspan⟩ := IsConcreteLE.exists_of_lt hspan
  have hNw : N w = 0 := hwker
  have hau : a u = u := sub_eq_zero.1 hNu
  have hav : a v = u + v := by rw [hu, hNx, sub_add_cancel]
  have haw : a w = w := sub_eq_zero.1 hNw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hwspan (Submodule.zero_mem _)
  have hvw : ∀ c : ZMod 2, c • w ≠ v := by
    intro c hc
    apply hu0
    rw [hu, ← hc, map_smul, hNw, smul_zero]
  have huvw : u ∉ Submodule.span (ZMod 2) {v, w} := by
    intro h
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 h
    have hN := congrArg N hst
    rw [map_add, map_smul, map_smul, hNw, smul_zero, add_zero, hNu, ← hu] at hN
    have hs : s = 0 := (smul_eq_zero.1 hN).resolve_right hu0
    rw [hs, zero_smul, zero_add] at hst
    have key : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases key t with rfl | rfl
    · rw [zero_smul] at hst
      exact hu0 hst.symm
    · rw [one_smul] at hst
      exact hwspan (by rw [hst]; exact Submodule.mem_span_singleton_self u)
  set β := basisThree hV hw0 hvw huvw with hβ
  have hβ0 : β 0 = u := (basisThree_apply hV hw0 hvw huvw).1
  have hβ1 : β 1 = v := (basisThree_apply hV hw0 hvw huvw).2.1
  have hβ2 : β 2 = w := (basisThree_apply hV hw0 hvw huvw).2.2
  refine ⟨β, Units.ext ?_⟩
  have key : (a : V →ₗ[ZMod 2] V) = Matrix.toLin β β t01 := by
    apply β.ext
    intro j
    rw [Matrix.toLin_self, Fin.sum_univ_three, hβ0, hβ1, hβ2]
    fin_cases j
    · simp [t01, hβ0, hau]
    · simp [t01, hβ1, hav]
    · simp [t01, hβ2, haw]
  rw [coe_toGL, key, LinearMap.toMatrix_toLin]
  rfl

theorem exists_closure_conj_eq_top (hV : finrank (ZMod 2) V = 3) {a : V ≃ₗ[ZMod 2] V}
    (ha : a * a = 1) (ha1 : a ≠ 1) : ∃ p : V ≃ₗ[ZMod 2] V,
      Subgroup.closure ({a, p * a * p⁻¹, p * (p * a * p⁻¹) * p⁻¹} :
        Set (V ≃ₗ[ZMod 2] V)) = ⊤ := by
  obtain ⟨β, hβ⟩ := exists_basis_toGL_eq_t01 hV ha ha1
  have hbij : Function.Bijective (toGL β) := (toGL_injective β).bijective_of_nat_card_le
    (by rw [card_GL3, natCard_linearEquiv hV])
  obtain ⟨p, hp⟩ := hbij.2 pGL
  refine ⟨p, eq_top_iff.2 fun x _ => ?_⟩
  have h2 : toGL β (p * a * p⁻¹) = T12 := by rw [map_mul, map_mul, map_inv, hp, hβ, pGL_conj_T01]
  have h3 : toGL β (p * (p * a * p⁻¹) * p⁻¹) = T20 := by
    rw [map_mul, map_mul, map_inv, hp, h2, pGL_conj_T12]
  have hx : toGL β x ∈ (Subgroup.closure ({a, p * a * p⁻¹, p * (p * a * p⁻¹) * p⁻¹} :
      Set (V ≃ₗ[ZMod 2] V))).map (toGL β) := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hβ,
      h2, h3, closure_tGL_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← toGL_injective β hyx]

end ThreeInvolutions

open ThreeInvolutions in
theorem GL3_three_involution_commutator_dimension_bound {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : finrank (ZMod 2) V = 3) {k E : Type*} [Field k] [AddCommGroup E]
    [Module k E] [FiniteDimensional k E] (ρ : Representation k (V ≃ₗ[ZMod 2] V) E)
    (hE : Submodule.span k {x : E | ∃ (g : V ≃ₗ[ZMod 2] V) (e : E), x = ρ g e - e} = ⊤)
    (a : V ≃ₗ[ZMod 2] V) (ha : a * a = 1) (ha1 : a ≠ 1) :
    finrank k E ≤ 3 * finrank k (LinearMap.range (ρ a - LinearMap.id)) := by
  obtain ⟨p, hp⟩ := exists_closure_conj_eq_top hV ha ha1
  set a₂ := p * a * p⁻¹ with ha₂
  set a₃ := p * a₂ * p⁻¹ with ha₃
  set R := LinearMap.range (ρ a - LinearMap.id) ⊔ LinearMap.range (ρ a₂ - LinearMap.id) ⊔
    LinearMap.range (ρ a₃ - LinearMap.id) with hR
  have hle : ∀ g ∈ Subgroup.closure ({a, a₂, a₃} : Set (V ≃ₗ[ZMod 2] V)),
      LinearMap.range (ρ g - LinearMap.id) ≤ R := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    | one =>
      rw [map_one]
      change LinearMap.range ((1 : Module.End k E) - 1) ≤ R
      rw [sub_self, LinearMap.range_zero]
      exact bot_le
    | mul x y _ _ hx hy =>
      have h : ρ (x * y) - LinearMap.id = (ρ x - LinearMap.id) ∘ₗ ρ y + (ρ y - LinearMap.id) := by
        rw [map_mul, LinearMap.sub_comp, LinearMap.id_comp]
        ext e
        simp
      rw [h]
      exact (LinearMap.range_add_le _ _).trans
        (sup_le ((LinearMap.range_comp_le_range _ _).trans hx) hy)
    | inv x _ hx =>
      have h : ρ x⁻¹ - LinearMap.id = -((ρ x - LinearMap.id) ∘ₗ ρ x⁻¹) := by
        ext e
        have h1 : ρ x (ρ x⁻¹ e) = e := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        simp [h1]
      rw [h, LinearMap.range_neg]
      exact (LinearMap.range_comp_le_range _ _).trans hx
  have hER : (⊤ : Submodule k E) ≤ R := by
    rw [← hE, Submodule.span_le]
    rintro _ ⟨g, e, rfl⟩
    exact hle g (hp ▸ Subgroup.mem_top g) ⟨e, by simp⟩
  have hconj : ∀ q b : V ≃ₗ[ZMod 2] V,
      finrank k (LinearMap.range (ρ (q * b * q⁻¹) - LinearMap.id)) ≤
      finrank k (LinearMap.range (ρ b - LinearMap.id)) := by
    intro q b
    have h : ρ (q * b * q⁻¹) - LinearMap.id = ρ q ∘ₗ ((ρ b - LinearMap.id) ∘ₗ ρ q⁻¹) := by
      ext e
      have h1 : ρ q (ρ q⁻¹ e) = e := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      simp [h1]
    rw [h, LinearMap.range_comp]
    exact (Submodule.finrank_map_le _ _).trans
      (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
  have h1 := Submodule.finrank_mono hER
  rw [finrank_top, hR] at h1
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (ρ a - LinearMap.id) ⊔ LinearMap.range (ρ a₂ - LinearMap.id))
    (LinearMap.range (ρ a₃ - LinearMap.id))
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (ρ a - LinearMap.id))
    (LinearMap.range (ρ a₂ - LinearMap.id))
  have h4 := hconj p a
  have h5 := hconj p a₂
  rw [← ha₂] at h4
  rw [← ha₃] at h5
  omega

end CFSG.LocalAnalysis.SteinbergBV
