module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.H13.L32AC44d
public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace SL3N

variable {F : Type} [Field F] [CharP F 2]

theorem tauSL_wJ : tauSL F (wJ : SL(3, F)) = wJ := by
  apply Subtype.ext
  rw [tauSL_coe, trInvMat, wJ_inv, wJ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def gammaSL : SL(3, F) ≃* SL(3, F) where
  toFun g := wJ * tauSL F g * wJ
  invFun g := wJ * tauSL F g * wJ
  left_inv g := by
    simp only [map_mul, tauSL_wJ, tauSL_tauSL]
    rw [show (wJ : SL(3, F)) * (wJ * g * wJ) * wJ = (wJ * wJ) * g * (wJ * wJ) by group,
      wJ_mul_self, one_mul, mul_one]
  right_inv g := by
    simp only [map_mul, tauSL_wJ, tauSL_tauSL]
    rw [show (wJ : SL(3, F)) * (wJ * g * wJ) * wJ = (wJ * wJ) * g * (wJ * wJ) by group,
      wJ_mul_self, one_mul, mul_one]
  map_mul' g h := by
    simp only [map_mul]
    rw [show (wJ : SL(3, F)) * (tauSL F g * tauSL F h) * wJ =
      wJ * tauSL F g * (wJ * wJ) * tauSL F h * wJ by rw [wJ_mul_self]; group]
    group

theorem gammaSL_apply (g : SL(3, F)) : gammaSL g = wJ * tauSL F g * wJ := rfl

theorem gammaSL_gammaSL (g : SL(3, F)) : gammaSL (gammaSL g) = g :=
  gammaSL.symm_apply_apply g

theorem gammaSL_up3 (x y z : F) : gammaSL (up3 x y z) = up3 z (y + z * x) x := by
  rw [gammaSL_apply, show tauSL F (up3 x y z) = u3 z (y + z * x) x from
    Subtype.ext (tau_up3 x y z), wJ_u3_wJ]

theorem gammaSL_mem_upperUni {u : SL(3, F)} (hu : u ∈ upperUni F) : gammaSL u ∈ upperUni F := by
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  rw [gammaSL_up3]
  exact mem_upperUni.mpr ⟨_, _, _, rfl⟩

theorem trace_gammaSL (g : SL(3, F)) :
    ((gammaSL g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace =
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace := by
  rw [gammaSL_apply, ← coe_mul_coe, ← coe_mul_coe, Matrix.trace_mul_cycle, coe_mul_coe wJ wJ,
    wJ_mul_self, show ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 from rfl, one_mul,
    tauSL_coe, trInvMat, Matrix.trace_transpose]

theorem gammaSL_not_inner : ¬ ∃ s : SL(3, F), ∀ g, gammaSL g = s * g * s⁻¹ := by
  rintro ⟨s, hs⟩
  have hdet : (!![0, 0, 1; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [Matrix.det_fin_three]
  have hdet' : (!![-1, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [Matrix.det_fin_three]
  set g : SL(3, F) := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], hdet⟩ with hg
  set h : SL(3, F) := ⟨!![-1, 1, 0; 0, 0, 1; 1, 0, 0], hdet'⟩ with hh
  have hgh : g * h = 1 := by
    apply Subtype.ext
    show !![0, 0, 1; 1, 0, 1; 0, 1, 0] * !![-1, 1, 0; 0, 0, 1; 1, 0, 0] =
      (1 : Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hginv : g⁻¹ = h := inv_eq_of_mul_eq_one_right hgh
  have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F).trace) (hs g)
  rw [trace_gammaSL, hginv, ← coe_mul_coe, ← coe_mul_coe, Matrix.trace_mul_cycle,
    coe_mul_coe s⁻¹ s, inv_mul_cancel, show ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 from
    rfl, one_mul] at h1
  have h2 : ((h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace = -1 := by
    simp [hh, Matrix.trace_fin_three]
  have h3 : ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace = 0 := by
    simp [hg, Matrix.trace_fin_three]
  rw [h2, h3] at h1
  exact one_ne_zero (neg_eq_zero.mp h1)

theorem mem_upperUni_of_borel (hF : Nat.card F = 2) {g : SL(3, F)} (hg : g ∈ borel F) :
    g ∈ upperUni F := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  refine mem_upperUni_of hg ?_ ?_
  · rcases G64.eq_zero_or_eq_one_of_card_two hF ((g : Matrix (Fin 3) (Fin 3) F) 0 0) with h | h
    · exact absurd h (diag00_ne_zero (e10 hg) (e20 hg) (e21 hg))
    · exact h
  · rcases G64.eq_zero_or_eq_one_of_card_two hF ((g : Matrix (Fin 3) (Fin 3) F) 2 2) with h | h
    · exact absurd h (diag22_ne_zero (e10 hg) (e20 hg) (e21 hg))
    · exact h

end SL3N

theorem false_of_equiv_sl32 (hN4 : LieBorelTwoInner) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 < n) (hq : CFSG.IsQuasisimple X) (hZ : Odd (Nat.card (Subgroup.center X)))
    (hLie : A315.IsLieChar2 n (X ⧸ Subgroup.center X)) (hr : CFSG.pRank 3 X = 1) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2) (φ : X ≃* SL(3, F)) : False := by
  classical
  have : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (n := 1) one_ne_zero
    (by rw [hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup X := (upperUni F).comap φ.toMonoidHom with hSdef
  have hSmem : ∀ y, y ∈ S ↔ φ y ∈ upperUni F := fun y => Iff.rfl
  have hS : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, ((isPGroup_upperUni (f := 1) (by rw [hF]; norm_num)).comap_of_injective
      φ.toMonoidHom φ.injective), ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, hSdef,
      Subgroup.index_comap_of_surjective _ φ.surjective]
    have h1 := (upperUni F).card_mul_index
    rw [card_upperUni, hF, LinearFlag.card_SL_eq (n := 3) (by norm_num), hF] at h1
    norm_num [Finset.prod_Icc_succ_top] at h1
    omega
  let α : MulAut X := (φ.trans SL3N.gammaSL).trans φ.symm
  have hα : ∀ y, φ (α y) = SL3N.gammaSL (φ y) := fun y => by simp [α]
  have hα2 : α ^ 2 ^ 1 = 1 := by
    refine MulEquiv.ext fun y => φ.injective ?_
    rw [pow_one, pow_two, MulAut.mul_apply, hα, hα, SL3N.gammaSL_gammaSL]
    rfl
  have hαS : S.map α.toMonoidHom = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hSmem _).mpr (by rw [show (α.toMonoidHom z) = α z from rfl, hα]; exact
        SL3N.gammaSL_mem_upperUni hz)
    · intro hy
      refine ⟨α y, (hSmem _).mpr ?_, ?_⟩
      · rw [hα]
        exact SL3N.gammaSL_mem_upperUni hy
      · apply φ.injective
        show φ (α (α y)) = φ y
        rw [hα, hα, SL3N.gammaSL_gammaSL]
  have hαB : ∀ b ∈ Subgroup.normalizer (S : Set X), α b * b⁻¹ ∈ S := by
    intro b hb
    have hbS : b ∈ S := by
      rw [hSmem]
      refine SL3N.mem_upperUni_of_borel hF (Subgroup.mem_normalizer_fintype fun u hu => ?_)
      have hu' : φ.symm u ∈ S := by rw [hSmem, MulEquiv.apply_symm_apply]; exact hu
      have h1 := (Subgroup.mem_normalizer_iff.mp hb _).mp hu'
      rw [hSmem, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      exact h1
    refine S.mul_mem ((hSmem _).mpr ?_) (S.inv_mem hbS)
    rw [hα]
    exact SL3N.gammaSL_mem_upperUni hbS
  obtain ⟨s, -, hs⟩ := hN4 X n hn hq hZ hLie hr S hS α ⟨1, hα2⟩ hαS hαB
  apply SL3N.gammaSL_not_inner (F := F)
  refine ⟨φ s, fun g => ?_⟩
  have h1 := congrArg (fun β : MulAut X => φ (β (φ.symm g))) hs
  simpa only [hα, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul, map_inv] using h1

end CFSG.Quasithin.H13.L32A.C
