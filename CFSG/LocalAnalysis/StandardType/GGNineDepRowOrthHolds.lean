module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowOrth
public import CFSG.LocalAnalysis.StandardType.GGNineDepNegLift
public import CFSG.LocalAnalysis.StandardType.GGWeylE8CardBound
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Weyl
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace NineDepOrth

@[expose] def cartanA7 : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (CartanMatrix.A 7).map (Int.cast : ℤ → ZMod 3)

@[expose] def refl7 : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  Matrix.of fun a b => (if a = b then 1 else 0) - (if a = 0 then cartanA7 0 b else 0)

@[expose] def isoG : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![2, 1, 1, 2, 2, 0, 0; 1, 0, 2, 0, 2, 2, 1; 1, 2, 2, 2, 1, 1, 1; 1, 1, 2, 2, 0, 0, 1;
    0, 1, 2, 1, 2, 0, 0; 1, 0, 0, 0, 0, 0, 2; 1, 0, 1, 0, 0, 2, 1]

@[expose] def isoH : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![2, 1, 1, 2, 2, 0, 1; 2, 0, 2, 1, 1, 1, 2; 1, 0, 0, 1, 1, 2, 0; 0, 1, 1, 1, 0, 0, 0;
    2, 1, 0, 1, 0, 1, 0; 0, 2, 2, 0, 1, 1, 2; 0, 0, 1, 1, 1, 1, 0]

@[expose] def isoGi : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 2, 1, 2, 1, 1, 2; 2, 2, 2, 0, 1, 1, 0; 1, 2, 0, 2, 0, 2, 1; 0, 1, 1, 1, 0, 0, 0;
    1, 1, 0, 2, 0, 2, 2; 0, 0, 2, 0, 2, 0, 1; 1, 2, 1, 2, 1, 0, 2]

@[expose] def isoHi : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![0, 0, 2, 2, 1, 0, 1; 1, 2, 1, 1, 1, 2, 2; 0, 2, 1, 2, 2, 1, 2; 2, 2, 1, 1, 0, 0, 2;
    1, 0, 1, 0, 0, 1, 0; 0, 2, 0, 0, 1, 1, 0; 0, 1, 2, 0, 1, 1, 2]

theorem isoG_isom : isoG.transpose * cartanA7 * isoG = cartanA7 := by decide +kernel

theorem isoH_isom : isoH.transpose * cartanA7 * isoH = cartanA7 := by decide +kernel

theorem isoG_mul_isoGi : isoG * isoGi = 1 := by decide +kernel

theorem isoGi_mul_isoG : isoGi * isoG = 1 := by decide +kernel

theorem isoH_mul_isoHi : isoH * isoHi = 1 := by decide +kernel

theorem isoHi_mul_isoH : isoHi * isoH = 1 := by decide +kernel

theorem refl7_mul_comm : refl7 * (isoG * isoH * isoGi * isoHi) = -1 := by decide +kernel

theorem cartanA7_succ_castSucc : ∀ l : Fin 6, cartanA7 l.succ l.castSucc = -1 := by decide

theorem cartanA7_castSucc_succ : ∀ l : Fin 6, cartanA7 l.castSucc l.succ = -1 := by decide

theorem cartanA7_symm (k l : Fin 7) : cartanA7 k l = cartanA7 l k := by
  simp only [cartanA7, Matrix.map_apply]
  rw [(CartanMatrix.A_isSymm 7).apply]

section D7

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}

theorem isIsom_of_polar_eq {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (g : U ≃ₗ[ZMod 3] U)
    (hg : ∀ u w, QuadraticMap.polar Q (g u) (g w) = QuadraticMap.polar Q u w) :
    ZS.IsIsom 3 Q g := by
  intro v
  have h1 := hg v v
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at h1
  have h2 := congrArg (fun c : ZMod 3 => 2 • c) h1
  simp only [smul_smul] at h2
  rw [show (2 : ℕ) * 2 = 4 from rfl] at h2
  have h4 : ∀ c : ZMod 3, (4 : ℕ) • c = c := by decide
  rwa [h4, h4] at h2

theorem false_d7 (X : GGNineDepCtx h α r s x) (hO : GGOrthType (ggNineQ X))
    (hd : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 7) : False := by
  classical
  have C := X.case
  haveI : Module.Finite (ZMod 3) V := l04nD2_finite C
  set TT := ggFixLineT r s with hTT
  let hT : Fin (9 - 1) → TT := fun i => ⟨h i, l04nD2_h_mem_T C i⟩
  have hli : LinearIndependent (ZMod 3) (fun j : Fin 7 => hT (ggNineSeven j)) :=
    LinearIndependent.of_comp TT.subtype (ggNineDep_linearIndependent_seven C)
  let b : Module.Basis (Fin 7) (ZMod 3) TT :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hd])
  have hb : ∀ j, b j = hT (ggNineSeven j) := fun j => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  obtain ⟨Q, -, hisom, hcomm⟩ := hO
  have hrA : ∀ i, r i ∈ ggLargeGrp r s := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  set ρ := ggLargeRho r s X.hA with hρ
  let gr : Fin (9 - 1) → (TT ≃ₗ[ZMod 3] TT) := fun i => ρ ⟨r i, hrA i⟩
  have hgrQ : ∀ i, gr i ∈ ggNineQ X := fun i => ⟨_, rfl⟩
  have hgr : ∀ i (u : TT), gr i u = u - α i (u : V) • hT i := by
    intro i u
    apply Subtype.ext
    rw [ggLargeRho_apply_coe]
    exact C.lin.refl_form i u
  have hgrh : ∀ i, gr i (hT i) = -hT i := by
    intro i
    rw [hgr]
    apply Subtype.ext
    simp only [hT, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg,
      l04nD2_pair_diag C i]
    module
  have hpol : ∀ i (u : TT), QuadraticMap.polar Q u (hT i) =
      2 * α i (u : V) * QuadraticMap.polar Q (hT i) (hT i) := by
    intro i u
    have hI : ∀ v, Q (gr i v) = Q v := hisom (gr i) (hgrQ i)
    have hiso : QuadraticMap.polar Q (gr i u) (gr i (hT i)) = QuadraticMap.polar Q u (hT i) := by
      simp only [QuadraticMap.polar, ← map_add, hI]
    rw [hgr, hgrh, QuadraticMap.polar_neg_right, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_smul_left, smul_eq_mul] at hiso
    have key : ∀ p a n : ZMod 3, -(p - a * n) = p → p = 2 * a * n := by decide
    exact key _ _ _ hiso
  let N : Fin 7 → ZMod 3 := fun l => QuadraticMap.polar Q (hT (ggNineSeven l)) (hT (ggNineSeven l))
  have hpair : ∀ k l : Fin 7, α (ggNineSeven l) ((hT (ggNineSeven k) : TT) : V) = cartanA7 l k := by
    intro k l
    rw [ggNineDep_pair_seven C]
    rfl
  have hgram : ∀ k l : Fin 7, QuadraticMap.polar Q (hT (ggNineSeven k)) (hT (ggNineSeven l)) =
      2 * cartanA7 l k * N l := by
    intro k l
    rw [hpol, hpair]
  have hsucc : ∀ l : Fin 6, N l.succ = N l.castSucc := by
    intro l
    have h1 := hgram l.castSucc l.succ
    have h2 := hgram l.succ l.castSucc
    rw [QuadraticMap.polar_comm] at h2
    rw [h2] at h1
    rw [cartanA7_succ_castSucc, cartanA7_castSucc_succ] at h1
    have key : ∀ m n : ZMod 3, 2 * -1 * m = 2 * -1 * n → n = m := by decide
    exact key _ _ h1
  have hN : ∀ l : Fin 7, N l = N 0 := by
    intro l
    fin_cases l
    · rfl
    · exact hsucc 0
    · exact (hsucc 1).trans (hsucc 0)
    · exact ((hsucc 2).trans (hsucc 1)).trans (hsucc 0)
    · exact (((hsucc 3).trans (hsucc 2)).trans (hsucc 1)).trans (hsucc 0)
    · exact ((((hsucc 4).trans (hsucc 3)).trans (hsucc 2)).trans (hsucc 1)).trans (hsucc 0)
    · exact (((((hsucc 5).trans (hsucc 4)).trans (hsucc 3)).trans (hsucc 2)).trans
        (hsucc 1)).trans (hsucc 0)
  have hM : LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin Q) = (2 * N 0) • cartanA7 := by
    ext k l
    rw [LinearMap.toMatrix₂_apply, QuadraticMap.polarBilin_apply_apply, hb, hb, hgram, hN,
      cartanA7_symm, Matrix.smul_apply, smul_eq_mul]
    ring
  have hiso : ∀ M Mi : Matrix (Fin 7) (Fin 7) (ZMod 3), M.transpose * cartanA7 * M = cartanA7 →
      M * Mi = 1 → Mi * M = 1 → ∃ g : TT ≃ₗ[ZMod 3] TT, ZS.IsIsom 3 Q g ∧
        (g : TT →ₗ[ZMod 3] TT) = Matrix.toLin b b M ∧
        (g.symm : TT →ₗ[ZMod 3] TT) = Matrix.toLin b b Mi := by
    intro M Mi hMiso h1 h2
    refine ⟨LinearEquiv.ofLinear (Matrix.toLin b b M) (Matrix.toLin b b Mi) ?_ ?_, ?_, rfl, rfl⟩
    · rw [← Matrix.toLin_mul, h1, Matrix.toLin_one]
    · rw [← Matrix.toLin_mul, h2, Matrix.toLin_one]
    · apply isIsom_of_polar_eq
      have hB : (QuadraticMap.polarBilin Q).compl₁₂ (Matrix.toLin b b M) (Matrix.toLin b b M) =
          QuadraticMap.polarBilin Q := by
        apply (LinearMap.toMatrix₂ b b).injective
        rw [LinearMap.toMatrix₂_compl₁₂ (b₁ := b) (b₂ := b), hM, LinearMap.toMatrix_toLin,
          Matrix.mul_smul,
          Matrix.smul_mul, hMiso]
      intro u w
      have := LinearMap.congr_fun₂ hB u w
      simpa [QuadraticMap.polarBilin_apply_apply] using this
  obtain ⟨gG, hGiso, hGl, hGs⟩ := hiso isoG isoGi isoG_isom isoG_mul_isoGi isoGi_mul_isoG
  obtain ⟨gH, hHiso, hHl, hHs⟩ := hiso isoH isoHi isoH_isom isoH_mul_isoHi isoHi_mul_isoH
  have hR : (gr (ggNineSeven 0) : TT →ₗ[ZMod 3] TT) = Matrix.toLin b b refl7 := by
    refine b.ext fun k => ?_
    rw [Matrix.toLin_self]
    change gr (ggNineSeven 0) (b k) = _
    rw [hgr, hb, hpair]
    simp only [refl7, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hb]
  have hmem : gr (ggNineSeven 0) * (gG * gH * gG⁻¹ * gH⁻¹) ∈ ggNineQ X :=
    (ggNineQ X).mul_mem (hgrQ _) (hcomm gG gH hGiso hHiso)
  have hneg : ∀ v, (gr (ggNineSeven 0) * (gG * gH * gG⁻¹ * gH⁻¹)) v = -v := by
    have hlin : ((gr (ggNineSeven 0) * (gG * gH * gG⁻¹ * gH⁻¹) : TT ≃ₗ[ZMod 3] TT) :
        TT →ₗ[ZMod 3] TT) = Matrix.toLin b b (-1) := by
      rw [← refl7_mul_comm, Matrix.toLin_mul b b b, Matrix.toLin_mul b b b,
        Matrix.toLin_mul b b b, Matrix.toLin_mul b b b, ← hR, ← hGl, ← hHl, ← hGs, ← hHs]
      apply LinearMap.ext
      intro v
      rfl
    intro v
    have := LinearMap.congr_fun hlin v
    simpa using this
  exact ggNineDep_false_of_neg_mem X (hd.trans_le (by norm_num)) hmem hneg

end D7


section Central

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}

theorem finrank_eq_nine_of_central (X : GGNineDepCtx h α r s x) {z : V ≃ₗ[ZMod 3] V}
    (hz : z ∈ Subgroup.closure (Set.range s)) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hcent : ∀ k, z * s k = s k * z) : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 9 := by
  classical
  have C := X.case
  haveI : Module.Finite (ZMod 3) V := l04nD2_finite C
  have hz2 : ∀ v, z (z v) = v := by
    intro v
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hzz
    simpa [LinearEquiv.mul_apply] using this
  have hzs : ∀ k v, z (s k v) = s k (z v) := by
    intro k v
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) (hcent k)
    simpa [LinearEquiv.mul_apply] using this
  let Vp : Submodule (ZMod 3) V := LinearMap.ker ((z : V →ₗ[ZMod 3] V) - LinearMap.id)
  let Vm : Submodule (ZMod 3) V := LinearMap.ker ((z : V →ₗ[ZMod 3] V) + LinearMap.id)
  have hVp : ∀ v, v ∈ Vp ↔ z v = v := by
    intro v
    simp [Vp, sub_eq_zero]
  have hVm : ∀ v, v ∈ Vm ↔ z v = -v := by
    intro v
    simp [Vm, add_eq_zero_iff_eq_neg]
  have h2 : ∀ c : ZMod 3, (2 : ZMod 3) * 2 * c = c := by decide
  have hdec : ∀ v, (2 : ZMod 3) • (v + z v) ∈ Vp ∧ (2 : ZMod 3) • (v - z v) ∈ Vm ∧
      v = (2 : ZMod 3) • (v + z v) + (2 : ZMod 3) • (v - z v) := by
    intro v
    refine ⟨(hVp _).mpr ?_, (hVm _).mpr ?_, ?_⟩
    · rw [map_smul, map_add, hz2, add_comm]
    · rw [map_smul, map_sub, hz2, ← smul_neg, neg_sub]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul (ZMod 3) v, smul_smul]
      have : (2 : ZMod 3) * 2 = 1 := by decide
      rw [this, one_smul]
  have hinf : ∀ v, v ∈ Vp → v ∈ Vm → v = 0 := by
    intro v hp hm
    rw [hVp] at hp
    rw [hVm, hp] at hm
    have h3 : (2 : ZMod 3) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hm]
      exact neg_add_cancel v
    have h4 := congrArg (fun u => (2 : ZMod 3) • u) h3
    simp only [smul_zero, smul_smul] at h4
    rwa [show (2 : ZMod 3) * 2 = 1 from rfl, one_smul] at h4
  have hsVp : ∀ k v, v ∈ Vp → s k v ∈ Vp := fun k v hv => by
    rw [hVp] at hv ⊢
    rw [hzs, hv]
  have hsVm : ∀ k v, v ∈ Vm → s k v ∈ Vm := fun k v hv => by
    rw [hVm] at hv ⊢
    rw [hzs, hv, map_neg]
  have hmove : ∀ k v, s k v - v ∈ ggLinMove (s k) := fun k v =>
    LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hside : ∀ k, ggLinMove (s k) ≤ Vp ∨ ggLinMove (s k) ≤ Vm := by
    intro k
    obtain ⟨w, hw0, hwspan⟩ := finrank_eq_one_iff'.mp (C.lin.s_refl k).2
    have hzw : (z (w : V)) ∈ ggLinMove (s k) := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
      refine LinearMap.mem_range.mpr ⟨z u, ?_⟩
      rw [← hu]
      simp [hzs]
    obtain ⟨c, hc⟩ := hwspan ⟨_, hzw⟩
    have hc' : c • (w : V) = z w := congrArg Subtype.val hc
    have hcc : c * c = 1 := by
      have h1 : (c * c) • (w : V) = (w : V) := by
        rw [← smul_smul, hc', ← map_smul, hc', hz2]
      by_contra hne
      have h2' : (c * c - 1) • (w : V) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2' with h3 | h3
      · exact hne (sub_eq_zero.mp h3)
      · exact hw0 (Subtype.ext h3)
    have hcases : ∀ c : ZMod 3, c * c = 1 → c = 1 ∨ c = -1 := by decide
    have hspan : ∀ m ∈ ggLinMove (s k), ∃ a : ZMod 3, a • (w : V) = m := by
      intro m hm
      obtain ⟨a, ha⟩ := hwspan ⟨m, hm⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    rcases hcases c hcc with rfl | rfl
    · left
      intro m hm
      obtain ⟨a, rfl⟩ := hspan m hm
      rw [hVp, map_smul, ← hc', one_smul]
    · right
      intro m hm
      obtain ⟨a, rfl⟩ := hspan m hm
      rw [hVm, map_smul, ← hc', neg_one_smul, smul_neg]
  have htrivm : ∀ k, ggLinMove (s k) ≤ Vp → ∀ v ∈ Vm, s k v = v := by
    intro k hk v hv
    have h1 := hinf (s k v - v) (hk (hmove k v)) (Vm.sub_mem (hsVm k v hv) hv)
    exact sub_eq_zero.mp h1
  have htrivp : ∀ k, ggLinMove (s k) ≤ Vm → ∀ v ∈ Vp, s k v = v := by
    intro k hk v hv
    have h1 := hinf (s k v - v) (Vp.sub_mem (hsVp k v hv) hv) (hk (hmove k v))
    exact sub_eq_zero.mp h1
  have hcomm : ∀ i j, ggLinMove (s i) ≤ Vp → ggLinMove (s j) ≤ Vm → s i * s j = s j * s i := by
    intro i j hi hj
    ext v
    obtain ⟨hp, hm, hv⟩ := hdec v
    set vp := (2 : ZMod 3) • (v + z v)
    set vm := (2 : ZMod 3) • (v - z v)
    have e1 : s j vp = vp := htrivp j hj vp hp
    have e2 : s i vm = vm := htrivm i hi vm hm
    have e3 : s i (s j vm) = s j vm := htrivm i hi _ (hsVm j vm hm)
    have e4 : s j (s i vp) = s i vp := htrivp j hj _ (hsVp i vp hp)
    simp only [LinearEquiv.mul_apply]
    rw [hv]
    simp only [map_add, e1, e2, e3, e4]
  have hsame : ∀ i j, (ggLinMove (s i) ≤ Vp ↔ ggLinMove (s j) ≤ Vp) := by
    have hne : ∀ k, ¬ (ggLinMove (s k) ≤ Vp ∧ ggLinMove (s k) ≤ Vm) := by
      rintro k ⟨hp, hm⟩
      obtain ⟨w, hw0, -⟩ := finrank_eq_one_iff'.mp (C.lin.s_refl k).2
      exact hw0 (Subtype.ext (hinf _ (hp w.2) (hm w.2)))
    have hadj : ∀ i j, (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Adj i j →
        (ggLinMove (s i) ≤ Vp ↔ ggLinMove (s j) ≤ Vp) := by
      intro i j hij
      rw [SimpleGraph.fromRel_adj] at hij
      obtain ⟨-, hij⟩ := hij
      constructor
      · intro hi
        rcases hside j with hj | hj
        · exact hj
        · exfalso
          rcases hij with h' | h'
          · exact h' (hcomm i j hi hj)
          · exact h' (hcomm i j hi hj).symm
      · intro hj
        rcases hside i with hi | hi
        · exact hi
        · exfalso
          rcases hij with h' | h'
          · exact h' (hcomm j i hj hi).symm
          · exact h' (hcomm j i hj hi)
    intro i j
    obtain ⟨p⟩ := C.lin.conn.preconnected i j
    induction p with
    | nil => exact Iff.rfl
    | cons ha _ ih => exact (hadj _ _ ha).trans ih
  have hclos : ∀ W : Submodule (ZMod 3) V, (∀ k, ∀ v ∈ W, s k v = v) →
      ∀ g ∈ Subgroup.closure (Set.range s), ∀ v ∈ W, g v = v := by
    intro W hW g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨k, rfl⟩ := ha
      exact hW k
    | one => intro v _; rfl
    | mul a b _ _ ha hb =>
      intro v hv
      rw [LinearEquiv.mul_apply, hb v hv, ha v hv]
    | inv a _ ha =>
      intro v hv
      have h1 := ha v hv
      rw [LinearEquiv.coe_inv]
      conv_lhs => rw [← h1]
      exact a.symm_apply_apply v
  have hallm : ∀ k, ggLinMove (s k) ≤ Vm := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    have hall : ∀ k, ggLinMove (s k) ≤ Vp := by
      intro k
      rcases hside k₀ with h' | h'
      · exact (hsame k₀ k).mp h'
      · exact absurd h' hk₀
    apply hz1
    ext v
    obtain ⟨hp, hm, hv⟩ := hdec v
    have hm0 : (2 : ZMod 3) • (v - z v) = 0 := by
      have h1 := hclos Vm (fun k => htrivm k (hall k)) z hz _ hm
      exact hinf _ ((hVp _).mpr h1) hm
    change z v = v
    have hp' := (hVp _).mp hp
    have hv' : (2 : ZMod 3) • (v + z v) = v := by
      have h1 := hv
      rw [hm0, add_zero] at h1
      exact h1.symm
    calc z v = z ((2 : ZMod 3) • (v + z v)) := by rw [hv']
      _ = (2 : ZMod 3) • (v + z v) := hp'
      _ = v := hv'
  have hVpx : Vp ≤ Submodule.span (ZMod 3) {x} := by
    intro v hv
    rw [← C.lin.fix_s]
    rintro _ ⟨k, rfl⟩
    exact htrivp k (hallm k) v hv
  have hzA : z ∈ ggLargeGrp r s :=
    Subgroup.closure_mono Set.subset_union_right hz
  have hVmT : Vm ≤ ggFixLineT r s := by
    intro v hv
    have h1 : z v - v = v := by
      rw [(hVm v).mp hv]
      have h3 : ∀ u : V, -u - u = u := by
        intro u
        have h4 : (3 : ZMod 3) • u = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_smul]
        have h5 : (3 : ZMod 3) • u = u + u + u := by
          rw [show (3 : ZMod 3) = 1 + 1 + 1 from rfl, add_smul, add_smul, one_smul]
        rw [h5] at h4
        calc -u - u = -u - u + (u + u + u) := by rw [h4, add_zero]
          _ = u := by abel
      exact h3 v
    rw [← h1]
    exact l04nD2_disp C z hzA v
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨hp, hm, hv⟩ := hdec v
    rw [hv]
    exact Submodule.add_mem_sup hp hm
  have hbot : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot _).mpr (hinf v hv.1 hv.2)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Vp Vm
  rw [hsup, hbot, finrank_top, finrank_bot, add_zero, ggNineDep_finrank_eq_nine C] at hsum
  have hp1 : Module.finrank (ZMod 3) Vp ≤ 1 :=
    (Submodule.finrank_mono hVpx).trans (finrank_span_singleton C.lin.x_ne).le
  have hle := Submodule.finrank_mono hVmT
  by_contra hd9
  have hd8 : Module.finrank (ZMod 3) ↥(ggFixLineT r s) ≤ 8 := by
    have := X.d_le
    omega
  have heq : Vm = ggFixLineT r s :=
    Submodule.eq_of_le_of_finrank_eq hVmT (by omega)
  refine ggNineDep_false_of_neg_mem X hd8 (z := ggLargeRho r s X.hA ⟨z, hzA⟩) ⟨_, rfl⟩ ?_
  intro v
  apply Subtype.ext
  rw [ggLargeRho_apply_coe]
  have hv : (v : V) ∈ Vm := by
    rw [heq]
    exact v.2
  exact (hVm _).mp hv

end Central


section Weyl

open CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem wordProd_smul_E8 (l : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem .E8).wordProd l • v = l.foldr (reflect .E8) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem exists_central_involution_weylE8 :
    ∃ z : WeylGroup .E8, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
  set w₀ := (coxeterSystem .E8).wordProd e8W0Word
  have hneg : ∀ v : Fin Tag.E8.rank → ℤ, w₀ • v = -v := by
    have h : weylAction (isFiniteType_cartan .E8) w₀ = -LinearMap.id := by
      refine LinearMap.pi_ext fun i c => ?_
      rw [← mul_one c, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
        wordProd_smul_E8, e8W0_single]
      simp
    intro v
    rw [smul_def, h]
    rfl
  refine ⟨w₀, ?_, ?_, ?_⟩
  · intro h1
    have h2 := hneg (Pi.single 0 1)
    rw [h1, one_smul] at h2
    have h3 := congrFun h2 0
    simp at h3
  · refine ext_single fun i => ?_
    rw [mul_smul, hneg, hneg, neg_neg, one_smul]
  · intro w
    refine ext_single fun i => ?_
    rw [mul_smul, mul_smul, hneg, hneg, smul_neg]

theorem exists_central_involution_of_mulEquiv {G H : Type*} [Group G] [Group H] (f : G ≃* H)
    (h : ∃ z : G, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z) :
    ∃ z : H, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
  obtain ⟨z, hz1, hzz, hc⟩ := h
  refine ⟨f z, fun h1 => hz1 (f.injective (h1.trans f.map_one.symm)), ?_, fun w => ?_⟩
  · rw [← map_mul, hzz, map_one]
  · obtain ⟨u, rfl⟩ := f.surjective w
    rw [← map_mul, hc, map_mul]

theorem coxeterMatrix_E8_eq : coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈ := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
  exact coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
    (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (hc.symm ▸ ggIntCartan_E₈)

theorem exists_central_involution_E8_reindex {ι : Type} (e : Fin 8 ≃ ι) :
    ∃ z : (CoxeterMatrix.E₈.reindex e).Group, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
  have key : ∀ M : CoxeterMatrix (Fin 8), coxeterMatrix (isFiniteType_cartan .E8) = M →
      ∃ z : M.Group, z ≠ 1 ∧ z * z = 1 ∧ ∀ w, z * w = w * z := by
    rintro M rfl
    exact exists_central_involution_weylE8
  exact exists_central_involution_of_mulEquiv (CoxeterMatrix.E₈.reindexGroupEquiv e).symm
    (key _ coxeterMatrix_E8_eq)

theorem weyl8_E8_or_card_le {M : CoxeterMatrix (Fin (9 - 1))} (hM : GGIsWeylMatrix M) :
    (∃ e : Fin 8 ≃ Fin (9 - 1), M = CoxeterMatrix.E₈.reindex e) ∨
      Nat.card M.Group ≤ 2 ^ 8 * Nat.factorial 8 := by
  have hcard : ∀ {n : ℕ}, (Fin n ≃ Fin (9 - 1)) → n = 8 := by
    intro n e
    simpa using Fintype.card_congr e
  rcases hM with ⟨n, e, -, hA | ⟨-, hB⟩ | ⟨-, hD⟩⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, hE⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · obtain rfl := hcard e
    exact Or.inr (l05nK3a_card_reindex_le _ e hA (l05nK3a_coxeterA_le 8))
  · obtain rfl := hcard e
    exact Or.inr (l05nK3a_card_reindex_le _ e hB (card_coxeterB_le 8))
  · obtain rfl := hcard e
    exact Or.inr (l05nK3a_card_reindex_le _ e hD (l05nK3a_coxeterD_le 8 (by norm_num)))
  · exact absurd (hcard e) (by norm_num)
  · exact absurd (hcard e) (by norm_num)
  · exact Or.inl ⟨e, hE⟩
  · exact absurd (hcard e) (by norm_num)
  · exact absurd (hcard e) (by norm_num)

end Weyl

section Order

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (9 - 1) → V} {α : Fin (9 - 1) → Module.Dual (ZMod 3) V}
    {r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)} {T : Type} {s : T → (V ≃ₗ[ZMod 3] V)} {x : V}

theorem card_le (C : GGNineDepCase 3 9 h α r s x) :
    Nat.card ↥(ggLargeGrp r s) ≤ 12 * Nat.card ↥(Subgroup.closure (Set.range s)) * (3 ^ 9 - 1) := by
  classical
  haveI : Module.Finite (ZMod 3) V := l04nD2_finite C
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V)) DFunLike.coe_injective
  set A := ggLargeGrp r s
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥A x)
  rw [MulAction.index_stabilizer] at h1
  have h2 : Nat.card (MulAction.stabilizer ↥A x) ≤
      12 * Nat.card ↥(Subgroup.closure (Set.range s)) := by
    refine le_trans ?_ (C.stab.trans_eq (by norm_num))
    refine Nat.card_le_card_of_injective
      (fun g => (⟨((g : ↥A) : V ≃ₗ[ZMod 3] V), (g : ↥A).2, ?_⟩ :
        ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x))) ?_
    · have hg := MulAction.mem_stabilizer_iff.mp g.2
      rw [Subgroup.smul_def] at hg
      exact MulAction.mem_stabilizer_iff.mpr hg
    · intro g g' hgg'
      have h := congrArg (fun y : ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) =>
        (y : V ≃ₗ[ZMod 3] V)) hgg'
      exact Subtype.ext (Subtype.ext h)
  have h3 : (MulAction.orbit ↥A x).ncard ≤ 3 ^ 9 - 1 := by
    have hsub : MulAction.orbit ↥A x ⊆ ({0} : Set V)ᶜ := by
      rintro _ ⟨g, rfl⟩ h0
      apply C.lin.x_ne
      have h0' : ((g : ↥A) : V ≃ₗ[ZMod 3] V) x = 0 := by
        simpa [Subgroup.smul_def] using h0
      simpa using congrArg ((g : ↥A) : V ≃ₗ[ZMod 3] V).symm h0'
    calc (MulAction.orbit ↥A x).ncard ≤ (({0} : Set V)ᶜ).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card V - 1 := by rw [Set.ncard_compl, Set.ncard_singleton]
      _ = 3 ^ 9 - 1 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 3), ggNineDep_finrank_eq_nine C, Nat.card_zmod]
  calc Nat.card ↥A = Nat.card (MulAction.stabilizer ↥A x) * (MulAction.orbit ↥A x).ncard := h1.symm
    _ ≤ (12 * Nat.card ↥(Subgroup.closure (Set.range s))) * (3 ^ 9 - 1) := Nat.mul_le_mul h2 h3

end Order

end NineDepOrth

open NineDepOrth in
theorem ggNineDepRowOrth_holds : GGNineDepRowOrthInput := by
  intro V _ _ h α r T s x X ⟨hO, hpow⟩
  have C := X.case
  have hd7 := X.d_ge
  have hd9 := X.d_le
  have hQA : Nat.card ↥(ggNineQ X) = Nat.card ↥(ggLargeGrp r s) :=
    (Nat.card_congr (MonoidHom.ofInjective X.restr.1).toEquiv).symm
  have hcard := card_le C
  obtain ⟨M, hMw, ⟨φ⟩⟩ := C.weylL
  have hsM : Nat.card ↥(Subgroup.closure (Set.range s)) = Nat.card M.Group :=
    (Nat.card_congr φ.toEquiv).symm
  rcases (by omega : Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 7 ∨
      Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 8 ∨
      Module.finrank (ZMod 3) ↥(ggFixLineT r s) = 9) with h7 | h8 | h9
  · exact false_d7 X hO h7
  · rcases weyl8_E8_or_card_le hMw with ⟨e, rfl⟩ | hle
    ·
      obtain ⟨z₀, hz1, hzz, hc⟩ := exists_central_involution_E8_reindex e
      have hφ1 : φ z₀ ≠ 1 := fun h1 => hz1 (φ.injective (h1.trans φ.map_one.symm))
      have hφzz : φ z₀ * φ z₀ = 1 := by rw [← map_mul, hzz, map_one]
      have h9' := finrank_eq_nine_of_central X (z := ((φ z₀ : ↥(Subgroup.closure (Set.range s))) :
          V ≃ₗ[ZMod 3] V)) (φ z₀).2 (fun h1 => hφ1 (Subtype.ext h1))
        (by simpa using congrArg Subtype.val hφzz) (fun k => by
          set w : ↥(Subgroup.closure (Set.range s)) := ⟨s k, Subgroup.subset_closure ⟨k, rfl⟩⟩
          have h1 : φ z₀ * w = w * φ z₀ := by
            obtain ⟨u, hu⟩ := φ.surjective w
            rw [← hu, ← map_mul, hc, map_mul]
          simpa using congrArg Subtype.val h1)
      omega
    ·
      rw [h8] at hpow
      have h1 : 3 ^ (8 * (8 - 1) / 2) ≤ 8 * (12 * (2 ^ 8 * Nat.factorial 8) * (3 ^ 9 - 1)) := by
        calc 3 ^ (8 * (8 - 1) / 2) ≤ 8 * Nat.card ↥(ggNineQ X) := hpow
          _ ≤ 8 * (12 * Nat.card ↥(Subgroup.closure (Set.range s)) * (3 ^ 9 - 1)) := by
            rw [hQA]; exact Nat.mul_le_mul_left 8 hcard
          _ ≤ 8 * (12 * (2 ^ 8 * Nat.factorial 8) * (3 ^ 9 - 1)) := by
            rw [hsM]; gcongr
      norm_num [Nat.factorial] at h1
  ·
    have hs : Nat.card M.Group ≤ 18114969600 := by
      rcases weyl8_E8_or_card_le hMw with ⟨e, rfl⟩ | hle
      · exact l05nK3a_card_reindex_le _ e rfl WeylE8Bound.card_coxeterE8_group_le
      · exact hle.trans (by norm_num [Nat.factorial])
    rw [h9] at hpow
    have h1 : 3 ^ (9 * (9 - 1) / 2) ≤ 8 * (12 * 18114969600 * (3 ^ 9 - 1)) := by
      calc 3 ^ (9 * (9 - 1) / 2) ≤ 8 * Nat.card ↥(ggNineQ X) := hpow
        _ ≤ 8 * (12 * Nat.card ↥(Subgroup.closure (Set.range s)) * (3 ^ 9 - 1)) := by
          rw [hQA]; exact Nat.mul_le_mul_left 8 hcard
        _ ≤ 8 * (12 * 18114969600 * (3 ^ 9 - 1)) := by
          rw [hsM]; gcongr
    norm_num at h1

end CFSG.StandardType

end
