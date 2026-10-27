module

public import CFSG.Quasithin.Background.F918Z0AuxCoord
public import CFSG.Quasithin.Background.F918Z5ATensor
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

section MatRows

variable {V : Type} [CommGroup V] {F : Type} [Field F] {d r : ℕ}

@[expose] def matColSub (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (j : Fin r) :
    Subgroup V where
  carrier := {v | ∀ a k, k ≠ j → Multiplicative.toAdd (β v) a k = 0}
  one_mem' := by intro a k _; simp
  mul_mem' := by
    intro u v hu hv a k hk
    simp [hu a k hk, hv a k hk]
  inv_mem' := by
    intro u hu a k hk
    simp [hu a k hk]

@[expose] def matRowSub (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (a : Fin d) :
    Subgroup V where
  carrier := {v | ∀ b k, b ≠ a → Multiplicative.toAdd (β v) b k = 0}
  one_mem' := by intro b k _; simp
  mul_mem' := by
    intro u v hu hv b k hb
    simp [hu b k hb, hv b k hb]
  inv_mem' := by
    intro u hu b k hb
    simp [hu b k hb]

@[expose] noncomputable def matColEquiv (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (j : Fin r) : ↥(matColSub β j) ≃* Multiplicative (Fin d → F) where
  toFun v := Multiplicative.ofAdd fun a => Multiplicative.toAdd (β (v : V)) a j
  invFun y := ⟨β.symm (Multiplicative.ofAdd (Matrix.of fun a k =>
    if k = j then Multiplicative.toAdd y a else 0)), by
      intro a k hk
      simp [hk]⟩
  left_inv v := by
    apply Subtype.ext
    apply β.injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    ext a k
    simp only [toAdd_ofAdd, Matrix.of_apply]
    by_cases hk : k = j
    · subst hk
      simp
    · rw [if_neg hk, v.2 a k hk]
  right_inv y := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [toAdd_ofAdd, Matrix.of_apply, MulEquiv.apply_symm_apply]
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [map_mul, toAdd_ofAdd, Matrix.of_apply]

@[expose] noncomputable def matRowEquiv (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (a : Fin d) : ↥(matRowSub β a) ≃* Multiplicative (Fin r → F) where
  toFun v := Multiplicative.ofAdd fun k => Multiplicative.toAdd (β (v : V)) a k
  invFun y := ⟨β.symm (Multiplicative.ofAdd (Matrix.of fun b k =>
    if b = a then Multiplicative.toAdd y k else 0)), by
      intro b k hb
      simp [hb]⟩
  left_inv v := by
    apply Subtype.ext
    apply β.injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    ext b k
    simp only [toAdd_ofAdd, Matrix.of_apply]
    by_cases hb : b = a
    · subst hb
      simp
    · rw [if_neg hb, v.2 b k hb]
  right_inv y := by
    apply Multiplicative.toAdd.injective
    ext k
    simp [toAdd_ofAdd, Matrix.of_apply, MulEquiv.apply_symm_apply]
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    ext k
    simp [map_mul, toAdd_ofAdd, Matrix.of_apply]

theorem matColEquiv_apply (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (j : Fin r)
    (v : ↥(matColSub β j)) (a : Fin d) :
    Multiplicative.toAdd (matColEquiv β j v) a = Multiplicative.toAdd (β v) a j := rfl

theorem matRowEquiv_apply (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (a : Fin d)
    (v : ↥(matRowSub β a)) (k : Fin r) :
    Multiplicative.toAdd (matRowEquiv β a v) k = Multiplicative.toAdd (β v) a k := rfl

variable {D X : Subgroup (MulAut V)} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F} {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

theorem stableUnder_matColSub (hM : IsMatModel D X β ρ σ) (j : Fin r) :
    StableUnder D (matColSub β j) := by
  intro g hg u hu a k hk
  rw [hM.hρ ⟨g, hg⟩ u, toAdd_ofAdd, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hu l k hk, mul_zero]

theorem stableUnder_matRowSub (hM : IsMatModel D X β ρ σ) (a : Fin d) :
    StableUnder X (matRowSub β a) := by
  intro x hx u hu b k hb
  rw [hM.hσ ⟨x, hx⟩ u, toAdd_ofAdd,
    CFSG.Quasithin.MatModel.row_mul_transpose, Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun l _ => by rw [hu b l hb, mul_zero]

theorem matColEquiv_act (hM : IsMatModel D X β ρ σ) (j : Fin r) (g : ↥D)
    (v v' : ↥(matColSub β j)) (hv : (v' : V) = (g : MulAut V) v) :
    Multiplicative.toAdd (matColEquiv β j v') =
      ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec
        (Multiplicative.toAdd (matColEquiv β j v)) := by
  ext a
  have hL : Multiplicative.toAdd (matColEquiv β j v') a =
      (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        Multiplicative.toAdd (β (v : V))) a j := by
    rw [matColEquiv_apply, hv, hM.hρ, toAdd_ofAdd]
  have hR : (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec
      (Multiplicative.toAdd (matColEquiv β j v))) a =
      (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        Multiplicative.toAdd (β (v : V))) a j := by
    rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [matColEquiv_apply]
  rw [hL, hR]

theorem matRowEquiv_act (hM : IsMatModel D X β ρ σ) (a : Fin d) (x : ↥X)
    (v v' : ↥(matRowSub β a)) (hv : (v' : V) = (x : MulAut V) v) :
    Multiplicative.toAdd (matRowEquiv β a v') =
      ((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F).mulVec
        (Multiplicative.toAdd (matRowEquiv β a v)) := by
  ext k
  have hL : Multiplicative.toAdd (matRowEquiv β a v') k =
      (Multiplicative.toAdd (β (v : V)) *
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ) a k := by
    rw [matRowEquiv_apply, hv, hM.hσ, toAdd_ofAdd]
  have hR : (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F).mulVec
      (Multiplicative.toAdd (matRowEquiv β a v))) k =
      (Multiplicative.toAdd (β (v : V)) *
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ) a k := by
    rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by
      rw [matRowEquiv_apply, Matrix.transpose_apply, mul_comm]
  rw [hL, hR]

theorem card_eq_card_pow_of_matEquiv [Finite F]
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) :
    Nat.card V = Nat.card F ^ (d * r) := by
  rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd, Matrix.card_matrix,
    Nat.card_fin, Nat.card_fin, Nat.mul_comm r d]

theorem card_matColSub [Finite F] (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (j : Fin r) : Nat.card ↥(matColSub β j) = Nat.card F ^ d := by
  rw [Nat.card_congr (matColEquiv β j).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fin]

theorem card_matRowSub [Finite F] (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
    (a : Fin d) : Nat.card ↥(matRowSub β a) = Nat.card F ^ r := by
  rw [Nat.card_congr (matRowEquiv β a).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fin]

theorem isIrrOn_matColSub (hM : IsMatModel D X β ρ σ) (hd : 0 < d) (j : Fin r) :
    IsIrrOn D (matColSub β j) ⊥ := by
  have hbot : (⊥ : Subgroup V) < matColSub β j := by
    rw [bot_lt_iff_ne_bot]
    intro hbot'
    let M : Matrix (Fin d) (Fin r) F :=
      Matrix.of fun a k => if a = ⟨0, hd⟩ ∧ k = j then 1 else 0
    let u : V := β.symm (Multiplicative.ofAdd M)
    have hu : u ∈ matColSub β j := by
      intro a k hk
      simp only [u, MulEquiv.apply_symm_apply, toAdd_ofAdd, M, Matrix.of_apply]
      rw [if_neg]
      rintro ⟨-, hkj⟩
      exact hk hkj
    have hu1 : u = 1 := by
      rw [hbot'] at hu
      exact Subgroup.mem_bot.mp hu
    have hM0 : M = 0 := by
      have h := congrArg (fun v => Multiplicative.toAdd (β v)) hu1
      simpa [u] using h
    have h1 := congrFun (congrFun hM0 ⟨0, hd⟩) j
    simp [M] at h1
  refine ⟨hbot, stableUnder_matColSub hM j, ?_, ?_⟩
  · intro g hg u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJ _ hJle
    let I := matColSub β j
    let J' : Subgroup (Multiplicative (Fin d → F)) :=
      (J.subgroupOf I).map (matColEquiv β j).toMonoidHom
    have hWinv : ∀ (g : ↥D), ∀ w ∈ Subgroup.toAddSubgroup' J',
        (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec w) ∈
          Subgroup.toAddSubgroup' J' := by
      intro g w hw
      rw [Subgroup.mem_toAddSubgroup'] at hw ⊢
      obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hw
      have huJ : (u : V) ∈ J := (Subgroup.mem_subgroupOf.mp hu)
      let u' : ↥I := ⟨(g : MulAut V) (u : V), stableUnder_matColSub hM j g g.2 u u.2⟩
      have hu' : u' ∈ J.subgroupOf I := by
        rw [Subgroup.mem_subgroupOf]
        exact hJ g g.2 (u : V) huJ
      have hmem : matColEquiv β j u' ∈ J' := Subgroup.mem_map_of_mem _ hu'
      have hact := matColEquiv_act hM j g u u' rfl
      have heq2 : (matColEquiv β j) u = Multiplicative.ofAdd w := heq
      have heq' : matColEquiv β j u' = Multiplicative.ofAdd
          (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec w) := by
        apply Multiplicative.toAdd.injective
        rw [hact, toAdd_ofAdd, heq2, toAdd_ofAdd]
      rw [← heq']
      exact hmem
    rcases hM.I_irr (Subgroup.toAddSubgroup' J') hWinv with hW | hW
    · left
      rw [eq_bot_iff]
      intro v hv
      have hvI : v ∈ I := hJle hv
      let u : ↥I := ⟨v, hvI⟩
      have hu : u ∈ J.subgroupOf I := by
        rw [Subgroup.mem_subgroupOf]
        exact hv
      have hmem : matColEquiv β j u ∈ J' := Subgroup.mem_map_of_mem _ hu
      have hmemW : Multiplicative.toAdd (matColEquiv β j u) ∈ Subgroup.toAddSubgroup' J' :=
        (Subgroup.mem_toAddSubgroup' J' _).2 (by simpa using hmem)
      rw [hW] at hmemW
      have hzero : Multiplicative.toAdd (matColEquiv β j u) = 0 := by
        simpa using hmemW
      have hone : matColEquiv β j u = 1 :=
        Multiplicative.toAdd.injective (by simpa using hzero)
      have hu1 : u = 1 := (matColEquiv β j).injective (by simpa using hone)
      have hv1 : v = 1 := by
        have h := congrArg (fun w : ↥I => (w : V)) hu1
        simpa [u] using h
      exact Subgroup.mem_bot.mpr hv1
    · right
      refine le_antisymm hJle ?_
      intro v hvI
      let u : ↥I := ⟨v, hvI⟩
      have hmem : Multiplicative.toAdd (matColEquiv β j u) ∈ Subgroup.toAddSubgroup' J' := by
        rw [hW]
        exact AddSubgroup.mem_top _
      have hmem' : matColEquiv β j u ∈ J' := by
        have h := (Subgroup.mem_toAddSubgroup' J' _).1 hmem
        simpa using h
      obtain ⟨u₀, hu₀, heq⟩ := Subgroup.mem_map.mp hmem'
      have hu₀J : (u₀ : V) ∈ J := (Subgroup.mem_subgroupOf.mp hu₀)
      have huu : u₀ = u := (matColEquiv β j).injective heq
      rw [huu] at hu₀J
      simpa [u] using hu₀J

theorem exists_moves_matColSub (hM : IsMatModel D X β ρ σ) (hD : D ≠ ⊥) (j : Fin r) :
    ∃ g ∈ D, ∃ u ∈ matColSub β j, g u ≠ u := by
  obtain ⟨g, hgD, hg1⟩ : ∃ g ∈ D, g ≠ 1 := by
    by_contra h
    push Not at h
    exact hD (eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr (h g hg))
  have hρ1 : ρ ⟨g, hgD⟩ ≠ 1 := by
    intro h
    have h' : ρ ⟨g, hgD⟩ = ρ (1 : ↥D) := by simpa using h
    exact hg1 (congrArg Subtype.val (hM.rho_injective h'))
  have hy : ∃ y : Fin d → F,
      (((ρ ⟨g, hgD⟩ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).mulVec y) ≠
        y := by
    by_contra h
    push Not at h
    apply hρ1
    ext i k
    have h1 := congrFun (h (Pi.single k 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h1
  obtain ⟨y, hy⟩ := hy
  let u : ↥(matColSub β j) := (matColEquiv β j).symm (Multiplicative.ofAdd y)
  refine ⟨g, hgD, (u : V), u.2, ?_⟩
  intro hgu
  let u' : ↥(matColSub β j) :=
    ⟨(g : MulAut V) (u : V), stableUnder_matColSub hM j g hgD u u.2⟩
  have hu' : u' = u := Subtype.ext hgu
  have hact := matColEquiv_act hM j ⟨g, hgD⟩ u u' rfl
  have h2 : Multiplicative.toAdd (matColEquiv β j u) = y := by
    simp [u]
  rw [hu', h2] at hact
  exact hy hact.symm

theorem exists_moves_matRowSub (hM : IsMatModel D X β ρ σ) (hX : X ≠ ⊥) (a : Fin d) :
    ∃ x ∈ X, ∃ u ∈ matRowSub β a, x u ≠ u := by
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hX (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  have hσ1 : σ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have h' : σ ⟨x, hxX⟩ = σ (1 : ↥X) := by simpa using h
    exact hx1 (congrArg Subtype.val (hM.sigma_injective h'))
  have hy : ∃ y : Fin r → F,
      (((σ ⟨x, hxX⟩ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F).mulVec y) ≠
        y := by
    by_contra h
    push Not at h
    apply hσ1
    ext i k
    have h1 := congrFun (h (Pi.single k 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h1
  obtain ⟨y, hy⟩ := hy
  let u : ↥(matRowSub β a) := (matRowEquiv β a).symm (Multiplicative.ofAdd y)
  refine ⟨x, hxX, (u : V), u.2, ?_⟩
  intro hxu
  let u' : ↥(matRowSub β a) :=
    ⟨(x : MulAut V) (u : V), stableUnder_matRowSub hM a x hxX u u.2⟩
  have hu' : u' = u := Subtype.ext hxu
  have hact := matRowEquiv_act hM a ⟨x, hxX⟩ u u' rfl
  have h2 : Multiplicative.toAdd (matRowEquiv β a u) = y := by
    simp [u]
  rw [hu', h2] at hact
  exact hy hact.symm

@[expose] noncomputable def matScal (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (c : F)
    (hc : c ≠ 0) : MulAut V :=
  (β.trans (AddEquiv.toMultiplicative
    (LinearEquiv.smulOfNeZero F (Matrix (Fin d) (Fin r) F) c hc).toAddEquiv)).trans β.symm

theorem matScal_apply (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (c : F) (hc : c ≠ 0)
    (v : V) :
    Multiplicative.toAdd (β (matScal β c hc v)) = c • Multiplicative.toAdd (β v) := by
  simp [matScal, AddEquiv.toMultiplicative_apply_apply, LinearEquiv.smulOfNeZero_apply]

theorem matScal_commute (hM : IsMatModel D X β ρ σ) (c : F) (hc : c ≠ 0) :
    (∀ g ∈ D, matScal β c hc * g = g * matScal β c hc) ∧
      ∀ x ∈ X, matScal β c hc * x = x * matScal β c hc := by
  constructor
  · intro g hg
    ext v
    have hρv : Multiplicative.toAdd (β (g v)) =
        ((ρ ⟨g, hg⟩ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          Multiplicative.toAdd (β v) := by
      simpa using congrArg Multiplicative.toAdd (hM.hρ ⟨g, hg⟩ v)
    have hρmv : Multiplicative.toAdd (β (g (matScal β c hc v))) =
        ((ρ ⟨g, hg⟩ : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          Multiplicative.toAdd (β (matScal β c hc v)) := by
      simpa using congrArg Multiplicative.toAdd (hM.hρ ⟨g, hg⟩ (matScal β c hc v))
    apply β.injective
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, MulAut.mul_apply, matScal_apply, hρv, hρmv, matScal_apply,
      Matrix.mul_smul]
  · intro x hx
    ext v
    have hσv : Multiplicative.toAdd (β (x v)) =
        Multiplicative.toAdd (β v) *
          (((σ ⟨x, hx⟩ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ := by
      simpa using congrArg Multiplicative.toAdd (hM.hσ ⟨x, hx⟩ v)
    have hσmv : Multiplicative.toAdd (β (x (matScal β c hc v))) =
        Multiplicative.toAdd (β (matScal β c hc v)) *
          (((σ ⟨x, hx⟩ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ := by
      simpa using congrArg Multiplicative.toAdd (hM.hσ ⟨x, hx⟩ (matScal β c hc v))
    apply β.injective
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, MulAut.mul_apply, matScal_apply, hσv, hσmv, matScal_apply,
      Matrix.smul_mul]

end MatRows

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
