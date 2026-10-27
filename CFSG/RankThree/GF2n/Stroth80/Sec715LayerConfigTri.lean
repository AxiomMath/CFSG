module

public import CFSG.RankThree.GF2n.Stroth80.Sec715Triality
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfigAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG.Open Module
open scoped Matrix

section Rep

variable {K : Type} [Field K] {H : Type} [Group H]
  {X Y Z : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

@[expose] def IsoRep (ρX : H →* (X ≃ₗ[K] X)) (ρY : H →* (Y ≃ₗ[K] Y)) : Prop :=
  ∃ e : X ≃ₗ[K] Y, ∀ h x, e (ρX h x) = ρY h (e x)

@[expose] def IsIrrLin (ρX : H →* (X ≃ₗ[K] X)) : Prop :=
  ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤

@[expose] def IsEqvPair (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (ρX : H →* (X ≃ₗ[K] X))
    (ρY : H →* (Y ≃ₗ[K] Y)) (γ : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop :=
  ∀ h x y, γ (ρX h x) (ρY h y) = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ γ x y

theorem IsoRep.symm {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)} (h : IsoRep ρX ρY) :
    IsoRep ρY ρX := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun g y => e.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem IsoRep.trans {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)} {ρZ : H →* (Z ≃ₗ[K] Z)}
    (h₁ : IsoRep ρX ρY) (h₂ : IsoRep ρY ρZ) : IsoRep ρX ρZ := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  exact ⟨e₁.trans e₂, fun g x => by rw [LinearEquiv.trans_apply, he₁, he₂]; rfl⟩

theorem IsEqvPair.compl₁₂ {X' Y' : Type} [AddCommGroup X'] [Module K X'] [AddCommGroup Y']
    [Module K Y'] {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {ρX : H →* (X ≃ₗ[K] X)}
    {ρY : H →* (Y ≃ₗ[K] Y)} {ρX' : H →* (X' ≃ₗ[K] X')} {ρY' : H →* (Y' ≃ₗ[K] Y')}
    {γ : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hγ : IsEqvPair φ ρX ρY γ)
    {f : X' →ₗ[K] X} (hf : ∀ h x, f (ρX' h x) = ρX h (f x))
    {g : Y' →ₗ[K] Y} (hg : ∀ h y, g (ρY' h y) = ρY h (g y)) :
    IsEqvPair φ ρX' ρY' (γ.compl₁₂ f g) := fun h x y => by
  simp only [LinearMap.compl₁₂_apply, hf, hg]
  exact hγ h (f x) (g y)

theorem IsEqvPair.flip {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {ρX : H →* (X ≃ₗ[K] X)}
    {ρY : H →* (Y ≃ₗ[K] Y)} {γ : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hγ : IsEqvPair φ ρX ρY γ) : IsEqvPair φ ρY ρX γ.flip := fun h y x => by
  simp only [LinearMap.flip_apply]
  exact hγ h x y

end Rep

section Tri

variable {K : Type} [Field K] {H : Type} [Group H]
  {X Y : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

structure TriPair (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (ρX : H →* (X ≃ₗ[K] X))
    (ρY : H →* (Y ≃ₗ[K] Y)) (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop where
  kerX : ∀ h : H, φ h = 1 → ρX h = 1
  kerY : ∀ h : H, φ h = 1 → ρY h = 1
  irrX : IsIrrLin ρX
  irrY : IsIrrLin ρY
  dimX : finrank K X = 8
  dimY : finrank K Y = 8
  eqv : IsEqvPair φ ρX ρY β
  ne_zero : β ≠ 0

variable {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
  {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem TriPair.flip (hT : TriPair φ ρX ρY β) : TriPair φ ρY ρX β.flip where
  kerX := hT.kerY
  kerY := hT.kerX
  irrX := hT.irrY
  irrY := hT.irrX
  dimX := hT.dimY
  dimY := hT.dimX
  eqv := hT.eqv.flip
  ne_zero h := hT.ne_zero (LinearMap.ext fun x => LinearMap.ext fun y => by
    simpa using LinearMap.congr_fun (LinearMap.congr_fun h y) x)

variable (hTri : Omega8TrialityStatement) [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
  (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) [FiniteDimensional K X] [FiniteDimensional K Y]

include hTri hq hφ

theorem TriPair.not_iso (hT : TriPair φ ρX ρY β) : ¬ IsoRep ρX ρY :=
  (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
    hT.ne_zero).1

theorem TriPair.unique (hT : TriPair φ ρX ρY β) {β' : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hβ' : IsEqvPair φ ρX ρY β') : ∃ c : K, β' = c • β :=
  (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
    hT.ne_zero).2.2.2.1 β' hβ'

theorem TriPair.cases (hT : TriPair φ ρX ρY β) {Z Z' : Type} [AddCommGroup Z] [Module K Z]
    [FiniteDimensional K Z] [AddCommGroup Z'] [Module K Z'] [FiniteDimensional K Z']
    {ρZ : H →* (Z ≃ₗ[K] Z)} {ρZ' : H →* (Z' ≃ₗ[K] Z')}
    {γ : Z →ₗ[K] Z' →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hγ : TriPair φ ρZ ρZ' γ) :
    (IsoRep ρZ ρX ∧ IsoRep ρZ' ρY) ∨ (IsoRep ρZ ρY ∧ IsoRep ρZ' ρX) :=
  (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
    hT.ne_zero).2.2.2.2.2.1 Z ρZ Z' ρZ' hγ.kerX hγ.kerY hγ.irrX hγ.irrY hγ.dimX hγ.dimY γ hγ.eqv
    hγ.ne_zero

theorem TriPair.exists_qX (hT : TriPair φ ρX ρY β) :
    ∃ qX : QuadraticForm K X, (∀ (h : H) (x : X), qX (ρX h x) = qX x) ∧
      ∀ x : X, (∀ x' : X, QuadraticMap.polar qX x x' = 0) → x = 0 :=
  (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
    hT.ne_zero).2.2.2.2.2.2.1

theorem TriPair.exists_qY (hT : TriPair φ ρX ρY β) :
    ∃ qY : QuadraticForm K Y, (∀ (h : H) (y : Y), qY (ρY h y) = qY y) ∧
      ∀ y : Y, (∀ y' : Y, QuadraticMap.polar qY y y' = 0) → y = 0 :=
  (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
    hT.ne_zero).2.2.2.2.2.2.2.1

theorem TriPair.ranks (hT : TriPair φ ρX ρY β) {qX : QuadraticForm K X} {qY : QuadraticForm K Y}
    (hqX : ∀ (h : H) (x : X), qX (ρX h x) = qX x) (hqY : ∀ (h : H) (y : Y), qY (ρY h y) = qY y)
    (hqX0 : qX ≠ 0) (hqY0 : qY ≠ 0) :
    (∀ y : Y, y ≠ 0 → qY y ≠ 0 → finrank K (LinearMap.range (β.flip y)) = 8) ∧
    (∀ y : Y, y ≠ 0 → qY y = 0 → finrank K (LinearMap.range (β.flip y)) = 4) ∧
    (∀ x : X, x ≠ 0 → qX x ≠ 0 → finrank K (LinearMap.range (β x)) = 8) ∧
    (∀ x : X, x ≠ 0 → qX x = 0 → finrank K (LinearMap.range (β x)) = 4) ∧
    ∀ (x : X) (y : Y), x ≠ 0 → y ≠ 0 → qX x = 0 → qY y = 0 →
      Odd (finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β.flip y))) := by
  obtain ⟨r1, r2, r3, r4, -, -, -, -, -, -, o⟩ :=
    (hTri K hq H φ hφ X ρX Y ρY hT.kerX hT.kerY hT.irrX hT.irrY hT.dimX hT.dimY β hT.eqv
      hT.ne_zero).2.2.2.2.2.2.2.2 qX qY hqX hqY hqX0 hqY0
  exact ⟨r1, fun y hy h0 => (r2 y hy h0).1, r3, fun x hx h0 => (r4 x hx h0).1, o⟩

end Tri

section Summand

variable {K : Type} [Field K] {H : Type} [Group H] {Mm Nn : Type} [AddCommGroup Mm] [Module K Mm]
  [AddCommGroup Nn] [Module K Nn] {ρM : H →* (Mm ≃ₗ[K] Mm)} {ρN : H →* (Nn ≃ₗ[K] Nn)}
  {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem restrictAct_eq_one {Y : Submodule K Mm} (hY : IsInvSub ρM Y)
    (hk : ∀ h : H, φ h = 1 → ρM h = 1) (h : H) (hh : φ h = 1) : restrictAct ρM hY h = 1 :=
  LinearEquiv.ext fun y => Subtype.ext (by rw [coe_restrictAct, hk h hh]; rfl)

theorem triPair_restrict (hkM : ∀ h : H, φ h = 1 → ρM h = 1) (hkN : ∀ h : H, φ h = 1 → ρN h = 1)
    (hβ : IsEqvPair φ ρM ρN β) {Y : Submodule K Mm} {Z : Submodule K Nn} (hY : IsIrrSub ρM Y)
    (hZ : IsIrrSub ρN Z) (hdY : finrank K Y = 8) (hdZ : finrank K Z = 8)
    (h0 : β.compl₁₂ Y.subtype Z.subtype ≠ 0) :
    TriPair φ (restrictAct ρM hY.2.1) (restrictAct ρN hZ.2.1) (β.compl₁₂ Y.subtype Z.subtype) where
  kerX := restrictAct_eq_one hY.2.1 hkM
  kerY := restrictAct_eq_one hZ.2.1 hkN
  irrX := restrictAct_irred ρM hY.2.1 hY
  irrY := restrictAct_irred ρN hZ.2.1 hZ
  dimX := hdY
  dimY := hdZ
  eqv := hβ.compl₁₂ (fun _ _ => rfl) (fun _ _ => rfl)
  ne_zero := h0

end Summand

section Helpers

variable {K : Type} [Field K] {H : Type} [Group H]
  {X Y : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem quadraticForm_ne_zero {q : QuadraticForm K X}
    (hnd : ∀ x : X, (∀ x' : X, QuadraticMap.polar q x x' = 0) → x = 0) (hX : finrank K X = 8) :
    q ≠ 0 := by
  rintro rfl
  have h0 : ∀ x : X, x = 0 := fun x => hnd x fun x' => by simp [QuadraticMap.polar]
  haveI : Subsingleton X := ⟨fun a b => by rw [h0 a, h0 b]⟩
  rw [finrank_zero_of_subsingleton] at hX
  exact absurd hX (by norm_num)

theorem exists_quadraticForm_of_iso {ρX : H →* (X ≃ₗ[K] X)} {ρY : H →* (Y ≃ₗ[K] Y)}
    (hiso : IsoRep ρX ρY)
    (hq : ∃ qY : QuadraticForm K Y, (∀ (h : H) (y : Y), qY (ρY h y) = qY y) ∧
      ∀ y : Y, (∀ y' : Y, QuadraticMap.polar qY y y' = 0) → y = 0) :
    ∃ qX : QuadraticForm K X, (∀ (h : H) (x : X), qX (ρX h x) = qX x) ∧
      ∀ x : X, (∀ x' : X, QuadraticMap.polar qX x x' = 0) → x = 0 := by
  obtain ⟨e, he⟩ := hiso
  obtain ⟨qY, hqY, hnd⟩ := hq
  refine ⟨qY.comp (e : X →ₗ[K] Y), fun h x => ?_, fun x hx => ?_⟩
  · rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe, he, hqY]
  · have hpol : ∀ x' : X, QuadraticMap.polar (qY.comp (e : X →ₗ[K] Y)) x x' =
        QuadraticMap.polar qY (e x) (e x') := fun x' => by
      simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]
    refine e.injective ((hnd (e x) fun y' => ?_).trans (map_zero e).symm)
    rw [← e.apply_symm_apply y', ← hpol]
    exact hx _

theorem projectionOnto_act {ρX : H →* (X ≃ₗ[K] X)} {p q : Submodule K X} (hpq : IsCompl p q)
    (hp : IsInvSub ρX p) (hq : IsInvSub ρX q) (h : H) (x : X) :
    p.projectionOnto q hpq (ρX h x) = restrictAct ρX hp h (p.projectionOnto q hpq x) := by
  apply Subtype.ext
  rw [coe_restrictAct]
  conv_lhs => rw [← Submodule.projection_add_projection_eq_self hpq x]
  rw [map_add, map_add,
    Submodule.projectionOnto_apply_of_mem_left hpq (hp h _ (Submodule.projection_apply_mem hpq x)),
    Submodule.projectionOnto_apply_of_mem_right hpq
      (hq h _ (Submodule.projection_apply_mem hpq.symm x)), add_zero]
  rfl

theorem map_mem_of_not_iso [FiniteDimensional K X] {ρX : H →* (X ≃ₗ[K] X)} {p q : Submodule K X}
    (hpq : IsCompl p q) (hp : IsIrrSub ρX p) (hq : IsIrrSub ρX q)
    (hdim : finrank K p = finrank K q)
    (hne : ¬ IsoRep (restrictAct ρX hp.2.1) (restrictAct ρX hq.2.1))
    {T : X →ₗ[K] X} (hT : ∀ h x, T (ρX h x) = ρX h (T x)) {x : X} (hx : x ∈ p) : T x ∈ p := by
  let S : ↥p →ₗ[K] ↥q := (q.projectionOnto p hpq.symm).comp (T.comp p.subtype)
  have hS : ∀ h y, S (restrictAct ρX hp.2.1 h y) = restrictAct ρX hq.2.1 h (S y) := by
    intro h y
    simp only [S, LinearMap.comp_apply, Submodule.subtype_apply, coe_restrictAct, hT]
    exact projectionOnto_act hpq.symm hq.2.1 hp.2.1 h _
  have h0 := eq_zero_of_not_equiv (restrictAct_irred ρX hp.2.1 hp) hdim hne hS
  have := LinearMap.congr_fun h0 ⟨x, hx⟩
  simp only [S, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] at this
  exact (Submodule.projectionOnto_apply_eq_zero_iff hpq.symm).mp this

theorem pairing_summands_eq_zero [FiniteDimensional K X] {ρX : H →* (X ≃ₗ[K] X)}
    {p q : Submodule K X} (hp : IsIrrSub ρX p) (hq : IsInvSub ρX q)
    (hdim : finrank K p = finrank K q) (hne : ¬ IsoRep (restrictAct ρX hp.2.1) (restrictAct ρX hq))
    (hQ : ∃ Q : QuadraticForm K ↥q, (∀ (h : H) (y : ↥q), Q (restrictAct ρX hq h y) = Q y) ∧
      ∀ y : ↥q, (∀ y' : ↥q, QuadraticMap.polar Q y y' = 0) → y = 0)
    {P : X →ₗ[K] X →ₗ[K] K} (hP : ∀ h x x', P (ρX h x) (ρX h x') = P x x')
    {x x' : X} (hx : x ∈ p) (hx' : x' ∈ q) : P x x' = 0 := by
  obtain ⟨Q, hQ, hQnd⟩ := hQ
  have h0 := pairing_eq_zero_of_not_equiv (restrictAct_irred ρX hp.2.1 hp) hdim hne Q hQ hQnd
    (P := P.compl₁₂ p.subtype q.subtype) (fun h y y' => hP h y y')
  exact LinearMap.congr_fun (LinearMap.congr_fun h0 ⟨x, hx⟩) ⟨x', hx'⟩

end Helpers

section Split

variable {K : Type} [Field K] {H : Type} [Group H] {Mm Nn : Type} [AddCommGroup Mm] [Module K Mm]
  [AddCommGroup Nn] [Module K Nn]

structure PairSplitHyp (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (ρM : H →* (Mm ≃ₗ[K] Mm))
    (ρN : H →* (Nn ≃ₗ[K] Nn)) (β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (Y₁ Y₂ : Submodule K Mm) (Z₁ Z₂ : Submodule K Nn) : Prop where
  kerM : ∀ h : H, φ h = 1 → ρM h = 1
  kerN : ∀ h : H, φ h = 1 → ρN h = 1
  eqv : IsEqvPair φ ρM ρN β
  sepL : ∀ m : Mm, (∀ f : Nn, β m f = 0) → m = 0
  sepR : ∀ f : Nn, (∀ m : Mm, β m f = 0) → f = 0
  complY : IsCompl Y₁ Y₂
  complZ : IsCompl Z₁ Z₂
  irrY₁ : IsIrrSub ρM Y₁
  irrY₂ : IsIrrSub ρM Y₂
  irrZ₁ : IsIrrSub ρN Z₁
  irrZ₂ : IsIrrSub ρN Z₂
  dimY₁ : finrank K Y₁ = 8
  dimY₂ : finrank K Y₂ = 8
  dimZ₁ : finrank K Z₁ = 8
  dimZ₂ : finrank K Z₂ = 8

variable {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {ρM : H →* (Mm ≃ₗ[K] Mm)} {ρN : H →* (Nn ≃ₗ[K] Nn)}
  {β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} {Y₁ Y₂ : Submodule K Mm} {Z₁ Z₂ : Submodule K Nn}

theorem PairSplitHyp.swapZ (hP : PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₁ Z₂) :
    PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₂ Z₁ where
  kerM := hP.kerM
  kerN := hP.kerN
  eqv := hP.eqv
  sepL := hP.sepL
  sepR := hP.sepR
  complY := hP.complY
  complZ := hP.complZ.symm
  irrY₁ := hP.irrY₁
  irrY₂ := hP.irrY₂
  irrZ₁ := hP.irrZ₂
  irrZ₂ := hP.irrZ₁
  dimY₁ := hP.dimY₁
  dimY₂ := hP.dimY₂
  dimZ₁ := hP.dimZ₂
  dimZ₂ := hP.dimZ₁

theorem compl₁₂_ne_zero_of_left (hsepL : ∀ m : Mm, (∀ f : Nn, β m f = 0) → m = 0)
    {Y : Submodule K Mm} (hY : Y ≠ ⊥) (hZ : IsCompl Z₁ Z₂) :
    β.compl₁₂ Y.subtype Z₁.subtype ≠ 0 ∨ β.compl₁₂ Y.subtype Z₂.subtype ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hY (eq_bot_iff.mpr fun y hy => (Submodule.mem_bot K).mpr (hsepL y fun f => ?_))
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ :=
    Submodule.mem_sup.mp (hZ.sup_eq_top.symm ▸ Submodule.mem_top : f ∈ Z₁ ⊔ Z₂)
  have e1 := LinearMap.congr_fun (LinearMap.congr_fun h1 ⟨y, hy⟩) ⟨f₁, hf₁⟩
  have e2 := LinearMap.congr_fun (LinearMap.congr_fun h2 ⟨y, hy⟩) ⟨f₂, hf₂⟩
  simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, LinearMap.zero_apply] at e1 e2
  rw [map_add, e1, e2, add_zero]

theorem compl₁₂_ne_zero_of_right (hsepR : ∀ f : Nn, (∀ m : Mm, β m f = 0) → f = 0)
    {Z : Submodule K Nn} (hZ : Z ≠ ⊥) (hY : IsCompl Y₁ Y₂) :
    β.compl₁₂ Y₁.subtype Z.subtype ≠ 0 ∨ β.compl₁₂ Y₂.subtype Z.subtype ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hZ (eq_bot_iff.mpr fun z hz => (Submodule.mem_bot K).mpr (hsepR z fun m => ?_))
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ :=
    Submodule.mem_sup.mp (hY.sup_eq_top.symm ▸ Submodule.mem_top : m ∈ Y₁ ⊔ Y₂)
  have e1 := LinearMap.congr_fun (LinearMap.congr_fun h1 ⟨m₁, hm₁⟩) ⟨z, hz⟩
  have e2 := LinearMap.congr_fun (LinearMap.congr_fun h2 ⟨m₂, hm₂⟩) ⟨z, hz⟩
  simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, LinearMap.zero_apply] at e1 e2
  rw [map_add, LinearMap.add_apply, e1, e2, add_zero]

end Split

section ConfigC

variable {K : Type} [Field K] {H : Type} [Group H] {Mm Nn : Type} [AddCommGroup Mm] [Module K Mm]
  [AddCommGroup Nn] [Module K Nn]

@[expose] def IsPairConfigC (ρM : H →* (Mm ≃ₗ[K] Mm)) (ρN : H →* (Nn ≃ₗ[K] Nn))
    (β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop :=
  ∃ (M₃ M₄ : Submodule K Mm) (N₄ N₃ : Submodule K Nn),
    IsCompl M₃ M₄ ∧ IsCompl N₄ N₃ ∧ IsIrrSub ρN N₄ ∧ IsIrrSub ρN N₃ ∧
    (∀ T : Nn →ₗ[K] Nn, (∀ h f, T (ρN h f) = ρN h (T f)) →
      (∀ f ∈ N₄, T f ∈ N₄) ∧ ∀ f ∈ N₃, T f ∈ N₃) ∧
    (∀ P : Mm →ₗ[K] Mm →ₗ[K] K, (∀ h m m', P (ρM h m) (ρM h m') = P m m') →
      ∀ m ∈ M₃, ∀ m' ∈ M₄, P m m' = 0) ∧
    (∀ m ∈ M₃, ∀ f ∈ N₃, β m f = 0) ∧ (∀ m ∈ M₄, ∀ f ∈ N₄, β m f = 0) ∧
    (∀ P : Nn →ₗ[K] Nn →ₗ[K] K, (∀ h f f', P (ρN h f) (ρN h f') = P f f') →
      ∀ f ∈ N₄, ∀ f' ∈ N₃, P f f' = 0) ∧
    ∀ f ∈ N₄, ∀ f' ∈ N₃, f ≠ 0 → f' ≠ 0 →
      5 ≤ finrank K (LinearMap.range (β.flip (f + f')))

variable (hTri : Omega8TrialityStatement) [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
  {φ : H →* GL (Fin 4 ⊕ Fin 4) K} (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
  [FiniteDimensional K Mm] [FiniteDimensional K Nn]
  {ρM : H →* (Mm ≃ₗ[K] Mm)} {ρN : H →* (Nn ≃ₗ[K] Nn)}
  {β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} {Y₁ Y₂ : Submodule K Mm} {Z₁ Z₂ : Submodule K Nn}

include hTri hq hφ in
theorem isPairConfigC_of_not_iso (hP : PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₁ Z₂)
    (h11 : β.compl₁₂ Y₁.subtype Z₁.subtype ≠ 0)
    (hne : ¬ IsoRep (restrictAct ρM hP.irrY₁.2.1) (restrictAct ρM hP.irrY₂.2.1)) :
    IsPairConfigC ρM ρN β := by
  have hT := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₁ hP.irrZ₁ hP.dimY₁ hP.dimZ₁ h11
  have hXY := hT.not_iso hTri hq hφ
  have h21 : β.compl₁₂ Y₂.subtype Z₁.subtype = 0 := by
    by_contra h0
    have hT' := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₂ hP.irrZ₁ hP.dimY₂ hP.dimZ₁ h0
    rcases hT.cases hTri hq hφ hT' with ⟨h2X, -⟩ | ⟨-, h1X⟩
    · exact hne h2X.symm
    · exact hXY h1X.symm
  have h22 : β.compl₁₂ Y₂.subtype Z₂.subtype ≠ 0 :=
    (compl₁₂_ne_zero_of_left hP.sepL hP.irrY₂.1 hP.complZ).resolve_left (not_not.mpr h21)
  have hT₂₂ := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₂ hP.irrZ₂ hP.dimY₂ hP.dimZ₂ h22
  obtain ⟨h2Y, h2X⟩ : IsoRep (restrictAct ρM hP.irrY₂.2.1) (restrictAct ρN hP.irrZ₁.2.1) ∧
      IsoRep (restrictAct ρN hP.irrZ₂.2.1) (restrictAct ρM hP.irrY₁.2.1) := by
    rcases hT.cases hTri hq hφ hT₂₂ with ⟨h2X, -⟩ | h
    · exact absurd h2X.symm hne
    · exact h
  have h12 : β.compl₁₂ Y₁.subtype Z₂.subtype = 0 := by
    by_contra h0
    have hT' := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₁ hP.irrZ₂ hP.dimY₁ hP.dimZ₂ h0
    rcases hT.cases hTri hq hφ hT' with ⟨-, h2Y'⟩ | ⟨h1Y, -⟩
    · exact hXY (h2X.symm.trans h2Y')
    · exact hXY h1Y
  have hZne : ¬ IsoRep (restrictAct ρN hP.irrZ₁.2.1) (restrictAct ρN hP.irrZ₂.2.1) :=
    fun h => hXY (h.trans h2X).symm
  have e12 : ∀ m ∈ Y₁, ∀ f ∈ Z₂, β m f = 0 := fun m hm f hf => by
    simpa using LinearMap.congr_fun (LinearMap.congr_fun h12 ⟨m, hm⟩) ⟨f, hf⟩
  have e21 : ∀ m ∈ Y₂, ∀ f ∈ Z₁, β m f = 0 := fun m hm f hf => by
    simpa using LinearMap.congr_fun (LinearMap.congr_fun h21 ⟨m, hm⟩) ⟨f, hf⟩
  refine ⟨Y₁, Y₂, Z₁, Z₂, hP.complY, hP.complZ, hP.irrZ₁, hP.irrZ₂, fun T hT' => ⟨fun f hf =>
    map_mem_of_not_iso hP.complZ hP.irrZ₁ hP.irrZ₂ (hP.dimZ₁.trans hP.dimZ₂.symm) hZne hT' hf,
    fun f hf => map_mem_of_not_iso hP.complZ.symm hP.irrZ₂ hP.irrZ₁
      (hP.dimZ₂.trans hP.dimZ₁.symm) (fun h => hZne h.symm) hT' hf⟩,
    fun P hPinv m hm m' hm' => pairing_summands_eq_zero hP.irrY₁ hP.irrY₂.2.1
      (hP.dimY₁.trans hP.dimY₂.symm) hne
      (exists_quadraticForm_of_iso h2Y (hT.exists_qY hTri hq hφ)) hPinv hm hm',
    e12, e21,
    fun P hPinv f hf f' hf' => pairing_summands_eq_zero hP.irrZ₁ hP.irrZ₂.2.1
      (hP.dimZ₁.trans hP.dimZ₂.symm) hZne
      (exists_quadraticForm_of_iso h2X (hT.exists_qX hTri hq hφ)) hPinv hf hf', ?_⟩
  intro f hf f' hf' hf0 hf'0
  obtain ⟨qX, hqX, hqXnd⟩ := hT.exists_qX hTri hq hφ
  obtain ⟨qY, hqY, hqYnd⟩ := hT.exists_qY hTri hq hφ
  obtain ⟨-, r2, r3, r4, hodd⟩ := hT.ranks hTri hq hφ hqX hqY
    (quadraticForm_ne_zero hqXnd hP.dimY₁) (quadraticForm_ne_zero hqYnd hP.dimZ₁)
  have r1 := (hT.ranks hTri hq hφ hqX hqY (quadraticForm_ne_zero hqXnd hP.dimY₁)
    (quadraticForm_ne_zero hqYnd hP.dimZ₁)).1
  obtain ⟨e₄, he₄⟩ := h2Y
  obtain ⟨e₃, he₃⟩ := h2X
  have he₄s : ∀ h z, e₄.symm (restrictAct ρN hP.irrZ₁.2.1 h z) =
      restrictAct ρM hP.irrY₂.2.1 h (e₄.symm z) := fun h z =>
    e₄.injective (by rw [LinearEquiv.apply_symm_apply, he₄, LinearEquiv.apply_symm_apply])
  have he₃s : ∀ h x, e₃.symm (restrictAct ρM hP.irrY₁.2.1 h x) =
      restrictAct ρN hP.irrZ₂.2.1 h (e₃.symm x) := fun h x =>
    e₃.injective (by rw [LinearEquiv.apply_symm_apply, he₃, LinearEquiv.apply_symm_apply])
  let y : ↥Z₁ := ⟨f, hf⟩
  let x : ↥Y₁ := e₃ ⟨f', hf'⟩
  have hy0 : y ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hx0 : x ≠ 0 := fun h =>
    hf'0 (congrArg Subtype.val (e₃.injective (h.trans (map_zero e₃).symm)))
  have hA : LinearMap.range ((β.compl₁₂ Y₁.subtype Z₁.subtype).flip y) ≤
      LinearMap.range (β.flip (f + f')) := by
    rintro _ ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [LinearMap.flip_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply, map_add,
      e12 m m.2 f' hf', add_zero]
    rfl
  have hβ'' : IsEqvPair φ (restrictAct ρN hP.irrZ₁.2.1) (restrictAct ρM hP.irrY₁.2.1)
      ((β.compl₁₂ Y₂.subtype Z₂.subtype).compl₁₂ (e₄.symm : ↥Z₁ →ₗ[K] ↥Y₂)
        (e₃.symm : ↥Y₁ →ₗ[K] ↥Z₂)) :=
    hT₂₂.eqv.compl₁₂ (fun h z => he₄s h z) (fun h x => he₃s h x)
  obtain ⟨c, hc⟩ := hT.flip.unique hTri hq hφ hβ''
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine h22 (LinearMap.ext fun m => LinearMap.ext fun g => ?_)
    have := LinearMap.congr_fun (LinearMap.congr_fun hc (e₄ m)) (e₃ g)
    simpa using this
  have hB : LinearMap.range ((β.compl₁₂ Y₁.subtype Z₁.subtype) x) ≤
      LinearMap.range (β.flip (f + f')) := by
    rintro _ ⟨z, rfl⟩
    have h1 := LinearMap.congr_fun (LinearMap.congr_fun hc z) x
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.flip_apply, Submodule.subtype_apply, LinearEquiv.symm_apply_apply, x] at h1
    refine ⟨c⁻¹ • (e₄.symm z : Mm), ?_⟩
    rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, map_add,
      e21 _ (e₄.symm z).2 f hf, zero_add, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rfl
  have hfin : ∀ S : Submodule K (Fin 4 ⊕ Fin 4 → K), S ≤ LinearMap.range (β.flip (f + f')) →
      finrank K S ≤ finrank K (LinearMap.range (β.flip (f + f'))) :=
    fun S hS => Submodule.finrank_mono hS
  by_cases hqy : qY y = 0
  · by_cases hqx : qX x = 0
    · have hA4 := r2 y hy0 hqy
      have hB4 := r4 x hx0 hqx
      exact (five_le_finrank_sup hB4 hA4 (hodd x y hx0 hy0 hqx hqy)).trans (hfin _ (sup_le hB hA))
    · have := hfin _ hB
      rw [r3 x hx0 hqx] at this
      omega
  · have := hfin _ hA
    rw [r1 y hy0 hqy] at this
    omega

end ConfigC

section ConfigA

variable {K : Type} [Field K] {H : Type} [Group H] {Mm Nn : Type} [AddCommGroup Mm] [Module K Mm]
  [AddCommGroup Nn] [Module K Nn]

@[expose] def IsPairConfigA (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (ρM : H →* (Mm ≃ₗ[K] Mm))
    (ρN : H →* (Nn ≃ₗ[K] Nn)) (β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop :=
  ∃ (L₃ L₄ : Type) (_ : AddCommGroup L₃) (_ : Module K L₃) (_ : AddCommGroup L₄)
    (_ : Module K L₄) (ρ₃ : H →* (L₃ ≃ₗ[K] L₃)) (ρ₄ : H →* (L₄ ≃ₗ[K] L₄))
    (eM : Mm ≃ₗ[K] (Fin 2 → L₃)) (eN : Nn ≃ₗ[K] (Fin 2 → L₄))
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (q₃ : QuadraticForm K L₃)
    (q₄ : QuadraticForm K L₄),
    finrank K L₃ = 8 ∧ finrank K L₄ = 8 ∧ IsIrrLin ρ₃ ∧ IsIrrLin ρ₄ ∧
    (∀ h m, eM (ρM h m) = fun i => ρ₃ h (eM m i)) ∧
    (∀ h f, eN (ρN h f) = fun i => ρ₄ h (eN f i)) ∧
    (∀ m f, β m f = ∑ i, μ (eM m i) (eN f i)) ∧
    IsEqvPair φ ρ₃ ρ₄ μ ∧ μ ≠ 0 ∧
    (∀ h a, q₃ (ρ₃ h a) = q₃ a) ∧ (∀ a, (∀ a', QuadraticMap.polar q₃ a a' = 0) → a = 0) ∧
    (∀ h c, q₄ (ρ₄ h c) = q₄ c) ∧ (∀ c, (∀ c', QuadraticMap.polar q₄ c c' = 0) → c = 0) ∧
    (∀ P : Mm →ₗ[K] Mm →ₗ[K] K, (∀ h m m', P (ρM h m) (ρM h m') = P m m') →
      ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ m m',
        P m m' = ∑ i, ∑ j, Φ i j * QuadraticMap.polar q₃ (eM m i) (eM m' j)) ∧
    ∀ P : Nn →ₗ[K] Nn →ₗ[K] K, (∀ h f f', P (ρN h f) (ρN h f') = P f f') →
      ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ f f',
        P f f' = ∑ i, ∑ j, Φ i j * QuadraticMap.polar q₄ (eN f i) (eN f' j)

theorem exists_act_ne_one {X : Type} [AddCommGroup X] [Module K X] {ρX : H →* (X ≃ₗ[K] X)}
    (hirr : IsIrrLin ρX) (hdim : finrank K X = 8) : ∃ h, ρX h ≠ 1 := by
  by_contra hcon
  have h1 : ∀ h, ρX h = 1 := fun h => by
    by_contra hh
    exact hcon ⟨h, hh⟩
  haveI : Module.Finite K X := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial X := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  rcases hirr (K ∙ x) (fun h y hy => by rw [h1 h]; exact hy) with h0 | h0
  · exact hx ((Submodule.span_singleton_eq_bot).mp h0)
  · have := finrank_span_singleton (K := K) hx
    rw [h0, finrank_top] at this
    omega

theorem exists_coords {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {ρX : H →* (X ≃ₗ[K] X)} {p q : Submodule K X} (hpq : IsCompl p q) (hp : IsInvSub ρX p)
    (hq : IsInvSub ρX q) (θ : ↥p ≃ₗ[K] ↥q)
    (hθ : ∀ h a, θ (restrictAct ρX hp h a) = restrictAct ρX hq h (θ a)) :
    ∃ e : X ≃ₗ[K] (Fin 2 → ↥p), (∀ a, e.symm a = (a 0 : X) + (θ (a 1) : X)) ∧
      ∀ h x, e (ρX h x) = fun i => restrictAct ρX hp h (e x i) := by
  let S : (Fin 2 → ↥p) →ₗ[K] X := p.subtype ∘ₗ LinearMap.proj 0 +
    q.subtype ∘ₗ (θ : ↥p →ₗ[K] ↥q) ∘ₗ LinearMap.proj 1
  have hS : ∀ a, S a = (a 0 : X) + (θ (a 1) : X) := fun a => rfl
  have hinj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun a ha => ?_
    rw [hS] at ha
    have h0 : (a 0 : X) = 0 := by
      have hmem : (a 0 : X) ∈ q := by
        rw [eq_neg_of_add_eq_zero_left ha]
        exact q.neg_mem (θ (a 1)).2
      exact (Submodule.disjoint_def.mp hpq.disjoint) _ (a 0).2 hmem
    have h1 : (θ (a 1) : X) = 0 := by rwa [h0, zero_add] at ha
    funext i
    fin_cases i
    · exact Subtype.ext h0
    · exact θ.injective (Subtype.ext (h1.trans (by simp)))
  have hdim : finrank K (Fin 2 → ↥p) = finrank K X := by
    rw [Module.finrank_pi_fintype, Fin.sum_univ_two, ← Submodule.finrank_add_eq_of_isCompl hpq,
      LinearEquiv.finrank_eq θ]
  let e := (S.linearEquivOfInjective hinj hdim).symm
  refine ⟨e, fun a => ?_, fun h x => ?_⟩
  · show S.linearEquivOfInjective hinj hdim a = _
    rw [LinearMap.linearEquivOfInjective_apply, hS]
  · show (S.linearEquivOfInjective hinj hdim).symm (ρX h x) = _
    rw [LinearEquiv.symm_apply_eq, LinearMap.linearEquivOfInjective_apply, hS]
    have hx : x = ((e x 0 : ↥p) : X) + (θ (e x 1) : X) := by
      rw [← hS]
      exact (LinearEquiv.apply_symm_apply (S.linearEquivOfInjective hinj hdim) x).symm
    conv_lhs => rw [hx]
    rw [map_add, coe_restrictAct, hθ, coe_restrictAct]

end ConfigA

section ConfigABuild

variable {K : Type} [Field K] {H : Type} [Group H] {Mm Nn : Type} [AddCommGroup Mm] [Module K Mm]
  [AddCommGroup Nn] [Module K Nn]

theorem exists_matrix_of_coords {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {ρX : H →* (X ≃ₗ[K] X)} {ρM : H →* (Mm ≃ₗ[K] Mm)}
    (hEnd : ∀ T : X →ₗ[K] X, (∀ h : H, T ∘ₗ (ρX h : X →ₗ[K] X) = (ρX h : X →ₗ[K] X) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id)
    (q : QuadraticForm K X) (hq : ∀ h x, q (ρX h x) = q x)
    (hnd : ∀ x, (∀ x', QuadraticMap.polar q x x' = 0) → x = 0) {e : Mm ≃ₗ[K] (Fin 2 → X)}
    (he : ∀ h m, e (ρM h m) = fun i => ρX h (e m i)) (P : Mm →ₗ[K] Mm →ₗ[K] K)
    (hP : ∀ h m m', P (ρM h m) (ρM h m') = P m m') :
    ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ m m',
      P m m' = ∑ i, ∑ j, Φ i j * QuadraticMap.polar q (e m i) (e m' j) := by
  have hes : ∀ h a, e.symm (fun i => ρX h (a i)) = ρM h (e.symm a) := fun h a => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  obtain ⟨Φ, hΦ⟩ := exists_matrix_of_invariant hEnd q hq hnd
    (P.compl₁₂ (e.symm : (Fin 2 → X) →ₗ[K] Mm) (e.symm : (Fin 2 → X) →ₗ[K] Mm))
    fun h a a' => by
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hes, hP]
  refine ⟨Φ, fun m m' => ?_⟩
  have := hΦ (e m) (e m')
  simpa using this

variable (hTri : Omega8TrialityStatement) (hEnd : Omega8EndScalarStatement) [Finite K] [CharP K 2]
  (hq : 4 ≤ Nat.card K) {φ : H →* GL (Fin 4 ⊕ Fin 4) K}
  (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))

include hEnd hq hφ in
theorem endScalar_of_irr {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {ρX : H →* (X ≃ₗ[K] X)} (hk : ∀ h : H, φ h = 1 → ρX h = 1) (hirr : IsIrrLin ρX)
    (hdim : finrank K X = 8) :
    ∀ T : X →ₗ[K] X, (∀ h : H, T ∘ₗ (ρX h : X →ₗ[K] X) = (ρX h : X →ₗ[K] X) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id :=
  hEnd K hq H φ hφ X ρX hk hirr (exists_act_ne_one hirr hdim) (by omega)

variable [FiniteDimensional K Mm] [FiniteDimensional K Nn]
  {ρM : H →* (Mm ≃ₗ[K] Mm)} {ρN : H →* (Nn ≃ₗ[K] Nn)}
  {β : Mm →ₗ[K] Nn →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} {Y₁ Y₂ : Submodule K Mm} {Z₁ Z₂ : Submodule K Nn}

include hTri hEnd hq hφ in
theorem isPairConfigA_of_iso (hP : PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₁ Z₂)
    (h11 : β.compl₁₂ Y₁.subtype Z₁.subtype ≠ 0)
    (hY : IsoRep (restrictAct ρM hP.irrY₁.2.1) (restrictAct ρM hP.irrY₂.2.1))
    (hZ : IsoRep (restrictAct ρN hP.irrZ₁.2.1) (restrictAct ρN hP.irrZ₂.2.1)) :
    IsPairConfigA φ ρM ρN β := by
  have hT := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₁ hP.irrZ₁ hP.dimY₁ hP.dimZ₁ h11
  obtain ⟨θ, hθ⟩ := hY
  obtain ⟨θ', hθ'⟩ := hZ
  obtain ⟨eM, heMs, heM⟩ := exists_coords hP.complY hP.irrY₁.2.1 hP.irrY₂.2.1 θ hθ
  obtain ⟨eN₀, heN₀s, heN₀⟩ := exists_coords hP.complZ hP.irrZ₁.2.1 hP.irrZ₂.2.1 θ' hθ'
  set μ := β.compl₁₂ Y₁.subtype Z₁.subtype with hμ
  let ι : Fin 2 → (↥Y₁ →ₗ[K] Mm) := ![Y₁.subtype, Y₂.subtype ∘ₗ (θ : ↥Y₁ →ₗ[K] ↥Y₂)]
  let ι' : Fin 2 → (↥Z₁ →ₗ[K] Nn) := ![Z₁.subtype, Z₂.subtype ∘ₗ (θ' : ↥Z₁ →ₗ[K] ↥Z₂)]
  have hι : ∀ i h a, ι i (restrictAct ρM hP.irrY₁.2.1 h a) = ρM h (ι i a) := by
    intro i h a
    fin_cases i
    · rfl
    · show ((θ (restrictAct ρM hP.irrY₁.2.1 h a) : ↥Y₂) : Mm) = ρM h ((θ a : ↥Y₂) : Mm)
      rw [hθ, coe_restrictAct]
  have hι' : ∀ j h c, ι' j (restrictAct ρN hP.irrZ₁.2.1 h c) = ρN h (ι' j c) := by
    intro j h c
    fin_cases j
    · rfl
    · show ((θ' (restrictAct ρN hP.irrZ₁.2.1 h c) : ↥Z₂) : Nn) = ρN h ((θ' c : ↥Z₂) : Nn)
      rw [hθ', coe_restrictAct]
  have hsumM : ∀ a, eM.symm a = ∑ i, ι i (a i) := fun a => by
    rw [heMs, Fin.sum_univ_two]
    rfl
  have hsumN : ∀ c, eN₀.symm c = ∑ j, ι' j (c j) := fun c => by
    rw [heN₀s, Fin.sum_univ_two]
    rfl
  have hblk : ∀ i j, ∃ c : K, β.compl₁₂ (ι i) (ι' j) = c • μ :=
    fun i j => hT.unique hTri hq hφ (hP.eqv.compl₁₂ (hι i) (hι' j))
  choose Ψ hΨ using hblk
  have hβc : ∀ a c, β (eM.symm a) (eN₀.symm c) = ∑ i, ∑ j, Ψ i j • μ (a i) (c j) := by
    intro a c
    rw [hsumM, hsumN]
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := LinearMap.congr_fun (LinearMap.congr_fun (hΨ i j) (a i)) (c j)
    rw [LinearMap.compl₁₂_apply] at this
    rw [this]
    rfl
  have hΨu : IsUnit (Matrix.of Ψ).det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hrow : ∀ i, ∑ j, Ψ i j * v j = 0 := fun i => by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    haveI : Nontrivial ↥Z₁ := Submodule.nontrivial_iff_ne_bot.mpr hP.irrZ₁.1
    obtain ⟨c₁, hc₁⟩ := exists_ne (0 : ↥Z₁)
    have hf : eN₀.symm (fun j => v j • c₁) = 0 := by
      refine hP.sepR _ fun m => ?_
      rw [← eM.symm_apply_apply m, hβc]
      calc ∑ i, ∑ j, Ψ i j • μ (eM m i) (v j • c₁)
          = ∑ i, (∑ j, Ψ i j * v j) • μ (eM m i) c₁ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, smul_smul]
        _ = 0 := by simp [hrow]
    have h0 : (fun j => v j • c₁) = 0 := eN₀.symm.injective (hf.trans (map_zero _).symm)
    exact hv0 (funext fun j => (smul_eq_zero.mp (congrFun h0 j)).resolve_right hc₁)
  let eN := eN₀.trans (matrixActFin2 (Matrix.of Ψ) hΨu)
  have heN : ∀ f i, eN f i = ∑ j, Ψ i j • eN₀ f j := fun f i => by
    simp only [eN, LinearEquiv.trans_apply, matrixActFin2_apply, Matrix.of_apply]
  have heNact : ∀ h f, eN (ρN h f) = fun i => restrictAct ρN hP.irrZ₁.2.1 h (eN f i) := by
    intro h f
    funext i
    rw [heN, heN, heN₀ h f, map_sum]
    simp only [map_smul]
  have hC3 : ∀ m f, β m f = ∑ i, μ (eM m i) (eN f i) := by
    intro m f
    conv_lhs => rw [← eM.symm_apply_apply m, ← eN₀.symm_apply_apply f]
    rw [hβc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heN, map_sum]
    simp only [map_smul]
  obtain ⟨q₃, hq₃, hq₃nd⟩ := hT.exists_qX hTri hq hφ
  obtain ⟨q₄, hq₄, hq₄nd⟩ := hT.exists_qY hTri hq hφ
  exact ⟨↥Y₁, ↥Z₁, inferInstance, inferInstance, inferInstance, inferInstance,
    restrictAct ρM hP.irrY₁.2.1, restrictAct ρN hP.irrZ₁.2.1, eM, eN, μ, q₃, q₄, hP.dimY₁,
    hP.dimZ₁, hT.irrX, hT.irrY, heM, heNact, hC3, hT.eqv, hT.ne_zero, hq₃, hq₃nd, hq₄, hq₄nd,
    fun P hP' => exists_matrix_of_coords
      (endScalar_of_irr hEnd hq hφ hT.kerX hT.irrX hP.dimY₁) q₃ hq₃ hq₃nd heM P hP',
    fun P hP' => exists_matrix_of_coords
      (endScalar_of_irr hEnd hq hφ hT.kerY hT.irrY hP.dimZ₁) q₄ hq₄ hq₄nd heNact P hP'⟩

include hTri hEnd hq hφ in
theorem isPairConfigA_or_isPairConfigC_of_ne_zero (hP : PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₁ Z₂)
    (h11 : β.compl₁₂ Y₁.subtype Z₁.subtype ≠ 0) :
    IsPairConfigA φ ρM ρN β ∨ IsPairConfigC ρM ρN β := by
  by_cases hY : IsoRep (restrictAct ρM hP.irrY₁.2.1) (restrictAct ρM hP.irrY₂.2.1)
  · left
    refine isPairConfigA_of_iso hTri hEnd hq hφ hP h11 hY ?_
    have hT := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₁ hP.irrZ₁ hP.dimY₁ hP.dimZ₁ h11
    have hXY := hT.not_iso hTri hq hφ
    rcases compl₁₂_ne_zero_of_right hP.sepR hP.irrZ₂.1 hP.complY with h12 | h22
    · have hT' := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₁ hP.irrZ₂ hP.dimY₁ hP.dimZ₂ h12
      rcases hT.cases hTri hq hφ hT' with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2.symm
      · exact absurd h1 hXY
    · have hT' := triPair_restrict hP.kerM hP.kerN hP.eqv hP.irrY₂ hP.irrZ₂ hP.dimY₂ hP.dimZ₂ h22
      rcases hT.cases hTri hq hφ hT' with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2.symm
      · exact absurd (hY.trans h1) hXY
  · exact Or.inr (isPairConfigC_of_not_iso hTri hq hφ hP h11 hY)

include hTri hEnd hq hφ in
theorem isPairConfigA_or_isPairConfigC (hP : PairSplitHyp φ ρM ρN β Y₁ Y₂ Z₁ Z₂) :
    IsPairConfigA φ ρM ρN β ∨ IsPairConfigC ρM ρN β := by
  rcases compl₁₂_ne_zero_of_left hP.sepL hP.irrY₁.1 hP.complZ with h | h
  · exact isPairConfigA_or_isPairConfigC_of_ne_zero hTri hEnd hq hφ hP h
  · exact isPairConfigA_or_isPairConfigC_of_ne_zero hTri hEnd hq hφ hP.swapZ h

end ConfigABuild

section Forms

variable {K : Type} [Field K]

theorem exists_polar_eq {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (q : QuadraticForm K X) (hnd : ∀ x : X, (∀ x' : X, QuadraticMap.polar q x x' = 0) → x = 0)
    (l : X →ₗ[K] K) : ∃ R : X, ∀ a, QuadraticMap.polar q R a = l a := by
  have hinj : Function.Injective (QuadraticMap.polarBilin q) := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy => hnd y fun y' => ?_
    have h := LinearMap.congr_fun hy y'
    rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
  let e := (QuadraticMap.polarBilin q).linearEquivOfInjective hinj Subspace.dual_finrank_eq.symm
  refine ⟨e.symm l, fun a => ?_⟩
  have h := LinearMap.congr_fun (e.apply_symm_apply l) a
  rwa [LinearMap.linearEquivOfInjective_apply, QuadraticMap.polarBilin_apply_apply] at h

variable {L Mm : Type} [AddCommGroup L] [Module K L] [AddCommGroup Mm] [Module K Mm]

theorem form_single (q : QuadraticForm K L) (e : Mm ≃ₗ[K] (Fin 2 → L))
    (Φ : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) (a a' : L) :
    ∑ i', ∑ j', Φ i' j' * QuadraticMap.polar q (e (e.symm (Pi.single i a)) i')
      (e (e.symm (Pi.single j a')) j') = Φ i j * QuadraticMap.polar q a a' := by
  simp only [LinearEquiv.apply_symm_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_right]

theorem matrix_symm_isUnit_of_form (q : QuadraticForm K L)
    (hnd : ∀ a : L, (∀ a' : L, QuadraticMap.polar q a a' = 0) → a = 0) (hL : ∃ a : L, a ≠ 0)
    (e : Mm ≃ₗ[K] (Fin 2 → L)) (P : Mm →ₗ[K] Mm →ₗ[K] K) (Φ : Matrix (Fin 2) (Fin 2) K)
    (hΦ : ∀ m m', P m m' = ∑ i, ∑ j, Φ i j * QuadraticMap.polar q (e m i) (e m' j))
    (hsymm : ∀ m m', P m m' = P m' m) (hnd' : ∀ m, (∀ m', P m m' = 0) → m = 0) :
    Φ.transpose = Φ ∧ IsUnit Φ.det := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨a', ha'⟩ : ∃ a', QuadraticMap.polar q a a' ≠ 0 := by
    by_contra hcon
    exact ha (hnd a fun a' => by
      by_contra h
      exact hcon ⟨a', h⟩)
  have hsingle : ∀ i j b b', P (e.symm (Pi.single i b)) (e.symm (Pi.single j b')) =
      Φ i j * QuadraticMap.polar q b b' := fun i j b b' => by
    rw [hΦ]
    exact form_single q e Φ i j b b'
  refine ⟨Matrix.ext fun i j => ?_, ?_⟩
  · rw [Matrix.transpose_apply]
    have h1 := hsingle i j a a'
    rw [hsymm, hsingle, QuadraticMap.polar_comm] at h1
    exact mul_right_cancel₀ ha' h1
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hrow : ∀ i, ∑ j, Φ i j * v j = 0 := fun i => by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    have ha'0 : a' ≠ 0 := by
      rintro rfl
      exact ha' (QuadraticMap.polar_zero_right q a)
    have hm : e.symm (fun j => v j • a') = 0 := by
      refine hnd' _ fun m => ?_
      rw [hsymm, hΦ]
      simp only [LinearEquiv.apply_symm_apply]
      calc ∑ i, ∑ j, Φ i j * QuadraticMap.polar q (e m i) (v j • a')
          = ∑ i, (∑ j, Φ i j * v j) * QuadraticMap.polar q (e m i) a' := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [QuadraticMap.polar_smul_right, smul_eq_mul]
            ring
        _ = 0 := by simp [hrow]
    have h0 : (fun j => v j • a') = 0 := e.symm.injective (hm.trans (map_zero _).symm)
    exact hv0 (funext fun j => (smul_eq_zero.mp (congrFun h0 j)).resolve_right ha'0)

end Forms

section Kappa

variable {K : Type} [Field K]
  {L₃ L₄ Mm Nn U V : Type} [AddCommGroup L₃] [Module K L₃] [FiniteDimensional K L₃]
  [AddCommGroup L₄] [Module K L₄] [AddCommGroup Mm] [Module K Mm] [AddCommGroup Nn]
  [Module K Nn] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

theorem exists_kappa_of_adjoint (q₃ : QuadraticForm K L₃)
    (hq₃nd : ∀ a : L₃, (∀ a' : L₃, QuadraticMap.polar q₃ a a' = 0) → a = 0)
    (q₄ : QuadraticForm K L₄) (eM : Mm ≃ₗ[K] (Fin 2 → L₃)) (eN : Nn ≃ₗ[K] (Fin 2 → L₄))
    {φ ψ : Matrix (Fin 2) (Fin 2) K} (hφs : φ.transpose = φ) (hφψ : φ * ψ = 1)
    (BM : Mm →ₗ[K] Mm →ₗ[K] K)
    (hBM : ∀ m m', BM m m' = ∑ i, ∑ j, φ i j * QuadraticMap.polar q₃ (eM m i) (eM m' j))
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] V) (β' : Mm →ₗ[K] Nn →ₗ[K] V)
    (hβ' : ∀ m f, β' m f = ∑ i, μ (eM m i) (eN f i)) (π : U →ₗ[K] V →ₗ[K] K)
    (X : Nn → U → Mm) (hX : ∀ f u m, BM (X f u) m = -π u (β' m f))
    (bN : Nn → Nn → K) (ω : U → U → K)
    (hbN : ∀ f f' u u', bN f f' * ω u u' = BM (X f u) (X f' u') - BM (X f' u) (X f u'))
    {Φ' : Matrix (Fin 2) (Fin 2) K}
    (hΦ' : ∀ f f', bN f f' = ∑ i, ∑ j, Φ' i j * QuadraticMap.polar q₄ (eN f i) (eN f' j))
    (hω : ∃ u u', ω u u' ≠ 0) (hq₄ : ∃ c c' : L₄, QuadraticMap.polar q₄ c c' ≠ 0) :
    ∃ κ : K, ∀ i j, Φ' i j = κ * ψ i j := by
  classical
  have hR : ∀ (u : U) (c : L₄), ∃ R : L₃, ∀ a, QuadraticMap.polar q₃ R a = π u (μ a c) :=
    fun u c => exists_polar_eq q₃ hq₃nd ((π u).comp (μ.flip c))
  choose R hR using hR
  have hR0 : ∀ u, R u 0 = 0 := fun u => hq₃nd _ fun a => by rw [hR, map_zero, map_zero]
  have hψφ : ψ * φ = 1 := mul_eq_one_comm.mp hφψ
  have hψs : ψ.transpose = ψ := by
    have h1 : ψ.transpose * φ = 1 := by
      rw [← hφs, ← Matrix.transpose_mul, hφψ, Matrix.transpose_one]
    calc ψ.transpose = ψ.transpose * (φ * ψ) := by rw [hφψ, Matrix.mul_one]
      _ = ψ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hstep2 : ∀ f u j a, ∑ i, φ i j * QuadraticMap.polar q₃ (eM (X f u) i) a =
      -π u (μ a (eN f j)) := by
    intro f u j a
    have h := hX f u (eM.symm (Pi.single j a))
    rw [hBM, hβ'] at h
    simp only [LinearEquiv.apply_symm_apply] at h
    convert h using 1
    · fin_cases j <;>
        simp [Fin.sum_univ_two, QuadraticMap.polar_zero_right, QuadraticMap.polar_zero_left]
    · fin_cases j <;> simp [Fin.sum_univ_two]
  have hstep3 : ∀ f u l a, QuadraticMap.polar q₃ (eM (X f u) l) a =
      ∑ j, ψ j l * -π u (μ a (eN f j)) := by
    intro f u l a
    simp_rw [← hstep2 f u, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ j, ψ j l * (φ i j * QuadraticMap.polar q₃ (eM (X f u) i) a) =
        (φ * ψ) i l * QuadraticMap.polar q₃ (eM (X f u) i) a := fun i => by
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [this, hφψ, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hstep4 : ∀ f f' u u', BM (X f u) (X f' u') =
      ∑ i, ∑ j, ψ j i * π u' (μ (R u (eN f i)) (eN f' j)) := by
    intro f f' u u'
    rw [hX, hβ', map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hR, QuadraticMap.polar_comm, hstep3, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpure : ∀ (k l : Fin 2) (c c' : L₄) (u u' : U),
      Φ' k l * QuadraticMap.polar q₄ c c' * ω u u' =
        ψ k l * (π u' (μ (R u c) c') - π u' (μ (R u c') c)) := by
    intro k l c c' u u'
    have h := hbN (eN.symm (Pi.single k c)) (eN.symm (Pi.single l c')) u u'
    rw [hΦ', form_single q₄ eN Φ' k l c c', hstep4, hstep4] at h
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [h]
    have hψ10 : ψ 1 0 = ψ 0 1 := by
      have := congrFun (congrFun hψs 0) 1
      rwa [Matrix.transpose_apply] at this
    fin_cases k <;> fin_cases l <;>
      simp [Fin.sum_univ_two, hR0, hψ10] <;> ring
  obtain ⟨u₀, u₀', hω₀⟩ := hω
  obtain ⟨c₀, c₀', hc₀⟩ := hq₄
  obtain ⟨k₀, l₀, hψ₀⟩ : ∃ k l, ψ k l ≠ 0 := by
    by_contra hcon
    have hψ0 : ψ = 0 := Matrix.ext fun k l => by
      by_contra h
      exact hcon ⟨k, l, h⟩
    rw [hψ0, Matrix.mul_zero] at hφψ
    have := congrFun (congrFun hφψ 0) 0
    simp at this
  set S₀ := π u₀' (μ (R u₀ c₀) c₀') - π u₀' (μ (R u₀ c₀') c₀)
  set X₀ := QuadraticMap.polar q₄ c₀ c₀' * ω u₀ u₀' with hX₀def
  have hX₀ : X₀ ≠ 0 := mul_ne_zero hc₀ hω₀
  refine ⟨Φ' k₀ l₀ / ψ k₀ l₀, fun k l => ?_⟩
  have h1 : Φ' k l * X₀ = ψ k l * S₀ := by rw [hX₀def, ← mul_assoc]; exact hpure k l c₀ c₀' u₀ u₀'
  have h0 : Φ' k₀ l₀ * X₀ = ψ k₀ l₀ * S₀ := by
    rw [hX₀def, ← mul_assoc]
    exact hpure k₀ l₀ c₀ c₀' u₀ u₀'
  refine mul_right_cancel₀ hX₀ ?_
  calc Φ' k l * X₀ = ψ k l * S₀ := h1
    _ = ψ k l * (Φ' k₀ l₀ * X₀ / ψ k₀ l₀) := by
      rw [h0]
      field_simp
    _ = Φ' k₀ l₀ / ψ k₀ l₀ * ψ k l * X₀ := by ring

end Kappa

end CFSG.RankThree.GF2n.Stroth80.S715L
