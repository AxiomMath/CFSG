module

public import CFSG.Quasithin.Background.G1Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

public section

open Matrix

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def IsPoint (A : Submodule F (Fin n → F)) : Prop := Module.finrank F A = 1

@[expose] def IsHyperplane (B : Submodule F (Fin n → F)) : Prop := Module.finrank F B + 1 = n

@[expose] def IsFlag (A B : Submodule F (Fin n → F)) : Prop := IsPoint A ∧ IsHyperplane B ∧ A ≤ B

@[expose] def actSub (g : Matrix.SpecialLinearGroup (Fin n) F) (A : Submodule F (Fin n → F)) :
    Submodule F (Fin n → F) :=
  A.map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F))

theorem mem_actSub {g : Matrix.SpecialLinearGroup (Fin n) F} {A : Submodule F (Fin n → F)}
    {v : Fin n → F} : v ∈ actSub g A ↔ ∃ w ∈ A, g • w = v := by
  unfold actSub
  rw [Submodule.mem_map]
  rfl

theorem isPoint_Vi (i : Fin n) : IsPoint (Vi F n i) := by
  unfold IsPoint Vi
  exact finrank_span_singleton (by simp)

theorem isHyperplane_Vhat (j : Fin n) : IsHyperplane (Vhat F n j) := by
  have hker : Vhat F n j = LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) j) := by
    ext v
    rw [mem_Vhat]
    rfl
  have hrange : LinearMap.range (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) j) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single j c, by simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) j)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  unfold IsHyperplane
  rw [hker]
  omega

theorem isFlag_Vi_Vhat {i j : Fin n} (hij : i ≠ j) : IsFlag (Vi F n i) (Vhat F n j) :=
  ⟨isPoint_Vi i, isHyperplane_Vhat j, fun _ hv => mem_Vhat.2 (mem_Vi.1 hv j (Ne.symm hij))⟩

theorem exists_smul_eq_of_coord_one (z : Fin n) {w : Fin n → F} (hw : w z = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, g • (Pi.single z (1 : F) : Fin n → F) = w := by
  set u : Fin n → F := w - Pi.single z 1 with hu
  have hdet : (1 + Matrix.vecMulVec u (Pi.single z (1 : F))).det = 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    have : (Pi.single z (1 : F) : Fin n → F) ⬝ᵥ u = 0 := by
      rw [dotProduct, Finset.sum_eq_single z]
      · simp [hu, hw]
      · intro b _ hb
        simp [hb]
      · simp
    rw [this, add_zero]
  let g : Matrix.SpecialLinearGroup (Fin n) F := ⟨1 + Matrix.vecMulVec u (Pi.single z (1 : F)), hdet⟩
  refine ⟨g, ?_⟩
  funext k
  rw [smul_eq_mulVec']
  simp only [g, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, hu, Pi.sub_apply]
  by_cases hk : k = z
  · subst hk; simp [hw]
  · simp [hk]

theorem exists_smul_coord_one (hn : 2 ≤ n) (z : Fin n) {v : Fin n → F} (hv : v ≠ 0) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) F, (h • v) z = 1 := by
  have key : ∀ w : Fin n → F, (∃ k, k ≠ z ∧ w k ≠ 0) →
      ∃ h : Matrix.SpecialLinearGroup (Fin n) F, (h • w) z = 1 := by
    rintro w ⟨k, hkz, hk⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection (Ne.symm hkz) ((1 - w z) / w k), ?_⟩
    rw [T_smul_apply]
    simp only [ite_true]
    field_simp
    ring
  by_cases hex : ∃ k, k ≠ z ∧ v k ≠ 0
  · exact key v hex
  · push Not at hex
    have hz : v z ≠ 0 := by
      intro h
      apply hv
      funext k
      by_cases hk : k = z
      · subst hk; simpa using h
      · exact hex k hk
    obtain ⟨o, hoz⟩ : ∃ o : Fin n, o ≠ z := by
      by_cases h0 : z.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by simp [← h] at h0⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 (by simp [← h])⟩
    set h₁ := Matrix.SpecialLinearGroup.transvection hoz (1 : F) with hh₁
    have : ∃ k, k ≠ z ∧ (h₁ • v) k ≠ 0 := by
      refine ⟨o, hoz, ?_⟩
      rw [T_smul_apply]
      simp [hex o hoz, hz]
    obtain ⟨h₂, hh₂⟩ := key _ this
    exact ⟨h₂ * h₁, by rwa [mul_smul]⟩

theorem exists_smul_single_eq (hn : 2 ≤ n) (z : Fin n) {v : Fin n → F} (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F, g • (Pi.single z (1 : F) : Fin n → F) = v := by
  obtain ⟨h, hh⟩ := exists_smul_coord_one hn z hv
  obtain ⟨g, hg⟩ := exists_smul_eq_of_coord_one z hh
  refine ⟨h⁻¹ * g, ?_⟩
  rw [mul_smul, hg, inv_smul_smul]

theorem exists_actSub_Vi_eq (hn : 2 ≤ n) (z : Fin n) {A : Submodule F (Fin n → F)}
    (hA : IsPoint A) : ∃ g : Matrix.SpecialLinearGroup (Fin n) F, actSub g (Vi F n z) = A := by
  obtain ⟨v, hv0, hv⟩ := (finrank_eq_one_iff' (K := F) (V := A)).1 hA
  have hv' : (v : Fin n → F) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨g, hg⟩ := exists_smul_single_eq hn z hv'
  refine ⟨g, ?_⟩
  ext x
  rw [mem_actSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have : g • (c • (Pi.single z (1 : F) : Fin n → F)) = c • (v : Fin n → F) := by
      rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', hg]
    rw [this]
    exact A.smul_mem c v.2
  · intro hx
    obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    refine ⟨c • (Pi.single z (1 : F) : Fin n → F), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    have : g • (c • (Pi.single z (1 : F) : Fin n → F)) = c • (v : Fin n → F) := by
      rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', hg]
    rw [this]
    exact congrArg Subtype.val hc

section Hyp

variable {U : Type*} [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]

@[expose] def commU (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) : AddSubgroup U :=
  AddSubgroup.closure {w | ∃ t ∈ X, ∃ u : U, w = t • u - u}

@[expose] def fixU (X : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) : AddSubgroup U where
  carrier := {u | ∀ t ∈ X, t • u = u}
  zero_mem' := fun t _ => smul_zero t
  add_mem' := fun {a b} ha hb t ht => by rw [smul_add, ha t ht, hb t ht]
  neg_mem' := fun {a} ha t ht => by rw [smul_neg, ha t ht]

@[expose] def actU (g : Matrix.SpecialLinearGroup (Fin n) F) : U →+ U :=
  AddMonoidHom.mk' (fun u => g • u) (fun a b => smul_add g a b)

variable (F n U) in
structure G13Hyp (φ : Submodule F (Fin n → F) → AddSubgroup U) : Prop where
  equivariant : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (A : Submodule F (Fin n → F)),
    IsPoint A → φ (actSub g A) = (φ A).map (actU g)
  commU_le : ∀ A B : Submodule F (Fin n → F), IsFlag A B → commU (rootGroup A B) ≤ φ A
  le_fixU : ∀ A B : Submodule F (Fin n → F), IsFlag A B → ∀ D : Submodule F (Fin n → F),
    IsPoint D → D ≤ B → φ D ≤ fixU (rootGroup A B)
  disjoint : ∀ A₁ A₂ : Submodule F (Fin n → F), IsPoint A₁ → IsPoint A₂ → A₁ ≠ A₂ →
    φ A₁ ⊓ φ A₂ = ⊥
  iSup_eq : ⨆ (A : Submodule F (Fin n → F)) (_ : IsPoint A), φ A = ⊤

variable (F n) in
@[expose] def Theorem_G_1_3 [Finite F] [CharP F 2] (hn : 2 ≤ n) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
    [Finite U], (∀ u : U, u + u = 0) → ∀ φ : Submodule F (Fin n → F) → AddSubgroup U,
      G13Hyp F n U φ →
      ∃ s : ℕ, Nat.card (φ (Vi F n ⟨0, by omega⟩)) = Nat.card F ^ s ∧
        ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ ⨆ j, W j = ⊤ ∧ ∀ j,
          (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (w : U), w ∈ W j → g • w ∈ W j) ∧
          ∃ f : (Fin n → F) →+ U, Function.Injective f ∧ f.range = W j ∧
            ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F), f (g • v) = g • f v

variable (U) in
@[expose] def stabU (W : AddSubgroup U) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∀ u : U, u ∈ W ↔ g • u ∈ W}
  one_mem' := fun u => by simp
  mul_mem' := fun {g h} hg hh u => by rw [hh u, hg (h • u), mul_smul]
  inv_mem' := fun {g} hg u => by
    have := hg (g⁻¹ • u)
    rw [smul_inv_smul] at this
    exact this.symm

theorem iSup_phi_Vi_eq_top (hn : 2 ≤ n) {φ : Submodule F (Fin n → F) → AddSubgroup U}
    (h : G13Hyp F n U φ) : ⨆ i : Fin n, φ (Vi F n i) = ⊤ := by
  set U' : AddSubgroup U := ⨆ i : Fin n, φ (Vi F n i) with hU'
  have hR : ∀ (i j : Fin n) (hij : i ≠ j), Rij F i j ≤ stabU U U' := by
    have step : ∀ (i j : Fin n) (hij : i ≠ j), ∀ t ∈ Rij F i j, ∀ u ∈ U', t • u ∈ U' := by
      intro i j hij t ht u hu
      have h1 : t • u - u ∈ φ (Vi F n i) :=
        h.commU_le _ _ (isFlag_Vi_Vhat hij) (AddSubgroup.subset_closure ⟨t, ht, u, rfl⟩)
      have h2 : φ (Vi F n i) ≤ U' := le_iSup (fun i : Fin n => φ (Vi F n i)) i
      have h3 : t • u = u + (t • u - u) := by abel
      rw [h3]
      exact U'.add_mem hu (h2 h1)
    intro i j hij t ht u
    exact ⟨step i j hij t ht u, fun hu => by
      have := step i j hij t⁻¹ ((Rij F i j).inv_mem ht) _ hu
      rwa [inv_smul_smul] at this⟩
  have hL : ∀ (i j : Fin n) (hij : i ≠ j), Lij F i j ≤ stabU U U' := fun i j hij =>
    sup_le (hR i j hij) (hR j i hij.symm)
  have hall : Ladj F n ≤ stabU U U' := by
    refine iSup₂_le fun k hk => hL _ _ ?_
    simp [Fin.ext_iff]
  rw [Ladj_eq_top hn] at hall
  rw [eq_top_iff]
  have hz : (⟨0, by omega⟩ : Fin n) = ⟨0, by omega⟩ := rfl
  rw [← h.iSup_eq]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨g, rfl⟩ := exists_actSub_Vi_eq hn ⟨0, by omega⟩ hA
  rw [h.equivariant g _ (isPoint_Vi _)]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ U' := le_iSup (fun i : Fin n => φ (Vi F n i)) ⟨0, by omega⟩ hx
  exact (hall (Subgroup.mem_top g) x).1 hx'

end Hyp

end CFSG.Quasithin.G1
