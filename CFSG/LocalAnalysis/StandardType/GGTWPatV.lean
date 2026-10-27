module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTWPat1
public import CFSG.LocalAnalysis.StandardType.GGTWPat2
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTW_pat1_V {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {pos : GGTWPos} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type}
    [Fintype Λa] [DecidableEq Λa] {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV : V}
    (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 1)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) :
    ∃ (a : Λa) (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n ∧
      (∀ c : Fin (N - 1), ggTWInJ N pos c.val →
        α (Sum.inr a) (h (Sum.inl (e c))) = (if c = c0 then (m : ZMod p) else 0) ∧
          α (Sum.inl (e c)) (h (Sum.inr a)) = (if c = c0 then (n : ZMod p) else 0)) ∧
      α (Sum.inr a) (h (Sum.inr a)) = 2 := by
  classical
  haveI : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨a⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
  let eJ : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ≃ {c : Fin (N - 1) // ggTWInJ N pos c.val} :=
    { toFun := fun i => ⟨e.symm i.1, (hJpos (e.symm i.1)).2 (by
          rw [Equiv.apply_symm_apply]; exact i.2)⟩
      invFun := fun c => ⟨e c.1, (hJpos c.1).1 c.2⟩
      left_inv := by intro i; ext; simp
      right_inv := by intro c; ext; simp }
  let F : ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ≃
      Option {c : Fin (N - 1) // ggTWInJ N pos c.val} :=
    { toFun := fun o => match o with
        | Sum.inl i => some (eJ i)
        | Sum.inr _ => none
      invFun := fun o => match o with
        | some c => Sum.inl (eJ.symm c)
        | none => Sum.inr a
      left_inv := by
        rintro (i | x)
        · show Sum.inl (eJ.symm (eJ i)) = Sum.inl i
          rw [Equiv.symm_apply_apply]
        · show Sum.inr a = Sum.inr x
          rw [Subsingleton.elim a x]
      right_inv := by
        rintro (_ | c)
        · rfl
        · show some (eJ (eJ.symm c)) = some c
          rw [Equiv.apply_symm_apply] }
  let MK' : CoxeterMatrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) := MK.reindex F
  let CK' : Matrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})
      (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) ℤ := Matrix.reindex F F CK
  have hWMK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK F
  have hCK' : GGIntCartan MK' CK' := GGIntCartan.reindex F hCK
  have hsomeF : ∀ c : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      F.symm (some c) = Sum.inl (eJ.symm c) := fun c => rfl
  have hnoneF : F.symm none = Sum.inr a := rfl
  have hJ' : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      (CK' (some i) (some j) : ZMod p) = (CartanMatrix.A (N - 1) i.1 j.1 : ZMod p) := by
    intro i j
    have hpk := hpairK (Sum.inl (eJ.symm i)) (Sum.inl (eJ.symm j))
    simp only [Sum.map_inl, id_eq] at hpk
    have h3 : (eJ.symm i).1 = e i.1 := rfl
    have h4 : (eJ.symm j).1 = e j.1 := rfl
    rw [show CK' (some i) (some j) = CK (F.symm (some i)) (F.symm (some j)) by
      simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply]]
    rw [hsomeF i, hsomeF j, ← hpk, h3, h4]
    exact hF.pair i.1 j.1
  obtain ⟨c0, m, n, hpat, hbonds⟩ :=
    ggTW_pattern1_rows (p := p) (N := N) hp hN pos hWMK' hCK' hJ'
  refine ⟨a, c0, m, n, hpat, ?_, ?_⟩
  · intro c hc
    have hb := hbonds ⟨c, hc⟩
    have hval : (eJ.symm ⟨c, hc⟩).1 = e c := rfl
    constructor
    · have hpk := hpairK (Sum.inr a) (Sum.inl (eJ.symm ⟨c, hc⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' none (some ⟨c, hc⟩) = CK (Sum.inr a) (Sum.inl (eJ.symm ⟨c, hc⟩)) := by
        simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply, hnoneF, hsomeF]
      rw [hpk, ← hck, hb.1]
      split_ifs <;> simp
    · have hpk := hpairK (Sum.inl (eJ.symm ⟨c, hc⟩)) (Sum.inr a)
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' (some ⟨c, hc⟩) none = CK (Sum.inl (eJ.symm ⟨c, hc⟩)) (Sum.inr a) := by
        simp only [CK', Matrix.reindex_apply, Matrix.submatrix_apply, hnoneF, hsomeF]
      rw [hpk, ← hck, hb.2]
      split_ifs <;> simp
  · have hpk := hpairK (Sum.inr a) (Sum.inr a)
    simp only [Sum.map_inr, id_eq] at hpk
    rw [hpk, hCK.1]
    norm_num

theorem ggTW_pat2_V {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) {pos : GGTWPos} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type}
    [Fintype Λa] [DecidableEq Λa] {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    {e : Fin (N - 1) ≃ Λ} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V} {xV : V}
    (hb : b₁ ≠ b₂) (hcard : Nat.card Λa = 2)
    (hJpos : ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂))
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hA2 : ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex eK)
    (hF : GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV)
    (hpairK : ∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) :
    ∃ (a₁ a₂ : Λa) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))), a₁ ≠ a₂ ∧
      GGTWPat2 N pos c.val (c₂.map Fin.val) ∧
      (∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
        α (Sum.inr a₁) (h (Sum.inl (e c'))) = (if c' = c then -1 else 0) ∧
          α (Sum.inl (e c')) (h (Sum.inr a₁)) = (if c' = c then -1 else 0) ∧
          α (Sum.inr a₂) (h (Sum.inl (e c'))) = (if some c' = c₂ then -1 else 0) ∧
          α (Sum.inl (e c')) (h (Sum.inr a₂)) = (if some c' = c₂ then -1 else 0)) ∧
      α (Sum.inr a₁) (h (Sum.inr a₂)) = (if c₂ = none then -1 else 0) ∧
      α (Sum.inr a₂) (h (Sum.inr a₁)) = (if c₂ = none then -1 else 0) ∧
      α (Sum.inr a₁) (h (Sum.inr a₁)) = 2 ∧ α (Sum.inr a₂) (h (Sum.inr a₂)) = 2 := by
  classical
  have hN5 : 5 ≤ N := by omega
  obtain ⟨eK, heK⟩ := hA2
  let eJ : {c : Fin (N - 1) // ggTWInJ N pos c.val} ≃ {i : Λ // i ≠ b₁ ∧ i ≠ b₂} :=
    { toFun := fun c => ⟨e c.1, (hJpos c.1).1 c.2⟩
      invFun := fun i => ⟨e.symm i.1, (hJpos (e.symm i.1)).2 (by simpa using i.2)⟩
      left_inv := by intro c; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }
  let ee : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ≃
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) := Equiv.sumCongr eJ (Equiv.refl Λa)
  let MK' : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) :=
    MK.reindex ee.symm
  let CK' : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ := CK.submatrix ee ee
  have hMK' : MK' = (CoxeterMatrix.A (N - 1)).reindex (eK.trans ee.symm) := by
    show MK.reindex ee.symm = _
    rw [heK]
    exact l05nBL_reindex_trans (CoxeterMatrix.A (N - 1)) eK ee.symm
  have hWK' : GGIsWeylMatrix MK' := l05nDP4_weyl_reindex hWMK ee.symm
  have hCK' : GGIntCartan MK' CK' := by
    have h := GGIntCartan.reindex (e := ee.symm) hCK
    simpa [CK', MK', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] using h
  have hcast : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      ((CK' (Sum.inl i) (Sum.inl j) : ℤ) : ZMod p) =
        ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
    intro i j
    have h1 := hpairK (Sum.inl (eJ i)) (Sum.inl (eJ j))
    simp only [Sum.map_inl, id_eq] at h1
    have h2 := hF.pair i.1 j.1
    have hval : CK' (Sum.inl i) (Sum.inl j) = CK (Sum.inl (eJ i)) (Sum.inl (eJ j)) := by
      simp [CK', ee, Matrix.submatrix_apply]
    rw [hval, ← h1]
    rw [show (eJ i).1 = e i.1 from rfl, show (eJ j).1 = e j.1 from rfl]
    exact h2
  have hJ' : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK' (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hCK'.1 (Sum.inl i)]
      simp [CartanMatrix.A]
    · have hne : Sum.inl i ≠
          (Sum.inl j : ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)) :=
        fun h => hij (by injection h)
      have hpair : (CK' (Sum.inl i) (Sum.inl j) = 0 ∧ CK' (Sum.inl j) (Sum.inl i) = 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) = -1 ∧ CK' (Sum.inl j) (Sum.inl i) = -1) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 2 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) ∨
          (CK' (Sum.inl i) (Sum.inl j) * CK' (Sum.inl j) (Sum.inl i) = 3 ∧
            CK' (Sum.inl i) (Sum.inl j) < 0 ∧ CK' (Sum.inl j) (Sum.inl i) < 0) := by
        rcases hCK'.2 (Sum.inl i) (Sum.inl j) hne with
          ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hb : CartanMatrix.A (N - 1) i.1 j.1 = 0 ∨
          CartanMatrix.A (N - 1) i.1 j.1 = -1 := by
        rcases l05nDP4_cartanA_mem (N - 1) i.1 j.1 with h2 | hm1 | h0
        · exact absurd (l05nDP4_cartanA_eq_two h2) hij'
        · exact Or.inr hm1
        · exact Or.inl h0
      have h1c := hcast i j
      have h2c : ((CK' (Sum.inl j) (Sum.inl i) : ℤ) : ZMod p) =
          ((CartanMatrix.A (N - 1) i.1 j.1 : ℤ) : ZMod p) := by
        rw [hcast j i, CFSG.ClassicalInvolution.ModelFacts.cartanA_symm (N - 1) j.1 i.1]
      exact (ggTW_cast_cartan_pair hp hpair hb h1c h2c).1
  obtain ⟨a₁, a₂, c, c₂, ha12, hpat2, hpair2, hp12, hp21, hp11, hp22⟩ :=
    ggTW_pattern2 hN5 pos hcard hWK' hCK' ⟨eK.trans ee.symm, hMK'⟩ hJ'
  refine ⟨a₁, a₂, c, c₂, ha12, hpat2, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    have hb := hpair2 ⟨c', hc'⟩
    have hval : (eJ ⟨c', hc'⟩).1 = e c' := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hpk := hpairK (Sum.inr a₁) (Sum.inl (eJ ⟨c', hc'⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' (Sum.inr a₁) (Sum.inl ⟨c', hc'⟩) =
          CK (Sum.inr a₁) (Sum.inl (eJ ⟨c', hc'⟩)) := by
        simp [CK', ee, Matrix.submatrix_apply]
      rw [hpk, ← hck, hb.1]
      split_ifs <;> simp
    · have hpk := hpairK (Sum.inl (eJ ⟨c', hc'⟩)) (Sum.inr a₁)
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₁) =
          CK (Sum.inl (eJ ⟨c', hc'⟩)) (Sum.inr a₁) := by
        simp [CK', ee, Matrix.submatrix_apply]
      rw [hpk, ← hck, hb.2.1]
      split_ifs <;> simp
    · have hpk := hpairK (Sum.inr a₂) (Sum.inl (eJ ⟨c', hc'⟩))
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' (Sum.inr a₂) (Sum.inl ⟨c', hc'⟩) =
          CK (Sum.inr a₂) (Sum.inl (eJ ⟨c', hc'⟩)) := by
        simp [CK', ee, Matrix.submatrix_apply]
      rw [hpk, ← hck, hb.2.2.1]
      split_ifs <;> simp
    · have hpk := hpairK (Sum.inl (eJ ⟨c', hc'⟩)) (Sum.inr a₂)
      simp only [Sum.map_inr, Sum.map_inl, id_eq, hval] at hpk
      have hck : CK' (Sum.inl ⟨c', hc'⟩) (Sum.inr a₂) =
          CK (Sum.inl (eJ ⟨c', hc'⟩)) (Sum.inr a₂) := by
        simp [CK', ee, Matrix.submatrix_apply]
      rw [hpk, ← hck, hb.2.2.2]
      split_ifs <;> simp
  · have hpk := hpairK (Sum.inr a₁) (Sum.inr a₂)
    simp only [Sum.map_inr, id_eq] at hpk
    have hck : CK' (Sum.inr a₁) (Sum.inr a₂) = CK (Sum.inr a₁) (Sum.inr a₂) := by
      simp [CK', ee, Matrix.submatrix_apply]
    rw [hpk, ← hck, hp12]
    split_ifs <;> simp
  · have hpk := hpairK (Sum.inr a₂) (Sum.inr a₁)
    simp only [Sum.map_inr, id_eq] at hpk
    have hck : CK' (Sum.inr a₂) (Sum.inr a₁) = CK (Sum.inr a₂) (Sum.inr a₁) := by
      simp [CK', ee, Matrix.submatrix_apply]
    rw [hpk, ← hck, hp21]
    split_ifs <;> simp
  · have hpk := hpairK (Sum.inr a₁) (Sum.inr a₁)
    simp only [Sum.map_inr, id_eq] at hpk
    rw [hpk, hCK.1]
    norm_num
  · have hpk := hpairK (Sum.inr a₂) (Sum.inr a₂)
    simp only [Sum.map_inr, id_eq] at hpk
    rw [hpk, hCK.1]
    norm_num

end CFSG.StandardType

end
