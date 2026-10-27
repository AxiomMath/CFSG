module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem exists_star_vectors {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ v w₁ w₂ w₃ : Fin (2 * m) → ZMod 2, v ≠ 0 ∧ b w₁ v = 1 ∧ b w₂ v = 1 ∧ b w₃ v = 1 ∧
      b w₁ w₂ = 0 ∧ b w₁ w₃ = 0 ∧ b w₂ w₃ = 0 ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ := by
  have hsymm := CFSG.Fischer.Classification.Recognition.SpU.Sp.b_symm halt
  obtain ⟨v, hv, -⟩ := CFSG.RankThree.SubgroupLists.SpFischer.exists_ne_zero_forall_eq_zero
    (b := b) (k := 0) (by omega) ![]
  obtain ⟨w₁, hw₁⟩ := CFSG.Fischer.Classification.Recognition.SpU.Sp.exists_b_eq_one halt hnd hv
  obtain ⟨x, hx0, hx⟩ := CFSG.RankThree.SubgroupLists.SpFischer.exists_ne_zero_forall_eq_zero
    (b := b) (by omega) ![v, w₁]
  obtain ⟨u, hu⟩ := CFSG.Fischer.Classification.Recognition.SpU.Sp.exists_b_eq_one halt hnd hx0
  obtain ⟨y, hy0, hy⟩ := CFSG.RankThree.SubgroupLists.SpFischer.exists_ne_zero_forall_eq_zero
    (b := b) (by omega) ![v, w₁, x, u]
  have hxv : b x v = 0 := by simpa using hx 0
  have hxw : b x w₁ = 0 := by simpa using hx 1
  have hyv : b y v = 0 := by simpa using hy 0
  have hyw : b y w₁ = 0 := by simpa using hy 1
  have hyx : b y x = 0 := by simpa using hy 2
  have hyu : b y u = 0 := by simpa using hy 3
  have hxy : x ≠ y := by
    rintro rfl
    rw [hsymm, hu] at hyu
    exact one_ne_zero hyu
  refine ⟨v, w₁, w₁ + x, w₁ + y, hv, hw₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hw₁, hxv]
  · simp [hw₁, hyv]
  · simp [halt w₁, hsymm w₁ x, hxw]
  · simp [halt w₁, hsymm w₁ y, hyw]
  · simp [halt w₁, hsymm w₁ y, hyw, hxw, hsymm x y, hyx]
  · exact fun h => hx0 (by simpa using h)
  · exact fun h => hy0 (by simpa using h)
  · exact fun h => hxy (add_left_cancel h)

private theorem orderOf_mul_eq_three {G : Type} [Group G] {a c : G} (ha : a * a = 1)
    (hc : c * c = 1) (h : orderOf (a * c) ∈ ({1, 2, 3} : Set ℕ)) (hnc : a * c ≠ c * a) :
    orderOf (a * c) = 3 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h
  · exfalso
    apply hnc
    have h1 : a * c = 1 := orderOf_eq_one_iff.mp h
    have hca : c = a := by
      calc c = a * a * c := by rw [ha, one_mul]
        _ = a * (a * c) := mul_assoc _ _ _
        _ = a := by rw [h1, mul_one]
    rw [hca]
  · exfalso
    apply hnc
    have e : a * c * (a * c) = 1 := by
      rw [← pow_two, ← h]
      exact pow_orderOf_eq_one _
    calc a * c = a * (a * c * (a * c)) * c := by rw [e, mul_one]
      _ = (a * a) * (c * a) * (c * c) := by simp only [mul_assoc]
      _ = c * a := by rw [ha, hc, one_mul, mul_one]
  · exact h

theorem hasCoreStar_of_spModel {G : Type} [Group G] {t : G} (hP : Pair G {x | IsConj t x})
    {m : ℕ} (hm : 3 ≤ m) {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    HasCoreStar G t := by
  obtain ⟨v, w₁, w₂, w₃, hv, h1, h2, h3, h12, h13, h23, n12, n13, n23⟩ :=
    exists_star_vectors hm halt hnd
  obtain ⟨φ, hφ⟩ := hmod
  have hsymm := CFSG.Fischer.Classification.Recognition.SpU.Sp.b_symm halt
  have hne0 : ∀ w, b w v = 1 → w ≠ 0 := fun w hw h => by simp [h] at hw
  let g : (Fin (2 * m) → ZMod 2) → G := fun w =>
    φ.symm ⟨CFSG.Fischer.Classification.sympTransvectionGL b halt w,
      CFSG.Fischer.Classification.sympTransvectionGL_mem_fischerMatrixGroup (b := b)
        (halt := halt) w⟩
  have hgD : ∀ w, w ≠ 0 → IsConj t (g w) := fun w hw => (hφ (g w)).mpr (by
    simpa [g] using CFSG.Fischer.Classification.sympTransvectionGL_mem_fischerTransvections
      (b := b) (halt := halt) hw)
  have hgcomm : ∀ w w', b w w' = 0 → g w * g w' = g w' * g w := fun w w' h => by
    simp only [g, ← map_mul]
    congr 1
    exact Subtype.ext
      (CFSG.RankThree.SubgroupLists.SpFischer.sympTransvectionGL_commute halt h)
  have hgne : ∀ w w', w ≠ 0 → w ≠ w' → g w ≠ g w' := fun w w' hw hww' h => by
    have h' := congrArg Subtype.val (φ.symm.injective h)
    exact hww' (CFSG.RankThree.SubgroupLists.SpFischer.eq_of_sympTransvectionGL_eq halt hnd hw h')
  have hgnc : ∀ w, b w v = 1 → g v * g w ≠ g w * g v := fun w hw h => by
    have h' : CFSG.Fischer.Classification.sympTransvectionGL b halt v *
        CFSG.Fischer.Classification.sympTransvectionGL b halt w =
        CFSG.Fischer.Classification.sympTransvectionGL b halt w *
        CFSG.Fischer.Classification.sympTransvectionGL b halt v := by
      have := congrArg (fun z => ((φ z : ↥(fischerMatrixGroup fun A =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)) : GL (Fin (2 * m)) (ZMod 2))) h
      simpa [g] using this
    have e := congrArg (fun z : GL (Fin (2 * m)) (ZMod 2) =>
      (z : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2)) *ᵥ v) h'
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec,
      CFSG.Fischer.Classification.sympTransvectionGL_mulVec] at e
    simp only [map_add, LinearMap.add_apply, halt v, hw, hsymm v w, zero_smul, add_zero,
      one_smul, zero_add] at e
    exact hv (by simpa using e)
  have hinv : ∀ w, w ≠ 0 → g w * g w = 1 := fun w hw => by
    rw [← pow_two, ← hP.2.2.1 (g w) (hgD w hw), pow_orderOf_eq_one]
  have hord : ∀ w, b w v = 1 → orderOf (g v * g w) = 3 := fun w hw =>
    orderOf_mul_eq_three (hinv v hv) (hinv w (hne0 w hw))
      (hP.2.2.2.1 (g v) (hgD v hv) (g w) (hgD w (hne0 w hw))) (hgnc w hw)
  exact hasCoreStar_of_center (hgD v hv) (hgD w₁ (hne0 w₁ h1)) (hgD w₂ (hne0 w₂ h2))
    (hgD w₃ (hne0 w₃ h3)) (hord w₁ h1) (hord w₂ h2) (hord w₃ h3) (hgcomm w₁ w₂ h12)
    (hgcomm w₁ w₃ h13) (hgcomm w₂ w₃ h23) (hgne w₁ w₂ (hne0 w₁ h1) n12)
    (hgne w₁ w₃ (hne0 w₁ h1) n13) (hgne w₂ w₃ (hne0 w₂ h2) n23)

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
