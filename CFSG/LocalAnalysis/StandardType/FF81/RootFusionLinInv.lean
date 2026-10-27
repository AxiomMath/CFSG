module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinDefs
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSL

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

@[expose] noncomputable def jN (N r : ℕ) : GL (Fin N) (ZMod 2) :=
  Matrix.SpecialLinearGroup.toGL (CFSG.StandardType.ggInvSL N r (ZMod 2))

theorem toGL_bijective (n : ℕ) :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2)) := by
  constructor
  · intro A B h
    ext i j
    have := congrArg (fun g : GL (Fin n) (ZMod 2) => (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j) h
    simpa using this
  · intro g
    have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      have hu : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 2)).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      generalize (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = d at hu
      have h2 : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide
      exact h2 _ (isUnit_iff_ne_zero.mp hu)
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

theorem nonempty_mulEquiv_gl_of_sl {X : Type*} [Group X] {n : ℕ}
    (h : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    Nonempty (X ≃* GL (Fin n) (ZMod 2)) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.ofBijective _ (toGL_bijective n))⟩

theorem exists_isConj_jN (N : ℕ) (x : GL (Fin N) (ZMod 2)) (hx : orderOf x = 2) :
    ∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ N ∧ IsConj (jN N r) x := by
  obtain ⟨u, hu⟩ := (toGL_bijective N).2 x
  have hu2 : orderOf u = 2 := by
    have h := orderOf_injective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin N) (ZMod 2) →* GL (Fin N) (ZMod 2))
      (toGL_bijective N).1 u
    rw [hu] at h
    exact h.symm.trans hx
  obtain ⟨l, hl1, hl2, a, rfl⟩ := CFSG.StandardType.ggSLInvolutionClassInput (ZMod 2) N u hu2
  refine ⟨l, hl1, hl2, ?_⟩
  rw [isConj_iff]
  refine ⟨Matrix.SpecialLinearGroup.toGL a, ?_⟩
  rw [← hu]
  simp [jN]

private theorem inv_map_centralizer {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (e : G →* H) =
      Subgroup.centralizer ({e a} : Set H) := by
  apply le_antisymm
  · simpa [Set.image_singleton] using
      Subgroup.map_centralizer_le_centralizer_image {a} (e : G →* H)
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

theorem nonempty_mulEquiv_cent (N r : ℕ) (h : 2 * r ≤ N) :
    Nonempty (Cent r (N - 2 * r) ≃*
      Subgroup.centralizer ({jN N r} : Set (GL (Fin N) (ZMod 2)))) := by
  let e : BlkIdx r (N - 2 * r) ≃ Fin N :=
    (Equiv.sumComm (Fin r) (Fin (N - 2*r) ⊕ Fin r)).trans
      ((Equiv.sumCongr
          ((Equiv.sumComm (Fin (N - 2*r)) (Fin r)).trans
            finSumFinEquiv)
          (Equiv.refl (Fin r))).trans
        (finSumFinEquiv.trans (finCongr (by omega))))
  have h1 : ∀ i : Fin r, e (.inl i) = (⟨N - r + i.1, by omega⟩ : Fin N) := by
    intro i
    simp [e]
    ext; simp; omega
  have h2 : ∀ j : Fin (N - 2*r), e (.inr (.inl j)) = (⟨r + j.1, by omega⟩ : Fin N) := by
    intro j
    simp [e]
    ext; simp
  have h3 : ∀ i : Fin r, e (.inr (.inr i)) = (⟨i.1, by omega⟩ : Fin N) := by
    intro i
    simp [e]
    ext; simp
  have hmat : (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e)
      (jGL r (N - 2*r) : Matrix (BlkIdx r (N-2*r)) (BlkIdx r (N-2*r)) (ZMod 2)) =
      (jN N r : Matrix (Fin N) (Fin N) (ZMod 2)) := by
    ext a b
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases a' with i | i | i <;> rcases b' with j | j | j <;>
      simp only [jGL, uGL, uMat, blk, Matrix.of_apply, jN,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.StandardType.coe_ggInvSL,
        ggInvMatrix, ggInvNil_apply, Matrix.add_apply, Matrix.one_apply, h1, h2, h3]
    all_goals (split_ifs <;> simp_all <;> omega)
  let Φ : GL (BlkIdx r (N - 2*r)) (ZMod 2) ≃* GL (Fin N) (ZMod 2) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e)
  have hΦ : Φ (jGL r (N - 2*r)) = jN N r := by
    apply Units.ext
    simp only [Φ, Units.coe_mapEquiv]
    exact hmat
  have hcent : (Cent r (N - 2*r)).map (Φ : GL (BlkIdx r (N-2*r)) (ZMod 2) →*
        GL (Fin N) (ZMod 2)) =
      Subgroup.centralizer ({jN N r} : Set (GL (Fin N) (ZMod 2))) := by
    rw [show Cent r (N - 2*r) = Subgroup.centralizer {jGL r (N - 2*r)} from rfl]
    rw [inv_map_centralizer Φ (jGL r (N - 2*r)), hΦ]
  exact ⟨(Φ.subgroupMap (Cent r (N - 2*r))).trans (MulEquiv.subgroupCongr hcent)⟩

theorem nonempty_mulEquiv_centralizer_of_isConj {Γ : Type*} [Group Γ] {z z' : Γ}
    (h : IsConj z z') :
    Nonempty (Subgroup.centralizer ({z} : Set Γ) ≃* Subgroup.centralizer ({z'} : Set Γ)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have key : (Subgroup.centralizer ({z} : Set Γ)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({z'} : Set Γ) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
    constructor
    · intro hx
      rw [← hc]
      calc x * (c * z * c⁻¹) = c * (c⁻¹ * x * c * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * x * c)) * c⁻¹ := by rw [hx]
        _ = c * z * c⁻¹ * x := by group
    · intro hx
      rw [← hc] at hx
      calc c⁻¹ * x * c * z = c⁻¹ * (x * (c * z * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [hx]
        _ = z * (c⁻¹ * x * c) := by group
  exact ⟨((MulAut.conj c).subgroupMap (Subgroup.centralizer ({z} : Set Γ))).trans
    (MulEquiv.subgroupCongr key)⟩

theorem nonempty_mulEquiv_cent_of_isConj (N r : ℕ) (h : 2 * r ≤ N)
    {z : GL (Fin N) (ZMod 2)} (hz : IsConj (jN N r) z) :
    Nonempty (Cent r (N - 2 * r) ≃* Subgroup.centralizer ({z} : Set (GL (Fin N) (ZMod 2)))) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_cent N r h
  obtain ⟨e₂⟩ := nonempty_mulEquiv_centralizer_of_isConj hz
  exact ⟨e₁.trans e₂⟩

end CFSG.StandardType.FF81.RootFusionLin

end
