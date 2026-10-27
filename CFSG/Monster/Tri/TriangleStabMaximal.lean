module

public import CFSG.Monster.Existence.TwoPoint.FourDGen
public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Monster.Existence.Compat.Triangles
public import CFSG.YGroups.Y443.Native.AlignConj
public import CFSG.Monster.Tri.CoverFactsGBase
public import CFSG.Monster.B.GSide.NativeCompletion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.TriStab

open CFSG.Monster.Tri.CoverG

theorem map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (d : G) :
    (Subgroup.centralizer {d}).map e.toMonoidHom = Subgroup.centralizer {e d} := by
  ext w
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem triMax_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {x y z : G}
    (h : TriMax x y z) : TriMax (e x) (e y) (e z) := by
  intro F hPF hFE
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hc : ∀ d : G, Subgroup.centralizer {e d} = (Subgroup.centralizer {d}).map e.toMonoidHom :=
    fun d => (map_centralizer_mulEquiv e d).symm
  have hF : F = (F.comap e.toMonoidHom).map e.toMonoidHom :=
    (Subgroup.map_comap_eq_self_of_surjective e.surjective F).symm
  have hE : Subgroup.centralizer {e x} ⊓ Subgroup.centralizer {e y} =
      (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}).map e.toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, ← hc, ← hc]
  have hP : Subgroup.centralizer {e x} ⊓ Subgroup.centralizer {e y} ⊓
      Subgroup.centralizer {e z} = (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y} ⊓
        Subgroup.centralizer {z}).map e.toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, ← hc, ← hc, ← hc]
  rw [hP, hF, Subgroup.map_le_map_iff_of_injective hinj] at hPF
  rw [hE, hF, Subgroup.map_le_map_iff_of_injective hinj] at hFE
  rw [hP, hE, hF]
  rcases h _ hPF hFE with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])

end CFSG.Monster.Tri.TriStab

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Monster.GMS CFSG.Monster.B.GSide
  CFSG.Monster.Tri CFSG.Monster.Tri.CoverG

theorem triMax_standard
    (hG : Gmat = AutO) :
    ∃ γ : MGriess, FourDGammaData hG cw0 γ ∧ TriMax tGriess uGriess γ := by
  have hC := centralizerInput_B
  obtain ⟨ρ, iv, hρ⟩ := exists_fourD_localMap
  let z : cgraph.neighborSet cv0 := ⟨cw0, cgraph_adj_cv0_cw0⟩
  obtain ⟨γ, hγ⟩ := exists_fourD_gammaData hG cgraph_adj_cv0_cw0
  refine ⟨γ, hγ, ?_⟩
  have hp : (iv z : stdGroup) ∈ rootClass := (iv z).2
  refine triMax_of_map_maximal _ _ _ (fdEdgeRho hG hC ρ) (fd_ker_fdEdgeRho_le hG hC hρ z hγ) ?_
  intro B hlt hB
  rw [fd_map_cent_gamma_eq hG hC hρ z hγ] at hlt
  rw [fdEdgeRho_range hG hC hρ] at hB ⊢
  exact fd_eq_Ginl_of_lt_map_inl hp hlt hB

end CFSG.Monster.Existence

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.Existence
  CFSG.Monster.GMS CFSG.Monster.Tri CFSG.Monster.Tri.CoverG CFSG.Monster.B.Short CFSG.Monster.B.GSide

@[expose] noncomputable def griessEquivGmat (hG : Gmat = AutO) : MGriess ≃* Gmat :=
  (MulEquiv.subgroupCongr hG).symm.trans (MulAut.conj Omega⁻¹)

theorem griessEquivGmat_tGriess
    (hG : Gmat = AutO) : griessEquivGmat hG tGriess = fM y443C := by
  apply Subtype.ext
  show ((Omega⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * tStar *
      ((Omega⁻¹⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)
  rw [inv_inv, ← omega_conj]
  simp only [Subgroup.coe_inv, coe_Omega]
  group

theorem exists_longTri_triMax
    (hG : Gmat = AutO) :
    ∃ x y z : ConjVert (fM y443C), longTri (fM y443C) x y z ∧
      TriMax (x : Gmat) (y : Gmat) (z : Gmat) := by
  obtain ⟨γ, hγ, hmax⟩ := triMax_standard hG
  set e := griessEquivGmat hG with he
  have het : e tGriess = fM y443C := griessEquivGmat_tGriess hG
  have hconj : ∀ {g : MGriess}, IsConj tGriess g → IsConj (fM y443C) (e g) := fun h => by
    rw [← het]
    exact e.toMonoidHom.map_isConj h
  have hu := uGriess_mem_twoANbr
  have htγ : tGriess * γ = γ * tGriess :=
    (Subgroup.mem_centralizer_singleton_iff.1 hγ.mem_cent).symm
  have hlong := isLongTriangle_of_fourD_gammaData hG cgraph_adj_cv0_cw0 hγ
  have hγtu : γ ≠ tGriess * uGriess :=
    ((Compat.isLongTriangle_iff orderOf_tGriess (IsConj.refl _) hu.1 hu.2).1 hlong).2
  have hγt : γ ≠ tGriess := by
    rintro rfl
    apply hγ.not_isConj_ut
    rw [mul_assoc, tGriess_mul_self, mul_one]
    exact hu.1
  have hγu : γ ≠ uGriess := by
    rintro rfl
    apply hγ.not_isConj_ut
    rw [uGriess_mul_self, one_mul]
  let x : ConjVert (fM y443C) := baseVertex (fM y443C)
  let y : ConjVert (fM y443C) := ⟨e uGriess, hconj hu.1⟩
  let z : ConjVert (fM y443C) := ⟨e γ, hconj hγ.isConj⟩
  have hx : (x : Gmat) = e tGriess := het.symm
  refine ⟨x, y, z, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro h
    exact uGriess_ne_tGriess (e.injective (by rw [← hx]; exact (congrArg Subtype.val h).symm))
  · show IsConj (fM y443C) ((x : Gmat) * e uGriess)
    rw [hx, ← map_mul]
    exact hconj hu.2
  · intro h
    exact hγu (e.injective (congrArg Subtype.val h).symm)
  · show IsConj (fM y443C) (e uGriess * e γ)
    rw [← map_mul]
    exact hconj hγ.isConj_u
  · intro h
    exact hγt (e.injective (by rw [← hx]; exact congrArg Subtype.val h))
  · show IsConj (fM y443C) (e γ * (x : Gmat))
    rw [hx, ← map_mul, ← htγ]
    exact hconj hγ.isConj_t
  · show e γ ≠ (x : Gmat) * e uGriess
    rw [hx, ← map_mul]
    exact fun h => hγtu (e.injective h)
  · show TriMax (x : Gmat) (e uGriess) (e γ)
    rw [hx]
    exact TriStab.triMax_map_mulEquiv e hmax

end CFSG.YGroups.Y443
