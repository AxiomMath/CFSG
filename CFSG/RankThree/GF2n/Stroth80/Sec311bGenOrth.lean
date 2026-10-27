module

public import CFSG.RankThree.GF2n.Stroth80.Sec310RootAux

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_gen_orth (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ r ∈ Rt M (LB M Q B) t,
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) := by
  classical
  obtain ⟨u, hQu, hu0, -, -, hL⟩ :=
    hc.omega_points_flag h34 hs hnotQB hK E hQ h3 hX φ hφ hker ψ hψ
  obtain ⟨P, hPe⟩ := exists_hypPair hQ hQu hu0
  have hPf0 : P.f ≠ 0 := fun h0 => by
    have := P.polar_ef
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  obtain ⟨w, hw, hQw⟩ := exists_perp_vector_map_ne_zero hQ h3 hPf0
  have hw' : polar Q' P.f w = 0 := hw
  set g : Gom Q' := eichlerG Q' P.f w with hg
  set A : X := E.equiv.symm g with hA
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = (A : GL ι K) := by
    have : (A : GL ι K) ∈ φ.range := by rw [hφ]; exact A.2
    exact MonoidHom.mem_range.mp this
  have hrv : (φ r : Matrix ι ι K) *ᵥ u = eichler Q' P.f w u := by
    have h1 := E.app A u
    rw [hA, MulEquiv.apply_symm_apply] at h1
    rw [hr]
    exact h1.symm
  have hne : polar Q' u ((φ r : Matrix ι ι K) *ᵥ u) ≠ 0 := by
    rw [hrv, ← hPe, polar_eichler_apply_left P.Q_e P.Q_f hw', P.polar_ef]
    simpa using hQw
  have hrX : (φ r : GL ι K) ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hQu' : Q' ((φ r : Matrix ι ι K) *ᵥ u) = 0 := by rw [E.quad_mulVec hrX]; exact hQu
  have hL2 : ((conjSubgroup (r : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL ((φ r : Matrix ι ι K) *ᵥ u) := by
    refine map_conjSubgroup_subgroupOf (e := E.equiv) φ hφ r (S := Lom Q' u)
      (S' := Lom Q' ((φ r : Matrix ι ι K) *ᵥ u)) (fun h' => ?_) hL
    have := mem_Lom_app_iff (E.equiv ⟨φ r, hrX⟩) u h'
    rwa [E.app ⟨φ r, hrX⟩ u] at this
  rw [← hc.LB_conj (hc.Rt_le_M t r.2)] at hL2
  exact ⟨r, r.2, le_sup_secOmega E hQ φ hφ hker hQu hQu' hne hL hL2⟩

end CFSG.RankThree.GF2n.Stroth80
