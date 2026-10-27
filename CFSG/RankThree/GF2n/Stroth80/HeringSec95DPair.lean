module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DGeo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem smul_mem_img_conj95 {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {z : G}
    (hzM : z ∈ M) {S : Subgroup G} (hSQ : S ≤ Q)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img S → c • e ∈ M₀.img S) (c : K) {e : M₀.E}
    (he : e ∈ M₀.img (conjSubgroup z S)) : c • e ∈ M₀.img (conjSubgroup z S) := by
  classical
  obtain ⟨φ, hφπ, -, -, hφsemi⟩ := exists_actionHom_M hc.hyp h
  obtain ⟨σ, hσ⟩ := hφsemi ⟨z, hzM⟩
  obtain ⟨a, haS, haQ, rfl⟩ := he
  have hv : z⁻¹ * a * z ∈ S := mem_conjSubgroup.mp haS
  have hvQ : z⁻¹ * a * z ∈ Q := hSQ hv
  have hπa : M₀.π a = φ ⟨z, hzM⟩ (M₀.π (z⁻¹ * a * z)) := by
    rw [← hφπ ⟨z, hzM⟩ _ hvQ]
    congr 1
    group
  have h1 : M₀.π (z⁻¹ * a * z) ∈ M₀.img S := M₀.pi_mem_img hv hvQ
  obtain ⟨v', hv'S, hv'Q, hv'⟩ := hS (σ.symm c) _ h1
  refine ⟨z * v' * z⁻¹, ?_, ?_, ?_⟩
  · rw [mem_conjSubgroup]
    have e : z⁻¹ * (z * v' * z⁻¹) * z = v' := by group
    rw [e]
    exact hv'S
  · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hzM) v').mp hv'Q
  · rw [hφπ ⟨z, hzM⟩ v' hv'Q, hv', hπa, hσ, RingEquiv.apply_symm_apply]

section Pair

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.polar_conj_eq_zero95 (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {z c : G}
    (hcR : c ∈ Rt M (LB M Q B) t)
    (hBV : B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t))
    (hCV : ∀ a ∈ conjSubgroup c B,
      a ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t))
    (hsing : ∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      IsSingV M Q Z B t u) :
    polar (quadPlus 2 K) C.u
      ((C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u) = 0 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨b₀, hb₀B, hb₀u⟩ := (C.hBiff C.u).mpr ⟨1, (one_smul K C.u).symm⟩
  have hcb₀V : c * (b₀ : G) * c⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hcR) b₀).mp b₀.2
  set v₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨c * (b₀ : G) * c⁻¹, hcb₀V⟩ with hv₂
  have hv₂vec : secVec C.ψ v₂ =
      (C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u := by
    rw [← hb₀u]
    exact C.hψ ⟨c, hcR⟩ b₀ v₂ rfl
  have hv₂D : (v₂ : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    hCV _ (conj_mem95 c hb₀B)
  have hv₁D : (b₀ : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    hBV hb₀B
  have hprod : (b₀ : G) * (v₂ : G) ∈
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    Subgroup.mul_mem _ hv₁D hv₂D
  have hsum : secVec C.ψ (b₀ * v₂) =
      C.u + (C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u := by
    rw [secVec_mul, hb₀u, hv₂vec]
  have h0 := C.quad_secVec_eq_zero_of_isSingV hs ((Vt M (LB M Q B) B Z t).mul_mem b₀.2 v₂.2)
    (hsing _ hprod)
  have hq2 := C.quad_secVec_eq_zero_of_isSingV hs hcb₀V (hsing _ hv₂D)
  have h0' : quadPlus 2 K (C.u +
      (C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u) = 0 := by
    rw [← hsum]
    exact h0
  have hq2' : quadPlus 2 K
      ((C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u) = 0 := by
    rw [← hv₂vec]
    exact hq2
  have h2 := QuadraticMap.map_add (quadPlus 2 K) C.u
    ((C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u)
  rw [h0', C.hQu, hq2'] at h2
  linear_combination -h2

theorem Coord95.mem_QB_of_pair95 (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {c : G}
    (hcR : c ∈ Rt M (LB M Q B) t)
    (hpol : polar (quadPlus 2 K) C.u
      ((C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ C.u) = 0) :
    (∀ b ∈ B, b ∈ QB (conjSubgroup c B)) ∧ ∀ b ∈ B, c * b * c⁻¹ ∈ QB B := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  constructor
  · intro b hb
    have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
    rw [C.mem_QB_conj_iff hs hcR hbV]
    obtain ⟨s, hs'⟩ := (C.hBiff (secVec C.ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
    rw [hs', polar_smul_right_eq, polar_comm, hpol, mul_zero]
  · intro b hb
    have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
    have hcbV : c * b * c⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hcR) b).mp hbV
    have h1R : (1 : G) ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).one_mem
    have key := C.mem_QB_conj_iff hs h1R hcbV
    rw [conjSubgroup_one] at key
    rw [key]
    have hvec : secVec C.ψ ⟨c * b * c⁻¹, hcbV⟩ =
        (C.φ ⟨c, hcR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨b, hbV⟩ :=
      C.hψ ⟨c, hcR⟩ ⟨b, hbV⟩ _ rfl
    obtain ⟨s, hs'⟩ := (C.hBiff (secVec C.ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
    have hφ1 : C.φ ⟨1, h1R⟩ = 1 := by
      have : (⟨1, h1R⟩ : ↥(Rt M (LB M Q B) t)) = 1 := rfl
      rw [this, map_one]
    rw [hvec, hs', Matrix.mulVec_smul, hφ1]
    simp only [Units.val_one, Matrix.one_mulVec]
    rw [polar_smul_right_eq, hpol, mul_zero]

end Pair

end HS9

end CFSG.RankThree.GF2n.Stroth80
