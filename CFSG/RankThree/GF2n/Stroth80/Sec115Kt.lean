module

public import CFSG.RankThree.GF2n.Stroth80.Sec114
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
import CFSG.RankThree.GF2n.Stroth80.Sec117U3Line
import CFSG.LinearAlgebra.FinTwoMatrixCharTwo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem sq_mem_map_ker_of_pow_two_pow_eq_one {Γ : Type*} [Group Γ] {K : Type*} [Field K]
    [CharP K 2] {S : Subgroup Γ} (f : ↥S →* Matrix.GeneralLinearGroup (Fin 2) K) {x : Γ}
    (hx : x ∈ S) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x ^ 2 ∈ f.ker.map S.subtype := by
  have h1 : (⟨x, hx⟩ : ↥S) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
  have h2 : ((f ⟨x, hx⟩ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) ^ 2 ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  have h3 := CFSG.LinearAlgebra.fin_two_sq_eq_one_of_pow_two_pow_eq_one h2
  refine ⟨⟨x, hx⟩ ^ 2, MonoidHom.mem_ker.mpr ?_, by simp⟩
  rw [map_pow]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, h3, Units.val_one])

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

section Model

variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

theorem liftF_mem_range_sub_one_of_commute (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {c t : Mbar M Q} (hcH : c ∈ bar M Q (H0 M Z)) (htH : t ∈ bar M Q (H0 M Z))
    (hct : c * t = t * c) {T : M₀.E ≃ₗ[K] M₀.E} (hT : liftF φ t = T) {w : M₀.E}
    (hw : w ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :
    liftF φ c w ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  subst hT
  obtain ⟨v, rfl⟩ := hw
  have e1 := liftF_mul hφ (mem_bar_H0_iff.mp hcH) (mem_bar_H0_iff.mp htH)
  have e2 := liftF_mul hφ (mem_bar_H0_iff.mp htH) (mem_bar_H0_iff.mp hcH)
  rw [hct, e2] at e1
  refine ⟨liftF φ c v, ?_⟩
  have e3 := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f v) e1
  simp only [LinearEquiv.mul_apply] at e3
  simp [LinearMap.sub_apply, e3]

private theorem Ctx.mem_normalizer_bar_LB_of_liftF_fix (hc : Ctx M Q Z B) [Finite K]
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {k : Mbar M Q}
    (hk : k ∈ bar M Q (H0 M Z)) (hkb : liftF φ k b = b) :
    k ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hk
  have hm' : (m : G) ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hm
  have h1 : φ ⟨m, hm'⟩ b = (1 : K) • b := by
    rw [one_smul, ← liftF_mkH hφker ⟨m, hm'⟩]
    exact hkb
  exact hc.mk_mem_normalizer_bar_LB_of_fix_line hB m.2
    (T := (φ ⟨m, hm'⟩ : M₀.E →ₗ[K] M₀.E)) (hφπ ⟨m, hm'⟩) (μ := 1) h1

theorem Ctx.exists_normal_normalizer_LB_of_model (hc : Ctx M Q Z B) [Finite K] [CharP K 2]
    (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (m : H0 M Z) (y : G), y ∈ Q → M₀.π ((m : G) * y * (m : G)⁻¹) = φ m (M₀.π y))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) :
    ∃ N : Subgroup (Mbar M Q),
      N ≤ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)) ∧
      (∀ c ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          ∀ k ∈ N, c * k * c⁻¹ ∈ N) ∧
      (∀ x ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ N) ∧
      N ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  set t : Mbar M Q := QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) with ht
  set C := Xbar M Q Z B ⊓ Subgroup.centralizer ({t} : Set (Mbar M Q)) with hC
  have hCH : C ≤ bar M Q (H0 M Z) := fun y hy => hc.Xbar_le_bar_H0 hy.1
  have htH : t ∈ bar M Q (H0 M Z) := mem_bar_H0_iff.mpr ⟨⟨a, hc.LB_le_H0 ha⟩, rfl⟩
  have htF : liftF φ t = φ ⟨a, hc.LB_le_H0 ha⟩ := liftF_mkH hφker ⟨a, hc.LB_le_H0 ha⟩
  obtain ⟨b, -, -, hB, hcent, -⟩ := hc.dictB hD
  have hbW := hc.mem_range_act_sub_one_of_mem_LB hD hφπ hφker hφiso hB hcent ha hA.2.1
  have hK : 1 < Nat.card K := by
    rw [hD.card]
    have := hc.hyp.q4
    omega
  have hW2 := ((isA2_iff M₀ hD.reg hD.card hK (φ ⟨a, hc.LB_le_H0 ha⟩)
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ha)).1 (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ha)).2
    (fun x hx => hφπ ⟨a, hc.LB_le_H0 ha⟩ x hx)).mp hA).2.2.1
  let ρ : ↥C →* (M₀.E ≃ₗ[K] M₀.E) :=
    { toFun := fun y => liftF φ (y : Mbar M Q)
      map_one' := liftF_one hφker
      map_mul' := fun y y' => liftF_mul hφker (mem_bar_H0_iff.mp (hCH y.2))
        (mem_bar_H0_iff.mp (hCH y'.2)) }
  obtain ⟨f, hf⟩ := exists_hom_GL_two_of_stable ρ _ hW2 fun y w hw =>
    liftF_mem_range_sub_one_of_commute hφker (hCH y.2) htH
      (Subgroup.mem_centralizer_singleton_iff.mp y.2.2) htF hw
  refine ⟨f.ker.map C.subtype, Subgroup.map_subtype_le _, fun c hcC k hk => ?_,
    fun x hx ⟨k, hk⟩ => sq_mem_map_ker_of_pow_two_pow_eq_one f hx hk, fun k hk => ?_⟩
  · obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    exact ⟨⟨c, hcC⟩ * k' * ⟨c, hcC⟩⁻¹, f.normal_ker.conj_mem k' hk' _, by simp⟩
  · obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    exact hc.mem_normalizer_bar_LB_of_liftF_fix hφker hφπ hB (hCH k'.2)
      ((hf k').mp (MonoidHom.mem_ker.mp hk') b hbW)

end Model

theorem Ctx.exists_normal_normalizer_LB_of_isA2 (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) :
    ∃ K : Subgroup (Mbar M Q),
      K ≤ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)) ∧
      (∀ c ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ x ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ K) ∧
      K ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  obtain ⟨k, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  exact hc.exists_normal_normalizer_LB_of_model hD hφπ hφker hφiso ha hA

end CFSG.RankThree.GF2n.Stroth80
