module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Coker
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableB.TwE6

variable {t : TwistTag} {K : Type} [Field K]

theorem rootDiagUnit_conj_orbitXProd
    (b : Fin t.tag.rank → Kˣ) (a : Fin t.foldedTag.rank) (γ : Fin t.tag.rank → K) :
    rootDiagUnit t.tag b * orbitXProd t a γ * (rootDiagUnit t.tag b)⁻¹ =
      orbitXProd t a fun j => (b j : K) * γ j := by
  unfold orbitXProd
  rw [← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, (root_diagonal_conjugation t.tag K b).1]


theorem compat_of_forall_conj_mem {σ : K →+* K} {b : Fin t.tag.rank → Kˣ}
    (h : ∀ g ∈ graphFixedRootGroup t K σ,
      rootDiagUnit t.tag b * g * (rootDiagUnit t.tag b)⁻¹ ∈ graphFixedRootGroup t K σ)
    (i : Fin t.tag.rank) : b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
  set a := t.orbitIndex (t.perm i)
  have hj : t.perm i ∈ t.orbit a := t.mem_orbit_orbitIndex _
  have hi : i ∈ t.orbit a := by
    have h' := t.perm_symm_mem_orbit hj
    rwa [Equiv.symm_apply_apply] at h'
  have hx : (orbitX t K σ a 1 : ModGL t.tag K) ∈ graphFixedRootGroup t K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a 1)
  have hF := ((mem_twistedFixedGroup_iff_twistHom t K σ).1
    (graphFixedRootGroup_le t K σ (h _ hx))).2
  rw [coe_orbitX_eq_orbitXProd, rootDiagUnit_conj_orbitXProd, twistHom_orbitXProd] at hF
  have h1 := eq_of_orbitXProd_eq t hF (t.perm i) hj
  have hγ : ∀ j ∈ t.orbit a, orbitParam t σ a ((1 : orbitField t K σ a) : K) j = 1 := by
    intro j hj'
    obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj'
    rw [orbitParam_pow t σ _ hk]
    simp
  simp only [Equiv.symm_apply_apply] at h1
  rw [hγ _ hi, hγ _ hj, mul_one, mul_one] at h1
  exact Units.ext (by simpa using h1.symm)

theorem rootDiagUnit_cartanChar_mem {σ : K →+* K} {s : Fin t.tag.rank → Kˣ}
    (hs : ∀ i, s (t.perm i) = Units.map σ.toMonoidHom (s i)) :
    rootDiagUnit t.tag (cartanChar s) ∈ graphFixedRootGroup t K σ := by
  obtain ⟨w, rfl⟩ := exists_compatDiag_eq hs
  rw [← list_prod_orbitH_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact orbitH_mem_graphFixedRootGroup t σ a (w a)

theorem twE6_rootDiag_cyclic [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q) {a a' : Fin 6 → Kˣ}
    (ha : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a * g *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (ha' : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a' * g *
      (rootDiagUnit TwistTag.E6.tag a')⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hn : rootDiagUnit TwistTag.E6.tag a' ∉ graphFixedRootGroup TwistTag.E6 K σ) :
    ∃ k : ℕ, rootDiagUnit TwistTag.E6.tag (a * (a' ^ k)⁻¹) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hca : a ∈ compat σ := fun i => compat_of_forall_conj_mem ha i
  have hca' : a' ∈ compat σ := fun i => compat_of_forall_conj_mem ha' i
  have hT : ∀ c ∈ torus₀ σ,
      rootDiagUnit TwistTag.E6.tag c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨s, hs, rfl⟩
    exact rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  obtain ⟨k, hk⟩ := exists_mul_inv_pow_mem hq hK hσ hca hca' fun h => hn (hT a' h)
  exact ⟨k, hT _ hk⟩

end TableB.TwE6

end CFSG.StandardType
