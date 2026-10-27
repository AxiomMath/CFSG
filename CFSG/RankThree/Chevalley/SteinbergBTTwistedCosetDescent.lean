module

public import CFSG.LieType.Chevalley.EvenDiagramFixedAmbientCentralizer
public import CFSG.GroupTheory.LangNormOneDescent
public import CFSG.LieType.AlgebraicGroups.SmoothTangentLocal
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GroupTheory
  CFSG.LieType.AlgebraicGroups

theorem exists_conj_eq_of_pow_eq_twisted_frobenius (t : TwistTag) {ℓ f n : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hq3 : 3 ≤ ℓ ^ f) (hn : 1 ≤ n) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (S : MulAut (adjointGroup t.tag L))
    (hSn : ∀ g, (((⇑S)^[n] g : adjointGroup t.tag L) : ModGL t.tag L) = twistHom t L Fr g)
    (hLang : ∀ y : adjointGroup t.tag L, ∃ h, y = h⁻¹ * S h)
    (ιH : graphFixedRootGroup t K σ →* adjointGroup t.tag L)
    (hιH : ∀ u, (ιH u : ModGL t.tag L) = baseChangeGL (algebraMap K L) u)
    (β : MulAut (graphFixedRootGroup t K σ)) (hβ : ∀ u, S (ιH u) = ιH (β u))
    (x : adjointGroup t.tag L) (α : MulAut (graphFixedRootGroup t K σ))
    (hα : ∀ u, ιH (α u) = x * S (ιH u) * x⁻¹) (hαn : α ^ n = 1) :
    ∃ ψ : MulAut (graphFixedRootGroup t K σ), ψ * α * ψ⁻¹ = β := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hι : Function.Injective ιH := fun u v huv => Subtype.ext (baseChangeGL_injective
    (algebraMap K L) (by rw [← hιH, ← hιH, huv]))
  have hcomm : (algebraMap K L).comp σ = Fr.comp (algebraMap K L) := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hσ, hFr, map_pow]
  have hSF : ∀ u, (⇑S)^[n] (ιH u) = ιH u := fun u => Subtype.ext (by
    rw [hSn, hιH, twistHom_baseChangeGL (algebraMap K L) hcomm]
    congr 1
    exact (graphFixedRootGroup_le t K σ u.2).2)
  set N : ℕ → adjointGroup t.tag L := fun k => ((List.range k).map fun i => (⇑S)^[i] x).prod
    with hNdef
  have hNsucc : ∀ k, N (k + 1) = x * S (N k) := fun k => by
    simp only [hNdef]
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, Function.iterate_zero_apply,
      map_list_prod, List.map_map, List.map_map]
    congr 2
    exact List.map_congr_left fun i _ => by
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  have hαk : ∀ k u, ιH ((α ^ k) u) = N k * (⇑S)^[k] (ιH u) * (N k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp [hNdef]
    | succ k ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, hα, ih, hNsucc, map_mul, map_mul, map_inv,
        Function.iterate_succ_apply']
      group
  have hNn : N n = 1 := by
    obtain ⟨-, -, hC, -⟩ := diagram_fixed_ambient_centralizer_trivial_of_three_le t hℓ hf hq3 K
      hK σ hσ L (algebraMap K L)
    refine Subtype.ext (hC _ (N n).2 fun g hg => ?_)
    obtain ⟨u, hu, rfl⟩ := hg
    have h1 := hαk n ⟨u, hu⟩
    rw [hαn, MulAut.one_apply, hSF] at h1
    have h2 : N n * ιH ⟨u, hu⟩ = ιH ⟨u, hu⟩ * N n := by
      calc N n * ιH ⟨u, hu⟩ = (N n * ιH ⟨u, hu⟩ * (N n)⁻¹) * N n := by group
        _ = ιH ⟨u, hu⟩ * N n := by rw [← h1]
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, hιH] at h3 ⊢
    exact h3
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom (m := n) hn hLang x
    (by simpa [hNdef] using hNn)
  have hxh' : x = h⁻¹ * S h := hxh
  have hSh : (⇑S)^[n] h = h := hR
  have hhF : twistHom t L Fr (h : ModGL t.tag L) = h := by rw [← hSn, hSh]
  obtain ⟨-, -, -, -, -, hnorml⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer t
    hℓ hf K hK σ hσ L Fr hFr
  have hmap : ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL t.tag L)).toMonoidHom =
        (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml ⟨h.2, hhF⟩)
  let eH : graphFixedRootGroup t K σ ≃*
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (graphFixedRootGroup t K σ) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))) :
      ModGL t.tag L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let ψ : MulAut (graphFixedRootGroup t K σ) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap).trans eH.symm)
  have hψ0 : ∀ u, baseChangeGL (algebraMap K L) (ψ u : ModGL t.tag K) =
      (h : ModGL t.tag L) * baseChangeGL (algebraMap K L) u * (h : ModGL t.tag L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap (eH u))) :
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))) : ModGL t.tag L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hψ : ∀ u, ιH (ψ u) = h * ιH u * h⁻¹ := fun u => Subtype.ext (by
    rw [hιH, hψ0, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hιH])
  have hψinv : ∀ u, ιH (ψ⁻¹ u) = h⁻¹ * ιH u * h := by
    intro u
    have h1 := hψ (ψ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨ψ, MulEquiv.ext fun u => hι ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hψ, hα, hψinv, ← hβ, map_mul, map_mul, map_inv, hxh']
  group

end CFSG.RankThree.Chevalley
