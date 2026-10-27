module

public import CFSG.RepresentationTheory.TrivialKernelMaps
public import CFSG.Quasithin.Background.RankOneCohomologyTensor
public import CFSG.Quasithin.Background.TrivialLineExtension
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Cohom
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped TensorProduct

theorem exists_unique_tensor_cover_of_finrank_H1_le_one
    {B Q X Z E W : Type*} [Group B] [Finite B]
    [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρQ : Representation (ZMod 2) B Q)
    (ρE : Representation (ZMod 2) B E)
    (ρW : Representation (ZMod 2) B W)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ))
    (hH1 : Module.finrank (ZMod 2)
      (H1 (Representation.dual ρQ)) ≤ 1)
    (hQ : ∀ ψ : Q →ₗ[ZMod 2] ZMod 2,
      (∀ g q, ψ (ρQ g q) = ψ q) → ψ = 0)
    (eE : E ≃ₗ[ZMod 2] (ZMod 2 × Q))
    (hE : ∀ g e,
      eE (ρE g e) =
        ((eE e).1 + d g (ρQ g (eE e).2), ρQ g (eE e).2))
    (i : Z →ₗ[ZMod 2] W)
    (qW : W →ₗ[ZMod 2] Q ⊗[ZMod 2] X)
    (hi : Function.Injective i)
    (hqW : Function.Surjective qW)
    (hker : LinearMap.range i = LinearMap.ker qW)
    (hfix : ∀ g z, ρW g (i z) = i z)
    (hqρ : ∀ g w,
      qW (ρW g w) =
        TensorProduct.map (ρQ g) LinearMap.id (qW w))
    (hW : ∀ ψ : W →ₗ[ZMod 2] ZMod 2,
      (∀ g w, ψ (ρW g w) = ψ w) → ψ = 0) :
    ∃ ξ : X →ₗ[ZMod 2] Z,
      ∃ F : E ⊗[ZMod 2] X →ₗ[ZMod 2] W,
        Function.Surjective ξ ∧
        Function.Surjective F ∧
        (∀ g u,
          F (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F u)) ∧
        (∀ e x,
          qW (F (e ⊗ₜ[ZMod 2] x)) = (eE e).2 ⊗ₜ[ZMod 2] x) ∧
        (∀ x,
          F ((eE.symm (1, 0)) ⊗ₜ[ZMod 2] x) = i (ξ x)) ∧
        (∀ F' : E ⊗[ZMod 2] X →ₗ[ZMod 2] W,
          (∀ g u,
            F' (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F' u)) →
          (∀ e x,
            qW (F' (e ⊗ₜ[ZMod 2] x)) = (eE e).2 ⊗ₜ[ZMod 2] x) →
          F' = F) := by
  classical
  let ρP : Representation (ZMod 2) B (Q ⊗[ZMod 2] X) :=
    ρQ.tprod (Representation.trivial (ZMod 2) B X)
  have hqρP : ∀ g m, qW (ρW g m) = ρP g (qW m) := by
    intro g m
    change qW (ρW g m) = TensorProduct.map (ρQ g) LinearMap.id (qW m)
    exact hqρ g m
  have hkerfix : ∀ g w, qW w = 0 → ρW g w = w := by
    intro g w hw
    have hw' : w ∈ LinearMap.range i := by
      rw [hker]
      exact hw
    obtain ⟨z, rfl⟩ := hw'
    exact hfix g z
  let ρD : Representation (ZMod 2) B (ZMod 2 × Q) := trivialLineExtension ρQ d hd
  have hconj : ∀ g v, eE.symm (ρD g v) = ρE g (eE.symm v) := by
    intro g v
    apply eE.injective
    rw [LinearEquiv.apply_symm_apply, hE g (eE.symm v), LinearEquiv.apply_symm_apply]
    rfl
  have hEperfect : ∀ ψ : E →ₗ[ZMod 2] ZMod 2,
      (∀ g e, ψ (ρE g e) = ψ e) → ψ = 0 := by
    intro ψ hψ
    let φ : (ZMod 2 × Q) →ₗ[ZMod 2] ZMod 2 := ψ.comp eE.symm.toLinearMap
    have hφ : ∀ g v, φ (ρD g v) = φ v := by
      intro g v
      have h1 := congrArg ψ (hconj g v)
      have h2 := hψ g (eE.symm v)
      simpa [φ, LinearMap.comp_apply] using h1.trans h2
    have hφ0 : φ = 0 :=
      trivialLineExtension_noInvariantFunctional ρQ d hd hdn hQ φ hφ
    ext e
    have h := congrArg (fun l : (ZMod 2 × Q) →ₗ[ZMod 2] ZMod 2 => l (eE e)) hφ0
    simpa [φ] using h
  have hUperfect : ∀ ψ : E ⊗[ZMod 2] X →ₗ[ZMod 2] ZMod 2,
      (∀ g u,
        ψ ((ρE.tprod (Representation.trivial (ZMod 2) B X)) g u) = ψ u) → ψ = 0 :=
    CFSG.RepresentationTheory.noInvariantFunctional_tprod_trivial ρE hEperfect
  obtain ⟨s, hs⟩ :=
    LinearMap.exists_rightInverse_of_surjective qW (LinearMap.range_eq_top.mpr hqW)
  obtain ⟨r₀, hr₀⟩ :=
    LinearMap.exists_leftInverse_of_injective i (LinearMap.ker_eq_bot.mpr hi)
  have hsq : ∀ p, qW (s p) = p := fun p => LinearMap.congr_fun hs p
  have hr₀i : ∀ z, r₀ (i z) = z := fun z => LinearMap.congr_fun hr₀ z
  have hqi : ∀ z, qW (i z) = 0 := by
    intro z
    have hz : i z ∈ LinearMap.range i := ⟨z, rfl⟩
    rw [hker] at hz
    exact hz
  let r : W →ₗ[ZMod 2] Z := r₀.comp (LinearMap.id - s.comp qW)
  have hri : ∀ z, r (i z) = z := by
    intro z
    simp only [r, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      hqi z, map_zero, sub_zero]
    exact hr₀i z
  have hrs : ∀ p, r (s p) = 0 := by
    intro p
    simp only [r, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hsq p,
      sub_self]
    exact map_zero r₀
  have hdecomp : ∀ w, i (r w) + s (qW w) = w := by
    intro w
    have hmem : w - s (qW w) ∈ LinearMap.range i := by
      rw [hker]
      change qW (w - s (qW w)) = 0
      rw [map_sub, hsq, sub_self]
    obtain ⟨z, hz⟩ := hmem
    have hzr : r w = z := by
      simp only [r, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      rw [← hz, hr₀i]
    rw [hzr, hz]
    abel
  let Tw : B → (Q ⊗[ZMod 2] X) →ₗ[ZMod 2] W := fun g => extTwist ρW ρP s g
  let c : B → (Q ⊗[ZMod 2] X) →ₗ[ZMod 2] Z := fun g => r.comp (Tw g)
  have hqTw : ∀ g p, qW (Tw g p) = 0 := by
    intro g p
    simp only [Tw, extTwist, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hqρP, hsq,
      Representation.self_inv_apply, sub_self]
  have hic : ∀ g p, i (c g p) = Tw g p := by
    intro g p
    have h := hdecomp (Tw g p)
    rw [hqTw g p, map_zero, add_zero] at h
    simpa [c] using h
  have hc : c ∈ Z1 (Representation.linHom ρP (Representation.trivial (ZMod 2) B Z)) := by
    intro g h
    apply LinearMap.ext
    intro p
    rw [← sub_eq_zero]
    change c (g * h) p - (c g p + c h (ρP g⁻¹ p)) = 0
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2)
      (c (g * h) p - (c g p + c h (ρP g⁻¹ p)))).mp ?_
    intro lam
    have hlam := s16sp_extCocycle_mem ρW ρP qW s hqρP hsq hkerfix (lam.comp r)
    have happ := DFunLike.congr_fun (hlam g h) p
    have hab : lam (c (g * h) p) = lam (c g p) + lam (c h (ρP g⁻¹ p)) := by
      simpa only [extCocycle, LinearMap.comp_apply, LinearMap.add_apply,
        Representation.dual_apply, Module.Dual.transpose_apply, Pi.add_apply,
        LinearMap.sub_apply, c, Tw] using happ
    rw [map_sub, map_add, hab, sub_self]
  obtain ⟨ξ, t, hB⟩ := exists_tensor_cocycle_normalForm ρQ d hd hdn hH1 c hc
  let L : B → (Q ⊗[ZMod 2] X) →ₗ[ZMod 2] Z := fun g =>
    TensorProduct.lift
      { toFun := fun q => (d g q) • ξ
        map_add' := by
          intro q₁ q₂
          rw [map_add, add_smul]
        map_smul' := by
          intro a q
          rw [map_smul, smul_assoc]
          rfl }
  have hL_tmul : ∀ g q x, L g (q ⊗ₜ[ZMod 2] x) = (d g q) • ξ x := by
    intro g q x
    simp [L, TensorProduct.lift.tmul]
  have hρP_tmul : ∀ (g : B) (q : Q) (x : X),
      ρP g (q ⊗ₜ[ZMod 2] x) = (ρQ g q) ⊗ₜ[ZMod 2] x := by
    intro g q x
    simp [ρP, Representation.tprod_apply, Representation.trivial_apply]
  have hB' : ∀ g, c g = L g + t.comp (ρP g⁻¹) - t := by
    intro g
    refine TensorProduct.ext' fun q x => ?_
    rw [hB g q x]
    change (d g) q • ξ x + (t ((ρQ g⁻¹) q ⊗ₜ[ZMod 2] x) -
        t (q ⊗ₜ[ZMod 2] x)) =
      L g (q ⊗ₜ[ZMod 2] x) + t ((ρP g⁻¹) (q ⊗ₜ[ZMod 2] x)) -
        t (q ⊗ₜ[ZMod 2] x)
    rw [hL_tmul, hρP_tmul]
    abel
  let s' : Q ⊗[ZMod 2] X →ₗ[ZMod 2] W := s - i.comp t
  let r' : W →ₗ[ZMod 2] Z := r + t.comp qW
  have hs' : ∀ p, qW (s' p) = p := by
    intro p
    simp only [s', LinearMap.sub_apply, map_sub, LinearMap.comp_apply, hsq, hqi (t p),
      sub_zero]
  have hr'i : ∀ z, r' (i z) = z := by
    intro z
    simp only [r', LinearMap.add_apply, LinearMap.comp_apply, hri z, hqi z, map_zero,
      add_zero]
  have hr's' : ∀ p, r' (s' p) = 0 := by
    intro p
    have h1 : r (s p - i (t p)) = - t p := by
      rw [map_sub, hrs, hri, zero_sub]
    have h2 : t (qW (s p - i (t p))) = t p := by
      rw [map_sub, hsq, hqi (t p), sub_zero]
    calc
      r' (s' p) = r (s p - i (t p)) + t (qW (s p - i (t p))) := by
            simp [r', s', LinearMap.comp_apply]
      _ = - t p + t p := by rw [h1, h2]
      _ = 0 := neg_add_cancel _
  have hdecomp' : ∀ w, i (r' w) + s' (qW w) = w := by
    intro w
    have h1 : i (r' w) = i (r w) + i (t (qW w)) := by
      simp [r', map_add]
    have h2 : s' (qW w) = s (qW w) - i (t (qW w)) := by
      simp [s']
    rw [h1, h2]
    calc
      i (r w) + i (t (qW w)) + (s (qW w) - i (t (qW w)))
          = i (r w) + s (qW w) := by abel
      _ = w := hdecomp w
  have hTw_s' : ∀ g p, extTwist ρW ρP s' g p = i (L g p) := by
    intro g p
    calc
      extTwist ρW ρP s' g p
          = ρW g (s (ρP g⁻¹ p)) - ρW g (i (t (ρP g⁻¹ p))) -
              (s p - i (t p)) := by
            simp only [s', extTwist, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
      _ = (ρW g (s (ρP g⁻¹ p)) - i (t (ρP g⁻¹ p))) - (s p - i (t p)) := by
            rw [hfix]
      _ = (extTwist ρW ρP s g p) - i (t (ρP g⁻¹ p)) + i (t p) := by
            simp only [extTwist, LinearMap.sub_apply, LinearMap.comp_apply]
            abel
      _ = i (c g p) - i (t (ρP g⁻¹ p)) + i (t p) := by rw [hic]
      _ = i (c g p - (t (ρP g⁻¹ p) - t p)) := by
            have hlin : i (c g p - (t (ρP g⁻¹ p) - t p))
                = i (c g p) - i (t (ρP g⁻¹ p)) + i (t p) := by
              simp only [map_sub]
              abel
            exact hlin.symm
      _ = i ((c g - (t.comp (ρP g⁻¹) - t)) p) := by simp
      _ = i (L g p) := by
            rw [hB' g]
            simp
  have hforward : ∀ g p, ρW g (s' p) = s' (ρP g p) + i (L g (ρP g p)) := by
    intro g p
    have h := hTw_s' g (ρP g p)
    simp only [extTwist, LinearMap.sub_apply, LinearMap.comp_apply,
      Representation.inv_self_apply] at h
    calc
      ρW g (s' p) = (ρW g (s' p) - s' (ρP g p)) + s' (ρP g p) :=
        (sub_add_cancel _ _).symm
      _ = i (L g (ρP g p)) + s' (ρP g p) := by rw [h]
      _ = s' (ρP g p) + i (L g (ρP g p)) := add_comm _ _
  let β : E ⊗[ZMod 2] X ≃ₗ[ZMod 2] X × (Q ⊗[ZMod 2] X) :=
    (TensorProduct.congr eE (LinearEquiv.refl (ZMod 2) X)).trans
      ((TensorProduct.prodLeft (ZMod 2) (ZMod 2) (ZMod 2) Q X).trans
        ((TensorProduct.lid (ZMod 2) X).prodCongr
          (LinearEquiv.refl (ZMod 2) (Q ⊗[ZMod 2] X))))
  have hβ_tmul : ∀ e x, β (e ⊗ₜ[ZMod 2] x) = ((eE e).1 • x, (eE e).2 ⊗ₜ[ZMod 2] x) := by
    intro e x
    cases h : eE e with
    | mk a q =>
      simp [β, h, TensorProduct.congr_tmul, TensorProduct.prodLeft_tmul,
        TensorProduct.lid_tmul]
  let e0 : E := eE.symm (1, 0)
  have he0 : eE e0 = (1, 0) := eE.apply_symm_apply (1, 0)
  have hβ_e0 : ∀ x, β (e0 ⊗ₜ[ZMod 2] x) = (x, 0) := by
    intro x
    rw [hβ_tmul, he0]
    simp
  let F : E ⊗[ZMod 2] X →ₗ[ZMod 2] W :=
    ((i.comp ξ).coprod s').comp β.toLinearMap
  have hF_tmul : ∀ e x,
      F (e ⊗ₜ[ZMod 2] x) = i ((eE e).1 • ξ x) + s' ((eE e).2 ⊗ₜ[ZMod 2] x) := by
    intro e x
    simp [F, LinearMap.coprod_apply, hβ_tmul]
  have hqF : ∀ e x,
      qW (F (e ⊗ₜ[ZMod 2] x)) = (eE e).2 ⊗ₜ[ZMod 2] x := by
    intro e x
    rw [hF_tmul, map_add, hqi, hs', zero_add]
  have hFj : ∀ x, F (e0 ⊗ₜ[ZMod 2] x) = i (ξ x) := by
    intro x
    rw [hF_tmul, he0]
    simp
  have hFB : ∀ g u,
      F (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F u) := by
    intro g u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul e x =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hF_tmul, hF_tmul, hE g e, map_add]
        rw [hfix, hforward, hρP_tmul, hL_tmul, add_smul, map_add]
        abel
  let R : Submodule (ZMod 2) Z := LinearMap.range ξ
  let π : Z →ₗ[ZMod 2] Z ⧸ R := R.mkQ
  let f : W →ₗ[ZMod 2] Z ⧸ R := π.comp r'
  have hπL : ∀ g p, π (L g p) = 0 := by
    intro g p
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add p₁ p₂ h₁ h₂ => simp [map_add, h₁, h₂]
    | tmul q x =>
        rw [hL_tmul]
        have hx : π (ξ x) = 0 := by
          simpa [π] using (Submodule.Quotient.mk_eq_zero (p := R)).mpr
            (show ξ x ∈ R from ⟨x, rfl⟩)
        rw [map_smul, hx, smul_zero]
  have hr'ρ : ∀ g w, r' (ρW g w) = r' w + L g (ρP g (qW w)) := by
    intro g w
    have hdec : ρW g w =
        i (r' w) + s' (ρP g (qW w)) + i (L g (ρP g (qW w))) := by
      calc
        ρW g w = ρW g (i (r' w) + s' (qW w)) := by rw [hdecomp']
        _ = ρW g (i (r' w)) + ρW g (s' (qW w)) := by rw [map_add]
        _ = i (r' w) + (s' (ρP g (qW w)) + i (L g (ρP g (qW w)))) := by
              rw [hfix, hforward]
        _ = i (r' w) + s' (ρP g (qW w)) + i (L g (ρP g (qW w))) := by abel
    calc
      r' (ρW g w)
          = r' (i (r' w)) + r' (s' (ρP g (qW w))) +
              r' (i (L g (ρP g (qW w)))) := by
            rw [hdec, map_add, map_add]
      _ = r' w + L g (ρP g (qW w)) := by
            rw [hr'i, hr's', hr'i]
            abel
  have hf : ∀ g w, f (ρW g w) = f w := by
    intro g w
    simp only [f, LinearMap.comp_apply, hr'ρ g w, map_add, hπL g (ρP g (qW w)), add_zero]
  have hf0 : f = 0 :=
    CFSG.RepresentationTheory.linearMap_eq_zero_of_invariant ρW hW f hf
  have hξsurj : Function.Surjective ξ := by
    intro z
    have hz : π z = 0 := by
      have h := congrArg (fun l : W →ₗ[ZMod 2] Z ⧸ R => l (i z)) hf0
      simpa [f, hr'i] using h
    have hzR : z ∈ R := by
      simpa [π] using (Submodule.Quotient.mk_eq_zero (p := R)).mp hz
    change z ∈ LinearMap.range ξ at hzR
    rwa [LinearMap.mem_range] at hzR
  have hFsurj : Function.Surjective F := by
    intro w
    obtain ⟨x, hx⟩ := hξsurj (r' w)
    refine ⟨β.symm (x, qW w), ?_⟩
    have h1 : F (β.symm (x, qW w)) = i (ξ x) + s' (qW w) := by
      simp [F, LinearMap.coprod_apply, LinearEquiv.apply_symm_apply]
    rw [h1, hx, hdecomp']
  have huniq : ∀ F' : E ⊗[ZMod 2] X →ₗ[ZMod 2] W,
      (∀ g u,
        F' (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F' u)) →
      (∀ e x,
        qW (F' (e ⊗ₜ[ZMod 2] x)) = (eE e).2 ⊗ₜ[ZMod 2] x) →
      F' = F := by
    intro F' hF'B hF'q
    have hq : qW.comp F' = qW.comp F := by
      refine TensorProduct.ext' fun e x => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hF'q e x, hqF e x]
    exact CFSG.RepresentationTheory.equivariant_eq_of_comp_eq_of_fixed_kernel
      (ρE.tprod (Representation.trivial (ZMod 2) B X)) ρW qW hkerfix
      hUperfect
      (fun g u => by
        change F' (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F' u)
        exact hF'B g u)
      (fun g u => by
        change F (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F u)
        exact hFB g u)
      hq
  exact ⟨ξ, F, hξsurj, hFsurj, hFB, hqF, hFj, huniq⟩


theorem exists_tensor_equiv_of_irreducible_multiplicity
    {B K Q X Z E W : Type*} [Group B] [Finite B] [Group K]
    [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z] [Nontrivial Z]
    [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρQ : Representation (ZMod 2) B Q)
    (ρE : Representation (ZMod 2) B E)
    (ρW : Representation (ZMod 2) B W)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ))
    (hH1 : Module.finrank (ZMod 2)
      (H1 (Representation.dual ρQ)) ≤ 1)
    (hQ : ∀ ψ : Q →ₗ[ZMod 2] ZMod 2,
      (∀ g q, ψ (ρQ g q) = ψ q) → ψ = 0)
    (eE : E ≃ₗ[ZMod 2] (ZMod 2 × Q))
    (hE : ∀ g e,
      eE (ρE g e) =
        ((eE e).1 + d g (ρQ g (eE e).2), ρQ g (eE e).2))
    (i : Z →ₗ[ZMod 2] W)
    (qW : W →ₗ[ZMod 2] Q ⊗[ZMod 2] X)
    (hi : Function.Injective i)
    (hqW : Function.Surjective qW)
    (hker : LinearMap.range i = LinearMap.ker qW)
    (hfix : ∀ g z, ρW g (i z) = i z)
    (hqρ : ∀ g w,
      qW (ρW g w) =
        TensorProduct.map (ρQ g) LinearMap.id (qW w))
    (hW : ∀ ψ : W →ₗ[ZMod 2] ZMod 2,
      (∀ g w, ψ (ρW g w) = ψ w) → ψ = 0)
    (κW : Representation (ZMod 2) K W)
    (κX : Representation (ZMod 2) K X)
    (κZ : Representation (ZMod 2) K Z)
    (hcomm : ∀ k g w, κW k (ρW g w) = ρW g (κW k w))
    (hiκ : ∀ k z, κW k (i z) = i (κZ k z))
    (hqκ : ∀ k w,
      qW (κW k w) = TensorProduct.map LinearMap.id (κX k) (qW w))
    (hX : κX.IsIrreducible) :
    ∃ e : E ⊗[ZMod 2] X ≃ₗ[ZMod 2] W,
      (∀ g u,
        e (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (e u)) ∧
      (∀ k u,
        e (TensorProduct.map LinearMap.id (κX k) u) = κW k (e u)) ∧
      (∀ v x,
        qW (e (v ⊗ₜ[ZMod 2] x)) = (eE v).2 ⊗ₜ[ZMod 2] x) := by
  classical
  obtain ⟨ξ, F, hξsurj, hFsurj, hFB, hqF, hFj, huniq⟩ :=
    exists_unique_tensor_cover_of_finrank_H1_le_one ρQ ρE ρW d hd hdn hH1 hQ eE hE
      i qW hi hqW hker hfix hqρ hW
  let Uk : K → (E ⊗[ZMod 2] X) →ₗ[ZMod 2] (E ⊗[ZMod 2] X) := fun k =>
    TensorProduct.map LinearMap.id (κX k)
  have hUk_comm : ∀ k g,
      (Uk k).comp (TensorProduct.map (ρE g) LinearMap.id) =
        (TensorProduct.map (ρE g) LinearMap.id).comp (Uk k) := by
    intro k g
    refine TensorProduct.ext' fun e x => ?_
    simp [Uk]
  let Fk : K → (E ⊗[ZMod 2] X) →ₗ[ZMod 2] W := fun k =>
    (κW k⁻¹).comp (F.comp (Uk k))
  have hFkB : ∀ k g u,
      Fk k (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (Fk k u) := by
    intro k g u
    have h1 : Uk k ((TensorProduct.map (ρE g) LinearMap.id) u) =
        (TensorProduct.map (ρE g) LinearMap.id) (Uk k u) := by
      have h := LinearMap.congr_fun (hUk_comm k g) u
      simpa [LinearMap.comp_apply] using h
    simp only [Fk, LinearMap.comp_apply]
    rw [h1, hFB g (Uk k u)]
    exact hcomm k⁻¹ g (F (Uk k u))
  have hFkq : ∀ k e x,
      qW (Fk k (e ⊗ₜ[ZMod 2] x)) = (eE e).2 ⊗ₜ[ZMod 2] x := by
    intro k e x
    simp only [Fk, LinearMap.comp_apply, Uk, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hqκ k⁻¹ (F (e ⊗ₜ[ZMod 2] κX k x))]
    rw [hqF e (κX k x)]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      Representation.inv_self_apply]
  have hFk_eq : ∀ k, Fk k = F := fun k => huniq (Fk k) (hFkB k) (hFkq k)
  have hFK : ∀ k u,
      F (TensorProduct.map LinearMap.id (κX k) u) = κW k (F u) := by
    intro k u
    have h := congrArg (fun l : E ⊗[ZMod 2] X →ₗ[ZMod 2] W => l u) (hFk_eq k)
    have h2 := congrArg (κW k) h
    simpa [Fk, Uk, Representation.self_inv_apply] using h2
  have hξκ : ∀ k x, ξ (κX k x) = κZ k (ξ x) := by
    intro k x
    have h := hFK k ((eE.symm (1, 0)) ⊗ₜ[ZMod 2] x)
    have hUk : TensorProduct.map LinearMap.id (κX k)
        ((eE.symm (1, 0)) ⊗ₜ[ZMod 2] x) =
        (eE.symm (1, 0)) ⊗ₜ[ZMod 2] κX k x := by
      simp
    rw [hUk, hFj, hFj, hiκ] at h
    exact hi h
  let ξi : κX.IntertwiningMap κZ :=
    { toLinearMap := ξ
      isIntertwining' := fun k => by
        apply LinearMap.ext
        intro x
        exact hξκ k x }
  have hξne : ξ ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := exists_ne (0 : Z)
    obtain ⟨x, hx⟩ := hξsurj z
    apply hz
    rw [← hx, h0]
    simp
  have hξinj : Function.Injective ξ := by
    have h := @Representation.IsIrreducible.injective_or_eq_zero (G := K) (k := ZMod 2)
      (V := X) (W := Z) (ρ := κX) (σ := κZ) _ _ _ _ _ _ ξi hX
    rcases h with hinj | hzero
    · intro x y hxy
      exact hinj hxy
    · exfalso
      apply hξne
      have h0 : (ξi : X →ₗ[ZMod 2] Z) = 0 := by
        simpa using congrArg
          (fun m : κX.IntertwiningMap κZ => m.toLinearMap) hzero
      simpa [ξi] using h0
  let β : E ⊗[ZMod 2] X ≃ₗ[ZMod 2] X × (Q ⊗[ZMod 2] X) :=
    (TensorProduct.congr eE (LinearEquiv.refl (ZMod 2) X)).trans
      ((TensorProduct.prodLeft (ZMod 2) (ZMod 2) (ZMod 2) Q X).trans
        ((TensorProduct.lid (ZMod 2) X).prodCongr
          (LinearEquiv.refl (ZMod 2) (Q ⊗[ZMod 2] X))))
  have hβ_tmul : ∀ e x, β (e ⊗ₜ[ZMod 2] x) = ((eE e).1 • x, (eE e).2 ⊗ₜ[ZMod 2] x) := by
    intro e x
    cases h : eE e with
    | mk a q =>
      simp [β, h, TensorProduct.congr_tmul, TensorProduct.prodLeft_tmul,
        TensorProduct.lid_tmul]
  have hqFβ : ∀ u, qW (F u) = (β u).2 := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp [map_add, hu, hv]
    | tmul e x => rw [hqF e x, hβ_tmul]
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h2 : (β u).2 = 0 := by
      rw [← hqFβ u, hu, map_zero]
    let x : X := (β u).1
    have hβu : β u = (x, 0) := by
      refine Prod.ext ?_ ?_
      · rfl
      · simpa [x] using h2
    have hβx : β ((eE.symm (1, 0)) ⊗ₜ[ZMod 2] x) = (x, 0) := by
      rw [hβ_tmul, eE.apply_symm_apply]
      simp
    have hju : u = (eE.symm (1, 0)) ⊗ₜ[ZMod 2] x := by
      apply β.injective
      rw [hβu, hβx]
    rw [hju, hFj] at hu
    have hξx : ξ x = 0 := by
      apply hi
      simpa using hu
    have hx0 : x = 0 := by
      apply hξinj
      simpa using hξx
    rw [hx0] at hju
    simpa using hju
  let e : E ⊗[ZMod 2] X ≃ₗ[ZMod 2] W :=
    LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro g u
    change F (TensorProduct.map (ρE g) LinearMap.id u) = ρW g (F u)
    exact hFB g u
  · intro k u
    change F (TensorProduct.map LinearMap.id (κX k) u) = κW k (F u)
    exact hFK k u
  · intro v x
    change qW (F (v ⊗ₜ[ZMod 2] x)) = (eE v).2 ⊗ₜ[ZMod 2] x
    exact hqF v x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
