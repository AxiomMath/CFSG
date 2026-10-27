module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CoreKAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q] [Module k Q]

private lemma w183b2Graph_sq {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {f : G} (hf : f ∈ Δ) : ρ f * ρ f = 1 := by
  have hf2 : f * f = 1 := by simpa [pow_two] using h.elem.2 f hf
  rw [← map_mul, hf2, map_one]

private def w183b2GraphConj {G : Type} [Group G] {N : Subgroup G} (hN : N.Normal) (f : G)
    (n : N) : N :=
  ⟨f * (n : G) * f⁻¹, hN.conj_mem (n : G) n.2 f⟩

private lemma w183b2GraphConj_invol {G : Type} [Group G] {N : Subgroup G} (hN : N.Normal)
    {f : G} (hf2 : f * f = 1) (n : N) :
    w183b2GraphConj hN f (w183b2GraphConj hN f n) = n := by
  apply Subtype.ext
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  show f * (f * (n : G) * f⁻¹) * f⁻¹ = (n : G)
  rw [hfinv]
  calc f * (f * (n : G) * f) * f = (f * f) * (n : G) * (f * f) := by group
    _ = (n : G) := by rw [hf2]; simp

private noncomputable def w183b2GraphTau {ρ : Representation k G Q} {U : Submodule k Q} {f : G}
    (hs : ρ f * ρ f = 1) (θ : U →ₗ[k] Q) (hθ : LinearMap.range θ = U.map (ρ f)) : U →ₗ[k] U where
  toFun u := ⟨ρ f (θ u), by
    obtain ⟨u', hu', hθu⟩ := Submodule.mem_map.mp (hθ ▸ LinearMap.mem_range.mpr ⟨u, rfl⟩)
    have h1 : ρ f (ρ f u') = u' := by
      have h2 : (ρ f * ρ f) u' = u' := by rw [hs, Module.End.one_apply]
      simpa only [Module.End.mul_apply] using h2
    rw [← hθu, h1]
    exact hu'⟩
  map_add' u v := Subtype.ext (by simp)
  map_smul' c u := Subtype.ext (by simp)

private noncomputable def w183b2GraphNu {ρ : Representation k G Q} {N : Subgroup G}
    {U : Submodule k Q} (hUinv : w183b2InvSub ρ N U) (n : N) : U →ₗ[k] U where
  toFun u := ⟨ρ (n : G) u, hUinv (n : G) n.2 u u.2⟩
  map_add' u v := Subtype.ext (by simp)
  map_smul' c u := Subtype.ext (by simp)

private lemma w183b2GraphTau_coe {ρ : Representation k G Q} {U : Submodule k Q} {f : G}
    (hs : ρ f * ρ f = 1) (θ : U →ₗ[k] Q) (hθ : LinearMap.range θ = U.map (ρ f)) (u : U) :
    ((w183b2GraphTau hs θ hθ u : U) : Q) = ρ f (θ u) := rfl

private lemma w183b2GraphNu_coe {ρ : Representation k G Q} {N : Subgroup G} {U : Submodule k Q}
    (hUinv : w183b2InvSub ρ N U) (n : N) (u : U) :
    ((w183b2GraphNu hUinv n u : U) : Q) = ρ (n : G) u := rfl

private lemma w183b2GraphTau_nu {ρ : Representation k G Q} {N : Subgroup G} {U : Submodule k Q}
    {f : G} (hN : N.Normal) (hs : ρ f * ρ f = 1) (θ : U →ₗ[k] Q)
    (hθ : LinearMap.range θ = U.map (ρ f)) (hUinv : w183b2InvSub ρ N U)
    (hθnlin : w183b2NLin ρ N U θ) (n : N) (u : U) :
    w183b2GraphTau hs θ hθ (w183b2GraphNu hUinv n u) =
      w183b2GraphNu hUinv (w183b2GraphConj hN f n) (w183b2GraphTau hs θ hθ u) := by
  apply Subtype.ext
  change ρ f (θ (w183b2GraphNu hUinv n u)) = ρ (f * (n : G) * f⁻¹) (ρ f (θ u))
  have hθnu : θ (w183b2GraphNu hUinv n u) = ρ (n : G) (θ u) :=
    hθnlin (n : G) n.2 u (w183b2GraphNu hUinv n u) rfl
  rw [hθnu, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact congrArg (fun g : G => ρ g (θ u))
    (by group : f * (n : G) = (f * (n : G) * f⁻¹) * f)

theorem w183b2_graph_step [IsAlgClosed k] [FiniteDimensional k Q] {ρ : Representation k G Q}
    {A₁ A₂ Δ : Subgroup G} (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q}
    (hU : w183b2SimpleSub ρ (A₁ ⊔ A₂) U) {f : G} (hf : f ∈ Δ) (hdisj : U.map (ρ f) ⊓ U = ⊥)
    (hiso : w183b2NIso ρ (A₁ ⊔ A₂) U (U.map (ρ f))) :
    ∃ Γ : Submodule k Q, w183b2SimpleSub ρ (A₁ ⊔ A₂) Γ ∧ Γ.map (ρ f) = Γ := by
  obtain ⟨θ, hθinj, hθrange, hθnlin⟩ := hiso
  haveI hN : (A₁ ⊔ A₂).Normal := w183b2_normal_sup h
  have hf2 : f * f = 1 := by simpa [pow_two] using h.elem.2 f hf
  have hs : ρ f * ρ f = 1 := w183b2Graph_sq h hf
  have hss : ∀ x : Q, ρ f (ρ f x) = x := by
    intro x
    have h2 : (ρ f * ρ f) x = x := by rw [hs, Module.End.one_apply]
    simpa only [Module.End.mul_apply] using h2
  have hUinv : w183b2InvSub ρ (A₁ ⊔ A₂) U := hU.2.1
  have hUne : U ≠ ⊥ := hU.1
  have hUsimple := hU.2.2
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  let τ : U →ₗ[k] U := w183b2GraphTau hs θ hθrange
  have hτnu : ∀ (n : ↥(A₁ ⊔ A₂)) (u : U),
      τ (w183b2GraphNu hUinv n u) = w183b2GraphNu hUinv (w183b2GraphConj hN f n) (τ u) :=
    fun n u => w183b2GraphTau_nu hN hs θ hθrange hUinv hθnlin n u
  have hττnu : ∀ (n : ↥(A₁ ⊔ A₂)) (u : U),
      (τ * τ) (w183b2GraphNu hUinv n u) = w183b2GraphNu hUinv n ((τ * τ) u) := by
    intro n u
    rw [Module.End.mul_apply, Module.End.mul_apply]
    rw [hτnu n u, hτnu (w183b2GraphConj hN f n) (τ u), w183b2GraphConj_invol hN hf2 n]
  obtain ⟨γ, hγeig⟩ : ∃ γ : k, Module.End.HasEigenvalue (τ * τ) γ :=
    Module.End.exists_eigenvalue (τ * τ)
  let E : Submodule k U := Module.End.eigenspace (τ * τ) γ
  have hEne : E ≠ ⊥ := hγeig
  have hEmapinj : Function.Injective (Submodule.map U.subtype) :=
    Submodule.map_injective_of_injective
      (show Function.Injective U.subtype from Subtype.coe_injective)
  have hEinv : w183b2InvSub ρ (A₁ ⊔ A₂) (E.map U.subtype) := by
    intro n hn w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨w183b2GraphNu hUinv ⟨n, hn⟩ u, ?_, ?_⟩
    · change w183b2GraphNu hUinv ⟨n, hn⟩ u ∈ Module.End.eigenspace (τ * τ) γ
      rw [Module.End.mem_eigenspace_iff]
      rw [hττnu ⟨n, hn⟩ u, Module.End.mem_eigenspace_iff.mp hu, map_smul]
    · exact w183b2GraphNu_coe hUinv ⟨n, hn⟩ u
  have hEmapne : E.map U.subtype ≠ ⊥ := by
    intro hbot
    exact hEne (hEmapinj (by rw [hbot, Submodule.map_bot]))
  have hEtop : E = ⊤ := by
    rcases hUsimple (E.map U.subtype) hEinv (Submodule.map_subtype_le U E) with hbot | htop
    · exact absurd hbot hEmapne
    · rw [eq_top_iff]
      intro u _
      have hmem : (u : Q) ∈ E.map U.subtype := by rw [htop]; exact u.2
      obtain ⟨e, he, heq⟩ := Submodule.mem_map.mp hmem
      have : e = u := Subtype.ext (by simpa using heq)
      rwa [this] at he
  have hττ : τ * τ = γ • 1 := by
    apply LinearMap.ext
    intro u
    have hu : u ∈ E := by rw [hEtop]; exact Submodule.mem_top
    have := (Module.End.mem_eigenspace_iff.mp hu : (τ * τ) u = γ • u)
    simpa using this
  have hτinj : Function.Injective τ := by
    intro u v huv
    apply hθinj
    have hcoe : ρ f (θ u) = ρ f (θ v) := congrArg (fun w : U => (w : Q)) huv
    have h2 := congrArg (ρ f) hcoe
    rwa [hss (θ u), hss (θ v)] at h2
  have hγne : γ ≠ 0 := by
    intro hγ0
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    have hzu : τ u = 0 := by
      apply hτinj
      rw [map_zero]
      have h0 : (τ * τ) u = 0 := by rw [hττ, hγ0, zero_smul, LinearMap.zero_apply]
      simpa only [Module.End.mul_apply] using h0
    exact hu (hτinj (by rw [hzu, map_zero]))
  obtain ⟨e, he⟩ := IsAlgClosed.exists_eq_mul_self γ
  have hene : e ≠ 0 := by
    intro h0
    exact hγne (by rw [he, h0, mul_zero])
  let θ' : U →ₗ[k] Q := e⁻¹ • θ
  have hθ'range : LinearMap.range θ' = U.map (ρ f) := by
    rw [show θ' = e⁻¹ • θ from rfl, LinearMap.range_smul θ (e⁻¹) (inv_ne_zero hene), hθrange]
  have hθ'nlin : w183b2NLin ρ (A₁ ⊔ A₂) U θ' := by
    intro n hn u v huv
    change (e⁻¹ • θ) v = ρ n ((e⁻¹ • θ) u)
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hθnlin n hn u v huv, map_smul]
  let τ' : U →ₗ[k] U := w183b2GraphTau hs θ' hθ'range
  have hτ' : τ' = e⁻¹ • τ := by
    ext u
    change ρ f (θ' u) = e⁻¹ • (τ u : Q)
    rw [show θ' = e⁻¹ • θ from rfl, LinearMap.smul_apply, map_smul]
    rfl
  have hτ'τ' : τ' * τ' = 1 := by
    rw [hτ']
    ext u
    simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply, map_smul]
    have h1 : τ (τ u) = γ • u := by
      have := congrArg (fun F : Module.End k U => F u) hττ
      simpa using this
    rw [h1, smul_smul, smul_smul]
    have hscal : (e⁻¹ * e⁻¹) * γ = 1 := by
      rw [he]
      field_simp
    rw [hscal, one_smul]
  let ψ : U →ₗ[k] Q := U.subtype + θ'
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    have hψu : (u : Q) + θ' u = 0 := by
      have := LinearMap.mem_ker.mp hu
      change (u : Q) + θ' u = 0 at this
      exact this
    have hmem : (u : Q) ∈ U.map (ρ f) := by
      have hneg : (u : Q) = -θ' u := eq_neg_of_add_eq_zero_left hψu
      rw [hneg]
      exact (U.map (ρ f)).neg_mem (hθ'range ▸ LinearMap.mem_range.mpr ⟨u, rfl⟩)
    have hbot : (u : Q) ∈ (⊥ : Submodule k Q) := by
      rw [← hdisj]
      exact ⟨hmem, u.2⟩
    have h0 : (u : Q) = 0 := (Submodule.mem_bot k).mp hbot
    exact Subtype.ext h0
  let Γ : Submodule k Q := LinearMap.range ψ
  have hΓinv : w183b2InvSub ρ (A₁ ⊔ A₂) Γ := by
    intro n hn w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨w183b2GraphNu hUinv ⟨n, hn⟩ u, ?_⟩
    change (w183b2GraphNu hUinv ⟨n, hn⟩ u : Q) + θ' (w183b2GraphNu hUinv ⟨n, hn⟩ u) =
      ρ n ((u : Q) + θ' u)
    rw [w183b2GraphNu_coe, hθ'nlin n hn u (w183b2GraphNu hUinv ⟨n, hn⟩ u) rfl, map_add]
  have hΓmap_le : Γ.map (ρ f) ≤ Γ := by
    rintro w ⟨w', hw', rfl⟩
    obtain ⟨u, rfl⟩ := hw'
    refine ⟨τ' u, ?_⟩
    change (τ' u : Q) + θ' (τ' u) = ρ f ((u : Q) + θ' u)
    have hθ'τ' : θ' (τ' u) = ρ f (u : Q) := by
      have hfix : τ' (τ' u) = u := by
        have := congrArg (fun F : Module.End k U => F u) hτ'τ'
        simpa [Module.End.mul_apply] using this
      have hcoe : ρ f (θ' (τ' u)) = (u : Q) := congrArg (fun w : U => (w : Q)) hfix
      calc θ' (τ' u) = ρ f (ρ f (θ' (τ' u))) := (hss (θ' (τ' u))).symm
        _ = ρ f (u : Q) := by rw [hcoe]
    rw [w183b2GraphTau_coe, hθ'τ', map_add, add_comm]
  have hcomp : (ρ f).comp (ρ f) = 1 := by
    rw [← Module.End.mul_eq_comp, hs]
  have hΓmap : Γ.map (ρ f) = Γ := by
    apply le_antisymm hΓmap_le
    calc Γ = (Γ.map (ρ f)).map (ρ f) := by
          rw [← Submodule.map_comp, hcomp, Module.End.one_eq_id, Submodule.map_id]
      _ ≤ Γ.map (ρ f) := Submodule.map_mono hΓmap_le
  have hΓne : Γ ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    have hmem : ψ u ∈ (⊥ : Submodule k Q) := by
      rw [← hbot]
      exact LinearMap.mem_range.mpr ⟨u, rfl⟩
    have hzero : ψ u = 0 := (Submodule.mem_bot k).mp hmem
    exact hu (hψinj (by rw [hzero, map_zero]))
  have hΓsimple : ∀ V : Submodule k Q, w183b2InvSub ρ (A₁ ⊔ A₂) V → V ≤ Γ →
      V = ⊥ ∨ V = Γ := by
    intro V hVinv hVle
    let V₀ : Submodule k U := V.comap ψ
    have hψnu : ∀ (n : G) (hn : n ∈ A₁ ⊔ A₂) (u : U),
        ψ (w183b2GraphNu hUinv ⟨n, hn⟩ u) = ρ n (ψ u) := by
      intro n hn u
      change (w183b2GraphNu hUinv ⟨n, hn⟩ u : Q) + θ' (w183b2GraphNu hUinv ⟨n, hn⟩ u) =
        ρ n ((u : Q) + θ' u)
      rw [w183b2GraphNu_coe, hθ'nlin n hn u (w183b2GraphNu hUinv ⟨n, hn⟩ u) rfl, map_add]
    have hV₁inv : w183b2InvSub ρ (A₁ ⊔ A₂) (V₀.map U.subtype) := by
      intro n hn w hw
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
      refine Submodule.mem_map.mpr ⟨w183b2GraphNu hUinv ⟨n, hn⟩ u, ?_, ?_⟩
      · rw [show V₀ = V.comap ψ from rfl, Submodule.mem_comap] at hu ⊢
        rw [hψnu n hn u]
        exact hVinv n hn (ψ u) hu
      · exact w183b2GraphNu_coe hUinv ⟨n, hn⟩ u
    rcases hUsimple (V₀.map U.subtype) hV₁inv (Submodule.map_subtype_le U V₀) with hbot | htop
    · left
      have hV₀bot : V₀ = ⊥ := hEmapinj (by rw [hbot, Submodule.map_bot])
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp (hVle hw)
      have huV₀ : u ∈ V₀ := by
        rw [show V₀ = V.comap ψ from rfl, Submodule.mem_comap]
        exact hw
      rw [hV₀bot] at huV₀
      have hu0 : u = 0 := (Submodule.mem_bot k).mp huV₀
      rw [hu0, map_zero]
    · right
      have hV₀top : V₀ = ⊤ := hEmapinj (by rw [htop, Submodule.map_top, Submodule.range_subtype])
      apply le_antisymm hVle
      intro w hw
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
      have huV₀ : u ∈ V₀ := by rw [hV₀top]; exact Submodule.mem_top
      rw [show V₀ = V.comap ψ from rfl, Submodule.mem_comap] at huV₀
      exact huV₀
  exact ⟨Γ, ⟨hΓne, hΓinv, hΓsimple⟩, hΓmap⟩

end CFSG.LocalAnalysis.WeakClosure81

end
