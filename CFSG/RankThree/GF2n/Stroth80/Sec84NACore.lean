module

public import CFSG.RankThree.GF2n.Stroth80.Sec84NACommCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Conj

variable (K : Type) [Field K] {X : Type} [AddCommGroup X] [Module K X] {Γ : Type} [Group Γ]
  [DistribMulAction Γ X] [SMulCommClass Γ K X]

abbrev naActConj (g : Γ) : Module.End K X ≃ₐ[K] Module.End K X :=
  (DistribMulAction.toLinearEquiv K X g).conjAlgEquiv K

theorem naActConj_apply_apply (g : Γ) (c : Module.End K X) (x : X) :
    naActConj K g c x = g • c (g⁻¹ • x) := by
  simp [naActConj, LinearEquiv.conjAlgEquiv_apply, DistribMulAction.toLinearEquiv]

theorem naActConj_mul (g h : Γ) (c : Module.End K X) :
    naActConj K (g * h) c = naActConj K g (naActConj K h c) := by
  ext x
  simp [naActConj_apply_apply, mul_smul, mul_inv_rev]

theorem naActConj_one (c : Module.End K X) : naActConj K (1 : Γ) c = c := by
  ext x
  simp [naActConj_apply_apply]

end Conj

section NACore

variable {K : Type} [Field K] [Finite K] {Γ : Type} [Group Γ]
  {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction Γ N]
  {U : Type} [AddCommGroup U] [Module K U] [DistribMulAction Γ U]
  {X : Type} [AddCommGroup X] [Module K X] [Module.Finite K X] [DistribMulAction Γ X]
  [SMulCommClass Γ K X]

theorem naOperators_comm [Nontrivial N]
    (ω : X →ₗ[K] X →ₗ[K] K) (hω_nd : ∀ x, (∀ y, ω x y = 0) → x = 0)
    (hω_symm : ∀ x y, ω x y = ω y x)
    (a : N →+ (U →ₗ[K] X)) (ha : ∀ (g : Γ) n u, a (g • n) (g • u) = g • a n u)
    (u₀ : U) (hu₀ : ∀ (g : Γ) (n : N), a n (g • u₀) = a n u₀)
    (hsym : ∀ n n' u u', ω (a n' u) (a n u') = ω (a n u) (a n' u'))
    (hτ : Function.Bijective (fun n : N => a n u₀))
    (hNirr : ∀ S : AddSubgroup N, (∀ g : Γ, ∀ n ∈ S, g • n ∈ S) → S = ⊥ ∨ S = ⊤)
    (hperm : ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ Module.finrank K X →
      ∀ h : Γ →* Equiv.Perm ι, (∀ g : Γ, (∀ x : X, g • x = x) → h g = 1) → h = 1)
    (hab : ∀ (C : Type) [Group C] [IsCyclic C] (h : Γ →* C),
      (∀ g : Γ, (∀ x : X, g • x = x) → h g = 1) → h = 1) :
    ∀ (g : Γ) (n : N) (u : U), a (g • n) u = g • a n u := by
  classical
  haveI : Finite X := Module.finite_of_finite K
  let τ₀ : N →+ X :=
    { toFun := fun n => a n u₀, map_zero' := by simp, map_add' := fun n n' => by simp }
  let τ : N ≃+ X := AddEquiv.ofBijective τ₀ hτ
  have hτg : ∀ (g : Γ) (n : N), τ (g • n) = g • τ n := fun g n => by
    show a (g • n) u₀ = g • a n u₀
    rw [← hu₀ g (g • n)]
    exact ha g n u₀
  have hτsymm : ∀ (g : Γ) (x : X), τ.symm (g • x) = g • τ.symm x := fun g x => by
    apply τ.injective
    rw [AddEquiv.apply_symm_apply, hτg, AddEquiv.apply_symm_apply]
  let Bf : U → X → X := fun u x => a (τ.symm x) u
  have hBadd : ∀ u x y, Bf u (x + y) = Bf u x + Bf u y := fun u x y => by
    simp [Bf]
  have hBuadd : ∀ u u' x, Bf (u + u') x = Bf u x + Bf u' x := fun u u' x => by
    simp [Bf]
  have hBusmul : ∀ (c : K) u x, Bf (c • u) x = c • Bf u x := fun c u x => by
    simp [Bf]
  have hB0 : ∀ x, Bf u₀ x = x := fun x => by
    show a (τ.symm x) u₀ = x
    exact τ.apply_symm_apply x
  have hBg : ∀ (g : Γ) u x, Bf (g • u) (g • x) = g • Bf u x := fun g u x => by
    show a (τ.symm (g • x)) (g • u) = g • a (τ.symm x) u
    rw [hτsymm, ha]
  have hBsym : ∀ u u' x x', ω (Bf u x') (Bf u' x) = ω (Bf u x) (Bf u' x') := fun u u' x x' =>
    hsym (τ.symm x) (τ.symm x') u u'
  have hBadj : ∀ u x x', ω (Bf u x') x = ω x' (Bf u x) := fun u x x' => by
    have h1 := hBsym u u₀ x x'
    rw [hB0, hB0] at h1
    rw [h1, hω_symm]
  have hBcomm : ∀ u u' x, Bf u' (Bf u x) = Bf u (Bf u' x) := by
    intro u u' x'
    have h0 : ∀ x, ω (Bf u' (Bf u x') - Bf u (Bf u' x')) x = 0 := by
      intro x
      rw [map_sub, LinearMap.sub_apply, hBadj u' x (Bf u x'), hBadj u x (Bf u' x')]
      rw [hBsym u u' x x', hω_symm (Bf u x) (Bf u' x'), sub_self]
    exact sub_eq_zero.mp (hω_nd _ h0)
  have hBsmul : ∀ u (c : K) x, Bf u (c • x) = c • Bf u x := by
    intro u c x
    have h1 : Bf (c • u₀) x = c • x := by rw [hBusmul, hB0]
    calc Bf u (c • x) = Bf u (Bf (c • u₀) x) := by rw [h1]
      _ = Bf (c • u₀) (Bf u x) := hBcomm (c • u₀) u x
      _ = c • Bf u x := by rw [hBusmul, hB0]
  let B : U → Module.End K X := fun u =>
    { toFun := Bf u, map_add' := hBadd u, map_smul' := fun c x => hBsmul u c x }
  have hBapp : ∀ u x, B u x = Bf u x := fun u x => rfl
  have hBcommute : (Set.range B).Pairwise Commute := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩ _
    ext x
    simp only [Module.End.mul_apply, hBapp]
    exact hBcomm u' u x
  let 𝒞 : Subalgebra K (Module.End K X) := Algebra.adjoin K (Set.range B)
  letI : CommRing 𝒞 := Algebra.adjoinCommRingOfComm K hBcommute
  have hBmem : ∀ u, B u ∈ 𝒞 := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  have hconjB : ∀ (g : Γ) u, naActConj K g (B u) = B (g • u) := by
    intro g u
    ext x
    rw [naActConj_apply_apply]
    simp only [hBapp]
    have := hBg g u (g⁻¹ • x)
    rw [smul_inv_smul] at this
    exact this.symm
  have hconjmem : ∀ (g : Γ) (c : Module.End K X), c ∈ 𝒞 → naActConj K g c ∈ 𝒞 := by
    intro g c hc
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hconjB]
      exact hBmem _
    | algebraMap r =>
      rw [AlgEquiv.commutes]
      exact 𝒞.algebraMap_mem r
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact 𝒞.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact 𝒞.mul_mem ihx ihy
  let σh : Γ → ↥𝒞 →ₐ[K] ↥𝒞 := fun g =>
    ((naActConj K g).toAlgHom.comp 𝒞.val).codRestrict 𝒞 (fun c => hconjmem g c c.2)
  have hσh : ∀ (g : Γ) (c : ↥𝒞), ((σh g c : ↥𝒞) : Module.End K X) = naActConj K g c :=
    fun g c => rfl
  let σe : Γ → (↥𝒞 ≃ₐ[K] ↥𝒞) := fun g =>
    AlgEquiv.ofAlgHom (σh g) (σh g⁻¹)
      (AlgHom.ext fun c => Subtype.ext (by
        rw [AlgHom.comp_apply, hσh, hσh, ← naActConj_mul, mul_inv_cancel, naActConj_one]; rfl))
      (AlgHom.ext fun c => Subtype.ext (by
        rw [AlgHom.comp_apply, hσh, hσh, ← naActConj_mul, inv_mul_cancel, naActConj_one]; rfl))
  have hσe : ∀ (g : Γ) (c : ↥𝒞), ((σe g c : ↥𝒞) : Module.End K X) = naActConj K g c :=
    fun g c => rfl
  let σ : Γ →* (↥𝒞 ≃ₐ[K] ↥𝒞) := MonoidHom.mk' σe (fun g h => AlgEquiv.ext fun c => Subtype.ext (by
    rw [AlgEquiv.mul_apply]
    show ((σe (g * h) c : ↥𝒞) : Module.End K X) = ((σe g (σe h c) : ↥𝒞) : Module.End K X)
    rw [hσe, hσe, hσe, naActConj_mul]))
  haveI : Nontrivial X := τ.toEquiv.symm.nontrivial
  haveI : Finite (Module.End K X) :=
    Finite.of_injective (fun f : Module.End K X => (f : X → X)) DFunLike.coe_injective
  haveI : Finite ↥𝒞 := inferInstance
  let ρ : Γ →* (X ≃ₗ[K] X) := DistribMulAction.toModuleAut K X
  have hcomp : ∀ (g : Γ) (c : ↥𝒞) (x : X), ρ g (c • x) = σ g c • ρ g x := by
    intro g c x
    show g • (c : Module.End K X) x = ((σe g c : ↥𝒞) : Module.End K X) (g • x)
    rw [hσe, naActConj_apply_apply, inv_smul_smul]
  have hirr : ∀ S : Submodule K X, (∀ g : Γ, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    let S' : AddSubgroup N := S.toAddSubgroup.comap τ.toAddMonoidHom
    have hS' : ∀ g : Γ, ∀ n ∈ S', g • n ∈ S' := by
      intro g n hn
      show τ (g • n) ∈ S
      rw [hτg]
      exact hS g _ hn
    rcases hNirr S' hS' with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : τ.symm x ∈ S' := by
        show τ (τ.symm x) ∈ S
        rw [AddEquiv.apply_symm_apply]
        exact hx
      rw [h] at this
      have h0 : τ.symm x = 0 := this
      have : x = 0 := by rw [← τ.apply_symm_apply x, h0, map_zero]
      rw [this]
      exact Submodule.zero_mem ⊥
    · right
      rw [eq_top_iff]
      intro x _
      have : τ.symm x ∈ S' := by rw [h]; trivial
      have h1 : τ (τ.symm x) ∈ S := this
      rwa [AddEquiv.apply_symm_apply] at h1
  have hfaith : ∀ c : ↥𝒞, (∀ x : X, c • x = 0) → c = 0 := fun c h =>
    Subtype.ext (LinearMap.ext fun x => h x)
  have htriv := commCore_trivial ρ σ hcomp hirr hfaith
    (fun ι _ hι h hh => hperm ι hι h (fun g hg => hh g (by
      refine LinearEquiv.ext fun x => ?_
      simpa [ρ] using hg x)))
    (fun C _ _ h hh => hab C h (fun g hg => hh g (by
      refine LinearEquiv.ext fun x => ?_
      simpa [ρ] using hg x)))
  have hBinv : ∀ (g : Γ) u, B (g • u) = B u := by
    intro g u
    have h1 : σe g ⟨B u, hBmem u⟩ = ⟨B u, hBmem u⟩ :=
      DFunLike.congr_fun (htriv g) ⟨B u, hBmem u⟩
    have h2 : naActConj K g (B u) = B u := by
      have := congrArg Subtype.val h1
      rw [hσe] at this
      exact this
    rw [← hconjB]
    exact h2
  intro g n u
  have h1 : a (g • n) u = Bf u (τ (g • n)) := by
    show a (g • n) u = a (τ.symm (τ (g • n))) u
    rw [AddEquiv.symm_apply_apply]
  rw [h1, hτg]
  have h2 : Bf (g • u) (g • τ n) = Bf u (g • τ n) := by
    have := congrArg (fun f : Module.End K X => f (g • τ n)) (hBinv g u)
    exact this
  rw [← h2, hBg]
  show g • a (τ.symm (τ n)) u = g • a n u
  rw [AddEquiv.symm_apply_apply]

theorem na_tau_bijective [Nontrivial N]
    (a : N →+ (U →ₗ[K] X)) (ha : ∀ (g : Γ) n u, a (g • n) (g • u) = g • a n u)
    (V₀ : Submodule K U) (hV₀ : ∀ n, ∀ u ∈ V₀, a n u = 0)
    (u₀ : U) (hu₀ : ∀ g : Γ, g • u₀ - u₀ ∈ V₀) (ha0 : a ≠ 0)
    (hcard : Nat.card N = Nat.card X)
    (hNirr : ∀ S : AddSubgroup N, (∀ g : Γ, ∀ n ∈ S, g • n ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnoEmb : ∀ f : N →+ (U →ₗ[K] X), (∀ n, f n u₀ = 0) → (∀ n, ∀ u ∈ V₀, f n u = 0) →
      (∀ (g : Γ) n u, f (g • n) (g • u) = g • f n u) → Function.Injective f → False) :
    Function.Bijective (fun n : N => a n u₀) := by
  classical
  haveI : Finite X := Module.finite_of_finite K
  let τ₀ : N →+ X :=
    { toFun := fun n => a n u₀, map_zero' := by simp, map_add' := fun n n' => by simp }
  have hτg : ∀ (g : Γ) (n : N), τ₀ (g • n) = g • τ₀ n := fun g n => by
    show a (g • n) u₀ = g • a n u₀
    have h1 : a (g • n) (g • u₀) = a (g • n) u₀ := by
      have := hV₀ (g • n) (g • u₀ - u₀) (hu₀ g)
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [← h1]
    exact ha g n u₀
  have hker : τ₀.ker = ⊥ := by
    rcases hNirr τ₀.ker (fun g n hn => by
      rw [AddMonoidHom.mem_ker] at hn ⊢
      rw [hτg, hn, smul_zero]) with h | h
    · exact h
    · exfalso
      have h0 : ∀ n, a n u₀ = 0 := fun n => by
        have : n ∈ τ₀.ker := by rw [h]; trivial
        exact this
      have hkera : a.ker = ⊥ := by
        rcases hNirr a.ker (fun g n hn => by
          rw [AddMonoidHom.mem_ker] at hn ⊢
          ext u
          have := ha g n (g⁻¹ • u)
          rw [smul_inv_smul, hn] at this
          simpa using this) with h' | h'
        · exact h'
        · exfalso
          apply ha0
          ext n u
          have : n ∈ a.ker := by rw [h']; trivial
          have := LinearMap.congr_fun (AddMonoidHom.mem_ker.mp this) u
          simpa using this
      exact hnoEmb a h0 hV₀ ha ((AddMonoidHom.ker_eq_bot_iff a).mp hkera)
  have hinj : Function.Injective τ₀ := (AddMonoidHom.ker_eq_bot_iff τ₀).mp hker
  exact Function.Injective.bijective_of_nat_card_le hinj hcard.ge

theorem na_split [Nontrivial N] [SMulCommClass Γ K U]
    (a : N →+ (U →ₗ[K] X)) (ha : ∀ (g : Γ) n u, a (g • n) (g • u) = g • a n u)
    (hcomm : ∀ (g : Γ) n u, a (g • n) u = g • a n u)
    (V₀ : Submodule K U) (hV₀inv : ∀ (g : Γ), ∀ u ∈ V₀, g • u ∈ V₀)
    (hV₀ : ∀ n, ∀ u ∈ V₀, a n u = 0)
    (u₀ : U) (hu₀ : ∀ g : Γ, g • u₀ - u₀ ∈ V₀)
    (hτ : Function.Bijective (fun n : N => a n u₀))
    (hUirr : ∀ S : Submodule K U, (∀ g : Γ, ∀ u ∈ S, g • u ∈ S) →
      V₀ ⊔ Submodule.span K {u₀} ≤ S → S = V₀ ⊔ Submodule.span K {u₀} ∨ S = ⊤)
    (hUnt : ∃ (g : Γ) (u : U), g • u - u ∉ V₀ ⊔ Submodule.span K {u₀}) :
    ∃ P : Submodule K U, (∀ g : Γ, ∀ u ∈ P, g • u ∈ P) ∧ V₀ ≤ P ∧
      P ⊔ Submodule.span K {u₀} = ⊤ ∧ P ⊓ Submodule.span K {u₀} ≤ V₀ ∧
      ∀ n, ∀ u ∈ P, a n u = 0 := by
  classical
  let P : Submodule K U := V₀ ⊔ Submodule.span K {w | ∃ (g : Γ) (u : U), w = g • u - u}
  have hspaninv : ∀ g' : Γ, ∀ w ∈ Submodule.span K {w | ∃ (g : Γ) (u : U), w = g • u - u},
      g' • w ∈ P := by
    intro g' w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, u, rfl⟩ := hx
      have : g' • (g • u - u) = ((g' * g) • u - u) - (g' • u - u) := by
        rw [smul_sub, mul_smul]; abel
      rw [this]
      exact P.sub_mem (Submodule.mem_sup_right (Submodule.subset_span ⟨g' * g, u, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨g', u, rfl⟩))
    | zero => simp
    | add x y _ _ ihx ihy => rw [smul_add]; exact P.add_mem ihx ihy
    | smul c x _ ihx => rw [smul_comm]; exact P.smul_mem c ihx
  have hPinv : ∀ g : Γ, ∀ u ∈ P, g • u ∈ P := by
    intro g u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    rw [smul_add]
    exact P.add_mem (Submodule.mem_sup_left (hV₀inv g x hx)) (hspaninv g y hy)
  have hspankill : ∀ n, ∀ u ∈ Submodule.span K {w | ∃ (g : Γ) (u : U), w = g • u - u},
      a n u = 0 := by
    intro n w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, u, rfl⟩ := hx
      have e1 := ha g (g⁻¹ • n) u
      have e2 := hcomm g (g⁻¹ • n) u
      rw [smul_inv_smul] at e1 e2
      rw [map_sub, e1, e2, sub_self]
    | zero => simp
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [map_smul, ihx, smul_zero]
  have hPkill : ∀ n, ∀ u ∈ P, a n u = 0 := by
    intro n u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, hV₀ n x hx, hspankill n y hy, add_zero]
  have hVu₀inv : ∀ g : Γ, ∀ u ∈ V₀ ⊔ Submodule.span K {u₀}, g • u ∈ V₀ ⊔ Submodule.span K {u₀} := by
    intro g u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_add, smul_comm]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hV₀inv g x hx)) ?_
    have : c • g • u₀ = c • (g • u₀ - u₀) + c • u₀ := by rw [smul_sub]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (V₀.smul_mem c (hu₀ g)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u₀)))
  have hVP : V₀ ≤ P := le_sup_left
  refine ⟨P, hPinv, hVP, ?_, ?_, hPkill⟩
  ·
    have hS : P ⊔ Submodule.span K {u₀} = ⊤ := by
      rcases hUirr (P ⊔ Submodule.span K {u₀}) (fun g u hu => by
        obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [smul_add, smul_comm]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (hPinv g x hx)) ?_
        have : c • g • u₀ = c • (g • u₀ - u₀) + c • u₀ := by rw [smul_sub]; abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hVP (V₀.smul_mem c (hu₀ g))))
          (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u₀))))
        (sup_le_sup_right hVP _) with h | h
      · exfalso
        obtain ⟨g, u, hgu⟩ := hUnt
        apply hgu
        rw [← h]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨g, u, rfl⟩))
      · exact h
    exact hS
  ·
    intro x hx
    obtain ⟨hxP, hxs⟩ := hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact V₀.zero_mem
    · exfalso
      obtain ⟨n, hn⟩ := exists_ne (0 : N)
      have h1 : a n (c • u₀) = 0 := hPkill n _ hxP
      rw [map_smul] at h1
      have h2 : a n u₀ = 0 := by
        rcases smul_eq_zero.mp h1 with h | h
        · exact absurd h hc
        · exact h
      apply hn
      apply hτ.1
      show a n u₀ = a 0 u₀
      rw [h2, map_zero]
      rfl

end NACore

end CFSG.RankThree.GF2n.Stroth80
