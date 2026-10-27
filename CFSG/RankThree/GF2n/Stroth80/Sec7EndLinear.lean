module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement
open scoped commutatorElement Matrix

section LinearModel

variable {X : Type} [Group X] {A H : Subgroup X}

private theorem endgI_act_act_inv {E : Type} (act : X →* Equiv.Perm E) (g : X) (e : E) :
    act g (act g⁻¹ e) = e := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

private theorem endgI_mul_apply {E : Type} (act : X →* Equiv.Perm E) (x y : X) (e : E) :
    act (x * y) e = act x (act y e) := by
  rw [map_mul, Equiv.Perm.mul_apply]

private theorem endgI_scalar_ne_zero {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {act : X →* Equiv.Perm E} (hinj : Function.Injective ⇑act) {x : X} (hx : x ≠ 1)
    {P : E → E} {c : K} (hc : ∀ e : E, act x e = e + c • P e) : c ≠ 0 := by
  intro h0
  apply hx
  apply hinj
  rw [map_one]
  ext e
  simp [hc e, h0]

private theorem endgI_inv_smul {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {act : X →* Equiv.Perm E} {g : X} {σ : K ≃+* K}
    (hσ : ∀ (c : K) (e : E), act g (c • e) = σ c • act g e) (c : K) (e : E) :
    act g⁻¹ (c • e) = σ.symm c • act g⁻¹ e := by
  apply (act g).injective
  rw [hσ, endgI_act_act_inv act g, endgI_act_act_inv act g, RingEquiv.apply_symm_apply]

private theorem endgI_psi_smul {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {act : X →* Equiv.Perm E} {ψ : E →ₗ[K] E} {g : X} {σ : K ≃+* K}
    (hσ : ∀ (c : K) (e : E), act g (c • e) = σ c • act g e) (k : K) (v : E) :
    act g (ψ (act g⁻¹ (k • v))) = k • act g (ψ (act g⁻¹ v)) := by
  rw [endgI_inv_smul hσ, map_smul, hσ, RingEquiv.apply_symm_apply]

private theorem endgI_conj_form {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {act : X →* Equiv.Perm E} {ψ : E →ₗ[K] E}
    (hadd : ∀ (g : X) (e e' : E), act g (e + e') = act g e + act g e')
    (hA : ∀ a ∈ A, ∃ c : K, ∀ e : E, act a e = e + c • ψ e)
    {g : X} {σ : K ≃+* K} (hσ : ∀ (c : K) (e : E), act g (c • e) = σ c • act g e)
    {x : X} (hx : x ∈ conjSubgroup g A) :
    ∃ c : K, ∀ e : E, act x e = e + c • act g (ψ (act g⁻¹ e)) := by
  rw [mem_conjSubgroup] at hx
  obtain ⟨c, hc⟩ := hA _ hx
  refine ⟨σ c, fun e => ?_⟩
  have hxe : act x = act g * act (g⁻¹ * x * g) * act g⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hxe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc, hadd g, hσ,
    endgI_act_act_inv act g]

private theorem endgI_formula {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {F G P Q : E → E} (hF : ∀ u v : E, F (u + v) = F u + F v) {c d : K}
    (hFc : ∀ w, F w = w + c • P w) (hGd : ∀ w, G w = w + d • Q w)
    (hP : ∀ (k : K) (v : E), P (k • v) = k • P v) (e : E) :
    F (G e) = e + d • Q e + c • P e + (c * d) • P (Q e) := by
  rw [hGd e, hF, hFc e, hFc (d • Q e), hP, smul_smul]
  abel

private theorem endgI_comm_core {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {F G P Q : E → E} (hF : ∀ u v : E, F (u + v) = F u + F v)
    (hG : ∀ u v : E, G (u + v) = G u + G v) {c d : K}
    (hFc : ∀ w, F w = w + c • P w) (hGd : ∀ w, G w = w + d • Q w)
    (hP : ∀ (k : K) (v : E), P (k • v) = k • P v)
    (hQ : ∀ (k : K) (v : E), Q (k • v) = k • Q v)
    (hPQ : ∀ e, P (Q e) = Q (P e)) (e : E) : F (G e) = G (F e) := by
  rw [endgI_formula hF hFc hGd hP e, endgI_formula hG hGd hFc hQ e, hPQ e, mul_comm d c]
  abel

private theorem endgI_comm_necessary {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {F G P Q : E → E} (hF : ∀ u v : E, F (u + v) = F u + F v)
    (hG : ∀ u v : E, G (u + v) = G u + G v) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (hFc : ∀ w, F w = w + c • P w) (hGd : ∀ w, G w = w + d • Q w)
    (hP : ∀ (k : K) (v : E), P (k • v) = k • P v)
    (hQ : ∀ (k : K) (v : E), Q (k • v) = k • Q v)
    (hcomm : ∀ e, F (G e) = G (F e)) : ∀ e, P (Q e) = Q (P e) := by
  intro e
  have h1 := hcomm e
  rw [endgI_formula hF hFc hGd hP e, endgI_formula hG hGd hFc hQ e, mul_comm d c] at h1
  have h2 : e + d • Q e + c • P e = e + c • P e + d • Q e := by abel
  rw [h2] at h1
  exact smul_right_injective E (mul_ne_zero hc hd) (add_left_cancel h1)

theorem endg_commAll_of_linModel (hL : EndLinModel X H A) : CommAllOf A := by
  obtain ⟨K, instK, E, instE, instM, act, ψ, hinj, hadd, hsemi, -, hA⟩ := hL.out
  intro g h x hx hx1 y hy hy1 hxy x' hx' y' hy'
  obtain ⟨σg, hσg⟩ := hsemi g
  obtain ⟨σh, hσh⟩ := hsemi h
  obtain ⟨c, hc⟩ := endgI_conj_form hadd hA hσg hx
  obtain ⟨d, hd⟩ := endgI_conj_form hadd hA hσh hy
  obtain ⟨c', hc'⟩ := endgI_conj_form hadd hA hσg hx'
  obtain ⟨d', hd'⟩ := endgI_conj_form hadd hA hσh hy'
  have hc0 : c ≠ 0 := endgI_scalar_ne_zero hinj hx1 hc
  have hd0 : d ≠ 0 := endgI_scalar_ne_zero hinj hy1 hd
  have hPg := endgI_psi_smul (ψ := ψ) hσg
  have hPh := endgI_psi_smul (ψ := ψ) hσh
  have hxy' : ∀ e, act x (act y e) = act y (act x e) := by
    intro e
    rw [← endgI_mul_apply act x y e, ← endgI_mul_apply act y x e, hxy]
  have hPQ := endgI_comm_necessary (F := ⇑(act x)) (G := ⇑(act y)) (hadd x) (hadd y)
    hc0 hd0 hc hd hPg hPh hxy'
  apply hinj
  ext e
  rw [endgI_mul_apply act x' y' e, endgI_mul_apply act y' x' e]
  exact endgI_comm_core (hadd x') (hadd y') hc' hd' hPg hPh hPQ e

theorem endg_centOne_of_linModel (hL : EndLinModel X H A) : CentOneOf H A := by
  obtain ⟨K, instK, E, instE, instM, act, ψ, hinj, hadd, -, hlin, hA⟩ := hL.out
  intro h hh a ha ha1 hha b hb
  obtain ⟨c₀, hc₀⟩ := hA a ha
  obtain ⟨c, hc⟩ := hA b hb
  have hc0 : c₀ ≠ 0 := endgI_scalar_ne_zero hinj ha1 hc₀
  have hcomm : ∀ e : E, act h (ψ e) = ψ (act h e) := by
    intro e
    have h1 : act h (act a e) = act a (act h e) := by
      rw [← endgI_mul_apply act h a e, ← endgI_mul_apply act a h e, hha]
    rw [hc₀ e, hc₀ (act h e), hadd h, hlin h hh] at h1
    exact smul_right_injective E hc0 (add_left_cancel h1)
  apply hinj
  ext e
  rw [endgI_mul_apply act h b e, endgI_mul_apply act b h e, hc e, hc (act h e), hadd h,
    hlin h hh, hcomm e]

end LinearModel

theorem endg_schur {K K' ι E Γ : Type} [Field K] [Field K'] [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module K E] [Group Γ]
    {Xcl : Subgroup (GL ι K')} (hcomm : AddCommutantScalar Xcl)
    (P : Submodule K E) (θ : K ≃+* K') (Ψ : ↥P ≃+ (ι → K'))
    (hΨ : ∀ (c : K) (w : ↥P), Ψ (c • w) = θ c • Ψ w)
    (π : Γ →* GL ι K') (hπ : π.range = Xcl) (S : Γ → E → E)
    (hSP : ∀ (x : Γ) (w : E), w ∈ P → S x w ∈ P)
    (hSΨ : ∀ (x : Γ) (w : ↥P), Ψ ⟨S x w, hSP x w w.2⟩ = (π x : Matrix ι ι K') *ᵥ Ψ w)
    (ψ φ : E →ₗ[K] E) (hψ : LinearMap.range ψ = P) (hker : LinearMap.ker ψ ≤ LinearMap.ker φ)
    (hφ : LinearMap.range φ ≤ P)
    (hψS : ∀ x e, ψ (S x e) = S x (ψ e)) (hφS : ∀ x e, φ (S x e) = S x (φ e)) :
    ∃ c : K, ∀ e, φ e = c • ψ e := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : E →ₗ[K] ↥P, ∀ e, (ψ' e : E) = ψ e :=
    ⟨ψ.codRestrict P (fun e => by rw [← hψ]; exact LinearMap.mem_range_self ψ e),
      fun e => rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : E →ₗ[K] ↥P, ∀ e, (φ' e : E) = φ e :=
    ⟨φ.codRestrict P (fun e => hφ (LinearMap.mem_range_self φ e)), fun e => rfl⟩
  have hex : ∀ w : ↥P, ∃ e : E, ψ' e = w := by
    intro w
    have hw : (w : E) ∈ LinearMap.range ψ := by
      rw [hψ]
      exact w.2
    obtain ⟨e, he⟩ := LinearMap.mem_range.1 hw
    exact ⟨e, Subtype.ext ((hψ' e).trans he)⟩
  have hsurj : LinearMap.range ψ' = ⊤ := LinearMap.range_eq_top.2 hex
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective ψ' hsurj
  have hs' : ∀ w : ↥P, ψ' (s w) = w := fun w => DFunLike.congr_fun hs w
  have hkey : ∀ e : E, φ' (s (ψ' e)) = φ' e := by
    intro e
    have h1 : ψ (s (ψ' e)) = ψ e := by
      have h2 := congrArg Subtype.val (hs' (ψ' e))
      exact (hψ' (s (ψ' e))).symm.trans (h2.trans (hψ' e))
    have h3 : s (ψ' e) - e ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_sub, h1, sub_self]
    have h4 : φ (s (ψ' e)) = φ e := by
      have h5 := LinearMap.mem_ker.1 (hker h3)
      rw [map_sub] at h5
      exact sub_eq_zero.mp h5
    exact Subtype.ext ((hφ' (s (ψ' e))).trans (h4.trans (hφ' e).symm))
  obtain ⟨g0, hg0⟩ : ∃ g0 : ↥P →ₗ[K] ↥P, ∀ e, g0 (ψ' e) = φ' e :=
    ⟨φ'.comp s, fun e => hkey e⟩
  obtain ⟨g, hg⟩ : ∃ g : (ι → K') →+ (ι → K'), ∀ v, g v = Ψ (g0 (Ψ.symm v)) :=
    ⟨Ψ.toAddMonoidHom.comp (g0.toAddMonoidHom.comp Ψ.symm.toAddMonoidHom), fun v => rfl⟩
  have hgc : ∀ A ∈ Xcl, ∀ v : ι → K',
      g ((A : Matrix ι ι K') *ᵥ v) = (A : Matrix ι ι K') *ᵥ g v := by
    intro A hA v
    have hA' : A ∈ π.range := by
      rw [hπ]
      exact hA
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hA'
    obtain ⟨w, rfl⟩ : ∃ w : ↥P, Ψ w = v := ⟨Ψ.symm v, Ψ.apply_symm_apply v⟩
    obtain ⟨e, he⟩ := hex w
    have hpe : ψ' (S x e) = ⟨S x w, hSP x w w.2⟩ := by
      apply Subtype.ext
      exact (hψ' (S x e)).trans ((hψS x e).trans
        (congrArg (S x) ((hψ' e).symm.trans (congrArg Subtype.val he))))
    have h3 : g0 ⟨S x w, hSP x w w.2⟩ = φ' (S x e) := by
      rw [← hpe]
      exact hg0 (S x e)
    have h4 : φ' (S x e) = ⟨S x (φ' e : E), hSP x (φ' e : E) (φ' e).2⟩ := by
      apply Subtype.ext
      exact (hφ' (S x e)).trans ((hφS x e).trans (congrArg (S x) (hφ' e).symm))
    have h5 : Ψ (φ' (S x e)) = (π x : Matrix ι ι K') *ᵥ Ψ (φ' e) := by
      rw [h4, hSΨ x (φ' e)]
    have h7 : g0 w = φ' e := by
      rw [← he]
      exact hg0 e
    rw [hg, hg, (hSΨ x w).symm, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
      h3, h5, h7]
  obtain ⟨c', hc'⟩ := hcomm g hgc
  have hpoint : ∀ w : ↥P, g0 w = θ.symm c' • w := by
    intro w
    apply Ψ.injective
    rw [hΨ, RingEquiv.apply_symm_apply]
    have h8 := hc' (Ψ w)
    rw [hg, AddEquiv.symm_apply_apply] at h8
    exact h8
  refine ⟨θ.symm c', fun e => ?_⟩
  calc φ e = ((φ' e : ↥P) : E) := (hφ' e).symm
    _ = ((g0 (ψ' e) : ↥P) : E) := by rw [hg0 e]
    _ = ((θ.symm c' • ψ' e : ↥P) : E) := by rw [hpoint (ψ' e)]
    _ = θ.symm c' • ψ e := by rw [Submodule.coe_smul, hψ' e]

end CFSG.RankThree.GF2n.Stroth80
