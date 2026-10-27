module

public import CFSG.Quasithin.Background.SmithB45Alt7Res
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57E7
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
  CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.B42A57

@[expose] def permL (σ : Perm (Fin 7)) : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (σ⁻¹ : Perm (Fin 7))

theorem permL_apply (σ : Perm (Fin 7)) (x : Fin 7 → ZMod 2) (i : Fin 7) :
    permL σ x i = x (σ⁻¹ i) := rfl

theorem permL_single (σ : Perm (Fin 7)) (k : Fin 7) :
    permL σ (Pi.single k 1) = Pi.single (σ k) 1 := by
  funext i
  rw [permL_apply]
  by_cases h : i = σ k
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    apply h
    rw [← h']
    simp

theorem permL_mul (σ τ : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permL (σ * τ) x = permL σ (permL τ x) := by
  funext i
  simp [permL_apply, mul_inv_rev]

theorem permL_one (x : Fin 7 → ZMod 2) : permL 1 x = x := by
  funext i
  simp [permL_apply]

section Triv

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

@[expose] noncomputable def phiT (v : Additive V) : (Fin 7 → ZMod 2) →ₗ[ZMod 2] Additive V :=
  Fintype.linearCombination (ZMod 2) (fun k => rho7 ι (tk k) v)

theorem phiT_single (v : Additive V) (k : Fin 7) :
    phiT ι v (Pi.single k 1) = rho7 ι (tk k) v := by
  unfold phiT
  rw [Fintype.linearCombination_apply_single, one_smul]

theorem fixed_of_gen {v : Additive V} (hv : ∀ b, sigma6 ι (gen b) v = v) (τ : S6) :
    sigma6 ι τ v = v := by
  let T : Subgroup S6 :=
    { carrier := {g | sigma6 ι g v = v}
      mul_mem' := fun {a b} ha hb => by
        change sigma6 ι (a * b) v = v
        rw [map_mul, LinearEquiv.mul_apply]
        rw [show sigma6 ι b v = v from hb]
        exact ha
      one_mem' := by
        change sigma6 ι 1 v = v
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha => by
        change sigma6 ι a⁻¹ v = v
        have ha' : sigma6 ι a v = v := ha
        calc sigma6 ι a⁻¹ v = sigma6 ι a⁻¹ (sigma6 ι a v) := by rw [ha']
          _ = v := ρ_inv_apply _ a v }
  have hT : (⊤ : Subgroup S6) ≤ T := by
    rw [← closure_xy, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hv false
    · exact hv true
  exact hT (Subgroup.mem_top τ)

theorem phiT_gen {v : Additive V} (hv : ∀ τ : S6, sigma6 ι τ v = v) (b : Bool)
    (x : Fin 7 → ZMod 2) :
    phiT ι v (permL (gen7 b) x) = rho7 ι (gen7 b) (phiT ι v x) := by
  have key : (phiT ι v).comp (permL (gen7 b)) =
      ((rho7 ι (gen7 b) : Additive V ≃ₗ[ZMod 2] Additive V) :
        Additive V →ₗ[ZMod 2] Additive V).comp (phiT ι v) := by
    apply linearMap_ext_basis (d := 7)
    intro k
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [permL_single, phiT_single, phiT_single, ← LinearEquiv.mul_apply, ← map_mul]
    have h1 : gen7 b * tk k = tk ((gen7 b : Perm (Fin 7)) k) * j6 (evalG (cosW b k.val)) :=
      Subtype.ext (coset_rel b k)
    rw [h1, map_mul, LinearEquiv.mul_apply]
    rw [show rho7 ι (j6 (evalG (cosW b k.val))) v = v from hv _]
  exact LinearMap.congr_fun key x

theorem phiT_permL {v : Additive V} (hv : ∀ τ : S6, sigma6 ι τ v = v) (γ : A7)
    (x : Fin 7 → ZMod 2) :
    phiT ι v (permL γ x) = rho7 ι γ (phiT ι v x) := by
  let T : Subgroup A7 :=
    { carrier := {g | ∀ x, phiT ι v (permL g x) = rho7 ι g (phiT ι v x)}
      mul_mem' := fun {a b} ha hb x => by
        change phiT ι v (permL ((a : Perm (Fin 7)) * b) x) = rho7 ι (a * b) (phiT ι v x)
        rw [permL_mul, ha, hb, map_mul, LinearEquiv.mul_apply]
      one_mem' := fun x => by
        change phiT ι v (permL 1 x) = rho7 ι 1 (phiT ι v x)
        rw [permL_one, map_one]
        rfl
      inv_mem' := fun {a} ha x => by
        change phiT ι v (permL ((a : Perm (Fin 7))⁻¹) x) = rho7 ι a⁻¹ (phiT ι v x)
        have h1 := ha (permL ((a : Perm (Fin 7))⁻¹) x)
        rw [← permL_mul, mul_inv_cancel, permL_one] at h1
        rw [h1, ρ_inv_apply] }
  have hT : (⊤ : Subgroup A7) ≤ T := by
    rw [← closure_gen7, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact phiT_gen ι hv b
  exact hT (Subgroup.mem_top γ) x

theorem tk_six : tk 6 = 1 := Subtype.ext (by decide +kernel)

@[expose] def pv (a b : Fin 7) : Fin 7 → ZMod 2 := Pi.single a 1 + Pi.single b 1

theorem pv_mem_coreMod (a b : Fin 7) :
    (Multiplicative.ofAdd (pv a b) : G6.PermMod 7) ∈ G6.coreMod 7 := by
  rw [G6.mem_coreMod]
  revert a b
  decide +kernel

theorem exists_coreEquiv (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hfix : fixV L = ⊥) {v : Additive V} (hv0 : v ≠ 0) (hv : ∀ b, sigma6 ι (gen b) v = v) :
    ∃ β : V ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : V),
      (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) = G6.permAct 7 (γ : Perm (Fin 7)) (β s) := by
  classical
  have hvA := fixed_of_gen ι hv
  let Φ : G6.PermMod 7 →* V := (MulEquiv.multiplicativeAdditive V).toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (phiT ι v).toAddMonoidHom)
  have hΦ : ∀ x, Φ x = Additive.toMul (phiT ι v (Multiplicative.toAdd x)) := fun x => rfl
  have hΦeq : ∀ (γ : A7) (x : G6.PermMod 7),
      Φ (G6.permAct 7 (γ : Perm (Fin 7)) x) = (ι.symm γ : MulAut V) (Φ x) := by
    intro γ x
    rw [hΦ, hΦ]
    have h1 : Multiplicative.toAdd (G6.permAct 7 (γ : Perm (Fin 7)) x) =
        permL γ (Multiplicative.toAdd x) := rfl
    rw [h1, phiT_permL ι hvA, rho7_apply]
    rfl
  let K : Subgroup (G6.PermMod 7) :=
    { carrier := {x | x ∈ G6.coreMod 7 ∧ Φ x = 1}
      one_mem' := ⟨(G6.coreMod 7).one_mem, map_one Φ⟩
      mul_mem' := fun ha hb => ⟨(G6.coreMod 7).mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2,
        one_mul]⟩
      inv_mem' := fun ha => ⟨(G6.coreMod 7).inv_mem ha.1, by rw [map_inv, ha.2, inv_one]⟩ }
  have hKle : K ≤ G6.coreMod 7 := fun x hx => hx.1
  have hKinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ K, G6.permAct 7 σ u ∈ K := by
    intro σ hσ u hu
    refine ⟨G6.permAct_mem_coreMod σ hu.1, ?_⟩
    have := hΦeq ⟨σ, hσ⟩ u
    rw [this, hu.2, map_one]
  have hK : K = ⊥ := by
    rcases coreMod7_irreducible K hKle hKinv with h | h
    · exact h
    · exfalso
      have hpair : ∀ k : Fin 7, phiT ι v (Pi.single k 1) = v := by
        intro k
        have hmem : (Multiplicative.ofAdd (pv 6 k) : G6.PermMod 7) ∈ K := by
          rw [h]
          exact pv_mem_coreMod 6 k
        have h2 : phiT ι v (pv 6 k) = 0 := by
          have := hmem.2
          rw [hΦ] at this
          exact this
        unfold pv at h2
        rw [map_add, phiT_single, tk_six, map_one] at h2
        have h3 : (1 : Additive V ≃ₗ[ZMod 2] Additive V) v = v := rfl
        rw [h3] at h2
        have h4 : v + phiT ι v (Pi.single k 1) = 0 := h2
        have h5 : ∀ w : Additive V, w + w = 0 := fun w => by
          rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
        calc phiT ι v (Pi.single k 1) = v + (v + phiT ι v (Pi.single k 1)) := by
              rw [← add_assoc, h5, zero_add]
          _ = v := by rw [h4, add_zero]
      have hfixv : Additive.toMul v ∈ fixV L := by
        intro l hl
        have h1 := phiT_permL ι hvA (ι ⟨l, hl⟩) (Pi.single 6 1)
        rw [permL_single, hpair, hpair, rho7_apply, MulEquiv.symm_apply_apply] at h1
        exact (congrArg Additive.toMul h1).symm
      rw [hfix, Subgroup.mem_bot] at hfixv
      exact hv0 hfixv
  have hinj : ∀ x ∈ G6.coreMod 7, ∀ y ∈ G6.coreMod 7, Φ x = Φ y → x = y := by
    intro x hx y hy hxy
    have hmem : x / y ∈ K := ⟨(G6.coreMod 7).div_mem hx hy, by
      rw [map_div, hxy, div_self']⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact div_eq_one.1 hmem
  let J : Subgroup V := (G6.coreMod 7).map Φ
  have hJinv : ∀ l ∈ L, ∀ w ∈ J, l w ∈ J := by
    rintro l hl _ ⟨x, hx, rfl⟩
    refine ⟨G6.permAct 7 ((ι ⟨l, hl⟩ : A7) : Perm (Fin 7)) x,
      G6.permAct_mem_coreMod _ hx, ?_⟩
    rw [hΦeq, MulEquiv.symm_apply_apply]
  have hJ : J = ⊤ := by
    rcases hirr J hJinv with h | h
    · exfalso
      have hmem : Φ (Multiplicative.ofAdd (pv 0 1)) ∈ J :=
        ⟨_, pv_mem_coreMod 0 1, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h1 := hinj _ (pv_mem_coreMod 0 1) 1 (G6.coreMod 7).one_mem
        (by rw [hmem, map_one])
      have h2 : pv 0 1 = 0 := congrArg Multiplicative.toAdd h1
      have h3 := congrFun h2 0
      simp [pv] at h3
    · exact h
  let f : ↥(G6.coreMod 7) → V := fun x => Φ x
  have hfb : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hinj x x.2 y y.2 h), fun w => ?_⟩
    have hw : w ∈ J := by rw [hJ]; trivial
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : ↥(G6.coreMod 7) ≃* V :=
    MulEquiv.ofBijective ((Φ.comp (G6.coreMod 7).subtype)) hfb
  refine ⟨e.symm, fun γ s => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective s
  rw [MulEquiv.symm_apply_apply]
  have h1 : (ι.symm γ : MulAut V) (e x) = e ⟨G6.permAct 7 (γ : Perm (Fin 7)) x,
      G6.permAct_mem_coreMod _ x.2⟩ := by
    change (ι.symm γ : MulAut V) (Φ x) = Φ (G6.permAct 7 (γ : Perm (Fin 7)) x)
    rw [hΦeq]
  rw [h1, MulEquiv.symm_apply_apply]

end Triv

end CFSG.Quasithin.B45Alt7
