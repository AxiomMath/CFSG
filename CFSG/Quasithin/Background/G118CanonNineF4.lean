module

public import CFSG.Quasithin.Background.G118CanonNineF2Tensor
public import CFSG.Quasithin.Background.G118CanonNineF4Psi
public import CFSG.Quasithin.Background.G118CanonNineF4Nat
public import CFSG.Quasithin.Background.G118CanonNineF4Semi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace Canon

open scoped TensorProduct Matrix

open F2Tensor F4Tensor

section Compat

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem comm_kappa {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (D : E11Data H I) {c : GLV V} (hc : c ∈ Subgroup.centralizer (H : Set (GLV V))) (f : D.F) :
    (c : Module.End (ZMod 2) V) * D.κ f = D.κ f * (c : Module.End (ZMod 2) V) := by
  have hcN : c ∈ Subgroup.normalizer (H : Set (GLV V)) := Subgroup.centralizer_le_normalizer _ hc
  have := D.κ_conj c hcN (RingEquiv.refl D.F) (D.θ ⟨c, hc⟩ : D.U →ₗ[D.F] D.U)
    (D.θ ⟨c, hc⟩).bijective (fun c₁ c₂ h u => ?_) f
  · simpa using this
  · have h' : c₂ * ⟨c, hc⟩ = ⟨c, hc⟩ * c₁ := Subtype.ext h
    have := congrArg (fun z => D.θ z u) h'
    rw [map_mul, map_mul] at this
    exact this

theorem compat_mul {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {C : Subgroup (GLV V)}
    (e : ↥C ≃* Equiv.Perm (Fin 3)) (s : Equiv.Perm (Fin 3) →* GLV V)
    (hs : ∀ π, s π = ((e.symm π : ↥C) : GLV V))
    (ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] W))
    (hψC : ∀ (π : Equiv.Perm (Fin 3)) (x : ↥(CFSG.Quasithin.permCore 3)) (a : W),
      ψ (s π (ψ.symm (x ⊗ₜ a))) = permActCore 3 π x ⊗ₜ a)
    (c : ↥C) (d : GLV V) (a a' : W) (x : ↥(CFSG.Quasithin.permCore 3))
    (hd : ψ (d (ψ.symm (x ⊗ₜ a))) = x ⊗ₜ a') :
    ψ (((c : GLV V) * d) (ψ.symm (x ⊗ₜ a))) = permActCore 3 (e c) x ⊗ₜ a' := by
  have h1 : d (ψ.symm (x ⊗ₜ a)) = ψ.symm (x ⊗ₜ a') := by
    rw [← hd, LinearEquiv.symm_apply_apply]
  have hcs : (c : GLV V) = s (e c) := by
    rw [hs, MulEquiv.symm_apply_apply]
  rw [LinearEquiv.mul_apply, h1, hcs]
  exact hψC (e c) x a'

end Compat

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem f4_nine {Γ H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (D : E11Data H I)
    (hle : H ≤ Γ) (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hd : Module.finrank (ZMod 2) V = 8) (hU : Module.finrank D.F D.U = 2)
    (hF : Nat.card D.F = 4) (φH : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (e : ↥(F2Group.cC Γ H) ≃* Equiv.Perm (Fin 3)) : IsG112Nine Γ := by
  let s : Equiv.Perm (Fin 3) →* GLV V := (F2Group.cC Γ H).subtype.comp e.symm.toMonoidHom
  have hs : ∀ π, s π = ((e.symm π : ↥(F2Group.cC Γ H)) : GLV V) := fun π => rfl
  have hsinj : Function.Injective s := fun a b hab => e.symm.injective (Subtype.ext hab)
  have hsH : ∀ π, ∀ h ∈ H, h * s π = s π * h := fun π h hh =>
    (F2Group.mem_cC.1 (e.symm π).2).2 h hh
  have hc3 : s rho3 ^ 3 = 1 := by rw [← map_pow, rho3_pow_three, map_one]
  have hc1 : s rho3 ≠ 1 := fun h => rho3_ne_one (hsinj (h.trans (map_one s).symm))
  have hy2 : s tau3 * s tau3 = 1 := by rw [← map_mul, tau3_mul_self, map_one]
  have hyc : s tau3 * s rho3 = (s rho3)⁻¹ * s tau3 := by
    rw [← map_inv, ← map_mul, ← map_mul, tau3_rho3]
  have hfree := fixed_eq_zero_s3 D hU hd (hsH rho3) (hsH tau3) hc3 hc1 hy2 hyc
  obtain ⟨hB4, hinf, hsup⟩ := fixSub_s3 hd hc3 hy2 hyc hfree
  have hBH : Invariant H (fixSub (s tau3)) := invariant_fixSub (hsH tau3)
  have hκB : ∀ f : D.F, ∀ b ∈ fixSub (s tau3), D.κ f b ∈ fixSub (s tau3) := by
    intro f b hb
    have hcomm := comm_kappa D (Subgroup.mem_centralizer_iff.2 (hsH tau3)) f
    have h2 := congrArg (fun T : Module.End (ZMod 2) V => T b) hcomm
    have h3 : s tau3 (D.κ f b) = D.κ f (s tau3 b) := h2
    rw [mem_fixSub] at hb ⊢
    rw [h3, hb]
  obtain ⟨α, ι, hι⟩ := exists_natural_B D hU hd hF φH hBH hB4 hκB
  have hdcomm : ∀ (d : ↥(F2Group.cD Γ H)) (c : GLV V), c ∈ F2Group.cC Γ H →
      ∀ v, (d : GLV V) (c v) = c ((d : GLV V) v) := by
    intro d c hc v
    have h := (F2Group.mem_cD.1 d.2).2 c hc
    exact (congrArg (fun g : GLV V => g v) h).symm
  have hγ : ∀ γ : ↥Γ, (γ : GLV V) = ((F2Group.eΓ hN hle e γ).1 : GLV V) *
      ((F2Group.eΓ hN hle e γ).2 : GLV V) := fun γ => (F2Group.eΓ_prod hN hle e γ).symm
  rcases F2Group.card_cD_cases hN hle e φH G118.autA5Input with h60 | h120
  ·
    obtain ⟨ψ, hψC, hψD⟩ := exists_psi s hc3 hfree hyc hinf hsup ι
    let eDH : ↥(F2Group.cD Γ H) ≃* ↥H :=
      MulEquiv.subgroupCongr (F2Group.eq_of_card_sixty hle φH h60).symm
    have hact : ∀ (d : ↥(F2Group.cD Γ H)) (b : Fin 2 → GaloisField 2 2),
        (d : GLV V) ((ι.symm b : ↥(fixSub (s tau3))) : V) =
          ((ι.symm (((α (eDH d) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ b) : ↥(fixSub (s tau3))) : V) := by
      intro d b
      have h1 := hι (eDH d) (ι.symm b)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : restrictHom H (fixSub (s tau3)) hBH (eDH d) (ι.symm b) =
          ι.symm (((α (eDH d) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ b) := by
        rw [← h1, LinearEquiv.symm_apply_apply]
      exact congrArg Subtype.val h2
    refine ⟨hd, Or.inr (Or.inr ⟨(F2Group.eΓ hN hle e).trans (MulEquiv.prodCongr e
      ((eDH.trans α).trans (specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)))), ψ, ?_⟩)⟩
    intro γ a a' b b' ha hb
    set c := (F2Group.eΓ hN hle e γ).1 with hc
    set d := (F2Group.eΓ hN hle e γ).2 with hdd
    have hd1 := hψD (d : GLV V) (hdcomm d (s rho3) (e.symm rho3).2) b _
      (hact d b) a
    have hmain := compat_mul e s hs ψ hψC c (d : GLV V) b _ a hd1
    have ha' : a' = permActCore 3 (e c) a := Subtype.ext ha
    rw [hγ γ, hmain, ha', hb]
    rfl
  ·
    have hbij := F2Group.actD_bijective hN hle e φH G118.autA5Input h120
    let eD := F2Group.eD120 hN hle φH G118.autA5Input hbij
    have hBD : Invariant (F2Group.cD Γ H) (fixSub (s tau3)) := by
      intro d hdD b hb
      rw [mem_fixSub] at hb ⊢
      have := hdcomm ⟨d, hdD⟩ (s tau3) (e.symm tau3).2 b
      exact this.symm.trans (by rw [hb])
    let ρ : ↥(F2Group.cD Γ H) →* (↥(fixSub (s tau3)) ≃ₗ[ZMod 2] ↥(fixSub (s tau3))) :=
      restrictHom (F2Group.cD Γ H) (fixSub (s tau3)) hBD
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro d hd1
      have hfix : ∀ b ∈ fixSub (s tau3), (d : GLV V) b = b := restrictHom_eq_one_iff.1 hd1
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      have hv : v ∈ fixSub (s tau3) ⊔ conjSub (s rho3) (fixSub (s tau3)) := by
        rw [hsup]
        exact Submodule.mem_top
      obtain ⟨b, hb, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨b', hb', rfl⟩ := hw
      show (d : GLV V) (b + s rho3 b') = b + s rho3 b'
      rw [map_add, hfix b hb, hdcomm d (s rho3) (e.symm rho3).2 b', hfix b' hb']
    have htr : ∀ b b' : ↥(fixSub (s tau3)), b ≠ 0 → b' ≠ 0 → ∃ g : ↥(F2Group.cD Γ H),
        ρ g b = b' := by
      intro b b' hb hb'
      obtain ⟨h, hh⟩ := exists_action_eq hι hb hb'
      refine ⟨⟨h, F2Group.le_cD hle h.2⟩, Subtype.ext ?_⟩
      exact congrArg Subtype.val hh
    obtain ⟨lam, hlam1, hlam2⟩ := exists_semilin_coords hB4 ρ hρinj h120 htr
    obtain ⟨ψ, hψC, hψD⟩ := exists_psi s hc3 hfree hyc hinf hsup lam
    have hdact : ∀ (d : ↥(F2Group.cD Γ H)) (a a' : Fin 2 → GaloisField 2 2),
        lam (ρ d (lam.symm a)) = a' →
          (d : GLV V) ((lam.symm a : ↥(fixSub (s tau3))) : V) =
            ((lam.symm a' : ↥(fixSub (s tau3))) : V) := by
      intro d a a' h
      have h2 : ρ d (lam.symm a) = lam.symm a' := (LinearEquiv.eq_symm_apply lam).2 h
      exact congrArg Subtype.val h2
    refine ⟨hd, Or.inl ⟨⟨(F2Group.eΓ hN hle e).trans (MulEquiv.prodCongr e eD)⟩,
      Or.inr ⟨ψ, ?_, ?_⟩⟩⟩
    · intro γ
      set c := (F2Group.eΓ hN hle e γ).1 with hc
      set d := (F2Group.eΓ hN hle e γ).2 with hdd
      obtain ⟨A, t, hAt⟩ := hlam1 d
      refine ⟨e c, specialLinearGroupEquivStatedSL 2 (GaloisField 2 2) A, t, ?_⟩
      intro first first' second hfirst
      have h1 := hAt (lam.symm second)
      rw [LinearEquiv.apply_symm_apply] at h1
      have hd1 := hψD (d : GLV V) (hdcomm d (s rho3) (e.symm rho3).2) second _
        (hdact d second _ h1) first
      have hmain := compat_mul e s hs ψ hψC c (d : GLV V) second _ first hd1
      have hf' : first' = permActCore 3 (e c) first := Subtype.ext hfirst
      have hvec : (if t then sqVec second else second) =
          fun coordinate => if t then second coordinate ^ 2 else second coordinate := by
        cases t <;> rfl
      rw [hγ γ, hmain, hf', hvec]
      rfl
    · intro σ matrix twisted
      have hAm : (((specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)).symm matrix :
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
          ((matrix : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := by
        have := specialLinearGroupEquivStatedSL_coe 2 (GaloisField 2 2)
          ((specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)).symm matrix)
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm
      obtain ⟨g, hg⟩ := hlam2 ((specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)).symm matrix)
        twisted
      refine ⟨F2Group.prodMap hN hle e (e.symm σ, g), ?_⟩
      intro first first' second hfirst
      have h1 := hg (lam.symm second)
      rw [LinearEquiv.apply_symm_apply] at h1
      have hd1 := hψD (g : GLV V) (hdcomm g (s rho3) (e.symm rho3).2) second _
        (hdact g second _ h1) first
      have hmain := compat_mul e s hs ψ hψC (e.symm σ) (g : GLV V) second _ first hd1
      have hf' : first' = permActCore 3 σ first := Subtype.ext hfirst
      have hvec : (if twisted then sqVec second else second) =
          fun coordinate => if twisted then second coordinate ^ 2 else second coordinate := by
        cases twisted <;> rfl
      rw [MulEquiv.apply_symm_apply, hAm, hvec] at hmain
      have hγ' : ((F2Group.prodMap hN hle e (e.symm σ, g) : ↥Γ) : GLV V) =
          ((e.symm σ : ↥(F2Group.cC Γ H)) : GLV V) * (g : GLV V) := rfl
      rw [hγ', hmain, hf']

end Main

theorem g118NineInputF4_holds : G118NineInputF4 := by
  unfold G118NineInputF4
  intro V _ _ _ Γ L I hHI D hle hd hU hA hC hmod
  obtain ⟨hF, -⟩ := hmod
  obtain ⟨φH⟩ := hA
  obtain ⟨e0⟩ := hC
  exact f4_nine D hle (normalClosure_normal Γ L) hd hU hF φH
    (e0 : ↥(F2Group.cC Γ (normalClosure Γ L)) ≃* Equiv.Perm (Fin 3))

theorem g118NineInput_holds : G118NineInput :=
  g118NineInput_of_cases g118NineInputF2_holds' g118NineInputF4_holds

end Canon

end G11

end CFSG.Quasithin
