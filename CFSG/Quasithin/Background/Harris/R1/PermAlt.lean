module

public import CFSG.Quasithin.Recognition.SzR1Fam
public import CFSG.Quasithin.Recognition.SzR1Gram

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem exists_act_eq (C : FamCtx K1 L2 S Zs Ω) [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) :
    ∀ σ : Equiv.Perm Ω, Equiv.Perm.sign σ = 1 → ∃ k : ↥K1, C.D.act k = σ := by
  obtain ⟨θ, hθs, hθ⟩ := F112J2.exists_theta C.h hL24
  let e : Ω → Fin 5 := fun ω => ((θ (C.D.kf ω) : A5) : Equiv.Perm (Fin 5)) 4
  have hθ4 : ∀ k : ↥K1, (k : G) ∈ borelOf K1 S → ((θ k : A5) : Equiv.Perm (Fin 5)) 4 = 4 :=
    fun k hk => (mem_A4s).1 ((hθ k).2 hk)
  have hθmul : ∀ (k l : ↥K1) (x : Fin 5), ((θ (k * l) : A5) : Equiv.Perm (Fin 5)) x =
      ((θ k : A5) : Equiv.Perm (Fin 5)) (((θ l : A5) : Equiv.Perm (Fin 5)) x) := by
    intro k l x
    rw [map_mul]
    rfl
  have hmemA : ∀ k : ↥K1, ((θ k : A5) : Equiv.Perm (Fin 5)) 4 = 4 → C.D.act k C.D.pt = C.D.pt :=
    fun k hk => (C.D.stab k).2 ((hθ k).1 ((mem_A4s).2 hk))
  have f1 : ∀ (k : ↥K1) (ω : Ω), e (C.D.act k ω) =
      ((θ k : A5) : Equiv.Perm (Fin 5)) (e ω) := by
    intro k ω
    set ω' := C.D.act k ω with hω'
    have hk' : C.D.act ((C.D.kf ω')⁻¹ * k * C.D.kf ω) C.D.pt = C.D.pt := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply, C.D.kf_spec]
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (C.D.kf_spec _).symm
    have h4 := hθ4 _ ((C.D.stab _).1 hk')
    have e1 : k * C.D.kf ω = C.D.kf ω' * ((C.D.kf ω')⁻¹ * k * C.D.kf ω) := by group
    show _ = ((θ k : A5) : Equiv.Perm (Fin 5)) (((θ (C.D.kf ω) : A5) : Equiv.Perm (Fin 5)) 4)
    rw [← hθmul, e1, hθmul, h4]
  have f2 : Function.Injective e := by
    intro ω₁ ω₂ h12
    have h1 := hθmul (C.D.kf ω₂) ((C.D.kf ω₂)⁻¹ * C.D.kf ω₁) 4
    rw [mul_inv_cancel_left] at h1
    have h2 : ((θ ((C.D.kf ω₂)⁻¹ * C.D.kf ω₁) : A5) : Equiv.Perm (Fin 5)) 4 = 4 := by
      apply ((θ (C.D.kf ω₂) : A5) : Equiv.Perm (Fin 5)).injective
      rw [← h1]
      exact h12
    have h3 := hmemA _ h2
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply, C.D.kf_spec] at h3
    rw [Equiv.Perm.inv_eq_iff_eq] at h3
    rw [C.D.kf_spec] at h3
    exact h3
  have hb : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨f2, by rw [hΩ, Fintype.card_fin]⟩
  let E : Ω ≃ Fin 5 := Equiv.ofBijective e hb
  intro σ hσ
  have hτ : Equiv.Perm.sign (E.permCongr σ) = 1 := by rw [Equiv.Perm.sign_permCongr, hσ]
  obtain ⟨k, hk⟩ := hθs ⟨E.permCongr σ, (Equiv.Perm.mem_alternatingGroup).2 hτ⟩
  refine ⟨k, Equiv.ext fun ω => f2 ?_⟩
  have h1 : e (C.D.act k ω) = ((θ k : A5) : Equiv.Perm (Fin 5)) (e ω) := f1 k ω
  rw [h1, hk]
  show (E.permCongr σ) (E ω) = E (σ ω)
  simp [Equiv.permCongr_apply]

end CFSG.Quasithin.Background.Harris.R1
