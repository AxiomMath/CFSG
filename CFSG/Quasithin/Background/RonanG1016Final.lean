module

public import CFSG.Quasithin.Background.RonanG1015Final
public import CFSG.Quasithin.Background.G10Sixteen
public import CFSG.Quasithin.Background.RonanG1016Core
public import CFSG.Quasithin.Background.RonanG1016Gen
public import CFSG.Quasithin.Background.RonanG1016Pair
public import CFSG.Quasithin.Background.RonanG1016Perf
public import CFSG.Quasithin.Background.RonanG1016SD
public import CFSG.Quasithin.Background.G10SixteenC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace RonanG1016

open CFSG.Quasithin.G11

theorem g10_16_final :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
        ∀ a ∈ X, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 →
          (∃ h ∈ normalClosure Γ L, a * h ≠ h * a) ∧
          (∀ I : Submodule (ZMod 2) V, G11.IrrPlus (normalClosure Γ L) I → conjSub a I = I) ∧
          (normalClosure Γ L ≤ normalClosure Γ (Subgroup.zpowers a) ∧
            ∀ I : Submodule (ZMod 2) V, G11.IrrPlus (normalClosure Γ L) I ↔
              G11.IrrPlus (normalClosure Γ (Subgroup.zpowers a)) I) ∧
          (IsIrr (normalClosure Γ L) ⊤ ∨
            ∃ I₁ I₂ : Submodule (ZMod 2) V, IsCompl I₁ I₂ ∧
              Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∧
              Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₂ ∧
              (HIso (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ I₂ ∨
                (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)) ∧
              (∃ c₁ : V, InducesTransvection a I₁ c₁) ∧ (∃ c₂ : V, InducesTransvection a I₂ c₂) ∧
              (InducesSp (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
                InducesOrth (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
                (∃ n : ℕ, IsSymNaturalSub (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ n) ∨
                (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁))) := by
  intro V _ _ _ B Γ v₁ W X X₀ L hyp a ha ha1 hrank
  have hcomm := hyp.exists_noncomm ha1 hrank
  have hfixI : ∀ I : Submodule (ZMod 2) V, G11.IrrPlus (normalClosure Γ L) I → conjSub a I = I :=
    fun I hI => hyp.conj_eq_of_finrank_le ha hrank hI
  refine ⟨hcomm, hfixI, ⟨hyp.le_normalClosure_zpowers ha hcomm,
    fun I => hyp.irrPlus_iff ha hrank hcomm⟩, ?_⟩
  obtain ⟨I, hI, -, h2, h3⟩ := CFSG.Quasithin.RonanG1015.g10_15_final V B Γ v₁ W X X₀ L hyp
  have hfaithI : FaithfulOn (normalClosure Γ L) I := by
    rcases h2 with h | h | h
    · exact h.2.2.1
    · exact h.2.2.1
    · exact (hyp.not_III ha ha1 hrank hI h).elim
  have hfaith : ∀ J, IsIrr (normalClosure Γ L) J → FaithfulOn (normalClosure Γ L) J :=
    fun J hJ => hyp.faithful_of_irr hI hfaithI hJ
  rcases hyp.irr_or_two ha hrank hcomm hfaith with
    hirr | ⟨J₁, J₂, hc, hJ₁, hJ₂, haJ₁, haJ₂, hf1, hf2⟩
  · exact Or.inl hirr
  · right
    have hT₁ := inducesTransvection_of_finrank_raU haJ₁ hf1
    have hT₂ := inducesTransvection_of_finrank_raU haJ₂ hf2
    have ha2 : a * a = 1 := hyp.X_sq a ha
    have haΓ : a ∈ Γ := hyp.X_le ha
    have hHΓ : normalClosure Γ L ≤ Γ := normalClosure_le hyp.component.1
    have hHK : normalClosure Γ L ≤ normalClosure Γ L ⊔ Subgroup.zpowers a := le_sup_left
    have haK : a ∈ normalClosure Γ L ⊔ Subgroup.zpowers a :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    have hKΓ : normalClosure Γ L ⊔ Subgroup.zpowers a ≤ Γ :=
      sup_le hHΓ ((Subgroup.zpowers_le).2 haΓ)
    have hHnorm : ∀ k ∈ normalClosure Γ L ⊔ Subgroup.zpowers a, ∀ h ∈ normalClosure Γ L,
        k * h * k⁻¹ ∈ normalClosure Γ L :=
      fun k hk h hh => normalClosure_normal Γ L k (hKΓ hk) h hh
    have hHne : normalClosure Γ L ≠ ⊥ := by
      obtain ⟨h, hh, hne⟩ := hcomm
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hh
      exact hne (by rw [hh]; simp)
    have hε : ∀ ε : ↥(normalClosure Γ L ⊔ Subgroup.zpowers a) →* ℤˣ, ∀ (h : GLV V)
        (hh : h ∈ normalClosure Γ L), ε ⟨h, hHK hh⟩ = 1 :=
      fun ε h hh => hyp.hom_eq_one_of_normalClosure hHK ε hh
    have hinv₁ : Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) J₁ :=
      hJ₁.1.sup_subgroup (invariant_zpowers haJ₁)
    have hinv₂ : Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) J₂ :=
      hJ₂.1.sup_subgroup (invariant_zpowers haJ₂)
    have hirrK₁ : IsIrr (normalClosure Γ L ⊔ Subgroup.zpowers a) J₁ :=
      ⟨hinv₁, hJ₁.2.1, fun J hJ hJ0 hJI => hJ₁.2.2 J (hJ.mono hHK) hJ0 hJI⟩
    have hTrv₁ : IsTransvOn J₁ a := ⟨haJ₁, (inducesTransvection_iff_finrank haJ₁).1 hT₁⟩
    have haT : a ∈ normalClosure (normalClosure Γ L ⊔ Subgroup.zpowers a) (Subgroup.zpowers a) :=
      Subgroup.subset_closure ⟨1, (normalClosure Γ L ⊔ Subgroup.zpowers a).one_mem, a,
        Subgroup.mem_zpowers a, by simp⟩
    have hKT₁ : normalClosure Γ L ⊔ Subgroup.zpowers a ≤
        normalClosure (normalClosure Γ L ⊔ Subgroup.zpowers a) (Subgroup.zpowers a) :=
      sup_le (hyp.le_normalClosure_hat ha hJ₁ (hfaith J₁ hJ₁) haJ₁ hT₁)
        ((Subgroup.zpowers_le).2 haT)
    have h3₁ : 3 ≤ Module.finrank (ZMod 2) ↥J₁ := hyp.two_lt_finrank hJ₁
    obtain ⟨γ, hγ, hJγ⟩ := hyp.exists_hiso_conj hI hJ₁
    have hfr : Module.finrank (ZMod 2) ↥J₁ = Module.finrank (ZMod 2) ↥I := by
      obtain ⟨φ, -⟩ := hJγ
      rw [LinearEquiv.finrank_eq φ, finrank_conjSub]
    have hAutAll : AutAll (normalClosure Γ L) J₁ →
        (Module.finrank (ZMod 2) ↥J₁ = 4 ∧ AutAll (normalClosure Γ L) J₁) := by
      intro hA
      refine ⟨?_, hA⟩
      rcases h3 with hnA | hfr4
      · exfalso
        have hA' : AutAll (normalClosure Γ L) (conjSub γ I) := autAll_of_hiso hJ₁.1 hJγ hA
        exact hnA (autAll_of_conj (normalClosure_normal Γ L) hγ hA')
      · rw [hfr, hfr4]
    rcases mclaughlin_core hirrK₁ hHK haK le_rfl ha2 hHnorm hJ₁.1 (hfaith J₁ hJ₁) hHne hε h3₁
        hKT₁ hTrv₁ with hA | ⟨hsd, hcl⟩
    · have h4 := hAutAll hA
      exact ⟨J₁, J₂, hc, hinv₁, hinv₂, Or.inr h4, hT₁, hT₂, Or.inr (Or.inr (Or.inr h4))⟩
    · have hsdH : SelfDual (normalClosure Γ L) J₁ := hsd.mono hHK
      have hsdI : SelfDual (normalClosure Γ L) I := by
        have h1 : SelfDual (normalClosure Γ L) (conjSub γ I) := selfDual_of_hiso hJ₁.1 hJγ hsdH
        have h2' : SelfDual (normalClosure Γ L) (conjSub γ⁻¹ (conjSub γ I)) :=
          selfDual_conjSub (fun k hk => by
            rw [inv_inv]
            exact normalClosure_normal Γ L γ hγ k hk) h1
        rwa [conjSub_inv_conjSub] at h2'
      have hhom : Homogeneous (normalClosure Γ L) := by
        rcases h2 with hI1 | hII | hIII
        · exact hI1.1
        · exact absurd hsdI hII.2.1
        · exact (hyp.not_III ha ha1 hrank hI hIII).elim
      have hiso : HIso (normalClosure Γ L) J₁ J₂ :=
        hhom J₁ J₂ (hJ₁.irrPlus hyp.fixedSpace_H) (hJ₂.irrPlus hyp.fixedSpace_H)
      have hisoK : HIso (normalClosure Γ L ⊔ Subgroup.zpowers a) J₁ J₂ :=
        hiso_sup_zpowers hJ₁ hJ₂ (normalClosure_normal Γ L a haΓ) ha2 haJ₁ haJ₂ hiso
      rcases hcl with hsp | horth | hsym
      · exact ⟨J₁, J₂, hc, hinv₁, hinv₂, Or.inl hisoK, hT₁, hT₂, Or.inl hsp⟩
      · exact ⟨J₁, J₂, hc, hinv₁, hinv₂, Or.inl hisoK, hT₁, hT₂, Or.inr (Or.inl horth)⟩
      · exact ⟨J₁, J₂, hc, hinv₁, hinv₂, Or.inl hisoK, hT₁, hT₂, Or.inr (Or.inr (Or.inl hsym))⟩

end RonanG1016

end CFSG.Quasithin
