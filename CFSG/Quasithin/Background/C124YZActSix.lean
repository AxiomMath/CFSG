module

public import CFSG.Quasithin.Background.C124YZSix
public import CFSG.Quasithin.Background.C124YZAct
public import CFSG.Quasithin.Background.SmithB42Alt6Norm
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C124YZOff

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm CFSG.Quasithin.S143

theorem dAct_injective {m : ℕ} (hm : 5 ≤ m) : Function.Injective (dAct m) := by
  rw [injective_iff_map_eq_one]
  exact fun ρ h => dAct_faithful hm ρ fun q => by rw [h]; rfl

@[expose] noncomputable def n6Model :
    B42Alt6.N6Model ((alternatingGroup (Fin 6)).map (dAct 6)) where
  Θ := S1549D.psiN6
  ρ := dAct 6
  ρ_inj := dAct_injective (by norm_num)
  Θ_ρ σ v := by
    refine QuotientGroup.induction_on v fun m => ?_
    exact S1549D.n6Rep_permAct σ m
  ρ_alt := rfl

theorem exists_perm_of_normalizes_six (φ : MulAut (DM 6))
    (hφ : ∀ σ ∈ alternatingGroup (Fin 6), ∃ τ ∈ alternatingGroup (Fin 6),
      ∀ y, dAct 6 σ (φ y) = φ (dAct 6 τ y)) : ∃ ρ : Perm (Fin 6), ∀ y, φ y = dAct 6 ρ y := by
  have hφinv : φ⁻¹ ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (dAct 6) : Subgroup (MulAut (DM 6))) :
        Set (MulAut (DM 6))) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨τ, hτ, hστ⟩ := hφ σ hσ
    have h : φ⁻¹ * dAct 6 σ * φ⁻¹⁻¹ = dAct 6 τ := by
      refine MulEquiv.ext fun y => ?_
      show φ.symm (dAct 6 σ (φ y)) = dAct 6 τ y
      rw [hστ y]
      exact φ.symm_apply_apply _
    rw [h]
    exact Subgroup.mem_map_of_mem _ hτ
  have hφN : φ ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (dAct 6) : Subgroup (MulAut (DM 6))) :
        Set (MulAut (DM 6))) := by
    simpa using Subgroup.inv_mem _ hφinv
  have hS : ∀ s : DM 6, s * s = 1 := fun s =>
    QuotientGroup.induction_on s fun m => by
      rw [← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (Subtype.ext (G6.permMod_mul_self _))
  obtain ⟨ρ, hρ⟩ := B42Alt6.N6Model.le_range n6Model hS
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) (dAct 6)
      (dAct_injective (by norm_num))).symm hφN
  exact ⟨ρ, fun y => by rw [← hρ]; rfl⟩

section TransportSix

variable {G : Type} [Group G] [Finite G] {X T V L R : Subgroup G} {hV : IsElemAbelian 2 V}

theorem transport_six (E : Entry X T V L R 6 hV)
    {π : ↥(alternatingGroup (Fin 6)) →* ↥(autI hV L)}
    (hreal : (FFModel.altDn 6).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) (hπ : Function.Injective π) :
    ∃ (ι : ↥(autI hV X) →* Perm (Fin 6)) (β : ↥(commV (autI hV L)) →* DM 6),
      Function.Injective ι ∧
      (∀ γ : ↥(alternatingGroup (Fin 6)),
        ι (Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp)) (π γ)) = γ) ∧
      Function.Surjective β ∧
      ∀ (g : ↥(autI hV X)) (u : ↥(commV (autI hV L)))
        (hu : (g : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
        β ⟨(g : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ = dAct 6 (ι g) (β u) := by
  classical
  obtain ⟨hπs, -, -, -, -, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hreal
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hLsXs : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hXsN := autI_normalizes hV E.normal
  let β : ↥(commV (autI hV L)) →* DM 6 := β₀
  have hβπ : ∀ (γ : ↥(alternatingGroup (Fin 6))) (u : ↥(commV (autI hV L)))
      (hu : (π γ : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
      β ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        dAct 6 (γ : Perm (Fin 6)) (β u) := by
    intro γ u hu
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hact : (FFModel.altDn 6).act γ (m₀ : (FFModel.altDn 6).Amb) ∈
        (FFModel.altDn 6).sec := G6.permAct_mem_coreMod _ m₀.2
    have h1 := hβ₀e γ u m₀ hu hact hm₀.symm
    have h1' : β ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        (QuotientGroup.mk (⟨(FFModel.altDn 6).act γ (m₀ : (FFModel.altDn 6).Amb), hact⟩ :
          ↥(G6.coreMod 6)) : DM 6) := h1
    have hm₀' : β u = (QuotientGroup.mk (m₀ : ↥(G6.coreMod 6)) : DM 6) := hm₀.symm
    rw [h1', hm₀']
    rfl
  have hkerinv : ∀ g ∈ autI hV X, ∀ (u : ↥(commV (autI hV L)))
      (hu : g (u : IntMod V hV) ∈ commV (autI hV L)), β u = 1 →
      β ⟨g (u : IntMod V hV), hu⟩ = 1 := by
    intro g hg u hu h1
    have h3 := (hβ₀k u).1 h1
    have h4 : g (u : IntMod V hV) ∈ fixV (autI hV L) ⊓ commV (autI hV L) :=
      ⟨apply_mem_fixV (hXsN hg) h3.1, hu⟩
    exact (hβ₀k _).2 h4
  obtain ⟨ι, hι, hιπ, hβe⟩ := exists_embedding_of_normalizer hLsXs (commV (autI hV L))
    (fun g hg u hu => apply_mem_commV (hXsN hg) hu)
    (act := dAct 6) (fun ρ hρ => dAct_faithful (by norm_num) ρ hρ)
    exists_perm_of_normalizes_six π hπs β hβ₀s hβπ hkerinv
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 (hXsN hg) l).1 hl)
    (fun g hg hc => eq_one_of_centralizes (by norm_num) E.fstarX hπs hπ hg hc)
  exact ⟨ι, β, hι, hιπ, hβ₀s, hβe⟩

end TransportSix

end CFSG.Quasithin.C124.YZ
