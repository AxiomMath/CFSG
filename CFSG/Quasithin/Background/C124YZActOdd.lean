module

public import CFSG.Quasithin.Background.C124YZAct
public import CFSG.Quasithin.Background.B69AltNorm
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C124YZOff

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Odd

variable {m : ℕ}

theorem natKer_odd (hodd : Odd m) :
    Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hz, hc⟩
  rcases mem_zpowers_allOnes hz with h | h
  · exact h
  · exfalso
    have hc' : G6.allOnes m ∈ G6.coreMod m := h ▸ hc
    rw [G6.mem_coreMod] at hc'
    have h1 : ∑ i : Fin m, Multiplicative.toAdd (G6.allOnes m) i = (m : ZMod 2) := by
      simp [G6.allOnes]
    rw [h1, ZMod.natCast_eq_zero_iff_even] at hc'
    exact (Nat.not_even_iff_odd.2 hodd) hc'

@[expose] noncomputable def dmEquivCore (hodd : Odd m) : DM m ≃* ↥(G6.coreMod m) :=
  (QuotientGroup.quotientMulEquivOfEq (show (FFModel.symDn m).ker.subgroupOf
      (FFModel.symDn m).sec = ⊥ by
    rw [show (FFModel.symDn m).ker = ⊥ from natKer_odd hodd, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

end Odd

section TransportOdd

variable {G : Type} [Group G] [Finite G] {X T V L R : Subgroup G} {m : ℕ}
  {hV : IsElemAbelian 2 V}

theorem transport_odd (E : Entry X T V L R m hV) (hodd : Odd m) (hm5 : 5 ≤ m)
    {π : ↥(alternatingGroup (Fin m)) →* ↥(autI hV L)}
    (hreal : (FFModel.altDn m).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) (hπ : Function.Injective π) :
    ∃ (ι : ↥(autI hV X) →* Perm (Fin m)) (β : ↥(commV (autI hV L)) →* ↥(G6.coreMod m)),
      Function.Injective ι ∧
      (∀ γ : ↥(alternatingGroup (Fin m)),
        ι (Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp)) (π γ)) = γ) ∧
      Function.Surjective β ∧
      ∀ (g : ↥(autI hV X)) (u : ↥(commV (autI hV L)))
        (hu : (g : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
        β ⟨(g : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
          G6.coreAct m (ι g) (β u) := by
  classical
  obtain ⟨hπs, -, -, -, -, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hreal
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hLsXs : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hXsN := autI_normalizes hV E.normal
  let β₁ : ↥(commV (autI hV L)) →* DM m := β₀
  have hβ₁s : Function.Surjective β₁ := hβ₀s
  let β : ↥(commV (autI hV L)) →* ↥(G6.coreMod m) := (dmEquivCore hodd).toMonoidHom.comp β₁
  have hβs : Function.Surjective β := (dmEquivCore hodd).surjective.comp hβ₁s
  have hβπ : ∀ (γ : ↥(alternatingGroup (Fin m))) (u : ↥(commV (autI hV L)))
      (hu : (π γ : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
      β ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        G6.coreAct m (γ : Perm (Fin m)) (β u) := by
    intro γ u hu
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hact : (FFModel.altDn m).act γ (m₀ : (FFModel.altDn m).Amb) ∈
        (FFModel.altDn m).sec := G6.permAct_mem_coreMod _ m₀.2
    have h1 := hβ₀e γ u m₀ hu hact hm₀.symm
    have h1' : β₁ ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        (QuotientGroup.mk (⟨(FFModel.altDn m).act γ (m₀ : (FFModel.altDn m).Amb), hact⟩ :
          ↥(G6.coreMod m)) : DM m) := h1
    have hm₀' : β₁ u = (QuotientGroup.mk (m₀ : ↥(G6.coreMod m)) : DM m) := hm₀.symm
    show dmEquivCore hodd (β₁ ⟨_, hu⟩) = G6.coreAct m _ (dmEquivCore hodd (β₁ u))
    rw [h1', hm₀']
    rfl
  have hkerinv : ∀ g ∈ autI hV X, ∀ (u : ↥(commV (autI hV L)))
      (hu : g (u : IntMod V hV) ∈ commV (autI hV L)), β u = 1 →
      β ⟨g (u : IntMod V hV), hu⟩ = 1 := by
    intro g hg u hu h1
    have h2 : β₁ u = 1 := (dmEquivCore hodd).map_eq_one_iff.1 h1
    have h3 := (hβ₀k u).1 h2
    have h4 : g (u : IntMod V hV) ∈ fixV (autI hV L) ⊓ commV (autI hV L) :=
      ⟨apply_mem_fixV (hXsN hg) h3.1, hu⟩
    exact (dmEquivCore hodd).map_eq_one_iff.2 ((hβ₀k _).2 h4)
  obtain ⟨ι, hι, hιπ, hβe⟩ := exists_embedding_of_normalizer hLsXs (commV (autI hV L))
    (fun g hg u hu => apply_mem_commV (hXsN hg) hu)
    (act := G6.coreAct m)
    (fun ρ hρ => G64.symCore_faithful (by omega) ρ fun x hx => by
      have := hρ ⟨x, hx⟩
      have h2 : (G64.symCoreModel m).act ρ x = x := congrArg Subtype.val this
      rw [h2, mul_inv_cancel]
      exact Subgroup.one_mem _)
    (fun φ hφ => B69.exists_perm_of_normalizes hodd hm5 φ hφ)
    π hπs β hβs hβπ hkerinv
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 (hXsN hg) l).1 hl)
    (fun g hg hc => eq_one_of_centralizes (by omega) E.fstarX hπs hπ hg hc)
  exact ⟨ι, β, hι, hιπ, hβs, hβe⟩

end TransportOdd

end CFSG.Quasithin.C124.YZ
