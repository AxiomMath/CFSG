module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepA6
public import CFSG.Quasithin.Background.GoldschmidtB69DeepQ
public import CFSG.Quasithin.Background.SmithB42Alt6Sp4
public import CFSG.Quasithin.Background.GoldschmidtB69DeepTwist

public section

namespace CFSG.Quasithin

open B6 B42Alt6

namespace B69

theorem exists_n6Equiv_of_altDn {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥H} (h : (FFModel.altDn 6).RealizesVia H ⊤ ⊥ π) :
    ∃ Θ : W ≃* S143.N6, ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : W),
      Θ (((π γ : ↥H) : MulAut W) w) = S143.n6Act γ (Θ w) := by
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv h
  let e' : W ≃* (FFModel.symDn 6).Mod := e
  refine ⟨e'.trans S1549D.psiN6, fun γ w => ?_⟩
  obtain ⟨m₀, hm⟩ : ∃ m₀ : ↥(G6.coreMod 6), (QuotientGroup.mk m₀ : (FFModel.symDn 6).Mod) = e' w :=
    QuotientGroup.mk_surjective _
  have hact : G6.permAct 6 (γ : Equiv.Perm (Fin 6)) (m₀ : G6.PermMod 6) ∈ G6.coreMod 6 :=
    G6.permAct_mem_coreMod (γ : Equiv.Perm (Fin 6)) m₀.2
  have h1 : e' (((π γ : ↥H) : MulAut W) w) =
      (QuotientGroup.mk ⟨G6.permAct 6 (γ : Equiv.Perm (Fin 6)) (m₀ : G6.PermMod 6), hact⟩ :
        (FFModel.symDn 6).Mod) :=
    he γ w m₀ hact hm.symm
  show S1549D.psiN6 (e' (((π γ : ↥H) : MulAut W) w)) = S143.n6Act γ (S1549D.psiN6 (e' w))
  rw [h1, ← hm]
  exact S1549D.n6Rep_permAct (γ : Equiv.Perm (Fin 6)) m₀

theorem asB69NoRankTwoA6_proved :
    AsB69NoRankTwoA6 := by
  intro V _ _ hV X T M A L hH W hW B hBA hBo hc
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, hAlt, -, hq, -⟩ := hc
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥(wtL L W),
      (FFModel.altDn 6).RealizesVia (wtL L W) ⊤ ⊥ π := hAlt
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨Θ, hΘ⟩ := exists_n6Equiv_of_altDn hπ
  have hρπ : ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : Sec W (W ⊓ fixV L)),
      rhoOf Θ (γ : Equiv.Perm (Fin 6)) w = ((π γ : ↥(wtL L W)) : MulAut _) w := by
    intro γ w
    apply Θ.injective
    rw [rhoOf_apply, hΘ]
  have hρA : (alternatingGroup (Fin 6)).map (rhoOf Θ) = wtL L W := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have : rhoOf Θ γ = ((π ⟨γ, hγ⟩ : ↥(wtL L W)) : MulAut _) :=
        MulEquiv.ext fun w => hρπ ⟨γ, hγ⟩ w
      rw [this]
      exact (π ⟨γ, hγ⟩).2
    · intro hx
      obtain ⟨γ, hγ⟩ : ∃ γ : ↥(alternatingGroup (Fin 6)), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
      refine ⟨γ, γ.2, ?_⟩
      have : rhoOf Θ γ = ((π γ : ↥(wtL L W)) : MulAut _) := MulEquiv.ext fun w => hρπ γ w
      rw [this, hγ]
  let M₆ : N6Model (wtL L W) :=
    ⟨Θ, rhoOf Θ, rhoOf_injective Θ, rhoOf_apply Θ, hρA⟩
  have hrange : ∀ σ, M₆.ρ σ ∈ M₆.ρ.range := fun σ => ⟨σ, rfl⟩
  have hn : BinaryNaturalSp4 M₆.ρ.range ⊤ ⊥ 1 :=
    M₆.binaryNaturalSp4 hrange (fun h ⟨σ, hσ⟩ => ⟨σ, hσ⟩)
  have hLH : wtL L W ≤ M₆.ρ.range := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := M₆.mem_L_iff.1 hx
    exact ⟨γ, rfl⟩
  have hnormH : ((wtL L W).subgroupOf M₆.ρ.range).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    obtain ⟨γ, hγ, hγn⟩ := M₆.mem_L_iff.1 hn'
    obtain ⟨σ, hσ⟩ := g.2
    rw [M₆.mem_L_iff]
    refine ⟨σ * γ * σ⁻¹, (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ, ?_⟩
    show M₆.ρ (σ * γ * σ⁻¹) = (g : MulAut _) * (n : MulAut _) * (g : MulAut _)⁻¹
    rw [map_mul, map_mul, map_inv, hσ, hγn]
  obtain ⟨S⟩ := exists_twist_data_a6 hmp hL hW hLH hn hnormH
  obtain ⟨W₂, hW₂, hne, -⟩ := exists_twist_member_sp4 S.r hW S.e₁ S.he₁ S.t S.ht S.ht' S.htw S.hniso
  exact false_of_one_le_rAV hV hA hLq hLA hW hW₂ hne
    (one_le_rAV_of_qOf hV hA hLq hLA hW hq.ge)

end B69

end CFSG.Quasithin
