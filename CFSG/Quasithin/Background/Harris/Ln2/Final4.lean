module

public import CFSG.Quasithin.Background.Harris.Ln2.Rank
public import CFSG.Quasithin.Background.Harris.Ln2.Full
public import CFSG.Quasithin.Background.Harris.Ln2.NoForm
public import CFSG.Quasithin.Background.Harris.Ln2.Wedge4
public import CFSG.Quasithin.Background.SmithB42LnL4Models

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.B42Ln

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem concl_of_case11 {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Case11 Γ H m) :
    G93Concl Γ H m := by
  unfold G93Concl
  iterate 11 right
  left
  exact h

theorem concl_of_case12 {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Case12 H m) :
    G93Concl Γ H m := by
  unfold G93Concl
  iterate 12 right
  left
  exact h

theorem oneCompFor_famLn2_four : OneCompFor (FamLn2 4) := by
  rintro V _ _ _ Γ A L m hs ⟨-, hmod⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_model hmod
  have hm4 := m_le_four hs e
  have hd := hs.bound
  have hρ := isSimpleRep_repL e hs.L_irr
  have hLΓ : L ≤ Γ := hs.L_comp.1
  rcases l4Model_of_finrank_lt hρ (by omega) with htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · exfalso
    obtain ⟨a, -, l, hl, hne⟩ := hs.L_comm
    have h1 : l = 1 := by
      ext v
      have := htriv (e ⟨l, hl⟩) v
      rwa [repL_apply_self] at this
    exact hne (by rw [h1]; simp)
  · have hact : ActsAs L (e.trans κ) natRep4 β := fun l v => by
      have := hβ (e l) v
      rwa [repL_apply_self] at this
    have hdim : Module.finrank (ZMod 2) V = 4 := by rw [β.finrank_eq]; simp
    have hfull : ∀ γ : GLV V, γ ∈ L := mem_of_actsAs_full hact fun φ => by
      obtain ⟨g, hg⟩ := exists_sl_of_linearEquiv φ
      exact ⟨g, fun w => hg w⟩
    have hLΓeq : L = Γ := le_antisymm hLΓ fun γ _ => hfull γ
    refine concl_of_case11 ⟨⟨by omega, hdim, hm4, ?_, hLΓeq, ?_⟩, ?_, not_selfDual_natRep4 hact⟩
    · rw [← hLΓeq]
      exact ⟨(e.trans κ).trans (specialLinearGroupEquivStatedSL 4 (ZMod 2)), β, hact⟩
    · rw [← hLΓeq]
      intro g
      refine ⟨(((Submodule.topEquiv.symm.trans g).trans Submodule.topEquiv : V ≃ₗ[ZMod 2] V)), hfull _, fun i => ?_⟩
      simp only [LinearEquiv.trans_apply]
      exact congrArg _ (Submodule.topEquiv.symm_apply_eq.mpr rfl)
    · refine endIsField_one_of_actsAs hs.L_irr hact natRep4_simple U4 (Pi.single 0 1)
        (by decide) (fun u hu => e0_mem_fixU u hu) fun x hx => ?_
      obtain ⟨c, hc⟩ := fixU_nat hx
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · left; simpa using hc
      · right; simpa using hc
  · have hact : ActsAs L e wedgeRep4' β := fun l v => by
      have := hβ (e l) v
      rwa [repL_apply_self] at this
    have hdim : Module.finrank (ZMod 2) V = 6 := by rw [β.finrank_eq]; simp
    obtain ⟨hperm, hsd⟩ := wedge4_concl hs.L_irr e β hact
    refine concl_of_case12 ⟨⟨by omega, hdim, hm4, hperm⟩, ?_, hsd⟩
    refine endIsField_one_of_actsAs hs.L_irr hact wedgeRep4'_simple U4 (Pi.single 0 1)
      (by decide) (fun u hu => e01_mem_fixU u hu) fun x hx => ?_
    exact (fixed_checks.2.2 x fun s => hx (x4 s) (x4_mem s))

end CFSG.Quasithin.G11.Harris.Ln2
