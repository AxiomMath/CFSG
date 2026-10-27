module

public import CFSG.Quasithin.Background.Harris.Ln2.Rank
public import CFSG.Quasithin.Background.Harris.Ln2.Full
public import CFSG.Quasithin.Background.Harris.Ln2.NoForm
public import CFSG.Quasithin.Background.Harris.Ln2.Wedge5
public import CFSG.Quasithin.Background.SmithB42LnL5Curtis
public import CFSG.Quasithin.Background.SmithB42LnL5Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.JonesParshall.Curtis

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem concl_of_case13 {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Case13 Γ H m) :
    G93Concl Γ H m := by
  unfold G93Concl
  iterate 13 right
  left
  exact h

theorem m_le_six_of_le {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m)
    (hΓL : Γ ≤ L) (e : ↥L ≃* G5) : m ≤ 6 := by
  have hAL : A ≤ L := hs.A_le.trans hΓL
  let E : Subgroup G5 := (A.subgroupOf L).map e.toMonoidHom
  have hcard : Nat.card E = 2 ^ m := by
    have h1 : Nat.card E = Nat.card (A.subgroupOf L) :=
      Nat.card_congr ((A.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv
    have h2 : Nat.card (A.subgroupOf L) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    rw [h1, h2, hs.A_card]
  have hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hh := hs.A_elem.1.is_comm.comm (⟨(a : GLV V), ha⟩ : ↥A) ⟨(b : GLV V), hb⟩
    exact Subtype.ext (congrArg (fun x : ↥A => (x : GLV V)) hh)
  have h2 : ∀ a ∈ E, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have := hs.A_elem.2 (a : GLV V) ha
    have h3 : a * a = 1 := Subtype.ext (by simpa [sq] using this)
    rw [h3, map_one]
  have := CFSG.Quasithin.B42Ln.card_le_of_elemAbelian hc h2
  rw [hcard] at this
  have h64 : (2 : ℕ) ^ m ≤ 2 ^ 6 := this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h64

theorem oneCompFor_famLn2_five :
    OneCompFor (FamLn2 5) := by
  rintro V _ _ _ Γ A L m hs ⟨-, hmod⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_model hmod
  have hm7 := m_le_seven hs e
  have hd := hs.bound
  have hρ := isSimpleRep_repL e hs.L_irr
  have hLΓ : L ≤ Γ := hs.L_comp.1
  rcases CFSG.Quasithin.B42Ln.l5Model_of_finrank_le hρ (by omega) with
    htriv | ⟨κ, β, hβ⟩ | ⟨κ, β, hβ⟩
  · exfalso
    obtain ⟨a, -, l, hl, hne⟩ := hs.L_comm
    have h1 : l = 1 := by
      ext v
      have := htriv (e ⟨l, hl⟩) v
      rwa [repL_apply_self] at this
    exact hne (by rw [h1]; simp)
  · have hact : ActsAs L (e.trans κ) natRep β := fun l v => by
      have := hβ (e l) v
      rwa [repL_apply_self] at this
    have hdim : Module.finrank (ZMod 2) V = 5 := by rw [β.finrank_eq]; simp
    have hfull : ∀ γ : GLV V, γ ∈ L := mem_of_actsAs_full hact fun φ => by
      obtain ⟨g, hg⟩ := exists_sl_of_linearEquiv φ
      exact ⟨g, fun w => hg w⟩
    have hLΓeq : L = Γ := le_antisymm hLΓ fun γ _ => hfull γ
    refine concl_of_case13 ⟨⟨?_, Or.inl ⟨hdim, by omega, ?_⟩, m_le_six_of_le hs hLΓeq.ge e, hLΓeq⟩,
      ?_, not_selfDual_natRep5 hact⟩
    · exact ⟨(MulEquiv.subgroupCongr hLΓeq.symm).trans
        (e.trans (specialLinearGroupEquivStatedSL 5 (ZMod 2)))⟩
    · rw [← hLΓeq]
      intro g
      refine ⟨(((Submodule.topEquiv.symm.trans g).trans Submodule.topEquiv : V ≃ₗ[ZMod 2] V)),
        hfull _, fun i => ?_⟩
      simp only [LinearEquiv.trans_apply]
      exact congrArg _ (Submodule.topEquiv.symm_apply_eq.mpr rfl)
    · exact endIsField_one_of_actsAs hs.L_irr hact natRep_simple Ugrp e0 e0_ne
        (fun u hu => e0_mem_fixU u hu) fun x hx => natRep_fix hx
  · have hact : ActsAs L (e.trans κ) wedgeRep β := fun l v => by
      have := hβ (e l) v
      rwa [repL_apply_self] at this
    have hdim : Module.finrank (ZMod 2) V = 10 := by rw [β.finrank_eq]; simp
    have hΓL : Γ ≤ L := fun γ hγ => mem_of_normalizes_wedge5 hs.L_normal hact γ hγ
    have hLΓeq : L = Γ := le_antisymm hLΓ hΓL
    refine concl_of_case13 ⟨⟨?_, Or.inr ⟨hdim, by omega⟩, m_le_six_of_le hs hΓL e, hLΓeq⟩,
      ?_, not_selfDual_wedgeRep5 hact⟩
    · exact ⟨(MulEquiv.subgroupCongr hLΓeq.symm).trans
        (e.trans (specialLinearGroupEquivStatedSL 5 (ZMod 2)))⟩
    · exact endIsField_one_of_actsAs hs.L_irr hact wedge_simple Ugrp e01 e01_ne
        (fun u hu => e01_mem_fixU u hu) fun x hx => wedge_fix hx

end CFSG.Quasithin.G11.Harris.Ln2
