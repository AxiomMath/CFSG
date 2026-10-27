module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.GoldschmidtC137KMod3

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B3 CFSG.Quasithin.S143 CFSG.Quasithin.H13.U3.GC137
open scoped Matrix

abbrev burnsideC137_Dsp : FFModel := FFModel.nat (StatedSp 2 (ZMod 2))

theorem burnsideC137_hDsp : burnsideC137_Dsp.IsActionModel := FFModel.nat_isActionModel _

noncomputable abbrev burnsideC137_theta : Equiv.Perm (Fin 6) ≃* ↥(StatedSp 2 (ZMod 2)) :=
  B5FinSp.theta (RingEquiv.refl (ZMod 2))

noncomputable def burnsideC137_d6E : (FFModel.symDn 6).Mod ≃* burnsideC137_Dsp.Mod :=
  FFModel.modEquivOfSurj (D := burnsideC137_Dsp) (D' := FFModel.symDn 6)
    (B5FinSp.ehat (RingEquiv.refl (ZMod 2))) (B5FinSp.ehat_surjective _) (by
      intro m
      change B5FinSp.lhom (RingEquiv.refl (ZMod 2)) (B5FinSp.chiHom m.1) ∈ (⊥ : Subgroup _) ↔ _
      rw [Subgroup.mem_bot, ← map_one (B5FinSp.lhom (RingEquiv.refl (ZMod 2))),
        (B5FinSp.lhom_injective _).eq_iff]
      exact B5FinSp.chiHom_eq_one_iff m.2)

theorem burnsideC137_d6E_act (σ : Equiv.Perm (Fin 6)) (m : ↥(G6.coreMod 6)) :
    burnsideC137_d6E (QuotientGroup.mk ⟨G6.permAct 6 σ m.1, G6.permAct_mem_coreMod σ m.2⟩) =
      burnsideC137_hDsp.modAct (burnsideC137_theta σ) (burnsideC137_d6E (QuotientGroup.mk m)) := by
  change (QuotientGroup.mk (B5FinSp.ehat (RingEquiv.refl (ZMod 2))
      ⟨G6.permAct 6 σ m.1, G6.permAct_mem_coreMod σ m.2⟩) : burnsideC137_Dsp.Mod) =
    QuotientGroup.mk (burnsideC137_hDsp.actSec (burnsideC137_theta σ)
      (B5FinSp.ehat (RingEquiv.refl (ZMod 2)) m))
  congr 1
  apply Subtype.ext
  have hσ : CFSG.ComponentClassification.PresentationLocal.omegaPerm
      (B5FinSp.omegaEquiv.symm σ) = σ := by
    rw [← B5FinSp.omegaEquiv_apply]
    exact B5FinSp.omegaEquiv.apply_symm_apply σ
  have h1 := B5FinSp.chiHom_permAct (B5FinSp.omegaEquiv.symm σ) m.2
  rw [hσ] at h1
  change B5FinSp.lhom (RingEquiv.refl (ZMod 2)) (B5FinSp.chiHom (G6.permAct 6 σ m.1)) =
    Multiplicative.ofAdd ((((burnsideC137_theta σ : ↥(StatedSp 2 (ZMod 2))) :
      GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      Multiplicative.toAdd (B5FinSp.lhom (RingEquiv.refl (ZMod 2)) (B5FinSp.chiHom m.1)))
  rw [h1]
  exact congrArg Multiplicative.ofAdd
    (B5FinSp.theta_mulVec_lfun (RingEquiv.refl (ZMod 2)) σ
      (Multiplicative.toAdd (B5FinSp.chiHom m.1))).symm

noncomputable def burnsideC137_d6Sp4 : Mod.V 6 Mod.ut0 ≃* burnsideC137_Dsp.Mod :=
  (n6ModEquiv.symm.trans S1549D.psiN6.symm).trans burnsideC137_d6E

theorem burnsideC137_d6Sp4_act (σ : Equiv.Perm (Fin 6)) (x : Mod.V 6 Mod.ut0) :
    burnsideC137_d6Sp4 (Mod.act 6 Mod.ut0 σ x) =
      burnsideC137_hDsp.modAct (burnsideC137_theta σ) (burnsideC137_d6Sp4 x) := by
  have key : ∀ m : ↥(G6.coreMod 6),
      Mod.act 6 Mod.ut0 σ (n6ModEquiv (S1549D.psiN6 (QuotientGroup.mk m))) =
        n6ModEquiv (S1549D.psiN6 (QuotientGroup.mk
          ⟨G6.permAct 6 σ m.1, G6.permAct_mem_coreMod σ m.2⟩)) := by
    intro m
    rw [S1549D.psiN6_mk]
    show _ = n6ModEquiv (S1549D.n6Rep ⟨G6.permAct 6 σ m.1, G6.permAct_mem_coreMod σ m.2⟩)
    rw [S1549D.n6Rep_permAct, n6ModEquiv_apply, n6ModEquiv_apply, n6ToV_act_perm]
  have key2 : ∀ m : ↥(G6.coreMod 6),
      burnsideC137_d6Sp4 (Mod.act 6 Mod.ut0 σ (n6ModEquiv (S1549D.psiN6 (QuotientGroup.mk m)))) =
        burnsideC137_hDsp.modAct (burnsideC137_theta σ)
          (burnsideC137_d6Sp4 (n6ModEquiv (S1549D.psiN6 (QuotientGroup.mk m)))) := by
    intro m
    rw [key m]
    simp only [burnsideC137_d6Sp4, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact burnsideC137_d6E_act σ m
  obtain ⟨a, rfl⟩ := n6ModEquiv.surjective x
  obtain ⟨q, rfl⟩ := S1549D.psiN6.surjective a
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact key2 m

@[expose] def burnsideC137_S6Marking {W : Type} [CommGroup W] (X₀ : Subgroup (MulAut W))
    (Z : Subgroup W) : Prop :=
  ∃ f : W →* burnsideC137_Dsp.Mod, Function.Surjective f ∧ (∀ w, f w = 1 ↔ w ∈ Z) ∧
    (∀ h ∈ X₀, (∀ w, f (h w) = f w) → h = 1) ∧
    (∀ h ∈ X₀, ∃ δ, ∀ w, f (h w) = burnsideC137_hDsp.modAct δ (f w)) ∧
    (∀ δ, ∃ h ∈ X₀, ∀ w, f (h w) = burnsideC137_hDsp.modAct δ (f w))

theorem burnsideC137_hDsp_injective : Function.Injective burnsideC137_hDsp.modAct := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply FFModel.nat_faithful
  intro m hm
  have h1 := DFunLike.congr_fun hγ (QuotientGroup.mk ⟨m, hm⟩)
  rw [MulAut.one_apply, FFModel.IsActionModel.modAct_apply,
    FFModel.IsActionModel.modEnd_mk] at h1
  have h2 := QuotientGroup.eq.mp h1.symm
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : (m : burnsideC137_Dsp.Amb)⁻¹ * burnsideC137_Dsp.act γ m ∈ burnsideC137_Dsp.ker := h2
  rwa [mul_comm] at h3

theorem burnsideC137_ker_projK {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) :
    (projK k).ker = fixV ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) := by
  refine Subgroup.eq_of_le_of_card_ge (ker_projK_le_fixV hk _) ?_
  rw [card_fixV_act hk, fixV_A6, Subgroup.card_bot, mul_one, card_ker_projK hk]

theorem burnsideC137_s6Marking {W : Type} [CommGroup W] {k : Mod}
    (hk : k = Mod.ut0 ∨ k = Mod.u0) {L₀ X₀ : Subgroup (MulAut W)} (N : KModel k L₀)
    (hX : (⊤ : Subgroup (Gp 6)).map N.ρ = X₀) : burnsideC137_S6Marking X₀ (fixV L₀) := by
  let f : W →* burnsideC137_Dsp.Mod :=
    burnsideC137_d6Sp4.toMonoidHom.comp ((projK k).comp N.Θ.toMonoidHom)
  have hf : ∀ w, f w = burnsideC137_d6Sp4 (projK k (N.Θ w)) := fun _ => rfl
  have hfρ : ∀ σ w, f (N.ρ σ w) =
      burnsideC137_hDsp.modAct (burnsideC137_theta σ) (f w) := by
    intro σ w
    rw [hf, hf, N.Θ_ρ, projK_act hk, burnsideC137_d6Sp4_act]
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := burnsideC137_d6Sp4.surjective q
    obtain ⟨y, rfl⟩ := projK_surjective hk x
    obtain ⟨w, rfl⟩ := N.Θ.surjective y
    exact ⟨w, rfl⟩
  have hmemX : ∀ σ, N.ρ σ ∈ X₀ := fun σ => hX ▸ ⟨σ, trivial, rfl⟩
  refine ⟨f, hfs, fun w => ?_, fun h hh hfix => ?_, fun h hh => ?_, fun δ => ?_⟩
  · rw [hf, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, burnsideC137_ker_projK hk]
    constructor
    · intro hw l hl
      rw [← N.ρ_alt] at hl
      obtain ⟨γ, hγ, rfl⟩ := hl
      apply N.Θ.injective
      rw [N.Θ_ρ]
      exact hw _ ⟨γ, hγ, rfl⟩
    · intro hw x hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [← N.Θ_ρ]
      congr 1
      have hmem : N.ρ γ ∈ L₀ := by
        have h := Subgroup.mem_map_of_mem N.ρ hγ
        rw [N.ρ_alt] at h
        exact h
      exact hw _ hmem
  · rw [← hX] at hh
    obtain ⟨σ, -, rfl⟩ := hh
    have h1 : burnsideC137_hDsp.modAct (burnsideC137_theta σ) = 1 := by
      ext q
      obtain ⟨w, rfl⟩ := hfs q
      rw [← hfρ, MulAut.one_apply]
      exact hfix w
    have h2 : burnsideC137_theta σ = 1 :=
      burnsideC137_hDsp_injective (h1.trans (map_one _).symm)
    have h3 : σ = 1 := burnsideC137_theta.injective (h2.trans (map_one _).symm)
    rw [h3, map_one]
  · rw [← hX] at hh
    obtain ⟨σ, -, rfl⟩ := hh
    exact ⟨burnsideC137_theta σ, hfρ σ⟩
  · obtain ⟨σ, rfl⟩ := burnsideC137_theta.surjective δ
    exact ⟨N.ρ σ, hmemX σ, hfρ σ⟩

end CFSG.ASVolI
