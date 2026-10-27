module

public import CFSG.Quasithin.Background.SmithB42Alt6Norm
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Assembly.LowTwoRank Equiv Equiv.Perm B5FinSp Matrix
  CFSG.ComponentClassification.PresentationLocal

variable {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}

theorem ehat_permAct {K : Type} [Field K] (c : ZMod 2 ≃+* K) (σ : Perm (Fin 6))
    (m : ↥(G6.coreMod 6)) :
    ((ehat c ⟨G6.permAct 6 σ (m : G6.PermMod 6), G6.permAct_mem_coreMod σ m.2⟩ :
        ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)))) :
        Multiplicative (Fin 2 ⊕ Fin 2 → K)) =
      natAct (StatedSp 2 K) (theta c σ)
        ((ehat c m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)))) :
          Multiplicative (Fin 2 ⊕ Fin 2 → K)) := by
  have hmc : (m : G6.PermMod 6) ∈ G6.coreMod 6 := m.2
  have hσ : omegaPerm (omegaEquiv.symm σ) = σ := omegaEquiv.apply_symm_apply σ
  have h1 := chiHom_permAct (omegaEquiv.symm σ) hmc
  rw [hσ] at h1
  change lhom c (chiHom (G6.permAct 6 σ (m : G6.PermMod 6))) =
    Multiplicative.ofAdd ((((theta c σ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Multiplicative.toAdd (lhom c (chiHom (m : G6.PermMod 6))))
  rw [h1]
  exact congrArg Multiplicative.ofAdd
    (theta_mulVec_lfun c σ (Multiplicative.toAdd (chiHom (m : G6.PermMod 6)))).symm

theorem ehat_ker {K : Type} [Field K] (c : ZMod 2 ≃+* K) (m : ↥(G6.coreMod 6)) :
    ((ehat c m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)))) :
        Multiplicative (Fin 2 ⊕ Fin 2 → K)) ∈
        (FFModel.nat (StatedSp 2 K)).ker ↔
      (m : G6.PermMod 6) ∈ (FFModel.symDn 6).ker := by
  change lhom c (chiHom (m : G6.PermMod 6)) ∈ (⊥ : Subgroup _) ↔ _
  rw [Subgroup.mem_bot, ← map_one (lhom c), (lhom_injective c).eq_iff]
  exact chiHom_eq_one_iff m.2

theorem N6Model.binaryNaturalSp4 (M : N6Model L) {H : Subgroup (MulAut S)}
    (hH : ∀ σ, M.ρ σ ∈ H) (hH' : ∀ h ∈ H, ∃ σ, M.ρ σ = h) : BinaryNaturalSp4 H ⊤ ⊥ 1 := by
  let c : ZMod 2 ≃+* ZMod 2 := RingEquiv.refl _
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  let E : (FFModel.symDn 6).Mod ≃* (FFModel.nat (StatedSp 2 (ZMod 2))).Mod :=
    FFModel.modEquivOfSurj (ehat c) (ehat_surjective c) (ehat_ker c)
  let π' : ↥(StatedSp 2 (ZMod 2)) →* ↥H :=
    (M.ρ.codRestrict H hH).comp (theta c).symm.toMonoidHom
  refine ⟨π', realizesVia_of_modEquiv (FFModel.nat_isActionModel _) H π' ?_
    (M.modEquiv.trans E) ?_⟩
  · intro h
    obtain ⟨σ, hσ⟩ := hH' h h.2
    refine ⟨theta c σ, Subtype.ext ?_⟩
    show M.ρ ((theta c).symm (theta c σ)) = h
    rw [MulEquiv.symm_apply_apply, hσ]
  · intro (g : ↥(StatedSp 2 (ZMod 2))) v m hm hv
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ↥(G6.coreMod 6),
        (QuotientGroup.mk m₀ : (FFModel.symDn 6).Mod) = M.modEquiv v :=
      QuotientGroup.mk_surjective _
    have h1 : E (QuotientGroup.mk m₀) = QuotientGroup.mk (ehat c m₀) := rfl
    have h2 : ehat c m₀ = m := by
      have h3 : E (M.modEquiv v) = QuotientGroup.mk m := hv
      rw [← hm₀, h1] at h3
      have h4 := QuotientGroup.eq.1 h3
      have h5 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h4)
      exact inv_mul_eq_one.1 (Subtype.ext h5)
    set σ := (theta c).symm g with hσ
    have h3 := M.modEquiv_act σ v m₀ (G6.permAct_mem_coreMod σ m₀.2) hm₀.symm
    show E (M.modEquiv (M.ρ σ v)) = _
    have h4 : E (QuotientGroup.mk ⟨G6.permAct 6 σ (m₀ : G6.PermMod 6),
        G6.permAct_mem_coreMod σ m₀.2⟩) = QuotientGroup.mk (ehat c ⟨G6.permAct 6 σ
          (m₀ : G6.PermMod 6), G6.permAct_mem_coreMod σ m₀.2⟩) := rfl
    rw [h3, h4]
    congr 1
    apply Subtype.ext
    rw [ehat_permAct, hσ, MulEquiv.apply_symm_apply, h2]
    rfl

end B42Alt6

end CFSG.Quasithin
