module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut
import CFSG.Quasithin.Background.B5FinSp
import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Id2519.USp4
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem fixedSub_fieldAut_equiv_perm_six {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) :
    Nonempty (↥(fixedSub (fieldAut 2 F σ)) ≃* Equiv.Perm (Fin 6)) := by
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, -, hk⟩ := ringEquiv_involution_facts (f := 2) (by norm_num) hF' hσσ hσ1
  set k := descentField σ with hkdef
  have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
  let Φ : StatedSp 2 k →* StatedProj (StatedSp 2 F) := (proj 2 F).comp (subfieldSpHom 2 k)
  have hΦinj : Function.Injective Φ :=
    UnitaryHigher.proj_bijective_of_charTwo.1.comp (subfieldSpHom_injective k)
  have hrange : fixedSub (fieldAut 2 F σ) = Φ.range := by
    ext p
    constructor
    · intro hp
      obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
      rw [mem_fixedSub, fieldAut_proj] at hp
      have hg : fieldSp 2 F σ g = g := UnitaryHigher.proj_bijective_of_charTwo.1 hp
      obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq hg
      refine ⟨g₀, ?_⟩
      change proj 2 F (subfieldSpHom 2 (descentField σ) g₀) = proj 2 F g
      rw [hg₀]
    · rintro ⟨g₀, rfl⟩
      rw [mem_fixedSub]
      simp only [Φ, MonoidHom.comp_apply]
      rw [fieldAut_proj, fieldSp_subfieldSpHom]
  haveI : Fintype k := Fintype.ofFinite k
  have hk2' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk2
  let c : ZMod 2 ≃+* k := ZMod.ringEquiv k hk2'
  exact ⟨(MulEquiv.subgroupCongr hrange).trans
    ((MonoidHom.ofInjective hΦinj).symm.trans (CFSG.Quasithin.B5FinSp.theta c).symm)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
