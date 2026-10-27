module

public import CFSG.Quasithin.MS93.S4A441B6
public import CFSG.Quasithin.MS93.S4A441B7

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S441C2NoSec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
      ∀ ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F), Function.Surjective ψ →
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α) (Uloc h.le L α) ⊥ ψ false 1 →
      ∀ (dual : Bool) (C : Subgroup (puAmalgam h.le).Universal),
        ¬ (Uloc h.le L α ≤ C ∧ ⁅C, stab (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α ∧
          ⁅conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ), Qv (puAmalgam h.le) α⁆ ≤
            Uloc h.le L α ⊔ Dloc h.le L α ∧
          IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
            (conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ)) C ψ dual 1 ∧
          ∀ w ∈ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ),
            ∀ g ∈ stab (puAmalgam h.le) α, w⁻¹ * (g * w * g⁻¹) ∈ C →
              w⁻¹ * (g * w * g⁻¹) ∈ Uloc h.le L α ⊔ Dloc h.le L α)

theorem s441C2Cent_of (h32 : S32) (h43 : S43) (hsec : S441C2NoSec) : S441C2Cent := by
  intro G _ _ M T L h F _ _ φ hH hb α α' μ hc hfail hc1 hconj x hx hxD hxB
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hV := h43 G M T L h hH.1 hH.2.1 hfull
  have hμ := mem_nablaSet_of_conj h hfull hC hH.2.1 hV hc hconj
  have hH0 : ¬ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α :=
    fun hle => hxD (hle hx)
  have hQUD := commutator_zm_qv_le_of_le_bloc h hH.2.2 hH.2.1 hc.1 hμ.1 hxB hH0
  rcases exists_good_conj_or_secD h hH.2.2 hC hb hc hμ hQUD hx hxD with
    hgood | ⟨ψ, dual, C, hψs, hψ, hsecD⟩
  · exact hgood
  · exact absurd hsecD
      (hsec G M T L h F inferInstance inferInstance φ hH hb α α' μ hc hfail hc1 hconj ψ hψs hψ
        dual C)

end CFSG.Quasithin.MS93.S4A.C441
