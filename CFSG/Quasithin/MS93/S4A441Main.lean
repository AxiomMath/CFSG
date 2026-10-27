module

public import CFSG.Quasithin.MS93.S4A441D
public import CFSG.Quasithin.MS93.S4A441W
import CFSG.Quasithin.MS93.ML3Pair
public import CFSG.Quasithin.MS93.S4A441C3

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S441C1Dual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      ∀ ψ : ↥(stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)) →* ↥(StatedSL 3 F),
        Function.Surjective ψ →
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2))
          (Uloc h.le L (geo (puAmalgam h.le) α α' 2)) ⊥ ψ false 1 →
        ∀ C : Subgroup (puAmalgam h.le).Universal,
          ¬ L441.IsSecD h.le L (geo (puAmalgam h.le) α α' 2) ψ true
            (conjCl (stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2))
              (ZM (puAmalgam h.le) α)) C

@[expose] def S441End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      False

namespace L441

section Claim1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ)
include h hH

theorem not_isC1_of_fail (hdual : S441C1Dual) (hb : 4 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hfail : ∀ g : (puAmalgam h.le).Universal,
      ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2))
    (g : (puAmalgam h.le).Universal) :
    ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
      (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
        (ZM (puAmalgam h.le) (g • α)))
      (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2)) := by
  intro hc1
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc₁ : IsCritical (puAmalgam h.le) (g • α) (g • α') := (isCritical_smul _ g α α').mpr hc
  have hgeo2 : geo (puAmalgam h.le) (g • α) (g • α') 2 = g • geo (puAmalgam h.le) α α' 2 :=
    geo_smul _ g α α' 2
  have hα₁ : IsMVtx (puAmalgam h.le) (g • α) := hc₁.1
  have hγ₁ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) (g • α) (g • α') 2) :=
    isMVtx_geo_two _ h20 hb0 hc₁
  have hαβ : (puAmalgam h.le).treeGraph.Adj (g • α) (geo (puAmalgam h.le) (g • α) (g • α') 1) :=
    adj_geo_one_of_isCritical _ hb0 hc₁
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) (g • α) (g • α') 1)
      (geo (puAmalgam h.le) (g • α) (g • α') 2) :=
    adj_geo _ (i := 1) (by rw [hc₁.2.1]; omega)
  rw [← hgeo2] at hc1
  have hfail₁ : ¬ Concl441 h.le L (g • α) (geo (puAmalgam h.le) (g • α) (g • α') 2) := by
    rw [hgeo2]
    exact hfail g
  have hH₁ : ¬ ⁅ZM (puAmalgam h.le) (g • α),
      Qv (puAmalgam h.le) (geo (puAmalgam h.le) (g • α) (g • α') 2)⁆ ≤
        Dloc h.le L (geo (puAmalgam h.le) (g • α) (g • α') 2) :=
    fun hle => hfail₁ fun hH' => absurd hle hH'
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hγ₁
  obtain ⟨dual, hPK⟩ :=
    exists_dual_of_isC1' h hγ₁ hφ (le_normalizer_conjCl _ _) hc1 hψs hψ
  obtain ⟨C, hs⟩ :=
    exists_isSecD_of_isC1 h hfull hb hφ hα₁ hγ₁ hαβ hβγ hH₁ hψs hψ hc1 hPK
  cases dual
  · exact hfail₁ (concl441_of_secD h hfull ms17i_holds hb hφ hα₁ hγ₁ hαβ hβγ hψs hψ hs)
  · refine hdual G M T L h F inferInstance inferInstance φ hH hb (g • α) (g • α') hc₁
      (fun g' => ?_) ψ hψs hψ C hs
    rw [hgeo2, ← mul_smul, ← mul_smul]
    exact hfail (g' * g)

end Claim1

end L441

theorem s441_of (hdual : S441C1Dual) (hend : S441End) : S441 := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc
  by_contra hfail₀
  have hfail : ∀ g : (puAmalgam h.le).Universal,
      ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2) := fun g hg =>
    hfail₀ ((concl441_smul h g α (geo (puAmalgam h.le) α α' 2)).mp hg)
  exact hend G M T L h F inferInstance inferInstance φ hH hb α α' hc hfail
    (L441.not_isC1_of_fail h hH hdual hb hc hfail)

end CFSG.Quasithin.MS93.S4A
