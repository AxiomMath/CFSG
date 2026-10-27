module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Card
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3c
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34CaseI
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34CaseII

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem good_of_PD (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) {δ δ' : Geo H M}
    (hp : PD δ δ') : Good δ := by
  by_contra hgood
  have hng : NG H M := fun δ₁ hδ₁ h => hgood (Good.of_vtype hδ₁ hp.vδ h)
  obtain ⟨α, hα, hbad⟩ : ∃ α ∈ nbrs δ, ¬ Zv α ≤ Qv δ' := by
    by_contra hcon
    push Not at hcon
    exact hp.not_le (iSup₂_le fun α hα => hcon α hα)
  by_cases h3 : bMin H M = 3
  · exact c3_bMin_ne_three hG hirr h15 hng hp h3
  · have hb5 : 5 ≤ bMin H M := by
      obtain ⟨k, hk⟩ := hG.odd
      have := hG.three_le
      omega
    by_cases hW : ∀ γ ∈ nbrs α, γ ≠ δ → Vn γ ≤ Vn δ ⊔ Qv δ'
    · exact case_i_false hG hirr h15 hng hp hb5 hα hbad hW
    · push Not at hW
      obtain ⟨γ, hγ, hγδ, hγW⟩ := hW
      exact case_ii_false hG hirr h15 hng hp hb5 hα hbad hγ hγδ hγW

end S34

theorem hss34At_of {G : Type} [Group G] [Finite G] {H M S : Subgroup G} (hA : F53Amalgam H M S)
    (h28 : Hss28At H M) (hirr : IrrSecSec) (h15 : Hss15Sec) :
    Hss34At H M := by
  intro α β α' hc hα hz
  have hG := S34.Glob.of_crit hA h28 hc hα hz
  have hvβ : vtype β = false := by
    cases h : vtype β
    · rfl
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
  have hvα' : vtype α' = false := by
    rw [(hss114_ab hA hc hz (by have := hG.three_le; omega)).2.2]
    exact hvβ
  have hαβ : α ∈ nbrs β := hc.adj.symm
  have hp : S34.PD β α' := by
    refine ⟨hvβ, hvα', hc.dist_eq', fun hle => hc.not_le ?_⟩
    refine (le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs β) => Zv ν) α hαβ le_rfl).trans
      hle
  have hgood := S34.good_of_PD hG hirr h15 hp
  have hZβ := hG.central β hvβ
  have hcard2 := S34.card_Zv_eq_two_of_good hG hvβ hgood
  refine ⟨?_, hcard2, by have := hG.three_le; omega, hgood⟩
  rw [EmptyFaithful.Stellmacher.OrdinaryProofs.card_Zv_eq_sq hA hα hc.adj hZβ, hcard2]
  norm_num

end F53.Stellmacher

end CFSG.Quasithin
