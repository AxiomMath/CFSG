module

public import CFSG.Quasithin.EmptyFaithful.S1469CaseA1
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA2
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA3
public import CFSG.Quasithin.EmptyFaithful.S1422Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts1469_of_ctxA5 (i4 : Input1469A5J) (i5 : Input1469A5C567)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four) (h5 : Stage1461Five)
    {H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) : Facts1469A5 T M u I K₁ K₂ :=
  let hc := Setting146.facts1469_c i4 h1 h2 h4 c
  let hd := Setting146.facts1469_d h1 h2 h4 c hc
  let he := Setting146.facts1469_e c hc
  let hf := Setting146.facts1469_f h5 c he
  let hg := Setting146.facts1469_g i5 h1 h2 h4 c hd
  ⟨hc, hd, he, hf, hg.1, hg.2.1, hg.2.2⟩

theorem Setting146.dOf1469_eq_bot (i6a : Input1469A5DOne) (i6b : Input1469A5DTwo)
    {H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (hf : Facts1469A5 T M u I K₁ K₂) :
    dOf1469 T I K₁ K₂ = ⊥ := by
  by_contra hD
  by_cases hLT : yOfL22 T M ⊔ T =
      (lD1469 T M (dOf1469 T I K₁ K₂) ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)
  · exact i6a G T M H u I K₁ K₂ ρ c hf hD hLT
      (c.ctx.setting.hyp.inf_centralizer_yOfL22_eq_bot c.ctx.setting.facts)
  · exact i6b G T M H u I K₁ K₂ ρ c hf hD hLT

theorem Setting146.caseA_false (i1 : Input1469C126) (i2 : Input1469Lin2) (i3 : Input1469C61)
    (i4 : Input1469A5J) (i5 : Input1469A5C567) (i6a : Input1469A5DOne) (i6b : Input1469A5DTwo)
    (i7 : Input1469A5Fin) (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four)
    (h5 : Stage1461Five) {H : Subgroup G} {u : G} {I : Subgroup G} (c : Ctx1469 T M H u I)
    (hchar : CharTwo I) : False := by
  obtain ⟨K₁, K₂, ρ, cA⟩ := Setting146.ctxA5_of_ctx i1 i2 i3 h1 h2 h4 c hchar
  have hf := Setting146.facts1469_of_ctxA5 i4 i5 h1 h2 h4 h5 cA
  exact i7 G T M H u I K₁ K₂ ρ cA hf (Setting146.dOf1469_eq_bot i6a i6b cA hf)

end CFSG.Quasithin
