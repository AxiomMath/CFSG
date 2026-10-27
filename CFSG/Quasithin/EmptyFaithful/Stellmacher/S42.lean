module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Hss113cAt (H M : Subgroup G) : Prop :=
  ∀ δ δ' : Geo H M, IsCritPair₁ δ δ' → ⁅Zv δ, Zv δ'⁆ ≠ ⊥ → vtype δ = false →
    IsNatSec (stab δ) (Zv δ ⊓ Subgroup.centralizer (oTwoRes (stab δ) : Set G)) (Zv δ) ∨
      IsOrthSec (stab δ) (Zv δ ⊓ Subgroup.centralizer (oTwoRes (stab δ) : Set G)) (Zv δ)

@[expose] def Hss42CommAt (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = false →
    (∀ μ : Geo H M, (graph (H ⊔ M) H M).Adj α μ → bMin H M < bAt μ) →
    ⁅Zv α, Zv α'⁆ = ⊥ → IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α)

theorem hss42At_of (hA : F53Amalgam H M S) (h41 : Hss41At H M) (h113c : Hss113cAt H M)
    (hcomm : Hss42CommAt H M)
    (hC : ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → Zv β ≤ centerOf (stab β) →
      Zv α ⊓ Subgroup.centralizer (oTwoRes (stab α) : Set G) = ⊥) :
    Hss42At H M := by
  intro α hα hαb hnb
  obtain ⟨β, hαβ⟩ := exists_adj α
  obtain ⟨α', hc⟩ := exists_critData hA hαb hαβ
  by_cases hz : ⁅Zv α, Zv α'⁆ = ⊥
  · exact hcomm α β α' hc hα hnb hz
  · have hzβ := h41 α β hαβ hα hαb (hnb β hαβ)
    have h0 := hC α β hαβ hzβ
    rcases h113c α α' ⟨hc.not_le, hc.dist_eq⟩ hz hα with hn | ho
    · rw [h0] at hn
      exact Or.inr hn
    · rw [h0] at ho
      exact Or.inl ho

theorem hss42At_of_hss113c (hA : F53Amalgam H M S) (h41 : Hss41At H M)
    (h113c : Hss113cAt H M) (hcomm : Hss42CommAt H M) : Hss42At H M :=
  hss42At_of hA h41 h113c hcomm fun _ _ hαβ hz =>
    EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_oTwoRes_eq_bot hA hαβ hz

end F53.Stellmacher

end CFSG.Quasithin
