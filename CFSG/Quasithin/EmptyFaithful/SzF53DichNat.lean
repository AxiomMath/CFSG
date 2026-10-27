module

public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResAux
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_F53EData_of_natural (hA : F53Amalgam H M S) {E : Subgroup G} (hE : F53EData H S E)
    (hnat : IsNatSec H ⊥ (VZ S H))
    (hirr : ∀ N : Subgroup G, ⊥ ≤ N → N ≤ VZ S H → H ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = VZ S H)
    (hno : ¬ IsOrthSec H ⊥ (VZ S H)) : False := by
  have hq := hA.quot_left
  have hSH : S ≤ H := hA.amalgam.sylow₁.1
  have hS2 : IsPGroup 2 S := hA.amalgam.sylow₁.2.1
  have hEH : E ≤ H := hE.le.trans hSH
  have hEne : E ≠ ⊥ := by
    intro h
    have := F53EData.card_ge hq hSH hE
    rw [h] at this
    simp at this
  have hSn : S ≤ Subgroup.normalizer (E : Set G) := fun s hs => hE.normal (hSH hs)
  obtain ⟨x, hxE, hx1, hx2, hxc⟩ := C134Res.exists_involution_central hS2 hE.le hSn hEne
  have hxZ : x ∈ VZ S H := by
    apply le_conjClosure
    apply Subgroup.subset_closure
    exact ⟨⟨hE.le hxE, Subgroup.mem_centralizer_iff.mpr fun t ht => hxc t ht⟩, hx2⟩
  have hZN : H ≤ Subgroup.normalizer (VZ S H : Set G) := le_normalizer_conjClosure _ _
  have hinfN : H ≤ Subgroup.normalizer ((E ⊓ VZ S H : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hE.normal hg, hZN hg⟩
  have hZE : VZ S H ≤ E := by
    rcases hirr (E ⊓ VZ S H) bot_le inf_le_right hinfN with h | h
    · exfalso
      have : x ∈ E ⊓ VZ S H := ⟨hxE, hxZ⟩
      rw [h, Subgroup.mem_bot] at this
      exact hx1 this
    · exact inf_eq_right.mp h
  have hZne : VZ S H ≠ ⊥ := fun h => hx1 (by rw [h, Subgroup.mem_bot] at hxZ; exact hxZ)
  have hstep : IsChiefStep H E ⊥ (VZ S H) :=
    ⟨F112W.isNormalIn_of_le_normalizer hZE hZN, D15Proof.isNormalIn_bot H E,
      bot_lt_iff_ne_bot.mpr hZne, fun K hK hbot hKZ =>
        hirr K hbot hKZ (D14.le_normalizer_of_isNormalIn hK)⟩
  have hnc : ¬ IsCentralStep H ⊥ (VZ S H) := by
    intro hc
    obtain ⟨_, θ, β, hθs, hθk, _⟩ := hnat
    have hall : ∀ g : ↥H, θ g = 1 := by
      intro g
      have hg : (g : G) ∈ cSecIn H ⊥ (VZ S H) :=
        Subgroup.subset_closure ⟨g.2, fun x hx => hc g g.2 x hx⟩
      have : g ∈ θ.ker := by
        rw [hθk]; exact hg
      exact this
    obtain ⟨g, hg⟩ := hθs (Equiv.swap (0 : Fin 5) 1)
    rw [hall g] at hg
    have h01 : (Equiv.swap (0 : Fin 5) 1) (0 : Fin 5) = 1 := by decide
    have := congrArg (fun σ : Equiv.Perm (Fin 5) => σ 0) hg
    simp at this
  obtain ⟨_, _, hN, hNat⟩ := F53EData.shape_five hq hE hstep hnc
  have := hN
  exact hno ((naturalSn_five_iff (F := H) (L := ⊥) (X := VZ S H)).mp hNat)

end F53

end CFSG.Quasithin
