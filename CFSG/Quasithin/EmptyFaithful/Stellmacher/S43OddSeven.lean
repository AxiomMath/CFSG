module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSevenB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSevenC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem exists_transvec_of_caseS (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb7 : 7 ≤ bMin H M) (hS : ∀ δ ∈ nbrs α, Nat.card (Vn δ) = 2 ^ 6) :
    ∃ x : G, x ∈ stab α ∧ x ∉ Qv α ∧ IsTransvec 1 x (Zv α) (Wn α) := by
  have hb5 : 5 ≤ bMin H M := by omega
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  obtain ⟨β, ν, hβ, hν, -, hdν, hdβ⟩ := Core.exists_crit_data hA hs hc
  obtain ⟨κ, hκ, hdκ⟩ := Core.exists_nbr_dist hA (x := α) (y := ν) (n := bMin H M - 2)
    (by omega)
  have hdκ' : dist α κ + 2 = bMin H M := by omega
  obtain ⟨l, l', h29⟩ := Core.exists_sit29_nu hA h26 hs ho hc hν
  have d : Twelve.Data α α' ν β l := ⟨hc, hν, hdν, hβ, hdβ, h29.n₂, h29.ne₁₂.symm⟩
  have h6β : Nat.card (Vn β) = 2 ^ 6 := hS β hβ
  have h6 : Nat.card (Vn α') = 2 ^ 6 := by
    rw [card_Vn_eq (Core.vtype_crit hA hs ho hc) (Core.vtype_beta hs hβ)]
    exact h6β
  obtain ⟨u, hu, huQ⟩ : ∃ u ∈ Zv l ⊓ Qv β, u ∉ Qv α := by
    by_contra hcon
    push Not at hcon
    exact crit4c hA h26 hs ho (by omega) hc hν hdν hβ hdβ h29.n₂ h29.ne₁₂.symm
      fun x hx => hcon x hx
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hWν := Seven.Wn_le_stab hA h26 hs ho hb5 d hκ hdκ' h6
  obtain ⟨w₀, hw₀, hw₀Q⟩ : ∃ w ∈ Wn α, w ∉ Qv ν := by
    by_contra hcon
    push Not at hcon
    exact Seven.not_Wn_le_Qv hA h26 hs ho hb5 d h6β h6 fun x hx => hcon x hx
  refine ⟨u, huα, huQ, ?_, ?_⟩
  · have hpos := secIdx_pos (Subgroup.zpowers u) (Zv α) (Wn α)
    have hne : secIdx (Subgroup.zpowers u) (Zv α) (Wn α) ≠ 1 := by
      intro h1
      have hWZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
        ((hs.Wn_le_Qv hA (by omega)).trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
      have h := (secIdx_eq_one_iff hWZ (stab_le_normalizer_Zv hA α huα)).mp h1
      apply huQ
      refine hs.faithful hA h26 (by omega) hs.vα hβ h6β huα fun w hw => ?_
      have e : ⁅w, u⁆ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Zv α).inv_mem (h w hw)
    omega
  · exact (Seven.secIdx_le_two hA h26 hs ho hb5 d h6 hWν hw₀ hw₀Q D hu huQ).trans
      (by norm_num)

theorem oddEndAt (H M : Subgroup G) : OddEndAt H M := by
  intro S hA h26 α hs ho hb7 β hβ h6
  have hS : ∀ δ ∈ nbrs α, Nat.card (Vn δ) = 2 ^ 6 := fun δ hδ => by
    rw [card_Vn_eq (Core.vtype_beta hs hδ) (Core.vtype_beta hs hβ)]
    exact h6
  obtain ⟨x, hx, -, hxt⟩ := exists_transvec_of_caseS hA h26 hs ho hb7 hS
  exact Even.false_of_transvec hA h26 hs (by omega) hβ h6
    (hs.comm_Wn_Qv_le hA h26 (by omega) hs.vα hβ h6) hx hxt

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
