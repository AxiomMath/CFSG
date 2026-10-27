module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Frattini

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

local notation "E_[" a ", " b "]" => MulAction.stabilizer G a ⊓ MulAction.stabilizer G b

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_gcircSubgroup {α β : V} (hαβ : Γ.Adj α β) :
    ∃ H : Subgroup G, (H : Set G) = Gcirc Γ G α β ∧ H ≤ E_[α, β] ∧
      H.relIndex E_[α, β] ≤ 2 ∧
      (H = E_[α, β] ↔ (nbrStab Γ G α).relIndex E_[α, β] = 2) := by
  obtain ⟨φ, key, hidx, hdvd, hne⟩ := F.exists_edge_char hαβ
  have : Fact (Fan86.valence Γ α).Prime := ⟨F.valence_isPrime α⟩
  have hp35 : Fan86.valence Γ α = 3 ∨ Fan86.valence Γ α = 5 := F.valence α
  have hmem := F.relIndex_nbrStab_mem_two_four hαβ
  rw [hidx] at hmem ⊢
  let χ : ↥E_[α, β] →* (ZMod (Fan86.valence Γ α))ˣ := (powMonoidHom 2).comp φ
  have hχ : ∀ e : ↥E_[α, β], χ e = 1 ↔ ((e : G) * e) ∈ nbrStab Γ G α := fun e => by
    rw [show ((e : G) * e) = ((e * e : ↥E_[α, β]) : G) from rfl, key, map_mul, ← pow_two]
    rfl
  have hker : (χ.ker.map (E_[α, β]).subtype).subgroupOf E_[α, β] = χ.ker := by
    ext e
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hmemH : ∀ g : G, g ∈ χ.ker.map (E_[α, β]).subtype ↔
      ∃ hg : g ∈ E_[α, β], χ ⟨g, hg⟩ = 1 := fun g => by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, he⟩
    · rintro ⟨hg, h1⟩
      exact ⟨⟨g, hg⟩, h1, rfl⟩
  have hrange : ∀ u ∈ χ.range, u ^ 2 = 1 := by
    rintro _ ⟨e, rfl⟩
    show (φ e ^ 2) ^ 2 = 1
    rw [← pow_mul]
    exact units_pow_four hp35 (φ e)
  have hcard : Nat.card χ.range ≤ 2 := by
    obtain ⟨⟨c, hc⟩, hgen⟩ := IsCyclic.exists_generator (α := χ.range)
    have h1 : orderOf (⟨c, hc⟩ : χ.range) = Nat.card χ.range :=
      orderOf_eq_card_of_forall_mem_zpowers hgen
    have h2 : (⟨c, hc⟩ : χ.range) ^ 2 = 1 := Subtype.ext (hrange c hc)
    exact h1 ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  refine ⟨χ.ker.map (E_[α, β]).subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · ext g
    rw [SetLike.mem_coe, hmemH]
    constructor
    · rintro ⟨hg, h1⟩
      exact ⟨hg, (hχ ⟨g, hg⟩).1 h1⟩
    · rintro ⟨hg, h1⟩
      exact ⟨hg, (hχ ⟨g, hg⟩).2 h1⟩
  · rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    exact hcard
  · constructor
    · intro hH
      by_contra hne2
      have h4 : Nat.card φ.range = 4 := by
        rcases hmem with h | h
        · exact absurd h hne2
        · exact h
      obtain ⟨⟨c, hc⟩, hgen⟩ := IsCyclic.exists_generator (α := φ.range)
      have hord : orderOf (⟨c, hc⟩ : φ.range) = 4 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hgen, h4]
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 hc
      have hg : (e : G) ∈ χ.ker.map (E_[α, β]).subtype := by rw [hH]; exact e.2
      obtain ⟨hg', h1⟩ := (hmemH _).1 hg
      have h2 : (φ e) ^ 2 = 1 := h1
      have h3 : (⟨c, hc⟩ : φ.range) ^ 2 = 1 := Subtype.ext (by subst he; exact h2)
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hord] at this
      omega
    · intro h2
      refine le_antisymm (Subgroup.map_subtype_le _) (fun g hg => ?_)
      rw [hmemH]
      refine ⟨hg, ?_⟩
      have h3 : (⟨φ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : φ.range) ^ Nat.card φ.range = 1 := pow_card_eq_one'
      rw [h2] at h3
      exact congrArg Subtype.val h3

end FanTree

end CFSG.Quasithin.Fan86
