module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def dbl5 : ↥(alternatingGroup (Fin 5)) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem dbl5_ne_one : dbl5 ≠ 1 := by
  intro h
  have := congrArg (fun σ : ↥(alternatingGroup (Fin 5)) => (σ : Perm (Fin 5)) 0) h
  revert this
  decide

theorem dbl5_sq : dbl5 ^ 2 = 1 := by
  apply Subtype.ext
  show (swap (0 : Fin 5) 1 * swap 2 3) ^ 2 = 1
  decide

theorem fix_dbl5 : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
    (∀ i, y i = y (((swap (0 : Fin 5) 1 * swap 2 3)⁻¹ : Perm (Fin 5)) i)) →
      y 0 = y 1 ∧ y 2 = y 3 ∧ y 4 = 0 := by
  decide

theorem card_fix_dbl5 :
    Fintype.card {y : Fin 5 → ZMod 2 // y 0 = y 1 ∧ y 2 = y 3 ∧ y 4 = 0} = 4 := by
  decide

theorem exists_inv_two_card_le (h5 : IsAltType K 5) (hZ : blockZ K = ⊥) :
    ∃ k ∈ K, k ∉ blockQ K ∧ k ^ 2 ∈ blockQ K ∧
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer ({k} : Set G)) ≤ 4 := by
  obtain ⟨α, hα, hαk, β, -, hβk, hβe⟩ := h5
  have hmemQ : ∀ x : ↥K, (x : G) ∈ blockQ K ↔ α x = 1 := by
    intro x
    rw [← MonoidHom.mem_ker, hαk]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hα dbl5
  refine ⟨k, k.2, fun h => dbl5_ne_one (hk ▸ (hmemQ k).mp h), ?_, ?_⟩
  · have := (hmemQ (k ^ 2)).mpr (by rw [map_pow, hk, dbl5_sq])
    simpa using this
  · have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
    let φ : ↥(blockU K ⊓ Subgroup.centralizer ({(k : G)} : Set G)) →
        {y : Fin 5 → ZMod 2 // y 0 = y 1 ∧ y 2 = y 3 ∧ y 4 = 0} := fun u =>
      ⟨((Multiplicative.toAdd (β ⟨u, u.2.1⟩) : evenWeight 5) : Fin 5 → ZMod 2), by
        apply fix_dbl5
        · exact (Multiplicative.toAdd (β ⟨u, u.2.1⟩)).2
        · intro i
          have hc : (k : G) * (u : G) * (k : G)⁻¹ = u := by
            have := Subgroup.mem_centralizer_singleton_iff.mp u.2.2
            rw [← this, mul_inv_cancel_right]
          have := hβe k ⟨u, u.2.1⟩ ⟨u, u.2.1⟩ hc.symm i
          rw [hk] at this
          exact this⟩
    have hφ : Function.Injective φ := by
      intro u v huv
      have h0 := congrArg Subtype.val huv
      have h1 : (Multiplicative.toAdd (β ⟨u, u.2.1⟩) : evenWeight 5) =
          Multiplicative.toAdd (β ⟨v, v.2.1⟩) := Subtype.ext h0
      have h2 := hβinj (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj h2)
    calc Nat.card ↥(blockU K ⊓ Subgroup.centralizer ({(k : G)} : Set G))
        ≤ Nat.card {y : Fin 5 → ZMod 2 // y 0 = y 1 ∧ y 2 = y 3 ∧ y 4 = 0} :=
          Nat.card_le_card_of_injective φ hφ
      _ = 4 := by rw [Nat.card_eq_fintype_card, card_fix_dbl5]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
