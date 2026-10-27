module

public import CFSG.Quasithin.Recognition.M12AscCountG
public import CFSG.Quasithin.Recognition.M12AscFive
public import CFSG.Quasithin.Recognition.M12AscEx166
public import CFSG.Quasithin.Recognition.M12AscSetup
public import CFSG.Quasithin.Recognition.M12AscTail
public import CFSG.Quasithin.Recognition.M12AscPin

public section

namespace CFSG.Quasithin

open CFSG.GH74.M12 (Asc03Hyp q8Subgroups S_Asc03_simple)
open CFSG.Blueprint

@[expose] def Asc86a_Ex166 : Prop :=
  ∀ (I : Type) [Group I] [Finite I] (K V : Subgroup I) (z y : I), KleinCore K V z y →
    Nonempty (↥K ≃* ↥(alternatingGroup (Fin 4))) ∨ Nonempty (↥K ≃* ↥(alternatingGroup (Fin 5)))

structure M10Amalgam {G : Type*} [Group G] (L K : Subgroup G) (v z r : G) : Prop where
  KL : K ≤ L
  L_card : Nat.card ↥L = 720
  pts : Nat.card (↥L ⧸ K.subgroupOf L) = 10
  L3 : ∀ a b : Fin 3 → (↥L ⧸ K.subgroupOf L), Function.Injective a → Function.Injective b →
    ∃! g : ↥L, ∀ i, g • a i = b i
  Q8 : ∃ l₀ ∈ L, l₀ ∉ K ∧ ∃ H : Subgroup G, (∀ g, g ∈ H ↔ g ∈ K ∧ l₀⁻¹ * g * l₀ ∈ K) ∧
    Nonempty (↥H ≃* QuaternionGroup 2)
  v_sq : v * v = 1
  v_K : ∀ k ∈ K, v * k * v⁻¹ ∈ K
  v_L : ∃ l ∈ L, v * l * v⁻¹ ∉ L
  r_L : r ∈ L
  r_K : r ∉ K
  r_sq : r * r = 1
  rv : (r * v) ^ 3 = 1
  z_sq : z * z = 1
  z_L : ∀ l ∈ L, z * l * z⁻¹ ∈ L
  z_n : z ∉ L
  vz : (v * z) ^ 3 = 1

@[expose] def Asc03b_M10Amalgam : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ z : G, Asc03Hyp G z →
    (∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))), K.Normal) →
    Nat.card G = 95040 → ∃ (L K : Subgroup G) (v z' r : G), M10Amalgam L K v z' r

theorem isSporadic_M12_of_M10Amalgam
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 95040) {L K : Subgroup G} {v z r : G} (h : M10Amalgam L K v z r) :
    NativeSporadic.IsSporadic G .M12 := by
  obtain ⟨M, hM, hfaith, hsharp, hQ⟩ := exists_sharply_five_transitive_of_M10_amalgam hG L K h.KL
    v z r h.L_card h.pts h.L3 h.Q8 h.v_sq h.v_K h.v_L ⟨h.r_L, h.r_K, h.r_sq, h.rv⟩ h.z_sq h.z_L
    h.z_n h.vz
  have := hfaith
  exact isSporadic_M12_of_sharply_five_transitive (Ω := G ⧸ M) hM hsharp hQ

theorem S_Asc03_simple_of_inputs
    (h166 : Asc86a_Ex166) (h4 : Asc03b_M10Amalgam) :
    S_Asc03_simple := by
  intro G _ _ hsimple z hyp hq8
  obtain ⟨m⟩ := exists_ascModel_of_asc03_normal_q8 hyp hq8
  obtain ⟨t, y, K, V, hD⟩ := m.exists_IData hyp
  have hcard := m.card_G_formula hyp hD
  have hK : Nat.card K = 12 ∨ Nat.card K = 60 := by
    rcases h166 G K V z y hD.klein with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    · right
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
  have hG : Nat.card G = 12096 ∨ Nat.card G = 95040 := by
    rcases hK with h | h
    · left; rw [hcard, h]
    · right; rw [hcard, h]
  have h95 : Nat.card G = 95040 := m.card_eq_95040 hyp hG
  obtain ⟨L, K', v, z', r, hA⟩ := h4 G hsimple z hyp hq8 h95
  exact isSporadic_M12_of_M10Amalgam h95 hA

theorem asc86a_ex166
    : Asc86a_Ex166 := fun _ _ _ _ _ _ _ h => exists_alt_equiv_of_kleinCore h

theorem S_Asc03_simple_of_M10Amalgam
    (h4 : Asc03b_M10Amalgam) : S_Asc03_simple :=
  S_Asc03_simple_of_inputs asc86a_ex166 h4

end CFSG.Quasithin
