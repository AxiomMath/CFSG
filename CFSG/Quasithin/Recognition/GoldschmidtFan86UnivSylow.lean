module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore

public section

namespace CFSG.Quasithin.Fan86.Univ

variable {G : Type*} [Group G] [Finite G] {E : Subgroup G}

theorem pCore_le_of_index_odd (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index) :
    Open.pCore 2 G ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp : IsPGroup 2 (Open.pCore 2 G) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  exact hp.le_sylow_of_normal (hE.toSylow hodd)

theorem normalCore_eq_pCore (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index) :
    E.normalCore = Open.pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  refine le_antisymm ?_ (Subgroup.normal_le_normalCore.2 (pCore_le_of_index_odd hE hodd))
  exact CFSG.LieType.BorelTits.le_pCore 2 E.normalCore_normal (hE.to_le E.normalCore_le)

theorem mem_pCore_of_forall_conj_mem (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index) {h : G}
    (hh : ∀ c : G, c⁻¹ * h * c ∈ E) : h ∈ Open.pCore 2 G := by
  rw [← normalCore_eq_pCore hE hodd]
  intro c
  simpa using hh c⁻¹

theorem conj_mem_of_mem_pCore (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index) {h : G}
    (hh : h ∈ Open.pCore 2 G) (c : G) : c⁻¹ * h * c ∈ E := by
  have hn : (Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : c⁻¹ * h * c ∈ Open.pCore 2 G := by simpa using hn.conj_mem h hh c⁻¹
  exact pCore_le_of_index_odd hE hodd h1

theorem exists_mem_not_forall (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index)
    (hne : ∃ e ∈ E, e ∉ Open.pCore 2 G) (a : G) :
    ∃ h : G, a⁻¹ * h * a ∈ E ∧ ¬ ∀ c : G, c⁻¹ * h * c ∈ E := by
  have hn : (Open.pCore 2 G).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  obtain ⟨e, he, hek⟩ := hne
  have h1 : a⁻¹ * (a * e * a⁻¹) * a = e := by group
  refine ⟨a * e * a⁻¹, by rwa [h1], fun hall => hek ?_⟩
  have h2 := hn.conj_mem _ (mem_pCore_of_forall_conj_mem hE hodd hall) a⁻¹
  have h3 : a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ = e := by group
  rwa [h3] at h2

theorem exists_mem_not_mem_pCore (hE : IsPGroup 2 E) (hodd : ¬ 2 ∣ E.index)
    (hQ : Nat.card (oTwoQuot G) ≠ E.index) : ∃ e ∈ E, e ∉ Open.pCore 2 G := by
  by_contra hcon
  have hle : E ≤ Open.pCore 2 G := fun e he => by
    by_contra h
    exact hcon ⟨e, he, h⟩
  have heq : E = Open.pCore 2 G := le_antisymm hle (pCore_le_of_index_odd hE hodd)
  have h1 : E.index * Nat.card (Open.pCore 2 G) = Nat.card G := by
    rw [← heq]
    exact E.index_mul_card
  have h2 := Model.card_oTwoQuot_mul G
  have hpos : 0 < Nat.card (Open.pCore 2 G) := Nat.card_pos
  exact hQ (Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm))

end CFSG.Quasithin.Fan86.Univ
