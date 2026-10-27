module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cY
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubC
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cQ8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D]

section Sub

variable {A B : Subgroup D} {z : D} {V : Subgroup D}
variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.exists_t (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ t : D, t ∈ pCoreOf 2 B ∧ t * t = 1 ∧ t ∉ pCoreOf 2 A := by
  obtain ⟨q₀, h₀, hinv⟩ := g.exists_q₀_invol hU hT
  refine ⟨q₀, q₀.2, hinv, fun hQ => ?_⟩
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hc : a * (q₀ : D) = (q₀ : D) * a := g.V_comm_QA g.a_mem hQ
  have : a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ = 1 := by rw [hc]; group
  rw [this] at hqa
  exact g.hyp.natural.z_ne hqa.symm

theorem Gen3.exists_subData (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ (Y W : Subgroup D) (y : D), SubData A (A ⊓ B) Y W y ∧
      Nonempty (↥Y ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  obtain ⟨y, hyA, hy3⟩ := g.hyp.gold.vertex_left.exists_order_three
  obtain ⟨Y, hYQ, hVY, hcard, hnorm, hiso⟩ := g.exists_Y hU hT hyA hy3
  obtain ⟨t, htQ, htt, htA⟩ := g.exists_t hU hT
  have htT : t ∈ A ⊓ B := g.hyp.gold.pCoreOf_right_le htQ
  have ht1 : t ≠ 1 := fun h => htA (h ▸ (pCoreOf 2 A).one_mem)
  have hWcases : ∀ w ∈ Subgroup.zpowers t, w = 1 ∨ w = t := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact zpow_eq_one_or_self (by rw [pow_two]; exact htt) k
  have hWQ : Subgroup.zpowers t ⊓ pCoreOf 2 A = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwQ⟩
    rcases hWcases w hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hwQ htA
  have hWY : Subgroup.zpowers t ⊓ Y = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left _ hYQ) hWQ.le)
  refine ⟨Y, Subgroup.zpowers t, y, ⟨g.hyp.gold.vertex_left, hYQ, hnorm, ?_, ?_, ?_, ?_, hyA, hy3,
    ?_⟩, hiso⟩
  · rw [g.card_QA hT, hcard]
  · exact Subgroup.zpowers_le.mpr htT
  · exact hWQ.le.trans bot_le
  · rw [hWY, Subgroup.card_bot, Nat.card_zpowers]
    have : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
    rw [this]
  · rintro w ⟨hwA, hwC⟩
    rw [← g.hyp.natural.centralizer_eq]
    exact ⟨hwA, Subgroup.centralizer_le (fun v hv => hVY hv) hwC⟩

theorem Gen3.exists_A' (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ A' : Subgroup D, A' ≤ A ∧ A'.relIndex A = 2 ∧ Vertex A' (A' ⊓ B) ∧
      Nonempty (↥(pCoreOf 2 A') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  obtain ⟨Y, W, y, d, e⟩ := g.exists_subData hU hT
  refine ⟨(Y ⊔ Subgroup.zpowers y) ⊔ W, d.H'_le_H, d.relIndex_H', ?_, ?_⟩
  · have h : ((Y ⊔ Subgroup.zpowers y) ⊔ W) ⊓ B = Y ⊔ W := by
      rw [← d.H'_inf_T]
      ext w
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, d.H'_le_H h1, h2⟩
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
    rw [h]
    exact d.vertex_H'
  · obtain ⟨e'⟩ := e
    exact ⟨(MulEquiv.subgroupCongr d.pCoreOf_H').trans e'⟩

end Sub

end GoldAmL3c

end F6

end CFSG.Quasithin
