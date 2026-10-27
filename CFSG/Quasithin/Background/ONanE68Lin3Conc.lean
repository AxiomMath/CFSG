module

public import CFSG.Quasithin.Background.ONanE68Lin3Par
public import CFSG.Quasithin.Background.ONanE68LieFacts

public section

namespace CFSG.Quasithin.E6.E68Proof.Lin3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Lin2.L3Core

theorem exists_finset_card_four {F : Type} [Finite F] (h : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact ⟨s, hs⟩

theorem e68Lin3Data_projectiveSL {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 2 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    E68Lin3Data (projUnitriangular 3 F) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hroot : ∀ z : projectiveSL 3 F, z ∈ omegaCenter (projUnitriangular 3 F) ↔
      ∃ c : F, z = hei 0 0 c := fun z => mem_omegaCenter_iff
  have hne : ∀ c : F, hei 0 0 c ≠ 1 → c ≠ 0 := fun c h hc => h (by rw [hc, hei_zero])
  refine ⟨?_, fun c hc h3 => four_lt_relIndex hq hc h3, ?_, ?_, ?_, ?_⟩
  · rw [normalizer_projUnitriangular 2]
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact ⟨A * B * A⁻¹ * B⁻¹, comm_mem_unitriangular hA hB, by simp [map_mul, map_inv]⟩
  · rw [← hcard]
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
      (fun c : F => (⟨hei 0 0 c, (hroot _).mpr ⟨c, rfl⟩⟩ : omegaCenter (projUnitriangular 3 F)))
      ⟨fun c c' h => (hei_inj (congrArg Subtype.val h)).2.2, fun ⟨z, hz⟩ => ?_⟩))
    obtain ⟨c, rfl⟩ := (hroot z).mp hz
    exact ⟨c, rfl⟩
  · obtain ⟨x, hx, hxs⟩ := exists_singer (F := F)
    refine ⟨x, hx, fun z hz hz1 w hw hw1 => ?_⟩
    obtain ⟨c₁, rfl⟩ := (hroot z).mp hz
    obtain ⟨c₂, rfl⟩ := (hroot w).mp hw
    exact hxs c₁ (hne c₁ hz1) c₂ (hne c₂ hw1)
  · intro g hg hg1 y hy
    obtain ⟨c, rfl⟩ := (hroot g).mp hg
    exact mem_normalizer_of_comm_hei (hne c hg1) hy
  · intro Y hY hYt
    exact not_isSolvable_of_between (exists_finset_card_four hq) hY hYt

end CFSG.Quasithin.E6.E68Proof.Lin3
