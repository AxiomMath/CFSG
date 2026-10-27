module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KM22

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint

section Embedding

variable {Y : Type} [Group Y] [Finite Y]

theorem Four4.map {S T : Type} [Group S] [Group T] (ι : S →* T) {u₁ u₂ w : S}
    (h : Four4 u₁ u₂ w) : Four4 (ι u₁) (ι u₂) (ι w) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one ι)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul ι u₁ u₂)))

theorem eInvNine_of_m22_embedding (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hsyl : ∀ P : Sylow 3 Y, Nat.card P = 9) (ι : ↥NativeSporadic.M22 →* Y)
    (hι : Function.Injective ι) : EInvNine Y := by
  obtain ⟨ha3, hb3, hab⟩ := KM22.rel_orders
  obtain ⟨hu₁, hu₂, hu, hu₁1, hu₂1, hu₁₂⟩ := KM22.rel_four
  obtain ⟨hva₁, hva₂, hvb₁, hvb₂⟩ := KM22.rel_four4
  have hdist := KM22.rel_dist
  have hmove := KM22.rel_move
  have hι1 : ∀ w : ↥NativeSporadic.M22, ι w = 1 → w = 1 := fun w h =>
    hι (by rw [h, map_one])
  have hconj : ∀ g t : Y, g * t = (g * t * g⁻¹) * g := fun g t => by group
  refine eInvNine_of_explicit_hout hZ hout hsyl (a := ι (KM22.ev KM22.wa))
    (b := ι (KM22.ev KM22.wb)) (u₁ := ι (KM22.ev KM22.wu1)) (u₂ := ι (KM22.ev KM22.wu2))
    (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
    (by rw [← map_mul, ← map_mul, hab]) ?_ (by rw [← map_mul, hu₁, map_one])
    (by rw [← map_mul, hu₂, map_one]) (by rw [← map_mul, ← map_mul, hu])
    (fun h => hu₁1 (hι1 _ h)) (fun h => hu₂1 (hι1 _ h)) (fun h => hu₁₂ (hι h))
    (va₁ := ι (KM22.ev KM22.wa) * ι (KM22.ev KM22.wu1) * (ι (KM22.ev KM22.wa))⁻¹)
    (va₂ := ι (KM22.ev KM22.wa) * ι (KM22.ev KM22.wu2) * (ι (KM22.ev KM22.wa))⁻¹)
    (vb₁ := ι (KM22.ev KM22.wb) * ι (KM22.ev KM22.wu1) * (ι (KM22.ev KM22.wb))⁻¹)
    (vb₂ := ι (KM22.ev KM22.wb) * ι (KM22.ev KM22.wu2) * (ι (KM22.ev KM22.wb))⁻¹) ?_ ?_ ?_ ?_
    (hconj _ _) (hconj _ _) (hconj _ _) (hconj _ _) ?_
  · intro i j k l h
    apply hdist i j k l
    apply hι
    simpa only [map_mul, map_pow] using h
  · simpa only [map_mul, map_inv] using Four4.map ι hva₁
  · simpa only [map_mul, map_inv] using Four4.map ι hva₂
  · simpa only [map_mul, map_inv] using Four4.map ι hvb₁
  · simpa only [map_mul, map_inv] using Four4.map ι hvb₂
  · intro h
    apply hmove
    apply hι
    simpa only [map_mul] using h

end Embedding

end CFSG.RankThree.PartTwo.Sec21.Hering214
