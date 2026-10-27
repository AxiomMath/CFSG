module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem table_of_isShapeGroup
    (hF : Facts10_1) (hB : B4Hyp G L) (ht : AsB45Table G L)
    [hs : IsSimpleGroup ↥L] (hsh : IsShapeGroup ↥L) :
    (∃ m, 1 ≤ m ∧ BinaryOrthogonalFour L ⊤ ⊥ m) ∨ (∃ f, BinaryNaturalSz L ⊤ ⊥ f) := by
  have hcard := shapeCard_of_isShapeGroup hsh
  have hnc := InternalSec.exists_noncomm_of_isQuasisimple hB.2.2.1
  have hnt : Nontrivial ↥L := hs.toNontrivial
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ ShapeCard N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, hsz, -⟩ | ⟨m, hm, ⟨K, _, _, _, hK, π, hR⟩, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨eY, heY, hw, π, hR⟩, -⟩ | ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ |
      ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨h2324, -⟩
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_2520).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_alt 7 (by norm_num)]
    decide
  · exact Or.inl ⟨m, hm, horth⟩
  · exact absurd hR.1 (hF.su3 K m hK _ hsh π)
  · exact Or.inr ⟨f, hsz⟩
  · exact absurd hR.1 (hF.nineTensor K m hm hK _ hsh π)
  · exact absurd hR.1 (hF.g2Derived K (by rw [hK]; norm_num) _ hsh π)
  · exact absurd hR.1 (hF.m12 eY heY hw _ hsh π)
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  · exact absurd hR.1 (hF.m22 x y hxy _ hsh π)
  · exact absurd hR.1 (hF.m22 x y hxy _ hsh π)
  · rcases h2324 with ⟨x, π, hR⟩ | ⟨x, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
    · exact absurd hR.1 (hF.m23 x _ hsh π)
    · exact absurd hR.1 (hF.m23 x _ hsh π)
    all_goals exact absurd hR.1 (hF.m24 _ hsh π)

theorem not_part3_of_isShapeGroup (hF : Facts10_1) (h3 : AsB45Part3 G L)
    (hsh : IsShapeGroup ↥L) : False := by
  obtain ⟨-, -, ⟨a, ha, K, _, _, _, hK, π, hR⟩ | ⟨hJ2, -, -⟩⟩ := h3
  · exact hF.sp4Twisted K a ha hK _ hsh π hR.1
  · exact hF.j2 _ hsh hJ2

end CFSG.Quasithin.Vol2.Ch10.SecA
