module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

namespace R3c18

theorem exists_sq_of_two_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : 2 ≤ CFSG.pRank p G) :
    ∃ E : Subgroup G, Nat.card E = p ^ 2 ∧ CFSG.Open.IsElemAbelian p E := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E₀, -, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) p (n := 2)
    (by rw [hcard]; exact pow_dvd_pow p h)
  refine ⟨K.map E₀.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨y', hy', hye⟩ := y.2
      apply Subtype.ext
      change (x : G) * (y : G) = (y : G) * (x : G)
      rw [← hxe, ← hye]
      exact congrArg Subtype.val (hE₀.1.is_comm.comm x' y')
    · obtain ⟨x', -, rfl⟩ := hx
      exact congrArg Subtype.val (show x' ^ p = 1 from Subtype.ext (hE₀.2 x'.1 x'.2))

theorem dvd_add_one_of_dvd_pow_add_one {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ p + 1) :
    p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

end R3c18

end CFSG.Quasithin
