module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431E81

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan431

section NoCfg

variable {S : Type} [Group S] [Finite S]

theorem noCfgS431_of_four_le_pRank (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) :
    NoCfgS431 S := fun _ _ _ hc => by
  have := hc.pRank_le
  omega

theorem noCfgS431_of_three_lt_pRank (h : 3 < CFSG.pRank 3 S) : NoCfgS431 S :=
  noCfgS431_of_four_le_pRank (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; omega)

theorem four_le_pRank_of_elemAbelian {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 3 E)
    (h81 : 81 ≤ Nat.card E) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have hle : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at h81
    omega
  exact hk4.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk)

theorem exists_e81_of_four_le_pRank (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup S)
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := 4)
    (by rw [hcard]; exact pow_dvd_pow 3 h)
  refine ⟨D.map E.subtype, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
    apply Subtype.ext
    change (x : S) * y = y * x
    exact congrArg Subtype.val (hE.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hD]
    norm_num

theorem noCfgS431_of_elemAbelian {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 3 E)
    (h81 : 81 ≤ Nat.card E) : NoCfgS431 S :=
  noCfgS431_of_four_le_pRank (four_le_pRank_of_elemAbelian hE h81)

end NoCfg

theorem isElemAbelian_map_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (E.map e.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    change e x * e y = e y * e x
    rw [← map_mul, hxy, map_mul]
  · rintro _ ⟨x, hx, rfl⟩
    change e x ^ 3 = 1
    rw [← map_pow, hE.2 x hx, map_one]

theorem rowSOf431_of_three_lt_pRank {X : Type} [Group X] (h : 3 < CFSG.pRank 3 X) :
    RowSOf431 X := fun _ _ _ _ _ ⟨e⟩ =>
  (noCfgS431_of_three_lt_pRank (by rwa [CFSG.pRank_congr_of_mulEquiv e 3])).rowS431

theorem rowSOf431_of_elemAbelian {X : Type} [Group X] {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 3 E) (h81 : 81 ≤ Nat.card E) : RowSOf431 X :=
  fun _ _ _ _ _ ⟨e⟩ => (noCfgS431_of_elemAbelian (isElemAbelian_map_mulEquiv e.symm hE)
    (by rwa [Subgroup.card_map_of_injective e.symm.injective])).rowS431

end CFSG.RankThree.PartTwo.Sec4.Ronan431E81
