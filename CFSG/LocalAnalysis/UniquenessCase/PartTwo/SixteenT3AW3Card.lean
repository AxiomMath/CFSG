module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Hyp
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

theorem s16t_w3_card_S (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : Nat.card S = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom h.injective h.perm
  have hker : 3 ^ 2 ∣ Nat.card ρ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    have h2 : Nat.card ρ.range ∣ 6 := by
      have h3 := Subgroup.card_subgroup_dvd_card ρ.range
      rwa [Nat.card_eq_fintype_card (α := Equiv.Perm ι), Fintype.card_perm, h.card_index]
        at h3
    obtain ⟨c, hc⟩ := h.dvd_card.trans (h1 ▸ mul_dvd_mul_left (Nat.card ρ.ker) h2)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hker
  have hK' : Nat.card ((K.map ρ.ker.subtype).map X.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK]
    norm_num
  have hK'S : (K.map ρ.ker.subtype).map X.subtype ≤ S := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine s16t_w3_mem_S_of_pow h hS (k : ↥X).2 (fun i => ?_) (k := 2) ?_
    · refine (hρ (k : ↥X) i).trans ?_
      rw [MonoidHom.mem_ker.1 k.2]
      rfl
    · have h1 : (⟨k, hk⟩ : ↥K) ^ (3 ^ 2) = 1 := hK ▸ pow_card_eq_one'
      have h2 := congrArg (fun z : ↥K => (((z : ρ.ker) : ↥X) : MulAut T)) h1
      simpa using h2
  have hP : IsPGroup 3 S := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact ((hS x).1 x.2).2.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hel : CFSG.Open.IsElemAbelian 3 S :=
    ⟨⟨⟨fun x y => Subtype.ext (hSc x x.2 y y.2)⟩⟩, fun x hx => ((hS x).1 hx).2.2⟩
  have hn2 : n ≤ 2 := by
    have h1 := CFSG.SectionRank.le_pRank (by norm_num) (fun x hx => ((hS x).1 hx).1) hel hn
    have h2 := h.not_three_le_pRank
    omega
  have h9 : 9 ≤ Nat.card S := hK' ▸ Subgroup.card_le_of_le hK'S
  rw [hn] at h9 ⊢
  interval_cases n <;> first | rfl | norm_num at h9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
