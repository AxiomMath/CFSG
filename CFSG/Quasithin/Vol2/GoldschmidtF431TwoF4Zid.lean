module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Model

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47
  CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false

universe u


theorem isSylowTwoOf_twoF4S_H : IsSylowTwoOf twoF4S twoF4H := by
  refine ⟨twoF4S_le_twoF4H, IsPGroup.of_card (n := 12) (by rw [card_twoF4S]; norm_num), ?_⟩
  have h := Subgroup.card_mul_index (twoF4S.subgroupOf twoF4H)
  rw [card_subgroupOf_eq twoF4S_le_twoF4H, card_twoF4S, card_twoF4H] at h
  have h5 : (twoF4S.subgroupOf twoF4H).index = 5 := by omega
  rw [h5]
  decide

theorem eq_titsZ_of_central {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4H)
    (hc : ∀ y ∈ twoF4H, y * x = x * y) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = titsZ := by
  have ho : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  obtain ⟨m, hm, hmx⟩ := exists_conj_mem_of_isSylowTwoOf_involution isSylowTwoOf_twoF4S_H hx ho
  have hcm : m⁻¹ * x * m = x := by
    rw [mul_assoc, ← hc m hm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcm] at hmx
  rcases twoF4S_center hmx (fun y hy => hc y (twoF4S_le_twoF4H hy)) with h | h
  · exact absurd h hx1
  · exact h

@[expose] noncomputable def twoF4ZH : ↥twoF4H := ⟨titsZ, twoF4S_le_twoF4H titsZ_mem_S⟩

@[expose] noncomputable def twoF4TH : ↥twoF4H := ⟨tEl.1, twoF4S_le_twoF4H tEl_mem_S⟩

@[expose] def isoV1 {X Y : Type u} [Group X] [Group Y] {A B : Subgroup X} {A' B' : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B')) :
    ↥A ≃* ↥A' := e.φ1

@[expose] def isoV2 {X Y : Type u} [Group X] [Group Y] {A B : Subgroup X} {A' B' : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B')) :
    ↥B ≃* ↥B' := e.φ2

theorem zid {G : Type} [Group G] {H L2 : Subgroup G}
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups H L2))
    {z : G} (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hcz : H ≤ Subgroup.centralizer {z}) :
    ((isoV1 e twoF4ZH : ↥H) : G) = z := by
  let a : ↥twoF4H := (isoV1 e).symm ⟨z, hzH⟩
  have hea : isoV1 e a = ⟨z, hzH⟩ := (isoV1 e).apply_symm_apply _
  have hcen : ∀ y ∈ twoF4H, y * a.1 = a.1 * y := by
    intro y hy
    have h1 : isoV1 e ⟨y, hy⟩ * isoV1 e a = isoV1 e a * isoV1 e ⟨y, hy⟩ := by
      rw [hea]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcz (isoV1 e ⟨y, hy⟩).2))
    have h2 : (⟨y, hy⟩ : ↥twoF4H) * a = a * ⟨y, hy⟩ :=
      (isoV1 e).injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have ha2 : a.1 * a.1 = 1 := by
    have : a * a = 1 := (isoV1 e).injective (by
      rw [map_mul, hea, map_one]
      exact Subtype.ext (by simpa [pow_two] using hz2))
    exact congrArg Subtype.val this
  have ha1 : a.1 ≠ 1 := by
    intro h
    have : a = 1 := Subtype.ext h
    rw [this, map_one] at hea
    exact hz1 (congrArg Subtype.val hea).symm
  have hz : a = twoF4ZH := Subtype.ext (eq_titsZ_of_central a.2 hcen ha2 ha1)
  rw [← hz, hea]

end CFSG.Quasithin.H13.F431.TwoF4
