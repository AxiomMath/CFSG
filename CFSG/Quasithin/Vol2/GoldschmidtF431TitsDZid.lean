module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDSpec

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

universe u


theorem isSylowTwoOf_titsS_H : IsSylowTwoOf titsS titsH := by
  refine ⟨titsS_le_titsH, IsPGroup.of_card (n := 11) (by rw [titsQS_facts.2.2.2]; norm_num), ?_⟩
  have h := Subgroup.card_mul_index (titsS.subgroupOf titsH)
  rw [card_subgroupOf_eq titsS_le_titsH, titsQS_facts.2.2.2, titsQH_facts.2.2.2] at h
  have h5 : (titsS.subgroupOf titsH).index = 5 := by omega
  rw [h5]
  decide

theorem eq_titsZ_of_central {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsH)
    (hc : ∀ y ∈ titsH, y * x = x * y) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = titsZ := by
  have ho : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  obtain ⟨m, hm, hmx⟩ := exists_conj_mem_of_isSylowTwoOf_involution isSylowTwoOf_titsS_H hx ho
  have hcm : m⁻¹ * x * m = x := by
    rw [mul_assoc, ← hc m hm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcm] at hmx
  have hmem : x ∈ ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
    refine ⟨⟨x, hmx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y.1 (titsS_le_titsH y.2))
  rw [titsS_center] at hmem
  rcases hmem with h | h
  · exact absurd h hx1
  · exact h

@[expose] noncomputable def titsZH : ↥titsH := ⟨titsZ, titsS_le_titsH titsZ_mem_titsS⟩

@[expose] noncomputable def titsTH : ↥titsH := ⟨tEl.1, titsS_le_titsH tEl_mem_titsS⟩

theorem zidD {G : Type} [Group G] {H L2 : Subgroup G}
    (e : (RankTwoAmalgam.ofSubgroups titsH titsN).Iso (RankTwoAmalgam.ofSubgroups H L2))
    {z : G} (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hcz : H ≤ Subgroup.centralizer {z}) :
    ((isoV1 e titsZH : ↥H) : G) = z := by
  let a : ↥titsH := (isoV1 e).symm ⟨z, hzH⟩
  have hea : isoV1 e a = ⟨z, hzH⟩ := (isoV1 e).apply_symm_apply _
  have hcen : ∀ y ∈ titsH, y * a.1 = a.1 * y := by
    intro y hy
    have h1 : isoV1 e ⟨y, hy⟩ * isoV1 e a = isoV1 e a * isoV1 e ⟨y, hy⟩ := by
      rw [hea]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcz (isoV1 e ⟨y, hy⟩).2))
    have h2 : (⟨y, hy⟩ : ↥titsH) * a = a * ⟨y, hy⟩ :=
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
  have hz : a = titsZH := Subtype.ext (eq_titsZ_of_central a.2 hcen ha2 ha1)
  rw [← hz, hea]

end CFSG.Quasithin.H13.F431.TitsD
