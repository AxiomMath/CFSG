module

public import CFSG.Quasithin.Background.A312SporJ1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.A312S CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J1Lat
open CFSG.Sporadic.J1

private theorem eq_bot_of_perfect {X : Type} [Group X] {B : Subgroup X} (hB : ⁅B, B⁆ = B)
    (hs : Group.IsSolvable B) : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := hs.solvable
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

private theorem sup_normalizer_of_map {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y)
    {T B : Subgroup X}
    (h : B.map ψ.toMonoidHom ⊔ Subgroup.normalizer ((T.map ψ.toMonoidHom : Subgroup Y) : Set Y) =
      ⊤) : B ⊔ Subgroup.normalizer (T : Set X) = ⊤ := by
  rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_sup] at h
  exact Subgroup.map_injective ψ.injective
    (h.trans (Subgroup.map_top_of_surjective _ ψ.surjective).symm)


theorem j1_center_eq_bot : Subgroup.center ↥J = ⊥ := by
  have := isSimpleGroup_J
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥J) with h | h
  · exact h
  · exfalso
    have hn : j1S.Normal := ⟨fun n hn g => by
      have hg : g ∈ Subgroup.center ↥J := h ▸ Subgroup.mem_top g
      rw [Subgroup.mem_center_iff] at hg
      rw [← hg n, mul_inv_cancel_right]
      exact hn⟩
    have hc := j1_card_S
    rcases Subgroup.Normal.eq_bot_or_eq_top j1S with h1 | h1
    · rw [h1, Subgroup.card_bot] at hc
      norm_num at hc
    · rw [h1, Subgroup.card_top, card_J] at hc
      norm_num at hc


private theorem j1K_Y16_le : j1Y 16 ≤ Subgroup.normalizer (j1S : Set ↥J) := by
  have hcY : Nat.card (j1Y 16) = 168 := by rw [j1_Y_card (by norm_num)]; rfl
  have h := (Certificates.certificate7128 (j1Y 16)
    (by rw [j1_S_eq]; exact j1_S_le_Y 16)).1 hcY
  rwa [j1_S_eq] at h

private theorem j1K_solvable : Group.IsSolvable ↥(j1Y 16) := by
  have hSY : j1S ≤ j1Y 16 := j1_S_le_Y 16
  have hSs : Group.IsSolvable ↥j1S := by
    have := (j1_S_isPGroup).isNilpotent
    infer_instance
  refine isSolvable_of_normal hSY j1K_Y16_le hSs ?_
  intro _
  have hcY : Nat.card (j1Y 16) = 168 := by rw [j1_Y_card (by norm_num)]; rfl
  have hcS : Nat.card ↥(j1S.subgroupOf (j1Y 16)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, j1_card_S]
    rfl
  have hq : Nat.card (↥(j1Y 16) ⧸ j1S.subgroupOf (j1Y 16)) = 3 ^ 1 * 7 ^ 1 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (j1S.subgroupOf (j1Y 16))
    rw [hcY, hcS] at h
    omega
  let _ : Fintype (↥(j1Y 16) ⧸ j1S.subgroupOf (j1Y 16)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three
    (q := 7) (by norm_num) (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hq)

private theorem j1K_sup {B : Subgroup ↥J} (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥) :
    B ⊔ Subgroup.normalizer (j1S : Set ↥J) = ⊤ := by
  set Z := B ⊔ Subgroup.normalizer (j1S : Set ↥J) with hZ
  have hYZ : j1Y 16 ≤ Z := j1K_Y16_le.trans le_sup_right
  obtain ⟨j, hj, hZj⟩ := j1_all Z ((j1_S_le_Y 16).trans hYZ)
  have hsize : (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size =
      17 := rfl
  rw [hsize] at hj hZj
  by_cases hj17 : j < 17
  · exfalso
    rw [memberOrTop, ite_eq_left hj17] at hZj
    have hmax : ∀ i < 17,
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[i]! * 2 ^ 3 ≤
          168 := by decide
    have heq : j1Y 16 = Z := Subgroup.eq_of_le_of_card_ge hYZ (by
      rw [hZj, j1_Y_card hj17, j1_Y_card (by norm_num)]
      exact (hmax j hj17).trans (by decide))
    have hsol : Group.IsSolvable ↥Z := by rw [← heq]; exact j1K_solvable
    exact hB1 (eq_bot_of_perfect hB (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_sup_left : B ≤ Z)) (Subgroup.inclusion_injective _)))
  · rw [memberOrTop, ite_eq_right hj17] at hZj
    exact hZj

theorem j1_sup_normalizer_eq_top {X : Type} [Group X] [Finite X] (e : X ≃* ↥J)
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥) :
    B ⊔ Subgroup.normalizer (T : Set X) = ⊤ := by
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hT' j1_sylow
  let φ : X ≃* ↥J := e.trans (MulAut.conj g)
  have hTφ : T.map φ.toMonoidHom = j1S := by
    rw [← hg, Subgroup.map_map]
    rfl
  refine sup_normalizer_of_map φ ?_
  rw [hTφ]
  refine j1K_sup ?_ ?_
  · rw [← Subgroup.map_commutator, hB]
  · intro h
    exact hB1 ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h)

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
