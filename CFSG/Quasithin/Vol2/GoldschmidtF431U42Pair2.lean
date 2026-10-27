module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Lat2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem eq_T_of_isPGroup
    {N : Subgroup Y} (hTN : T ≤ N) (hN : IsPGroup 2 N) : N = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have h1 : Nat.card N ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card N
  rw [hn, show Nat.card Y = 25920 from card_Xs] at h1
  have hn6 : n ≤ 6 := by
    by_contra h
    have h7 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := dvd_trans h7 h1
    norm_num at this
  have hle : Nat.card N ≤ Nat.card T := by
    rw [hn, card_T]
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
      _ = 64 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTN hle).symm

theorem normal_le_T {R : Subgroup Y}
    (hR : R.Normal) (hp : IsPGroup 2 R) : R ≤ T := by
  have hT : IsPGroup 2 T := isSylow_T.2.1
  have hsup : IsPGroup 2 ↥(T ⊔ R) := hT.to_sup_of_normal_right hp
  have : T ⊔ R = T := eq_T_of_isPGroup le_sup_left hsup
  exact this ▸ le_sup_right

theorem center_T_spec {t : Y} (htT : t ∈ T)
    (hc : ∀ s ∈ T, s * t = t * s) : t = 1 ∨ t = xY := by
  obtain ⟨i, hi, hti⟩ := (mem_T_iff t).1 htT
  have hall : ((List.range 5).all fun k =>
      comp (Tl.getD i []) (gTL k) == comp (gTL k) (Tl.getD i [])) = true := by
    refine List.all_eq_true.2 fun k hk => ?_
    have hk5 := List.mem_range.1 hk
    have hgk : gTY k ∈ T := Subgroup.subset_closure ⟨⟨k, hk5⟩, rfl⟩
    have h := hc _ hgk
    have e1 : RepL (comp (Tl.getD i []) (gTL k)) (((t * gTY k : Y)) : P45) :=
      repL_mul hti (repL_gTY k)
    have e2 : RepL (comp (gTL k) (Tl.getD i [])) (((gTY k * t : Y)) : P45) :=
      repL_mul (repL_gTY k) hti
    rw [beq_iff_eq]
    exact repL_unique e1 (by rw [show t * gTY k = gTY k * t from h.symm]; exact e2)
  rcases chkT_spec.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi with h | h | h
  · rw [hall] at h
    exact absurd h (by simp)
  · left
    apply Subtype.ext
    refine eq_of_repL hti ?_
    rw [h]
    exact repL_one 45
  · right
    apply Subtype.ext
    exact eq_of_repL hti (by rw [h]; exact repL_x)

theorem x_mem_of_normal
    {R : Subgroup Y} (hR : R.Normal) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) : xY ∈ R := by
  have hRT := normal_le_T hR hp
  have hT : IsPGroup 2 T := isSylow_T.2.1
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hR' : (R.subgroupOf T).Normal := hR.subgroupOf T
  have hne' : R.subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRT hr⟩ : T) ∈ R.subgroupOf T := hr
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨t, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc
  have htR : ((t : T) : Y) ∈ R := t.2.1
  have htZ : (t : T) ∈ Subgroup.center T := t.2.2
  have ht1 : ((t : T) : Y) ≠ 1 := fun h => ht (Subtype.ext (Subtype.ext h))
  rcases center_T_spec (t : T).2 (fun s hs => by
      have := Subgroup.mem_center_iff.1 htZ ⟨s, hs⟩
      exact congrArg Subtype.val this) with h | h
  · exact absurd h ht1
  · rwa [h] at htR

theorem normal_two_group_trivial
    {R : Subgroup Y} (hR : R.Normal) (hp : IsPGroup 2 R) : R = ⊥ := by
  by_contra hne
  have hx := x_mem_of_normal hR hp hne
  have hs : ∀ i : Fin 45, (⟨sT i, sT_mem i⟩ : Y) ∈ R := fun i =>
    hR.conj_mem xY hx ⟨wordP (wpW.getD i []), wordP_mem _⟩
  have hy : yY ∈ R := by
    have : yY = (⟨sT 31, sT_mem 31⟩ : Y) * ⟨sT 5, sT_mem 5⟩ * ⟨sT 36, sT_mem 36⟩ *
        ⟨sT 44, sT_mem 44⟩ := Subtype.ext y45_eq_s
    rw [this]
    exact R.mul_mem (R.mul_mem (R.mul_mem (hs 31) (hs 5)) (hs 36)) (hs 44)
  have htop : R = ⊤ := by
    rw [eq_top_iff, ← closure_xy_top, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  rw [htop] at hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [Subgroup.card_top, show Nat.card Y = 25920 from card_Xs] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem repL_Dj_inv (j : ℕ) : RepL (evalW (invW (DW.getD j []))) (((Dj j : Y) : P45)⁻¹) := by
  have : ((Dj j : Y) : P45)⁻¹ = wordP (invW (DW.getD j [])) := by
    rw [wordP_invW]
    rfl
  rw [this]
  exact repL_wordP _

theorem not_normalizes {j : ℕ}
    (hj : ∃ k < 5, Tl.contains (comp (comp (DL j) (gTL k)) (evalW (invW (DW.getD j [])))) = false) :
    Dj j ∉ Subgroup.normalizer (T : Set Y) := by
  intro h
  obtain ⟨k, hk5, hk⟩ := hj
  have hgk : gTY k ∈ T := Subgroup.subset_closure ⟨⟨k, hk5⟩, rfl⟩
  have hmem : Dj j * gTY k * (Dj j)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 h _).1 hgk
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff _).1 hmem
  have e : RepL (comp (comp (DL j) (gTL k)) (evalW (invW (DW.getD j []))))
      (((Dj j * gTY k * (Dj j)⁻¹ : Y)) : P45) :=
    repL_mul (repL_mul (repL_Dj j) (repL_gTY k)) (repL_Dj_inv j)
  have hl := repL_unique e hrep
  have : Tl.contains (comp (comp (DL j) (gTL k)) (evalW (invW (DW.getD j [])))) = true := by
    rw [hl, List.contains_iff_mem, List.mem_iff_getElem]
    exact ⟨i, by have := chkT_spec.1; omega, by rw [List.getElem_eq_getD ([] : PL)]⟩
  rw [hk] at this
  exact Bool.false_ne_true this

theorem normalizer_T :
    Subgroup.normalizer (T : Set Y) = B0 := by
  have hD1 := not_normalizes (misc_spec.2.1)
  have hD2 := not_normalizes (misc_spec.2.2.1)
  rcases lattice B0_le_normalizer_T with h | h | h | h
  · exact h
  · exact absurd (h ▸ D1_mem_P1) hD1
  · exact absurd (h ▸ D2_mem_P2) hD2
  · exact absurd (h ▸ Subgroup.mem_top (Dj 1)) hD1

end CFSG.Quasithin.H13.F431.U42
