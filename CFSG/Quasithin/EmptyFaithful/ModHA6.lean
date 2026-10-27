module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.ModH

open Equiv

theorem a6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem a6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem a6_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  intro h
  have := a6_simple
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 6))).2 h
  have c1 : (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have c2 : (swap (0 : Fin 6) 1 * swap 1 3 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h2 : (swap (0 : Fin 6) 1 * swap 1 2) * (swap 0 1 * swap 1 3) =
      (swap 0 1 * swap 1 3) * (swap 0 1 * swap 1 2) :=
    congrArg Subtype.val (hcomm ⟨_, c1⟩ ⟨_, c2⟩)
  revert h2
  decide

theorem a6_no_solvable_72 (H : Subgroup (alternatingGroup (Fin 6))) (hs : Group.IsSolvable ↥H)
    (h72 : 72 ∣ Nat.card ↥H) : False := by
  have := a6_simple
  have hmul := Subgroup.card_mul_index H
  rw [a6_card] at hmul
  obtain ⟨m, hm⟩ := h72
  have h1 : 72 * (m * H.index) = 72 * 5 := by
    rw [hm] at hmul
    calc 72 * (m * H.index) = 72 * m * H.index := by ring
      _ = 360 := hmul
      _ = 72 * 5 := by norm_num
  have h2 : m * H.index = 5 := Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hidx : H.index ∣ 5 := ⟨m, by rw [← h2]; ring⟩
  have hle5 : H.index ≤ 5 := Nat.le_of_dvd (by norm_num) hidx
  have hi : H.index = 1 ∨ H.index = 5 := by
    have h5 : Nat.divisors 5 = {1, 5} := by decide
    have hmem : H.index ∈ Nat.divisors 5 := Nat.mem_divisors.2 ⟨hidx, by norm_num⟩
    rw [h5] at hmem
    simpa using hmem
  rcases hi with h1 | h5
  ·
    have htop : H = ⊤ := Subgroup.index_eq_one.1 h1
    apply a6_not_solvable
    subst htop
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (alternatingGroup (Fin 6))).subtype)
      (by intro x; exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  ·
    let φ := MulAction.toPermHom (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6) ⧸ H)
    have hnorm : φ.ker.Normal := MonoidHom.normal_ker φ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hb
      have h1 : Nat.card (alternatingGroup (Fin 6)) ≤ Nat.card (Perm (alternatingGroup (Fin 6) ⧸ H)) :=
        Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card (Perm (alternatingGroup (Fin 6) ⧸ H)) = 120 := by
        rw [Nat.card_perm, ← Subgroup.index_eq_card, h5]
        decide
      rw [a6_card, h2] at h1
      omega
    · apply absurd h5
      have htop : H = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have hg : g ∈ φ.ker := by rw [ht]; exact Subgroup.mem_top g
        have h1 := congrArg (fun σ => σ ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H))
          (MonoidHom.mem_ker.1 hg)
        simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.coe_one, id_eq] at h1
        have h2 : ((g * 1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H) =
            ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H) := h1
        rw [QuotientGroup.eq] at h2
        simpa using H.inv_mem h2
      rw [htop, Subgroup.index_top]
      norm_num

end CFSG.Quasithin.ModH
