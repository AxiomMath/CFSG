module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompBasic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Assembly.LowTwoRank

theorem exists_ne_comm_of_center_eq_bot {G : Type*} [Group G] [Nontrivial G]
    (h : Subgroup.center G = ⊥) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : Subgroup.center G = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => hcomm g x
  rw [h] at this
  exact (bot_ne_top : (⊥ : Subgroup G) ≠ ⊤) this

theorem exists_ne_comm_alternatingGroup {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : ↥(alternatingGroup (Fin n)), a * b ≠ b * a :=
  have : Nontrivial ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  exists_ne_comm_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp; omega))

theorem centralizer_alternatingGroup_eq_bot {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : 5 ≤ Nat.card α) :
    Subgroup.centralizer (alternatingGroup α : Set (Equiv.Perm α)) = ⊥ := by
  by_contra hne
  have hnt : Nontrivial ↥(Subgroup.centralizer (alternatingGroup α : Set (Equiv.Perm α))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hle := Equiv.Perm.alternatingGroup_le_of_normal h5 hnt
  have hc : Subgroup.center ↥(alternatingGroup α) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle x.2)) g g.2)
  rw [alternatingGroup.center_eq_bot (by omega)] at hc
  have : Nontrivial ↥(alternatingGroup α) := alternatingGroup.nontrivial_of_three_le_card (by omega)
  exact (bot_ne_top : (⊥ : Subgroup ↥(alternatingGroup α)) ≠ ⊤) hc

theorem notSL2_alternating_seven : NotSL2 ↥(alternatingGroup (Fin 7)) :=
  notSL2_of_card 3 (by rw [F6.card_alternating_seven]; norm_num)
    (by rw [F6.card_alternating_seven]; norm_num)

theorem isQuasisimple_alternating_seven : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 7)) :=
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  isQuasisimple_of_isSimpleGroup (exists_ne_comm_alternatingGroup (by norm_num))

theorem socle_alternating_seven : Socle ↥(alternatingGroup (Fin 7)) :=
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  socle_of_isSimpleGroup (exists_ne_comm_alternatingGroup (by norm_num)) notSL2_alternating_seven

theorem socle_perm_seven : Socle (Equiv.Perm (Fin 7)) := by
  have hC := centralizer_alternatingGroup_eq_bot (α := Fin 7) (by simp)
  refine Or.inr ⟨alternatingGroup (Fin 7), inferInstance, isQuasisimple_alternating_seven, ?_,
    notSL2_alternating_seven, fun _ => hC⟩
  rw [hC, Subgroup.card_bot]
  exact odd_one

section Hat

variable {W : Type*} [Group W] {n : ℕ}

theorem isQuasisimple_of_isHatAlt (h : F6.IsHatAlt n W) (hn : 4 ≤ n) : CFSG.IsQuasisimple W := by
  obtain ⟨⟨hperf, hs⟩, -, ⟨e⟩⟩ := h
  obtain ⟨a, b, hab⟩ := exists_ne_comm_alternatingGroup hn
  refine ⟨Group.isPerfect_def.mpr hperf, hs, e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem card_of_isHatAlt (h : F6.IsHatAlt n W) :
    Nat.card W = Nat.card ↥(alternatingGroup (Fin n)) * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W),
    Nat.card_congr e.toEquiv, h3]

theorem socle_of_isHatAlt (h : F6.IsHatAlt n W) (hn : 4 ≤ n) (hS : NotSL2 W) : Socle W :=
  socle_of_isQuasisimple (isQuasisimple_of_isHatAlt h hn)
    (by rw [h.2.1]; decide) hS

theorem notSL2_of_isHatAlt (h : F6.IsHatAlt n W) (hn : n = 6 ∨ n = 7) : NotSL2 W := by
  have hc := card_of_isHatAlt h
  rcases hn with rfl | rfl
  · rw [card_alternating_six] at hc
    exact notSL2_of_card 3 (by rw [hc]; norm_num) (by rw [hc]; norm_num)
  · rw [F6.card_alternating_seven] at hc
    exact notSL2_of_card 3 (by rw [hc]; norm_num) (by rw [hc]; norm_num)

theorem socle_of_isHatSym (h : F6.IsHatSym n W) (hn : n = 6 ∨ n = 7) : Socle W := by
  obtain ⟨φ, hφ, -, hA⟩ := h
  have hn5 : 5 ≤ n := by omega
  set N := (alternatingGroup (Fin n)).comap φ
  have hCA := centralizer_alternatingGroup_eq_bot (α := Fin n) (by simp; omega)
  have hC : Subgroup.centralizer (N : Set W) ≤ N := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hφx :
        φ x ∈ Subgroup.centralizer (alternatingGroup (Fin n) : Set (Equiv.Perm (Fin n))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨w, rfl⟩ := hφ a
      rw [← map_mul, ← map_mul, hx w ha]
    rw [hCA, Subgroup.mem_bot] at hφx
    change φ x ∈ alternatingGroup (Fin n)
    rw [hφx]
    exact Subgroup.one_mem _
  exact Or.inr ⟨N, goodSocle_of_centralizer_le inferInstance
    (isQuasisimple_of_isHatAlt hA (by omega)) hC (by rw [hA.2.1]; decide)
    (notSL2_of_isHatAlt hA hn)⟩

end Hat

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
