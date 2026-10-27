module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive


public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem card_map_sup_le {X : Type*} [AddCommGroup X] [Finite X] (T : X →+ X)
    (R Y : AddSubgroup X) (h : Y.map T ≤ R ⊓ Y) :
    Nat.card ↥(Y.map T) * Nat.card ↥(R ⊔ Y) ≤ Nat.card ↥R * Nat.card ↥Y := by
  have hcard : Nat.card ↥(Y.map T) ≤ Nat.card ↥(R ⊓ Y) := AddSubgroup.card_le_of_le h
  calc Nat.card ↥(Y.map T) * Nat.card ↥(R ⊔ Y)
      ≤ Nat.card ↥(R ⊓ Y) * Nat.card ↥(R ⊔ Y) := Nat.mul_le_mul hcard le_rfl
    _ = Nat.card ↥(R ⊔ Y) * Nat.card ↥(R ⊓ Y) := Nat.mul_comm _ _
    _ = Nat.card ↥R * Nat.card ↥Y := card_sup_mul_card_inf_addSubgroup R Y

theorem card_range_sup_ker_eq {X : Type*} [AddCommGroup X] [Finite X] (T ε : X →+ X)
    (hcomm : ∀ x, T (ε x) = ε (T x)) :
    Nat.card ↥(T.range ⊔ ε.ker) = Nat.card ↥ε.ker * Nat.card ↥(ε.range.map T) := by
  have hmap : (T.range ⊔ ε.ker).map ε = ε.range.map T := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, k, hk, rfl⟩ := AddSubgroup.mem_sup.1 hz
      obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.1 hy
      refine AddSubgroup.mem_map.2 ⟨ε w, AddMonoidHom.mem_range.2 ⟨w, rfl⟩, ?_⟩
      rw [map_add, AddMonoidHom.mem_ker.1 hk, add_zero]
      exact hcomm w
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.1 hx
      exact AddSubgroup.mem_map.2
        ⟨T w, AddSubgroup.mem_sup_left (AddMonoidHom.mem_range.2 ⟨w, rfl⟩), (hcomm w).symm⟩
  have hk : ε.ker ⊓ (T.range ⊔ ε.ker) = ε.ker :=
    inf_eq_left.2 (le_sup_right : ε.ker ≤ T.range ⊔ ε.ker)
  have h1 := AddSubgroup.relIndex_mul_card ε.ker (T.range ⊔ ε.ker)
  rw [hk, AddSubgroup.relIndex_ker, hmap] at h1
  exact h1.symm.trans (Nat.mul_comm _ _)

theorem step78_module_ineq {X : Type*} [AddCommGroup X] [Finite X] (T ε : X →+ X)
    (hcomm : ∀ x, T (ε x) = ε (T x)) (hle : ε.range ≤ ε.ker) :
    Nat.card ↥(ε.range.map T) ^ 2 * Nat.card ↥(ε.ker.map T ⊔ ε.range) ≤
      Nat.card ↥T.range * Nat.card ↥ε.range := by
  have hWinv : ε.ker.map T ≤ ε.ker := by
    rintro _ ⟨x, hx, rfl⟩
    rw [AddMonoidHom.mem_ker, ← hcomm x, AddMonoidHom.mem_ker.1 hx, map_zero]
  have hAinv : ε.range.map T ≤ ε.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.1 hx
    exact AddMonoidHom.mem_range.2 ⟨T w, (hcomm w).symm⟩
  have hsub1 : ε.ker.map T ≤ T.range ⊓ ε.ker := by
    refine le_inf ?_ hWinv
    rintro _ ⟨x, _, rfl⟩
    exact AddMonoidHom.mem_range.2 ⟨x, rfl⟩
  have F1 := card_map_sup_le T T.range ε.ker hsub1
  have F2 := card_range_sup_ker_eq T ε hcomm
  have hsub2 : ε.range.map T ≤ ε.ker.map T ⊓ ε.range :=
    le_inf (AddSubgroup.map_mono hle) hAinv
  have F4 := card_map_sup_le T (ε.ker.map T) ε.range hsub2
  have hpos : 0 < Nat.card ↥ε.ker := Nat.card_pos
  have F3 : Nat.card ↥(ε.ker.map T) * Nat.card ↥(ε.range.map T) ≤ Nat.card ↥T.range := by
    rw [F2] at F1
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ↥(ε.ker.map T) * Nat.card ↥(ε.range.map T) * Nat.card ↥ε.ker
        = Nat.card ↥(ε.ker.map T) * (Nat.card ↥ε.ker * Nat.card ↥(ε.range.map T)) := by ring
      _ ≤ Nat.card ↥T.range * Nat.card ↥ε.ker := F1
  calc Nat.card ↥(ε.range.map T) ^ 2 * Nat.card ↥(ε.ker.map T ⊔ ε.range)
      = Nat.card ↥(ε.range.map T) *
          (Nat.card ↥(ε.range.map T) * Nat.card ↥(ε.ker.map T ⊔ ε.range)) := by ring
    _ ≤ Nat.card ↥(ε.range.map T) * (Nat.card ↥(ε.ker.map T) * Nat.card ↥ε.range) :=
        Nat.mul_le_mul le_rfl F4
    _ = (Nat.card ↥(ε.ker.map T) * Nat.card ↥(ε.range.map T)) * Nat.card ↥ε.range := by ring
    _ ≤ Nat.card ↥T.range * Nat.card ↥ε.range := Nat.mul_le_mul F3 le_rfl

theorem step78_arith {q n m c Y : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m)
    (h1 : q ^ 4 * c ≤ q ^ (2 * m)) (h2 : q ^ (2 * n + 2) = q ^ (4 * m + 2) * Y)
    (h3 : Y ≤ c ^ 4) : 2 * n + 16 ≤ 12 * m := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 4 := ⟨2 * m - 4, by omega⟩
  have e1 : q ^ (2 * m) = q ^ 4 * q ^ k := by
    rw [hk]
    ring
  have h1' : q ^ 4 * c ≤ q ^ 4 * q ^ k := by
    rw [← e1]
    exact h1
  have hc : c ≤ q ^ k := Nat.le_of_mul_le_mul_left h1' (pow_pos (by omega) 4)
  have hY : Y ≤ (q ^ k) ^ 4 := h3.trans (Nat.pow_le_pow_left hc 4)
  have h4 : q ^ (2 * n + 2) ≤ q ^ (6 * k + 10) := by
    calc q ^ (2 * n + 2) = q ^ (4 * m + 2) * Y := h2
      _ ≤ q ^ (4 * m + 2) * (q ^ k) ^ 4 := Nat.mul_le_mul le_rfl hY
      _ = q ^ (6 * k + 10) := by
        rw [← pow_mul, ← pow_add, show 4 * m + 2 + k * 4 = 6 * k + 10 by omega]
  have h5 : 2 * n + 2 ≤ 6 * k + 10 :=
    (Nat.pow_le_pow_iff_right (show 1 < q by omega)).1 h4
  omega

end CFSG.RankThree.GF2n.Stroth80
