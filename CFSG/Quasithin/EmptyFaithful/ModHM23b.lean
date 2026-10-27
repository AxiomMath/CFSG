module

public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import CFSG.Quasithin.EmptyFaithful.ModHM24a

public section

namespace CFSG.Quasithin.ModH.M23b

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.E2P.SporB

abbrev G23 : Type := ↥NativeSporadic.M23

@[expose] def m23Ord : Array ℕ :=
  #[128, 443520, 40320, 5760, 2688, 40320, 2688, 1920, 5760, 1920, 384, 384, 384, 384, 384, 1152]

theorem hall_640 {h k m : ℕ} (hr : h * k = 640 * m)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = 5) (hk2 : ¬ 2 ∣ k) (hk5 : ¬ 5 ∣ k)
    (hm2 : ¬ 2 ∣ m) (hm5 : ¬ 5 ∣ m) : h = 640 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => hm2 (h0 ▸ dvd_zero 2))
  have hhm : Nat.Coprime h m := by
    apply Nat.coprime_of_dvd
    intro q hq hqh hqm
    rcases hh q hq hqh with rfl | rfl
    · exact hm2 hqm
    · exact hm5 hqm
  have hh640 : h ∣ 640 := hhm.dvd_of_dvd_mul_right (Dvd.intro k hr)
  have hk640 : Nat.Coprime k 640 := by
    have h2 : Nat.Coprime k (2 ^ 7) :=
      Nat.Coprime.pow_right 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2).symm
    have h5 : Nat.Coprime k 5 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk5).symm
    have := Nat.Coprime.mul_right h2 h5
    simpa using this
  have hkm : k ∣ m := hk640.dvd_of_dvd_mul_left (Dvd.intro_left h hr)
  have hh_le : h ≤ 640 := Nat.le_of_dvd (by norm_num) hh640
  have hk_le : k ≤ m := Nat.le_of_dvd hm hkm
  by_contra hne
  have hlt : h < 640 := lt_of_le_of_ne hh_le hne
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkm hm
  nlinarith

section Lattice

theorem m23_hL :
    m23CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := m23_lat_cert.2.2

theorem m23_hN :
    m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1

theorem m23_S_card :
    Nat.card ↥m23CtxB.S = 128 := by
  rw [m23CtxB.S_card]
  rfl

theorem m23_S_sylow :
    IsSylowTwoOf m23CtxB.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m23CtxB.S
  rw [m23CtxB.S_card, m23CtxB.hΓ, m23_hN] at h1
  have h2 : m23CtxB.S.index = 79695 := by
    have : m23CtxB.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem m23_overgroup
    {Z : Subgroup G23} (hSZ : m23CtxB.S ≤ Z) :
    Z = ⊤ ∨ ∃ j < 16, Z = m23CtxB.Y j := by
  obtain ⟨j, hj, hZ⟩ := lat_all m23CtxB m23_hL Z hSZ
  by_cases hjJ : j < 16
  · right
    refine ⟨j, hjJ, ?_⟩
    rw [hZ]
    exact list_member (L := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]) hjJ
  · left
    have h16 : j = 16 := by
      have : j ≤ 16 := hj
      omega
    rw [hZ]
    unfold memberOrTop
    rw [ite_eq_right (by simp [h16])]

theorem m23_card_Y
    {j : ℕ} (hj : j < 16) :
    Nat.card ↥(m23CtxB.Y j) = m23Ord[j]! := by
  have h := lat_card m23CtxB m23_hL j hj
  rw [h]
  interval_cases j <;> rfl

theorem no_hall
    {Z : Subgroup G23} (hSZ : m23CtxB.S ≤ Z)
    (hZs : Group.IsSolvable ↥Z) (hZtop : Z ≠ ⊤) {m : ℕ} (hZc : Nat.card ↥Z = 640 * m)
    (hm2 : ¬ 2 ∣ m) (hm5 : ¬ 5 ∣ m) : False := by
  have hS : IsSylowTwoOf m23CtxB.S ⊤ := m23_S_sylow
  have hU : IsPGroup 2 ↥(m23CtxB.S.subgroupOf Z) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  obtain ⟨H, hUH, hHq, hk2, hk5⟩ :=
    M24a.exists_hall_two_p hZs (m23CtxB.S.subgroupOf Z) hU 5 (by norm_num)
  have hSH : m23CtxB.S ≤ H.map Z.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSZ]
    exact Subgroup.map_mono hUH
  have hcardH : Nat.card ↥(H.map Z.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Z.subtype Subtype.val_injective).toEquiv).symm
  have h640 : Nat.card ↥H = 640 :=
    hall_640 (h := Nat.card ↥H) (k := H.index) (m := m)
      (by rw [Subgroup.card_mul_index H]; exact hZc) hHq hk2 hk5 hm2 hm5
  rcases m23_overgroup hSH with htop | ⟨j, hj, hHj⟩
  · apply hZtop
    have : (⊤ : Subgroup G23) ≤ Z := htop ▸ Subgroup.map_subtype_le H
    exact top_le_iff.1 this
  · have h1 := m23_card_Y hj
    rw [← hHj, hcardH, h640] at h1
    interval_cases j <;> simp [m23Ord] at h1

theorem ne_top_of_solvable (hns : ¬ Group.IsSolvable G23) {Z : Subgroup G23}
    (hZs : Group.IsSolvable ↥Z) : Z ≠ ⊤ := by
  intro htop
  apply hns
  rw [htop] at hZs
  exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup G23).subtype)
    (by intro x; exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)

theorem eq_Y15
    (hns : ¬ Group.IsSolvable G23) {Z : Subgroup G23}
    (hSZ : m23CtxB.S ≤ Z) (hZs : Group.IsSolvable ↥Z) (h9 : 9 ∣ Nat.card ↥Z) :
    Z = m23CtxB.Y 15 := by
  have hZtop := ne_top_of_solvable hns hZs
  rcases m23_overgroup hSZ with htop | ⟨j, hj, rfl⟩
  · exact absurd htop hZtop
  · have h1 := m23_card_Y hj
    have h9' : 9 ∣ m23Ord[j]! := h1 ▸ h9
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 8 ∨ j = 15 := by
      interval_cases j <;> simp [m23Ord] at h9' ⊢
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (no_hall hSZ hZs hZtop (m := 693) (by rw [h1]; rfl) (by norm_num) (by norm_num)).elim
    · exact (no_hall hSZ hZs hZtop (m := 63) (by rw [h1]; rfl) (by norm_num) (by norm_num)).elim
    · exact (no_hall hSZ hZs hZtop (m := 9) (by rw [h1]; rfl) (by norm_num) (by norm_num)).elim
    · exact (no_hall hSZ hZs hZtop (m := 63) (by rw [h1]; rfl) (by norm_num) (by norm_num)).elim
    · exact (no_hall hSZ hZs hZtop (m := 9) (by rw [h1]; rfl) (by norm_num) (by norm_num)).elim
    · rfl

theorem three_members :
    m23CtxB.Y 10 ≤ m23CtxB.Y 15 ∧ m23CtxB.Y 12 ≤ m23CtxB.Y 15 ∧ m23CtxB.Y 13 ≤ m23CtxB.Y 15 ∧
      m23CtxB.Y 10 ≠ m23CtxB.Y 12 ∧ m23CtxB.Y 10 ≠ m23CtxB.Y 13 ∧
      m23CtxB.Y 12 ≠ m23CtxB.Y 13 := by
  refine ⟨(m23_Y_le_iff (by norm_num) (by norm_num)).2 (by decide),
    (m23_Y_le_iff (by norm_num) (by norm_num)).2 (by decide),
    (m23_Y_le_iff (by norm_num) (by norm_num)).2 (by decide), ?_, ?_, ?_⟩
  · intro h
    exact absurd ((m23_Y_le_iff (j := 10) (jj := 12) (by norm_num) (by norm_num)).1 h.le)
      (by decide)
  · intro h
    exact absurd ((m23_Y_le_iff (j := 10) (jj := 13) (by norm_num) (by norm_num)).1 h.le)
      (by decide)
  · intro h
    exact absurd ((m23_Y_le_iff (j := 12) (jj := 13) (by norm_num) (by norm_num)).1 h.le)
      (by decide)

end Lattice

end CFSG.Quasithin.ModH.M23b
