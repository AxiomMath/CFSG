module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSixPart

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

theorem card_zpowers_sup_cyc3 {α : Type*} [DecidableEq α] [Fintype α] {x y z u v w : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hd : ∀ p ∈ ({x, y, z} : Set α), ∀ q ∈ ({u, v, w} : Set α), p ≠ q) :
    Nat.card (↥(Subgroup.zpowers (cyc3 x y z) ⊔ Subgroup.zpowers (cyc3 u v w))) = 9 := by
  classical
  let g : Perm α := cyc3 x y z
  let h : Perm α := cyc3 u v w
  change Nat.card (↥(Subgroup.zpowers g ⊔ Subgroup.zpowers h)) = 9
  have hgx : g x = y := cyc3_apply_left hxy hxz hyz
  have hgy : g y = z := cyc3_apply_middle hxy hxz hyz
  have hgz : g z = x := cyc3_apply_right hxy hxz hyz
  have hhu : h u = v := cyc3_apply_left huv huw hvw
  have hhv : h v = w := cyc3_apply_middle huv huw hvw
  have hhw : h w = u := cyc3_apply_right huv huw hvw
  have hg3 : g ^ 3 = 1 := by
    ext p
    change (g ^ 3) p = p
    rcases eq_or_ne p x with rfl | hpx
    · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hgy, hgz]
    · rcases eq_or_ne p y with rfl | hpy
      · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hgz, hgx]
      · rcases eq_or_ne p z with rfl | hpz
        · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
            hgz, hgx, hgy]
        · simpa using Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
            (cyc3_apply_of_ne hpx hpy hpz) 3
  have hh3 : h ^ 3 = 1 := by
    ext p
    change (h ^ 3) p = p
    rcases eq_or_ne p u with rfl | hpu
    · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hhu, hhv, hhw]
    · rcases eq_or_ne p v with rfl | hpv
      · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hhv, hhw, hhu]
      · rcases eq_or_ne p w with rfl | hpw
        · rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
            hhw, hhu, hhv]
        · simpa using Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
            (cyc3_apply_of_ne hpu hpv hpw) 3
  have hg1 : g ≠ 1 := by
    intro hg
    have hxg : g x = x := by rw [hg]; rfl
    rw [hgx] at hxg
    exact hxy hxg.symm
  have hh1 : h ≠ 1 := by
    intro hh
    have huh : h u = u := by rw [hh]; rfl
    rw [hhu] at huh
    exact huv huh.symm
  have hgord : orderOf g = 3 := orderOf_eq_prime (p := 3) hg3 hg1
  have hhord : orderOf h = 3 := orderOf_eq_prime (p := 3) hh3 hh1
  have hgcard : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hgord]
  have hhcard : Nat.card (Subgroup.zpowers h) = 3 := by rw [Nat.card_zpowers, hhord]
  have hdisj : Equiv.Perm.Disjoint g h := by
    intro p
    by_cases hp : p ∈ ({x, y, z} : Set α)
    · right
      have hp' : p ∉ ({u, v, w} : Set α) := fun hq => (hd p hp p hq) rfl
      exact cyc3_apply_of_ne (fun hpu => hp' (by simp [hpu]))
        (fun hpv => hp' (by simp [hpv])) (fun hpw => hp' (by simp [hpw]))
    · left
      exact cyc3_apply_of_ne (fun hpx => hp (by simp [hpx]))
        (fun hpy => hp (by simp [hpy])) (fun hpz => hp (by simp [hpz]))
  have hbot : Subgroup.zpowers g ⊓ Subgroup.zpowers h = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk.1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk.2
    have hd2 : Equiv.Perm.Disjoint (g ^ i) (h ^ j) := hdisj.zpow_disjoint_zpow i j
    rw [hj] at hd2
    ext p
    rcases hd2 p with hh | hh <;> exact hh
  let H : Bool → Subgroup (Perm α) := fun b => if b then Subgroup.zpowers h else Subgroup.zpowers g
  have hH0 : H false = Subgroup.zpowers g := by simp [H]
  have hH1 : H true = Subgroup.zpowers h := by simp [H]
  have hcomm_g : ∀ a ∈ Subgroup.zpowers g, ∀ b ∈ Subgroup.zpowers h, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hdisj.commute.zpow_zpow m n
  have hcomm : Pairwise fun i j : Bool => ∀ a b : Perm α, a ∈ H i → b ∈ H j → Commute a b := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · intro a b ha hb
      rw [hH0] at ha
      rw [hH1] at hb
      exact hcomm_g a ha b hb
    · intro a b ha hb
      rw [hH1] at ha
      rw [hH0] at hb
      exact (hcomm_g b hb a ha).symm
    · exact absurd rfl hij
  have hind : iSupIndep H := by
    rw [iSupIndep_pair (i := false) (j := true) (by decide) (fun k => by cases k <;> simp)]
    rw [disjoint_iff, hH0, hH1]
    exact hbot
  have hinj : Function.Injective (Subgroup.noncommPiCoprod hcomm) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : (Subgroup.noncommPiCoprod hcomm).range =
      Subgroup.zpowers g ⊔ Subgroup.zpowers h := by
    rw [Subgroup.noncommPiCoprod_range, iSup_bool_eq, hH1, hH0, sup_comm]
  have hpi : Nat.card (∀ b : Bool, H b) = 9 := by
    rw [Nat.card_pi, Fintype.prod_bool, hH1, hH0, hhcard, hgcard]
    norm_num
  have hfinal : Nat.card (↥(Subgroup.zpowers g ⊔ Subgroup.zpowers h)) = 9 := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective (f := Subgroup.noncommPiCoprod hcomm)
      hinj).symm.toEquiv, hpi]
  exact hfinal

theorem b5_FiveSixNine_exists_two_disjoint_triples {n : ℕ} {S : Set (Fin n)}
    (hS : 6 ≤ S.ncard) :
    ∃ x y z u v w : Fin n,
      x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ u ∈ S ∧ v ∈ S ∧ w ∈ S ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (∀ p ∈ ({x, y, z} : Set (Fin n)), ∀ q ∈ ({u, v, w} : Set (Fin n)), p ≠ q) := by
  classical
  have h2 : 2 < S.ncard := by omega
  obtain ⟨x, y, z, hxS, hyS, hzS, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (s := S)).mp h2
  have hsub : ({x, y, z} : Set (Fin n)) ⊆ S := by
    intro p hp
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hcard3 : ({x, y, z} : Set (Fin n)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hdiff : (S \ ({x, y, z} : Set (Fin n))).ncard = S.ncard - 3 := by
    rw [Set.ncard_sdiff hsub, hcard3]
  have h3 : 2 < (S \ ({x, y, z} : Set (Fin n))).ncard := by
    rw [hdiff]; omega
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
    (Set.two_lt_ncard_iff (s := S \ ({x, y, z} : Set (Fin n)))).mp h3
  have huS : u ∈ S := hu.1
  have hvS : v ∈ S := hv.1
  have hwS : w ∈ S := hw.1
  have hu' : u ∉ ({x, y, z} : Set (Fin n)) := hu.2
  have hv' : v ∉ ({x, y, z} : Set (Fin n)) := hv.2
  have hw' : w ∉ ({x, y, z} : Set (Fin n)) := hw.2
  have hdisj : ∀ p ∈ ({x, y, z} : Set (Fin n)), ∀ q ∈ ({u, v, w} : Set (Fin n)), p ≠ q := by
    intro p hp q hq hpq
    have hq' : q ∉ ({x, y, z} : Set (Fin n)) := by
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact hu'
      · exact hv'
      · exact hw'
    exact hq' (hpq ▸ hp)
  exact ⟨x, y, z, u, v, w, hxS, hyS, hzS, huS, hvS, hwS,
    hxy, hxz, hyz, huv, huw, hvw, hdisj⟩

theorem b5_FiveSixNine_exists_nine_le_of_six {n : ℕ} {S : Set (Fin n)} (hS : 6 ≤ S.ncard) :
    ∃ P : Subgroup (Perm (Fin n)), Nat.card P = 9 ∧ P ≤ alternatingGroup (Fin n) ∧
      P ≤ partStab S := by
  obtain ⟨x, y, z, u, v, w, hxS, hyS, hzS, huS, hvS, hwS,
    hxy, hxz, hyz, huv, huw, hvw, hd⟩ := b5_FiveSixNine_exists_two_disjoint_triples hS
  refine ⟨Subgroup.zpowers (cyc3 x y z) ⊔ Subgroup.zpowers (cyc3 u v w), ?_, ?_, ?_⟩
  · exact card_zpowers_sup_cyc3 hxy hxz hyz huv huw hvw hd
  · exact sup_le
      (Subgroup.zpowers_le.mpr (cyc3_mem_alternatingGroup hxy hyz))
      (Subgroup.zpowers_le.mpr (cyc3_mem_alternatingGroup huv hvw))
  · exact sup_le
      (Subgroup.zpowers_le.mpr (cyc3_mem_partStab_of_mem hxS hyS hzS))
      (Subgroup.zpowers_le.mpr (cyc3_mem_partStab_of_mem huS hvS hwS))

theorem b5_FiveSixNine_exists_nine_le_of_split {n : ℕ} {Γ : Set (Fin n)}
    (hΓ : 3 ≤ Γ.ncard) (hΓc : 3 ≤ Γᶜ.ncard) :
    ∃ P : Subgroup (Perm (Fin n)), Nat.card P = 9 ∧ P ≤ alternatingGroup (Fin n) ∧
      P ≤ partStab Γ := by
  have h2Γ : 2 < Γ.ncard := by omega
  obtain ⟨x, y, z, hxΓ, hyΓ, hzΓ, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (s := Γ)).mp h2Γ
  have h2Γc : 2 < Γᶜ.ncard := by omega
  obtain ⟨u, v, w, huΓc, hvΓc, hwΓc, huv, huw, hvw⟩ := (Set.two_lt_ncard_iff (s := Γᶜ)).mp h2Γc
  have hd : ∀ p ∈ ({x, y, z} : Set (Fin n)), ∀ q ∈ ({u, v, w} : Set (Fin n)), p ≠ q := by
    intro p hp q hq hpq
    have hpΓ : p ∈ Γ := by
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    have hqΓc : q ∈ Γᶜ := by
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> assumption
    exact hqΓc (hpq ▸ hpΓ)
  refine ⟨Subgroup.zpowers (cyc3 x y z) ⊔ Subgroup.zpowers (cyc3 u v w), ?_, ?_, ?_⟩
  · exact card_zpowers_sup_cyc3 hxy hxz hyz huv huw hvw hd
  · exact sup_le
      (Subgroup.zpowers_le.mpr (cyc3_mem_alternatingGroup hxy hyz))
      (Subgroup.zpowers_le.mpr (cyc3_mem_alternatingGroup huv hvw))
  · exact sup_le
      (Subgroup.zpowers_le.mpr (cyc3_mem_partStab_of_mem hxΓ hyΓ hzΓ))
      (Subgroup.zpowers_le.mpr (cyc3_mem_partStab_of_notMem huΓc hvΓc hwΓc))

theorem exists_card_nine_le {n : ℕ} {Γ : Set (Fin n)}
    (h : (3 ≤ Γ.ncard ∧ 3 ≤ Γᶜ.ncard) ∨ 6 ≤ Γ.ncard ∨ 6 ≤ Γᶜ.ncard) :
    ∃ P : Subgroup (Perm (Fin n)), Nat.card P = 9 ∧ P ≤ alternatingGroup (Fin n) ∧
      P ≤ partStab Γ := by
  rcases h with ⟨hΓ, hΓc⟩ | h6 | h6
  · exact b5_FiveSixNine_exists_nine_le_of_split hΓ hΓc
  · exact b5_FiveSixNine_exists_nine_le_of_six h6
  · obtain ⟨P, hP9, hPalt, hPstab⟩ := b5_FiveSixNine_exists_nine_le_of_six h6
    exact ⟨P, hP9, hPalt, by rw [← partStab_compl Γ]; exact hPstab⟩

end CFSG.LocalAnalysis.WeakClosure81
