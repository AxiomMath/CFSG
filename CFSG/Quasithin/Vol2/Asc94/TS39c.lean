module

public import CFSG.Quasithin.Vol2.Asc94.TS39b
public import CFSG.Quasithin.Vol2.Asc94.TSGen2

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

structure Frame2 (G : Type) [Group G] (z : G) extends Frame1 G z where
  A : Subgroup G
  A' : Subgroup G
  A_le_T : A ≤ T
  A'_le_T : A' ≤ T
  A_normal : ∀ t ∈ T, ∀ a ∈ A, t⁻¹ * a * t ∈ A
  A'_normal : ∀ t ∈ T, ∀ a ∈ A', t⁻¹ * a * t ∈ A'
  A_elem : IsElemAbelian 2 A
  A'_elem : IsElemAbelian 2 A'
  card_A : Nat.card A = 64
  card_A' : Nat.card A' = 64
  z_mem_A : z ∈ A
  card_A_U : Nat.card ↥(A ⊓ U) = 8
  card_A'_U : Nat.card ↥(A' ⊓ U) = 4
  A_max : ∀ E : Subgroup G, E ≤ T → IsElemAbelian 2 E → Nat.card E = 64 → E = A ∨ E = A'
  AU_max : ∀ E : Subgroup G, IsElemAbelian 2 E →
    E ≤ Subgroup.centralizer ((A ⊓ U : Subgroup G) : Set G) → E ≤ A ∨ E ≤ U

theorem Frame2.isPGroup_A (F : Frame2 G z) : IsPGroup 2 F.A :=
  IsPGroup.of_card (n := 6) (by rw [F.card_A]; norm_num)

theorem Frame2.comm_A (F : Frame2 G z) {a b : G} (ha : a ∈ F.A) (hb : b ∈ F.A) : a * b = b * a :=
  congrArg Subtype.val (F.A_elem.1.is_comm.comm (⟨a, ha⟩ : F.A) ⟨b, hb⟩)

theorem Frame0.conjSubgroup_U (F : Frame0 G z) {n : G} (hn : n ∈ Cz z) :
    cjS n F.U = F.U :=
  Gen.mem_normalizer_iff_cj.1 (F.le_normalizer_U hn)

theorem s39_6_1 (F : Frame2 G z) : ¬ ∃ g : G, cjS g F.A = F.A' := by
  rintro ⟨g, hg⟩
  obtain ⟨P, hP⟩ := s39_2 F.toFrame1.toFrame0
  have hA : (F.A'.subgroupOf (P : Subgroup G)).Normal := by
    rw [hP]
    exact Gen.normal_subgroupOf_of_conj F.A'_normal
  have hB : (F.A.subgroupOf (P : Subgroup G)).Normal := by
    rw [hP]
    exact Gen.normal_subgroupOf_of_conj F.A_normal
  obtain ⟨n, hn, hnA⟩ := Gen.exists_normalizer_conj_of_normal P hA hB
    (by rw [hP]; exact F.A'_le_T) (by rw [hP]; exact F.A_le_T) hg
  rw [hP] at hn
  have hnH : n ∈ Cz z := F.toFrame1.toFrame0.normalizer_T_le_H n hn
  have h1 : cjS n (F.A ⊓ F.U) = F.A' ⊓ F.U := by
    rw [Gen.cj_inf, hnA, F.toFrame1.toFrame0.conjSubgroup_U hnH]
  have h2 := Gen.card_conjSubgroup n (F.A ⊓ F.U)
  rw [h1, F.card_A_U, F.card_A'_U] at h2
  omega

theorem s39_6_2 (F : Frame2 G z) : WeaklyClosedIn F.A F.T := by
  refine ⟨F.A_le_T, fun g hg => ?_⟩
  have hel := Gen.isElemAbelian_conjSubgroup g F.A_elem
  have hcard : Nat.card (cjS g F.A) = 64 := by rw [Gen.card_conjSubgroup, F.card_A]
  rcases F.A_max _ hg hel hcard with h | h
  · exact h
  · exact absurd ⟨g, h⟩ (s39_6_1 F)

theorem s39_6_3 (F : Frame2 G z) {a b g : G} (ha : a ∈ F.A) (hb : b ∈ F.A)
    (hab : g⁻¹ * a * g = b) :
    ∃ n ∈ Subgroup.normalizer (F.A : Set G), n⁻¹ * a * n = b := by
  obtain ⟨P, hP⟩ := s39_2 F.toFrame1.toFrame0
  have hwc : WeaklyClosedIn F.A (P : Subgroup G) := by
    rw [hP]
    exact s39_6_2 F
  exact normalizer_controls_fusion_of_weaklyClosedIn_pGroup F.isPGroup_A
    (Gen.weaklyClosedIn_of_sylow P hwc) (fun s hs => F.comm_A ha hs) (fun s hs => F.comm_A hb hs)
    hab

theorem cj_le_centralizer {D X : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (D : Set G)) (hX : ∀ x ∈ X, ∀ d ∈ D, d * x = x * d) :
    cjS n X ≤ Subgroup.centralizer (D : Set G) := by
  intro x hx
  rw [Gen.mem_cj] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : n⁻¹ * d * n ∈ D := by
    have h := (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * d * n)).2
    refine h ?_
    rw [show n * (n⁻¹ * d * n) * n⁻¹ = d by group]
    exact hd
  have h1 := hX _ hx _ hd'
  calc d * x = n * ((n⁻¹ * d * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * (n⁻¹ * d * n)) * n⁻¹ := by rw [h1]
    _ = x * d := by group

theorem s39_6_4 (F : Frame2 G z) :
    Subgroup.normalizer ((F.A ⊓ F.U : Subgroup G) : Set G) =
      Subgroup.normalizer (F.A : Set G) ⊓ Subgroup.normalizer (F.U : Set G) := by
  have hUab : ∀ x ∈ F.U, ∀ y ∈ F.U, y * x = x * y := fun x hx y hy =>
    (congrArg Subtype.val (F.U_elem.1.is_comm.comm (⟨x, hx⟩ : F.U) ⟨y, hy⟩)).symm
  have hAab : ∀ x ∈ F.A, ∀ y ∈ F.A, y * x = x * y := fun x hx y hy => (F.comm_A hx hy).symm
  have hcardU : Nat.card F.U = 16 := F.card_U
  apply le_antisymm
  · intro n hn
    have hAC := cj_le_centralizer (X := F.A) hn
      (fun x hx d hd => hAab x hx d (Subgroup.mem_inf.1 hd).1)
    have hUC := cj_le_centralizer (X := F.U) hn
      (fun x hx d hd => hUab x hx d (Subgroup.mem_inf.1 hd).2)
    have hnA : cjS n F.A = F.A := by
      rcases F.AU_max _ (Gen.isElemAbelian_conjSubgroup n F.A_elem) hAC with h | h
      · exact Subgroup.eq_of_le_of_card_ge h (by rw [Gen.card_conjSubgroup])
      · exfalso
        have := Subgroup.card_le_of_le h
        rw [Gen.card_conjSubgroup, F.card_A, hcardU] at this
        omega
    have hnU : cjS n F.U = F.U := by
      rcases F.AU_max _ (Gen.isElemAbelian_conjSubgroup n F.U_elem) hUC with h | h
      · exfalso
        have hni : cjS n⁻¹ F.A = F.A := by
          conv_lhs => rw [← hnA]
          exact Gen.cj_inv_cj n _
        have hUA : F.U ≤ F.A := by
          intro u hu
          have h1 : u ∈ cjS n⁻¹ (cjS n F.U) := by
            rw [Gen.cj_inv_cj]
            exact hu
          have h2 : cjS n⁻¹ (cjS n F.U) ≤ cjS n⁻¹ F.A :=
            Subgroup.map_mono h
          rw [hni] at h2
          exact h2 h1
        have h3 : F.A ⊓ F.U = F.U := inf_eq_right.2 hUA
        have h4 := F.card_A_U
        rw [h3, hcardU] at h4
        omega
      · exact Subgroup.eq_of_le_of_card_ge h (by rw [Gen.card_conjSubgroup])
    exact ⟨Gen.mem_normalizer_iff_cj.2 hnA, Gen.mem_normalizer_iff_cj.2 hnU⟩
  · intro n hn
    have hnA := Gen.mem_normalizer_iff_cj.1 (Subgroup.mem_inf.1 hn).1
    have hnU := Gen.mem_normalizer_iff_cj.1 (Subgroup.mem_inf.1 hn).2
    refine Gen.mem_normalizer_iff_cj.2 ?_
    rw [Gen.cj_inf, hnA, hnU]

end CFSG.Quasithin.A94
