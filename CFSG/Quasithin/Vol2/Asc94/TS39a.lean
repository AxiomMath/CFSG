module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame
public import CFSG.Quasithin.Vol2.Asc94.TSGen
public import CFSG.Quasithin.Vol2.Asc94.TSNat4

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame0.z_ne_one (F : Frame0 G z) : z ≠ 1 := by
  intro h
  have := F.ord
  rw [h] at this
  simp at this

theorem Frame0.z_mem_T (F : Frame0 G z) : z ∈ F.T := F.U_le_T F.z_mem_U

theorem Frame0.z_comm_T (F : Frame0 G z) {t : G} (ht : t ∈ F.T) : z * t = t * z :=
  (Subgroup.mem_centralizer_singleton_iff.1 (F.T_le_H ht)).symm

theorem Frame0.isPGroup_T (F : Frame0 G z) : IsPGroup 2 F.T := by
  rw [IsPGroup.iff_card]
  exact ⟨10, F.card_T⟩

theorem Frame0.normalizer_T_le_H (F : Frame0 G z) :
    ∀ n ∈ Subgroup.normalizer (F.T : Set G), n ∈ Cz z := by
  intro n hn
  have hz1 : z ≠ 1 := F.z_ne_one
  have hnz : n * z * n⁻¹ ∈ F.T := (Subgroup.mem_normalizer_iff.1 hn z).1 F.z_mem_T
  have hcomm : ∀ y ∈ F.T, (n * z * n⁻¹) * y = y * (n * z * n⁻¹) := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ F.T := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
      simpa using this
    have h := F.z_comm_T hy'
    calc (n * z * n⁻¹) * y = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by rw [h]
      _ = y * (n * z * n⁻¹) := by group
  rcases F.center_T _ hnz hcomm with h | h
  · exfalso
    apply hz1
    have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    rw [this, h]
    group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : n * z = z * n := by
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [h]
    exact h2

theorem Frame0.eq_T_of_le_H (F : Frame0 G z) {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQH : Q ≤ Cz z) (hTQ : F.T ≤ Q) :
    Q = F.T := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  have hdvd : Nat.card Q ∣ Nat.card (Cz z) := Subgroup.card_dvd_of_le hQH
  rw [F.card_H, hk] at hdvd
  have hk10 : k ≤ 10 := by
    by_contra hk11
    have h2 : 2 ^ 11 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h3 : 2 ^ 11 ∣ 21504 := h2.trans hdvd
    omega
  have hle : Nat.card F.T ≤ Nat.card Q := Subgroup.card_le_of_le hTQ
  rw [F.card_T, hk] at hle
  have : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk10
  have heq : Nat.card Q = Nat.card F.T := by
    rw [F.card_T, hk]
    omega
  exact (Subgroup.eq_of_le_of_card_ge hTQ heq.le).symm

theorem s39_2 (F : Frame0 G z) : ∃ P : Sylow 2 G, (P : Subgroup G) = F.T := by
  have hmax := Gen.maximal_pSubgroup_of_normalizer_le (p := 2) (P := F.T) (C := Cz z) (K := ⊤)
    F.isPGroup_T F.T_le_H le_top (fun Q hQ hQH hTQ => F.eq_T_of_le_H hQ hQH hTQ)
    (fun n _ hn => F.normalizer_T_le_H n hn)
  obtain ⟨P, hP⟩ := F.isPGroup_T.exists_le_sylow
  exact ⟨P, (hmax P P.isPGroup' le_top hP).symm ▸ rfl⟩


theorem Frame0.le_normalizer_U (F : Frame0 G z) : Cz z ≤ Subgroup.normalizer (F.U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have := F.U_normal h⁻¹ (Subgroup.inv_mem _ hh) u hu
    simpa using this
  · intro hu
    have := F.U_normal h hh _ hu
    simpa [mul_assoc] using this

theorem Frame0.centralizer_U_le (F : Frame0 G z) {x : G} (hx : ∀ u ∈ F.U, x * u = u * x) :
    x ∈ F.U :=
  F.U_cent x (Subgroup.mem_centralizer_singleton_iff.2 (hx z F.z_mem_U)) hx

theorem Frame0.card_normalizer_of_ne (F : Frame0 G z)
    (hne : ∃ m ∈ Subgroup.normalizer (F.U : Set G), m⁻¹ * z * m ≠ z) :
    Nat.card (Subgroup.normalizer (F.U : Set G)) = 322560 := by
  set M := Subgroup.normalizer (F.U : Set G) with hM
  have hHM : Cz z ≤ M := F.le_normalizer_U
  obtain ⟨m, hm, hmz⟩ := hne
  have hz1 : z ≠ 1 := F.z_ne_one
  have hconj : ∀ l ∈ M, ∀ u ∈ F.U, l⁻¹ * u * l ∈ F.U := by
    intro l hl u hu
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl) u).1 hu
    simpa using this
  have hO : {x : G | ∃ l ∈ M, x = l⁻¹ * z * l} = (F.U : Set G) \ {1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨hconj l hl z F.z_mem_U, fun h => hz1 ?_⟩
      have : z = l * (l⁻¹ * z * l) * l⁻¹ := by group
      rw [this, h]
      group
    · rintro ⟨hx, hx1⟩
      by_cases hxz : x = z
      · exact ⟨1, Subgroup.one_mem _, by simp [hxz]⟩
      · have hw : m⁻¹ * z * m ∈ F.U := hconj m hm z F.z_mem_U
        have hw1 : m⁻¹ * z * m ≠ 1 := fun h => hz1 (by
          have : z = m * (m⁻¹ * z * m) * m⁻¹ := by group
          rw [this, h]
          group)
        obtain ⟨h, hh, hxh⟩ := F.U_trans _ hw hw1 hmz x hx hx1 hxz
        refine ⟨m * h, M.mul_mem hm (hHM hh), ?_⟩
        rw [hxh]
        group
  have hcard := Gen.card_conjOrbit_mul_card_stab M z
  have hset : Nat.card {x : G // ∃ l ∈ M, x = l⁻¹ * z * l} = 15 := by
    have h1 : Nat.card {x : G // ∃ l ∈ M, x = l⁻¹ * z * l} =
        Set.ncard {x : G | ∃ l ∈ M, x = l⁻¹ * z * l} := Nat.card_coe_set_eq _
    have h2 : Set.ncard (F.U : Set G) = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact F.card_U
    rw [h1, hO, Set.ncard_sdiff_singleton_of_mem F.U.one_mem, h2]
  have hMH : M ⊓ Cz z = Cz z := inf_eq_right.2 hHM
  rw [hMH, hset, F.card_H] at hcard
  omega


theorem s39_3 (F : Frame0 G z) :
    Subgroup.normalizer (F.U : Set G) = Cz z ∨
      NaturalSL F.U (Subgroup.normalizer (F.U : Set G)) 4 1 := by
  by_cases hne : ∃ m ∈ Subgroup.normalizer (F.U : Set G), m⁻¹ * z * m ≠ z
  · right
    refine CFSG.Quasithin.A94.TS.naturalSL_of_card_four (E := F.U) F.card_U ?_ ?_
      (F.card_normalizer_of_ne hne)
    · intro a ha b hb
      refine ⟨?_, congrArg Subtype.val (F.U_elem.1.is_comm.comm (⟨a, ha⟩ : F.U) ⟨b, hb⟩)⟩
      rw [← sq]
      exact F.U_elem.2 a ha
    · intro g hg
      exact F.centralizer_U_le hg
  · left
    push Not at hne
    apply le_antisymm
    · intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hne m hm
      calc m * z = m * (m⁻¹ * z * m) := by rw [h]
        _ = z * m := by group
    · exact F.le_normalizer_U

end CFSG.Quasithin.A94
