module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_or_eq_of_card_nine {X : Type*} [Group X] [Finite X] {E H Q : Subgroup X}
    (hE : Nat.card E = 27) (hH : Nat.card H = 9) (hHQ : H ≤ Q) (hQE : Q ≤ E) : Q = H ∨ Q = E := by
  have h1 : Nat.card Q ∣ 27 := hE ▸ Subgroup.card_dvd_of_le hQE
  have h2 : 9 ∣ Nat.card Q := hH ▸ Subgroup.card_dvd_of_le hHQ
  have h3 : Nat.card Q = 9 ∨ Nat.card Q = 27 := by
    obtain ⟨m, hm⟩ := h2
    rw [hm] at h1
    obtain ⟨t, ht⟩ := h1
    have hmt : m * t = 3 := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9)
      rw [← mul_assoc]
      omega
    have hm3 : m ∣ 3 := Dvd.intro t hmt
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
    · left; simpa using hm
    · right; simpa using hm
  rcases h3 with h3 | h3
  · left
    exact (Subgroup.eq_of_le_of_card_ge hHQ (by rw [h3, hH])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hQE (by rw [h3, hE])

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem a6_config148 {c : G} {L : Subgroup G} (hS : Sec14Std G A c L)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {B : Subgroup G} (hB : IsHyperplane A B)
    {b d : G} (hbB : b ∈ B) (hdB : d ∈ B) (hd1 : d ≠ 1) (hbd : b ∉ Subgroup.zpowers d)
    {J K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hJc : IsComponent J)
    (hJ6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6))) (hKc : IsComponent K)
    (hK6 : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6))) (hKJ : K ≠ J)
    (hAJ : img148 A Y A ≤ Subgroup.normalizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAK : img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hBJ : img148 A Y B ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hdZ : J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers (alpha148 A Y d (hB.1 hdB)))
    (hKZ : K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    alpha148 A Y b (hB.1 hbB) ∈ K ∧
      alpha148 A Y b (hB.1 hbB) ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
      img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
          Subgroup.zpowers (alpha148 A Y b (hB.1 hbB)) = img148 A Y A ∧
      Nat.card ↥(img148 A Y A ⊓ J) = 9 ∧
      Subgroup.zpowers (alpha148 A Y b (hB.1 hbB)) ⊔ img148 A Y A ⊓ J = img148 A Y A := by
  have hA : Late.IsE27 A := hS.isE27
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  set bα := alpha148 A Y b hbA with hbαdef
  set dα := alpha148 A Y d hdA with hdαdef
  have hAE := img148_isE27 (Y := Y) hA
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hAY hw hw3
  have hJp : Group.IsPerfect ↥J := hJc.1.1
  have hKp : Group.IsPerfect ↥K := hKc.1.1
  obtain ⟨hBA, -, hmax⟩ := Ronan148J.img148_hyperplane_max (Y := Y) hA hB
  have hB9 : Nat.card (img148 A Y B) = 9 := by
    rw [Ronan148J.card_img148_of_le hA.1.2 hB.1]
    have := hB.2
    rw [hA.2] at this
    omega
  have hbα : bα ∈ img148 A Y B := mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hbA, hbB, rfl⟩
  have hdα : dα ∈ img148 A Y B := mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdαJZ : dα ∈ J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hdZ]; exact Subgroup.mem_zpowers _
  have hdαKZ : dα ∈ K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hKZ]; exact hdαJZ
  have hJK : ∀ x ∈ J, x ∈ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x hx =>
    Res2LBal.mem_centralizer_of_mem_of_ne hKc hJc hKJ hx
  have hKJ' : ∀ x ∈ K, x ∈ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun x hx =>
    Res2LBal.mem_centralizer_of_mem_of_ne hJc hKc (Ne.symm hKJ) hx
  obtain ⟨j, hjA, hjJ, hjnc⟩ := Ronan148J.exists_noncentral_mem_of_tripleCover hJ6 hJp hA3 hF3
    hAJ hBJ hBA hmax
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjC : j ∉ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    obtain ⟨y, hy, hjy⟩ := hjnc
    exact fun hjC => hjy (Subgroup.mem_centralizer_iff.mp hjC y hy).symm
  have hCB : img148 A Y A ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      have hjC' : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjC hjC'.2
  have hdα1 : dα ≠ 1 := fun h1 => hd1 (alpha148_injective hA.1.2 hdA A.one_mem
    (h1.trans ((alpha148_eq_mk' A.one_mem).trans
      (mk'_ker148_eq_one_iff.mpr (Subgroup.one_mem _))).symm))
  have hdα3 : dα ^ 3 = 1 := hA3 dα hdαA
  have hjd : j ∉ Subgroup.zpowers dα := fun h =>
    hjC ((Subgroup.zpowers_le.mpr hdαJZ.2) h)
  set E₁ := Subgroup.zpowers dα ⊔ Subgroup.zpowers j with hE₁
  have hE₁9 : Nat.card E₁ = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine (hAab _ hdαA _ hjA) hdα3 hdα1 hj3 hjd
  have hE₁A : E₁ ≤ img148 A Y A :=
    sup_le (Subgroup.zpowers_le.mpr hdαA) (Subgroup.zpowers_le.mpr hjA)
  have hE₁K : E₁ ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    sup_le (Subgroup.zpowers_le.mpr hdαKZ.2) (Subgroup.zpowers_le.mpr (hJK j hjJ))
  have hE₁J : E₁ ≤ J := sup_le (Subgroup.zpowers_le.mpr hdαJZ.1) (Subgroup.zpowers_le.mpr hjJ)
  have hE₁max : ∀ H : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), E₁ ≤ H → H ≤ img148 A Y A →
      H = E₁ ∨ H = img148 A Y A := fun H h1 h2 => eq_or_eq_of_card_nine hAE.2 hE₁9 h1 h2
  obtain ⟨k, hkA, hkK, hknc⟩ := Ronan148J.exists_noncentral_mem_of_tripleCover hK6 hKp hA3 hF3
    hAK hE₁K hE₁A hE₁max
  have hk3 : k ^ 3 = 1 := hA3 k hkA
  have hkC : k ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    obtain ⟨y, hy, hky⟩ := hknc
    exact fun hkC => hky (Subgroup.mem_centralizer_iff.mp hkC y hy).symm
  have hkB : k ∈ img148 A Y B := by
    rw [← hCB]
    exact ⟨hkA, hKJ' k hkK⟩
  have hkd : k ∉ Subgroup.zpowers dα := fun h => hkC ((Subgroup.zpowers_le.mpr hdαKZ.2) h)
  have hBdk : img148 A Y B = Subgroup.zpowers dα ⊔ Subgroup.zpowers k := by
    refine (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hdα) (Subgroup.zpowers_le.mpr hkB)) ?_).symm
    rw [hB9, Ronan148J.card_zpowers_sup_zpowers_eq_nine (hAab _ hdαA _ hkA) hdα3 hdα1 hk3 hkd]
  have hbK : bα ∈ K := by
    have h1 : bα ∈ Subgroup.zpowers dα ⊔ Subgroup.zpowers k := hBdk ▸ hbα
    exact (sup_le (Subgroup.zpowers_le.mpr hdαKZ.1) (Subgroup.zpowers_le.mpr hkK)) h1
  have hbC : bα ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro hbC
    have h1 : bα ∈ K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := ⟨hbK, hbC⟩
    rw [hKZ, hdZ] at h1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hbd
    have hdn : d ^ n ∈ A := A.zpow_mem hdA n
    have e1 : alpha148 A Y (d ^ n) hdn = bα := by
      rw [← hn, alpha148_eq_mk', hdαdef, alpha148_eq_mk', ← map_zpow]
      congr 1
    rw [alpha148_injective hA.1.2 hbA hdn e1.symm]
    exact Subgroup.zpow_mem_zpowers d n
  have hbE₁ : bα ∉ E₁ := fun h => hbC (hE₁K h)
  refine ⟨hbK, hbC, ?_, ?_, ?_⟩
  · rcases hE₁max _ ((le_inf hE₁A hE₁K).trans le_sup_left)
      (sup_le inf_le_left (Subgroup.zpowers_le.mpr (alpha148_mem_img148 hbA))) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers bα ≤ _) (Subgroup.mem_zpowers bα)) hbE₁
    · exact h
  · have hAJE : img148 A Y A ⊓ J = E₁ := by
      rcases hE₁max _ (le_inf hE₁A hE₁J) inf_le_left with h | h
      · exact h
      · exfalso
        have hbJ : bα ∈ img148 A Y A ⊓ J := by rw [h]; exact alpha148_mem_img148 hbA
        exact hbC (hJK _ hbJ.2)
    rw [hAJE, hE₁9]
  · rcases hE₁max _ ((le_inf hE₁A hE₁J).trans le_sup_right)
      (sup_le (Subgroup.zpowers_le.mpr (alpha148_mem_img148 hbA)) inf_le_left) with h | h
    · exact absurd (h ▸ (le_sup_left : Subgroup.zpowers bα ≤ _) (Subgroup.mem_zpowers bα)) hbE₁
    · exact h

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
