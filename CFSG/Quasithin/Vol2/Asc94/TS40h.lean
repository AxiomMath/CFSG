module

public import CFSG.Quasithin.Vol2.Asc94.TS40g
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame3.Δ2_sub_Sz' (F : Frame3 G z) (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    F.Δ 2 ⊆ F.Sz := by
  intro a ha
  obtain ⟨haU, ha1, haz⟩ := F.Δ2_sub a ha
  have hA : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨2, ha⟩
  rw [F.Δ_union] at hA
  exact ⟨hA.1, ha1, hU2 a haU ha1⟩

theorem Frame3.exists_y21 (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) (h21 : F.Sz.ncard = 21) :
    ∃ y : Fin 7, (y = 4 ∨ y = 5) ∧ F.Δ y ⊆ F.Sz ∧
      ∀ i : Fin 7, F.Δ i ⊆ F.Sz → (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = y) := by
  classical
  have hsum := F.sum_Sz' hU1 hU2
  have hfin7 : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide
  by_cases h4 : F.Δ 4 ⊆ F.Sz <;> by_cases h5 : F.Δ 5 ⊆ F.Sz <;>
    by_cases h6 : F.Δ 6 ⊆ F.Sz <;> simp [h4, h5, h6] at hsum
  all_goals first
    | (exfalso; omega)
    | skip
  · refine ⟨4, Or.inl rfl, h4, fun i hi => ?_⟩
    rcases hfin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd hi F.not_Δ3_sub_Sz
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd hi h5
    · exact absurd hi h6
  · refine ⟨5, Or.inr rfl, h5, fun i hi => ?_⟩
    rcases hfin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd hi F.not_Δ3_sub_Sz
    · exact absurd hi h4
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd hi h6


@[expose] def Frame3.Tp (F : Frame3 G z) : Set G := {t | t ∈ F.Sz ∧ t ∉ F.D}

theorem Frame3.D_split (F : Frame3 G z) {a : G} (ha : a ∈ F.D) :
    a = 1 ∨ a ∈ F.Δ 0 ∨ a ∈ F.Δ 1 := by
  by_cases h1 : a = 1
  · exact Or.inl h1
  · by_cases hz : a = z
    · right
      left
      rw [F.Δ0]
      exact hz
    · right
      right
      rw [F.Δ1]
      exact ⟨ha, by simp [h1, hz]⟩

theorem Frame3.Δ1_sub_D (F : Frame3 G z) {a : G} (ha : a ∈ F.Δ 1) : a ∈ F.D := by
  rw [F.Δ1] at ha
  exact ha.1

theorem Frame3.Δ_sub_A (F : Frame3 G z) {i : Fin 7} {a : G} (ha : a ∈ F.Δ i) : a ∈ F.A ∧ a ≠ 1 := by
  have : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨i, ha⟩
  rw [F.Δ_union] at this
  exact this

theorem Frame3.Tp_eq (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) {y : Fin 7} (hy45 : y = 4 ∨ y = 5) (hyS : F.Δ y ⊆ F.Sz)
    (hyall : ∀ i : Fin 7, F.Δ i ⊆ F.Sz → (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = y)) :
    F.Tp = F.Δ 2 ∪ F.Δ y := by
  have hy0 : y ≠ 0 := by rcases hy45 with rfl | rfl <;> decide
  have hy1 : y ≠ 1 := by rcases hy45 with rfl | rfl <;> decide
  have hy2 : y ≠ 2 := by rcases hy45 with rfl | rfl <;> decide
  have hnD : ∀ {a : G} {i : Fin 7}, a ∈ F.Δ i → i ≠ 0 → i ≠ 1 → a ∉ F.D := by
    intro a i ha hi0 hi1 haD
    obtain ⟨-, ha1⟩ := F.Δ_sub_A ha
    rcases F.D_split haD with h | h | h
    · exact ha1 h
    · exact Set.disjoint_left.1 (F.Δ_disj i 0 hi0) ha h
    · exact Set.disjoint_left.1 (F.Δ_disj i 1 hi1) ha h
  ext a
  constructor
  · rintro ⟨haS, haD⟩
    obtain ⟨haA, ha1⟩ := (⟨haS.1, haS.2.1⟩ : a ∈ F.A ∧ a ≠ 1)
    have haU : a ∈ ⋃ i, F.Δ i := by
      rw [F.Δ_union]
      exact ⟨haA, ha1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haU
    have hiS : F.Δ i ⊆ F.Sz := by
      rcases F.dich i with h | h
      · exact h
      · exact absurd haS (Set.disjoint_left.1 h hi)
    rcases hyall i hiS with rfl | rfl | rfl | rfl
    · rw [F.Δ0] at hi
      exact absurd (by rw [Set.mem_singleton_iff.1 hi]; exact F.z_mem_D) haD
    · exact absurd (F.Δ1_sub_D hi) haD
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (ha | ha)
    · exact ⟨F.Δ2_sub_Sz' hU2 ha, hnD ha (by decide) (by decide)⟩
    · exact ⟨hyS ha, hnD ha hy0 hy1⟩


theorem Frame3.z_mem_Sz (F : Frame3 G z) : z ∈ F.Sz := ⟨F.z_mem_A, F.z_ne_one, 1, by simp⟩

theorem Frame3.card_Dm_inf_D (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hII : Subgroup.normalizer (F.U : Set G) = Cz z) {s : G} (hs : s ∈ F.Δ 1) :
    Nat.card ↥(F.Dm s ⊓ F.D) = 4 := by
  have hsSz : s ∈ F.Sz := F.Δ1_sub_Sz hU1 hs
  have hsD : s ∈ F.D := F.Δ1_sub_D hs
  have hs1 : s ≠ 1 := (F.Δ_sub_A hs).2
  have hsz : s ≠ z := by
    rw [F.Δ1] at hs
    have := hs.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this.2
  have hz1 : z ≠ 1 := F.z_ne_one
  have hsDz : s ∈ F.Dm z := by rw [F.Dm_z]; exact hsD
  have hzDs : z ∈ F.Dm s := F.Dm_symm hU1 F.z_mem_Sz hsSz hsDz
  have hsDs : s ∈ F.Dm s := F.mem_Dm_self hsSz
  have hdvd : Nat.card ↥(F.Dm s ⊓ F.D) ∣ 8 := by
    rw [← F.card_A_U]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h3 : 3 ≤ Nat.card ↥(F.Dm s ⊓ F.D) := by
    have hsub : ({1, z, s} : Set G) ⊆ ((F.Dm s ⊓ F.D : Subgroup G) : Set G) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact (F.Dm s ⊓ F.D).one_mem
      · exact ⟨hzDs, F.z_mem_D⟩
      · exact ⟨hsDs, hsD⟩
    have hc : ({1, z, s} : Set G).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hz1, Ne.symm hs1]),
        Set.ncard_pair (Ne.symm hsz)]
    have := Set.ncard_le_ncard hsub
    rw [hc, ← Nat.card_coe_set_eq] at this
    exact this
  have hne8 : Nat.card ↥(F.Dm s ⊓ F.D) ≠ 8 := by
    intro h8
    have hDcard : Nat.card ↥F.D = 8 := F.card_A_U
    have heq : F.Dm s ⊓ F.D = F.D :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hDcard])
    have hle : F.D ≤ F.Dm s := inf_eq_right.1 heq
    have heq2 : F.D = F.Dm s :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [F.card_Dm hsSz, hDcard])
    exact hsz (F.Dm_inj hII hsSz heq2.symm)
  have hmem : Nat.card ↥(F.Dm s ⊓ F.D) ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hdiv8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdiv8] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem Frame3.card_Dm_diff (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hII : Subgroup.normalizer (F.U : Set G) = Cz z) {s : G} (hs : s ∈ F.Δ 1) :
    ((F.Dm s : Set G) \ (F.D : Set G)).ncard = 4 := by
  have hsSz : s ∈ F.Sz := F.Δ1_sub_Sz hU1 hs
  have h1 := Set.ncard_inter_add_ncard_diff_eq_ncard (F.Dm s : Set G) (F.D : Set G)
  have h2 : ((F.Dm s : Set G) ∩ (F.D : Set G)).ncard = 4 := by
    rw [← Subgroup.coe_inf, ← Nat.card_coe_set_eq]
    exact F.card_Dm_inf_D hU1 hII hs
  have h3 : (F.Dm s : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact F.card_Dm hsSz
  omega

theorem Frame3.rr_values (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hII : Subgroup.normalizer (F.U : Set G) = Cz z) {t : G} (ht : t ∈ F.Tp) :
    (F.Δ 1 ∩ (F.Dm t : Set G)).ncard = 0 ∨ (F.Δ 1 ∩ (F.Dm t : Set G)).ncard = 1 ∨
      (F.Δ 1 ∩ (F.Dm t : Set G)).ncard = 3 := by
  obtain ⟨htS, htD⟩ := ht
  have hztD : z ∉ F.Dm t := by
    intro hz
    have := F.Dm_symm hU1 htS F.z_mem_Sz hz
    rw [F.Dm_z] at this
    exact htD this
  have hset : ((F.Dm t ⊓ F.D : Subgroup G) : Set G) = {1} ∪ (F.Δ 1 ∩ (F.Dm t : Set G)) := by
    ext x
    constructor
    · rintro ⟨hxt, hxD⟩
      rcases F.D_split hxD with h | h | h
      · left
        exact h
      · exfalso
        rw [F.Δ0, Set.mem_singleton_iff] at h
        rw [h] at hxt
        exact hztD hxt
      · right
        exact ⟨h, hxt⟩
    · rintro (h | ⟨h1, h2⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact (F.Dm t ⊓ F.D).one_mem
      · exact ⟨h2, F.Δ1_sub_D h1⟩
  have hdisj : Disjoint ({1} : Set G) (F.Δ 1 ∩ (F.Dm t : Set G)) := by
    rw [Set.disjoint_singleton_left]
    intro h
    exact (F.Δ_sub_A h.1).2 rfl
  have hcard : Nat.card ↥(F.Dm t ⊓ F.D) = 1 + (F.Δ 1 ∩ (F.Dm t : Set G)).ncard := by
    have hc : Nat.card ↥(F.Dm t ⊓ F.D) = ((F.Dm t ⊓ F.D : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq ((F.Dm t ⊓ F.D : Subgroup G) : Set G)
    rw [hc, hset, Set.ncard_union_eq hdisj, Set.ncard_singleton]
  have hdvd : Nat.card ↥(F.Dm t ⊓ F.D) ∣ 8 := by
    rw [← F.card_A_U]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hne8 : Nat.card ↥(F.Dm t ⊓ F.D) ≠ 8 := by
    intro h8
    have hDcard : Nat.card ↥F.D = 8 := F.card_A_U
    have heq : F.Dm t ⊓ F.D = F.D :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hDcard])
    have hle : F.D ≤ F.Dm t := inf_eq_right.1 heq
    have heq2 : F.D = F.Dm t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [F.card_Dm htS, hDcard])
    have := F.Dm_inj hII htS heq2.symm
    exact htD (this ▸ F.z_mem_D)
  have hmem : Nat.card ↥(F.Dm t ⊓ F.D) ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hdiv8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdiv8] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega


theorem Frame3.rr_conj (F : Frame3 G z) {t n : G} (ht : t ∈ F.Tp) (hn : n ∈ F.NA) :
    (F.Δ 1 ∩ (F.Dm (n⁻¹ * t * n) : Set G)).ncard = (F.Δ 1 ∩ (F.Dm t : Set G)).ncard := by
  have hset : F.Δ 1 ∩ (F.Dm (n⁻¹ * t * n) : Set G) =
      (fun x => n⁻¹ * x * n) '' (F.Δ 1 ∩ (F.Dm t : Set G)) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hx2' : n * x * n⁻¹ ∈ F.Dm t := (F.mem_Dm_conj ht.1 hn).1 hx2
      have hx1' : n * x * n⁻¹ ∈ F.Δ 1 := by
        have := F.Δ_inv 1 x hx1 n⁻¹ ⟨Subgroup.inv_mem _ hn.1, Subgroup.inv_mem _ hn.2⟩
        simpa using this
      exact ⟨n * x * n⁻¹, ⟨hx1', hx2'⟩, by group⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨F.Δ_inv 1 y hy1 n hn, ?_⟩
      show n⁻¹ * y * n ∈ F.Dm (n⁻¹ * t * n)
      rw [F.mem_Dm_conj ht.1 hn, show n * (n⁻¹ * y * n) * n⁻¹ = y by group]
      exact hy2
  rw [hset]
  exact Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel (mul_right_cancel h))

theorem card_filter_mem {α : Type*} [Fintype α] (S : Set α) [DecidablePred (· ∈ S)] :
    (Finset.univ.filter (· ∈ S)).card = S.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

theorem Frame3.false_of_card_21 (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) (hII : Subgroup.normalizer (F.U : Set G) = Cz z)
    (h21 : F.Sz.ncard = 21) : False := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨y, hy45, hyS, hyall⟩ := F.exists_y21 hU1 hU2 h21
  have hTp := F.Tp_eq hU1 hU2 hy45 hyS hyall
  have hy2 : y ≠ 2 := by rcases hy45 with rfl | rfl <;> decide
  obtain ⟨t₂, ht₂⟩ := F.Δ_nonempty 2
  obtain ⟨ty, hty⟩ := F.Δ_nonempty y
  have ht₂T : t₂ ∈ F.Tp := by rw [hTp]; exact Or.inl ht₂
  have htyT : ty ∈ F.Tp := by rw [hTp]; exact Or.inr hty
  have hr₂ := F.rr_values hU1 hII ht₂T
  have hry := F.rr_values hU1 hII htyT
  have hΔ2c : (F.Δ 2).ncard = 2 := by simpa using F.Δ_card 2
  have hΔyc : (F.Δ y).ncard = 12 := by
    rw [F.Δ_card y]
    rcases hy45 with rfl | rfl <;> rfl
  let P : Finset G := Finset.univ.filter (· ∈ F.Δ 1)
  let Tf : Finset G := Finset.univ.filter (· ∈ F.Tp)
  let P2 : Finset G := Finset.univ.filter (· ∈ F.Δ 2)
  let Py : Finset G := Finset.univ.filter (· ∈ F.Δ y)
  have hPm : ∀ x, x ∈ P ↔ x ∈ F.Δ 1 := fun x => by simp [P]
  have hTm : ∀ x, x ∈ Tf ↔ x ∈ F.Tp := fun x => by simp [Tf]
  have hP2m : ∀ x, x ∈ P2 ↔ x ∈ F.Δ 2 := fun x => by simp [P2]
  have hPym : ∀ x, x ∈ Py ↔ x ∈ F.Δ y := fun x => by simp [Py]
  have hPcard : P.card = 6 := by
    rw [card_filter_mem]
    simpa using F.Δ_card 1
  have hP2card : P2.card = 2 := by
    rw [card_filter_mem]
    exact hΔ2c
  have hPycard : Py.card = 12 := by
    rw [card_filter_mem]
    exact hΔyc
  have hTsplit : Tf = P2 ∪ Py := by
    ext x
    rw [hTm, Finset.mem_union, hP2m, hPym, hTp]
    rfl
  have hdisj : Disjoint P2 Py := by
    rw [Finset.disjoint_left]
    intro x hx2 hxy
    exact Set.disjoint_left.1 (F.Δ_disj 2 y (Ne.symm hy2)) ((hP2m x).1 hx2) ((hPym x).1 hxy)
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := P) (t := Tf)
    (fun s t => t ∈ F.Dm s)
  have hL : ∀ s ∈ P, (Tf.bipartiteAbove (fun s t => t ∈ F.Dm s) s).card = 4 := by
    intro s hs
    have hsΔ : s ∈ F.Δ 1 := (hPm s).1 hs
    have hset : ((Tf.bipartiteAbove (fun s t => t ∈ F.Dm s) s : Finset G) : Set G) =
        (F.Dm s : Set G) \ (F.D : Set G) := by
      ext t
      simp only [Finset.bipartiteAbove, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_diff,
        SetLike.mem_coe, hTm]
      constructor
      · rintro ⟨⟨-, htD⟩, ht⟩
        exact ⟨ht, htD⟩
      · rintro ⟨ht, htD⟩
        have ht1 : t ≠ 1 := fun h => htD (h ▸ F.D.one_mem)
        exact ⟨⟨F.Dm_sub_Sz hU1 (F.Δ1_sub_Sz hU1 hsΔ) ht ht1, htD⟩, ht⟩
    rw [← Set.ncard_coe_finset, hset]
    exact F.card_Dm_diff hU1 hII hsΔ
  have hLsum : ∑ s ∈ P, (Tf.bipartiteAbove (fun s t => t ∈ F.Dm s) s).card = 24 := by
    rw [Finset.sum_const_nat hL, hPcard]
  have hR : ∀ t ∈ Tf, (P.bipartiteBelow (fun s t => t ∈ F.Dm s) t).card =
      (F.Δ 1 ∩ (F.Dm t : Set G)).ncard := by
    intro t ht
    have htT : t ∈ F.Tp := (hTm t).1 ht
    have hset : ((P.bipartiteBelow (fun s t => t ∈ F.Dm s) t : Finset G) : Set G) =
        F.Δ 1 ∩ (F.Dm t : Set G) := by
      ext s
      simp only [Finset.bipartiteBelow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
        SetLike.mem_coe, hPm]
      constructor
      · rintro ⟨hs, hts⟩
        exact ⟨hs, F.Dm_symm hU1 (F.Δ1_sub_Sz hU1 hs) htT.1 hts⟩
      · rintro ⟨hs, hst⟩
        exact ⟨hs, F.Dm_symm hU1 htT.1 (F.Δ1_sub_Sz hU1 hs) hst⟩
    rw [← Set.ncard_coe_finset, hset]
  have hconst : ∀ {i : Fin 7} {a : G}, a ∈ F.Δ i → ∀ t ∈ F.Δ i, t ∈ F.Tp → a ∈ F.Tp →
      (F.Δ 1 ∩ (F.Dm t : Set G)).ncard = (F.Δ 1 ∩ (F.Dm a : Set G)).ncard := by
    intro i a ha t ht htT haT
    obtain ⟨n, hn, htn⟩ := F.Δ_trans i a ha t ht
    rw [htn]
    exact F.rr_conj haT hn
  have hRsum : ∑ t ∈ Tf, (P.bipartiteBelow (fun s t => t ∈ F.Dm s) t).card =
      2 * (F.Δ 1 ∩ (F.Dm t₂ : Set G)).ncard + 12 * (F.Δ 1 ∩ (F.Dm ty : Set G)).ncard := by
    rw [Finset.sum_congr rfl hR, hTsplit, Finset.sum_union hdisj]
    have e2 : ∑ t ∈ P2, (F.Δ 1 ∩ (F.Dm t : Set G)).ncard =
        2 * (F.Δ 1 ∩ (F.Dm t₂ : Set G)).ncard := by
      rw [← hP2card]
      apply Finset.sum_const_nat
      intro t ht
      have htΔ := (hP2m t).1 ht
      exact hconst ht₂ t htΔ (by rw [hTp]; exact Or.inl htΔ) ht₂T
    have ey : ∑ t ∈ Py, (F.Δ 1 ∩ (F.Dm t : Set G)).ncard =
        12 * (F.Δ 1 ∩ (F.Dm ty : Set G)).ncard := by
      rw [← hPycard]
      apply Finset.sum_const_nat
      intro t ht
      have htΔ := (hPym t).1 ht
      exact hconst hty t htΔ (by rw [hTp]; exact Or.inr htΔ) htyT
    rw [e2, ey]
  have := hdc.symm.trans hLsum
  rw [hRsum] at this
  omega

end CFSG.Quasithin.A94
