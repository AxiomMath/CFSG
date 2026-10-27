module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23SettingProof
public import Certificates.Certificate7055

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction
open scoped Pointwise

theorem card_filter_pres56 :
    (Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ Pres56 σ).card = 120 :=
  Certificates.certificate7055.1

theorem card_filter_pres0123 :
    (Finset.univ.filter fun σ : Perm (Fin 7) =>
      Perm.sign σ = 1 ∧ ∀ i : Fin 7, ((σ i).val < 4 ↔ i.val < 4)).card = 72 :=
  Certificates.certificate7055.2.1

theorem card_filter_fix4 :
    (Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ 4 = 4).card = 360 :=
  Certificates.certificate7055.2.2.1

theorem card_filter_fix4_pow5 :
    (Finset.univ.filter fun σ : Perm (Fin 7) =>
      Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ ^ 5 = 1).card = 145 :=
  Certificates.certificate7055.2.2.2.1

theorem card_filter_pow35 :
    (Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 35 = 1).card = 1225 :=
  Certificates.certificate7055.2.2.2.2.1

theorem card_filter_pow7 :
    (Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 7 = 1).card = 721 :=
  Certificates.certificate7055.2.2.2.2.2.1

theorem card_filter_commute_involution :
    ∀ x : Perm (Fin 7), Perm.sign x = 1 → x ≠ 1 →
    x * x = 1 →
      (Finset.univ.filter fun y : Perm (Fin 7) => Perm.sign y = 1 ∧ x * y = y * x).card = 24 :=
  Certificates.certificate7055.2.2.2.2.2.2

theorem card_eq_card_filter {S : Subgroup (Perm (Fin 7))} {p : Perm (Fin 7) → Prop}
    [DecidablePred p] (h : ∀ σ, σ ∈ S ↔ p σ) : Nat.card S = (Finset.univ.filter p).card := by
  classical
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => by simp [h σ])

theorem card_le_card_filter {S : Subgroup (Perm (Fin 7))} {p : Perm (Fin 7) → Prop}
    [DecidablePred p] (h : ∀ σ ∈ S, p σ) : Nat.card S ≤ (Finset.univ.filter p).card := by
  classical
  rw [card_eq_card_filter (p := fun σ => σ ∈ S) fun σ => Iff.rfl]
  exact Finset.card_le_card fun σ hσ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact h σ hσ

theorem card_filter_le_card {S : Subgroup (Perm (Fin 7))} {p : Perm (Fin 7) → Prop}
    [DecidablePred p] (h : ∀ σ, p σ → σ ∈ S) : (Finset.univ.filter p).card ≤ Nat.card S := by
  classical
  rw [card_eq_card_filter (p := fun σ => σ ∈ S) fun σ => Iff.rfl]
  exact Finset.card_le_card fun σ hσ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact h σ hσ

theorem mem_of_relIndex_eq {G : Type*} [Group G] [Finite G] {Z W : Subgroup G} {r : ℕ}
    (hr : Z.relIndex W = r) {g : G} (hg : g ∈ W) {m : ℕ} (hm : g ^ m = 1)
    (hcop : Nat.Coprime m r.factorial) : g ∈ Z := by
  set Z' := Z.subgroupOf W
  have hidx : Z'.index = r := hr
  have hN : Z'.normalCore.index ∣ r.factorial := by
    have := Z'.index_normalCore_dvd_factorial_index
    rwa [hidx] at this
  set g' : W := ⟨g, hg⟩
  have h1 : g' ^ Z'.normalCore.index ∈ Z'.normalCore := Z'.normalCore.pow_index_mem g'
  have hm' : g' ^ m = 1 := Subtype.ext (by simp [g', hm])
  have hcop' : Nat.Coprime Z'.normalCore.index (orderOf g') :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hm')
      (Nat.Coprime.coprime_dvd_left hN hcop.symm)
  have h2 : g' ∈ Z'.normalCore :=
    (Subgroup.zpowers_le.mpr h1) (CFSG.Quasithin.A4.mem_zpowers_pow_of_coprime hcop')
  exact Subgroup.mem_subgroupOf.mp (Z'.normalCore_le h2)

theorem seven_dvd_card_of_transitive {Z : Subgroup (Perm (Fin 7))}
    (h : ∀ j : Fin 7, ∃ σ ∈ Z, σ 5 = j) : 7 ∣ Nat.card Z := by
  have horb : MulAction.orbit Z (5 : Fin 7) = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, rfl⟩ := h j
    exact ⟨⟨σ, hσ⟩, rfl⟩
  have hc := MulAction.index_stabilizer Z (5 : Fin 7)
  rw [horb, Set.ncard_univ, Nat.card_fin] at hc
  have h := (MulAction.stabilizer Z (5 : Fin 7)).index_dvd_card
  rwa [hc] at h

theorem orbitRel_symm {Z : Subgroup (Perm (Fin 7))} {i j : Fin 7} (h : ∃ σ ∈ Z, σ i = j) :
    ∃ σ ∈ Z, σ j = i := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact ⟨σ⁻¹, Z.inv_mem hσ, by simp⟩

theorem orbitRel_trans {Z : Subgroup (Perm (Fin 7))} {i j k : Fin 7} (h₁ : ∃ σ ∈ Z, σ i = j)
    (h₂ : ∃ σ ∈ Z, σ j = k) : ∃ σ ∈ Z, σ i = k := by
  obtain ⟨σ, hσ, rfl⟩ := h₁
  obtain ⟨τ, hτ, rfl⟩ := h₂
  exact ⟨τ * σ, Z.mul_mem hτ hσ, rfl⟩

theorem fin7_cases (i : Fin 7) : i.val < 4 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.ext_iff]
  omega

theorem forall_pres56_of_card {Y : Subgroup (Perm (Fin 7))}
    (hYA : Y ≤ alternatingGroup (Fin 7))
    (hcard : Nat.card Y = 120)
    (horb : ∀ i j : Fin 7, omegaTOrbit i = omegaTOrbit j → ∃ σ ∈ Y, σ i = j) :
    ∀ σ ∈ Y, Pres56 σ := by
  have hR0 : ∀ a b : Fin 7, a.val < 4 → b.val < 4 → ∃ σ ∈ Y, σ a = b := fun a b ha hb =>
    horb a b (by simp [omegaTOrbit, ha, hb])
  have hR56 : ∃ σ ∈ Y, σ 5 = 6 := horb 5 6 (by decide)
  have hrefl : ∀ i : Fin 7, ∃ σ ∈ Y, σ i = i := fun i => ⟨1, Y.one_mem, rfl⟩
  by_cases h4 : ∃ σ ∈ Y, σ 5 = 4 <;> by_cases h0 : ∃ σ ∈ Y, σ 5 = 0
  ·
    exfalso
    have h7 := seven_dvd_card_of_transitive (Z := Y) fun j => by
      rcases fin7_cases j with hj | rfl | rfl | rfl
      · exact orbitRel_trans h0 (hR0 0 j (by decide) hj)
      · exact h4
      · exact hrefl 5
      · exact hR56
    rw [hcard] at h7
    norm_num at h7
  ·
    exfalso
    have hR5 : ∀ j : Fin 7, 4 ≤ j.val → ∃ σ ∈ Y, σ 5 = j := by
      intro j hj
      rcases fin7_cases j with hj' | rfl | rfl | rfl
      · omega
      · exact h4
      · exact hrefl 5
      · exact hR56
    have hpres : ∀ σ ∈ Y, ∀ i : Fin 7, ((σ i).val < 4 ↔ i.val < 4) := by
      intro σ hσ i
      constructor
      · intro hσi
        by_contra hi
        exact h0 (orbitRel_trans (orbitRel_trans (hR5 i (by omega)) ⟨σ, hσ, rfl⟩)
          (hR0 (σ i) 0 hσi (by decide)))
      · intro hi
        by_contra hσi
        exact h0 (orbitRel_trans (orbitRel_trans (hR5 (σ i) (by omega))
          (orbitRel_symm ⟨σ, hσ, rfl⟩)) (hR0 i 0 hi (by decide)))
    have hle := card_le_card_filter (S := Y)
      (p := fun σ => Perm.sign σ = 1 ∧ ∀ i : Fin 7, ((σ i).val < 4 ↔ i.val < 4))
      fun σ hσ => ⟨hYA hσ, hpres σ hσ⟩
    rw [hcard, card_filter_pres0123] at hle
    norm_num at hle
  ·
    exfalso
    have hfix : ∀ σ ∈ Y, σ 4 = 4 := by
      intro σ hσ
      by_contra hne
      have h45 : ∃ τ ∈ Y, τ 4 = 5 := by
        rcases fin7_cases (σ 4) with hj | hj | hj | hj
        · exact orbitRel_trans (orbitRel_trans ⟨σ, hσ, rfl⟩ (hR0 (σ 4) 0 hj (by decide)))
            (orbitRel_symm h0)
        · exact absurd hj hne
        · exact ⟨σ, hσ, hj⟩
        · exact orbitRel_trans ⟨σ, hσ, hj⟩ (orbitRel_symm hR56)
      exact h4 (orbitRel_symm h45)
    set W : Subgroup (Perm (Fin 7)) :=
      alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (4 : Fin 7) with hW
    have hmemW : ∀ σ, σ ∈ W ↔ Perm.sign σ = 1 ∧ σ 4 = 4 := fun σ => by
      rw [hW, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def,
        Perm.mem_alternatingGroup]
    have hYW : Y ≤ W := fun σ hσ => (hmemW σ).mpr ⟨hYA hσ, hfix σ hσ⟩
    have hWc : Nat.card W = 360 := by
      rw [card_eq_card_filter hmemW, card_filter_fix4]
    have h3 : Y.relIndex W = 3 := by
      have h := Subgroup.relIndex_mul_card (H := Y) (K := W)
      rw [inf_of_le_left hYW, hcard, hWc] at h
      omega
    have hge := card_filter_le_card (S := Y)
      (p := fun σ => Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ ^ 5 = 1) fun σ hσ =>
        mem_of_relIndex_eq h3 ((hmemW σ).mpr ⟨hσ.1, hσ.2.1⟩) hσ.2.2 (by decide)
    rw [hcard, card_filter_fix4_pow5] at hge
    norm_num at hge
  ·
    intro σ hσ
    have h5 : σ 5 = 5 ∨ σ 5 = 6 := by
      rcases fin7_cases (σ 5) with hj | hj | hj | hj
      · exact absurd (orbitRel_trans ⟨σ, hσ, rfl⟩ (hR0 (σ 5) 0 hj (by decide))) h0
      · exact absurd ⟨σ, hσ, hj⟩ h4
      · exact Or.inl hj
      · exact Or.inr hj
    have h6 : σ 6 = 5 ∨ σ 6 = 6 := by
      have hR6 : ∃ τ ∈ Y, τ 5 = σ 6 := orbitRel_trans hR56 ⟨σ, hσ, rfl⟩
      rcases fin7_cases (σ 6) with hj | hj | hj | hj
      · exact absurd (orbitRel_trans hR6 (hR0 (σ 6) 0 hj (by decide))) h0
      · exact absurd (hj ▸ hR6) h4
      · exact Or.inl hj
      · exact Or.inr hj
    have hne : σ 5 ≠ σ 6 := fun h => absurd (σ.injective h) (by decide)
    rcases h5 with h5 | h5 <;> rcases h6 with h6 | h6
    · exact absurd (h5.trans h6.symm) hne
    · exact Or.inl ⟨h5, h6⟩
    · exact Or.inr ⟨h5, h6⟩
    · exact absurd (h5.trans h6.symm) hne

theorem mem_iff_of_card {Y : Subgroup (Perm (Fin 7))}
    (hYA : Y ≤ alternatingGroup (Fin 7))
    (hcard : Nat.card Y = 120)
    (horb : ∀ i j : Fin 7, omegaTOrbit i = omegaTOrbit j → ∃ σ ∈ Y, σ i = j) (σ : Perm (Fin 7)) :
    σ ∈ Y ↔ Perm.sign σ = 1 ∧ Pres56 σ := by
  classical
  have hpres := forall_pres56_of_card hYA hcard horb
  refine ⟨fun hσ => ⟨hYA hσ, hpres σ hσ⟩, fun hσ => ?_⟩
  have hsub : (Finset.univ.filter fun τ => τ ∈ Y) ⊆
      Finset.univ.filter fun τ : Perm (Fin 7) => Perm.sign τ = 1 ∧ Pres56 τ := fun τ hτ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    exact ⟨hYA hτ, hpres τ hτ⟩
  have hc : (Finset.univ.filter fun τ => τ ∈ Y).card = 120 := by
    rw [← card_eq_card_filter (S := Y) fun τ => Iff.rfl, hcard]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc, card_filter_pres56])
  have : σ ∈ Finset.univ.filter fun τ => τ ∈ Y := by
    rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hσ
  simpa using this

theorem exists_pres56_apply (a b : Fin 7) (ha : a.val < 5) (hb : b.val < 5) :
    ∃ σ : Perm (Fin 7), (Perm.sign σ = 1 ∧ Pres56 σ) ∧ σ a = b := by
  by_cases hab : a = b
  · exact ⟨1, ⟨by simp, Or.inl ⟨rfl, rfl⟩⟩, hab⟩
  have ha5 : a ≠ 5 := fun h => by rw [h] at ha; exact absurd ha (by decide)
  have ha6 : a ≠ 6 := fun h => by rw [h] at ha; exact absurd ha (by decide)
  have hb5 : b ≠ 5 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  have hb6 : b ≠ 6 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  refine ⟨swap a b * swap 5 6, ⟨?_, Or.inr ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap (by decide)]
    decide
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm ha6) (Ne.symm hb6)]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm ha5) (Ne.symm hb5)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha5 ha6, swap_apply_left]

theorem pres56_or_eq_alt {Z : Subgroup (Perm (Fin 7))}
    (hZA : Z ≤ alternatingGroup (Fin 7))
    (hZ : ∀ σ : Perm (Fin 7), Perm.sign σ = 1 → Pres56 σ → σ ∈ Z) :
    (∀ σ ∈ Z, Pres56 σ) ∨ ∀ σ ∈ alternatingGroup (Fin 7), σ ∈ Z := by
  by_cases hp : ∀ σ ∈ Z, Pres56 σ
  · exact Or.inl hp
  right
  push Not at hp
  obtain ⟨σ, hσZ, hσ⟩ := hp
  have hR : ∀ a b : Fin 7, a.val < 5 → b.val < 5 → ∃ τ ∈ Z, τ a = b := fun a b ha hb => by
    obtain ⟨τ, hτ, hτab⟩ := exists_pres56_apply a b ha hb
    exact ⟨τ, hZ τ hτ.1 hτ.2, hτab⟩
  have hR56 : ∃ τ ∈ Z, τ 5 = 6 := by
    refine ⟨swap 5 6 * swap 0 1, hZ _ ?_ (Or.inr ⟨by decide, by decide⟩), by decide⟩
    rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    decide
  have hj : ∃ j : Fin 7, j.val < 5 ∧ ∃ τ ∈ Z, τ 5 = j := by
    by_cases h5 : (σ 5).val < 5
    · exact ⟨σ 5, h5, σ, hσZ, rfl⟩
    by_cases h6 : (σ 6).val < 5
    · exact ⟨σ 6, h6, orbitRel_trans hR56 ⟨σ, hσZ, rfl⟩⟩
    exfalso
    have hne : σ 5 ≠ σ 6 := fun h => absurd (σ.injective h) (by decide)
    rcases fin7_cases (σ 5) with h | h | h | h <;> rcases fin7_cases (σ 6) with h' | h' | h' | h'
    all_goals omega
  obtain ⟨j, hj5, hjZ⟩ := hj
  have htrans : ∀ k : Fin 7, ∃ τ ∈ Z, τ 5 = k := by
    intro k
    rcases fin7_cases k with hk | rfl | rfl | rfl
    · exact orbitRel_trans hjZ (hR j k hj5 (by omega))
    · exact orbitRel_trans hjZ (hR j 4 hj5 (by decide))
    · exact ⟨1, Z.one_mem, rfl⟩
    · exact hR56
  have h7 := seven_dvd_card_of_transitive htrans
  set S : Subgroup (Perm (Fin 7)) :=
    alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) ({5, 6} : Set (Fin 7))
    with hS
  have hmemS : ∀ τ, τ ∈ S ↔ Perm.sign τ = 1 ∧ Pres56 τ := fun τ => by
    rw [hS, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, smul_pair_set_eq_iff,
      Perm.mem_alternatingGroup]
  have h120 : 120 ∣ Nat.card Z := by
    have := Subgroup.card_dvd_of_le (fun τ hτ => hZ τ ((hmemS τ).mp hτ).1 ((hmemS τ).mp hτ).2 :
      S ≤ Z)
    rwa [card_eq_card_filter hmemS, card_filter_pres56] at this
  have h2520 : Nat.card Z ∣ 2520 := by
    have := Subgroup.card_dvd_of_le hZA
    rwa [card_alternatingGroup_seven] at this
  have h840 : 840 ∣ Nat.card Z :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 120) h7 h120
  obtain ⟨k, hk⟩ := h840
  have hk3 : k = 1 ∨ k = 3 := by
    obtain ⟨l, hl⟩ := h2520
    have hkl : k * l = 3 := by
      have : 840 * (k * l) = 840 * 3 := by rw [← mul_assoc, ← hk, ← hl]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    have hk3' : k ∣ 3 := Dvd.intro l hkl
    have hkle : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3'
    interval_cases k <;> simp_all
  rcases hk3 with rfl | rfl
  ·
    exfalso
    have h3 : Z.relIndex (alternatingGroup (Fin 7)) = 3 := by
      have h := Subgroup.relIndex_mul_card (H := Z) (K := alternatingGroup (Fin 7))
      rw [inf_of_le_left hZA, hk, card_alternatingGroup_seven] at h
      omega
    have hge := card_filter_le_card (S := Z)
      (p := fun τ => Perm.sign τ = 1 ∧ τ ^ 35 = 1) fun τ hτ =>
        mem_of_relIndex_eq h3 (Perm.mem_alternatingGroup.mpr hτ.1) hτ.2 (by decide)
    rw [hk, card_filter_pow35] at hge
    norm_num at hge
  ·
    have hZeq : Z = alternatingGroup (Fin 7) :=
      Subgroup.eq_of_le_of_card_ge hZA (by rw [hk, card_alternatingGroup_seven])
    intro τ hτ
    rw [hZeq]
    exact hτ

theorem card_ne_504 {Z : Subgroup (Perm (Fin 7))}
    (hZA : Z ≤ alternatingGroup (Fin 7)) :
    Nat.card Z ≠ 504 := by
  intro hZ
  have h5 : Z.relIndex (alternatingGroup (Fin 7)) = 5 := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := alternatingGroup (Fin 7))
    rw [inf_of_le_left hZA, hZ, card_alternatingGroup_seven] at h
    omega
  have hge := card_filter_le_card (S := Z)
    (p := fun τ => Perm.sign τ = 1 ∧ τ ^ 7 = 1) fun τ hτ =>
      mem_of_relIndex_eq h5 (Perm.mem_alternatingGroup.mpr hτ.1) hτ.2 (by decide)
  rw [hZ, card_filter_pow7] at hge
  norm_num at hge

theorem card_le_of_le_centralizer {X : Subgroup (Perm (Fin 7))}
    (hXA : X ≤ alternatingGroup (Fin 7)) {x : Perm (Fin 7)} (hxA : x ∈ alternatingGroup (Fin 7))
    (hx1 : x ≠ 1) (hxx : x * x = 1) (hX : ∀ y ∈ X, x * y = y * x) : Nat.card X ≤ 24 := by
  have hle := card_le_card_filter (S := X)
    (p := fun y => Perm.sign y = 1 ∧ x * y = y * x) fun y hy => ⟨hXA hy, hX y hy⟩
  rwa [card_filter_commute_involution x hxA hx1 hxx] at hle

end CFSG.Quasithin.H13
