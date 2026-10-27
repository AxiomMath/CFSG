module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.Group.TypeTags.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private def s16e_d5_lineVec : Fin 4 → Fin 2 → ZMod 3 :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, 2]]

private lemma s16e_d5_lineVec_ne_zero : ∀ i : Fin 4, s16e_d5_lineVec i ≠ 0 := by
  decide

private lemma s16e_d5_three_nsmul_eq_zero :
    ∀ w : Fin 2 → ZMod 3, 3 • w = 0 := by
  decide

private lemma s16e_d5_orderOf_ofAdd (w : Fin 2 → ZMod 3) (hw : w ≠ 0) :
    orderOf (Multiplicative.ofAdd w) = 3 := by
  apply orderOf_eq_prime
  · rw [(ofAdd_nsmul 3 w).symm, s16e_d5_three_nsmul_eq_zero w]
    simp
  · intro h
    exact hw (ofAdd_eq_one.mp h)

private lemma s16e_d5_line_cover :
    ∀ w : Fin 2 → ZMod 3, w ≠ 0 →
      ∃ i : Fin 4, ∃ m : ZMod 3, m • s16e_d5_lineVec i = w := by
  decide

private lemma s16e_d5_line_distinct :
    ∀ i j : Fin 4, i ≠ j → ∀ n : Fin 3,
      n.val • s16e_d5_lineVec i ≠ s16e_d5_lineVec j := by
  decide

private lemma s16e_d5_ofAdd_smul :
    ∀ (i : Fin 4) (m : ZMod 3), Multiplicative.ofAdd (m • s16e_d5_lineVec i) =
      (Multiplicative.ofAdd (s16e_d5_lineVec i)) ^ m.val := by
  decide

theorem s16e_d5_four_lines {G : Type*} [Group G] {L : Subgroup G}
    (hL : Nonempty (↥L ≃* Multiplicative (Fin 2 → ZMod 3))) :
    ∃ K : Fin 4 → Subgroup G, (∀ i, K i ≤ L) ∧ (∀ i, Nat.card ↥(K i) = 3) ∧
      Function.Injective K ∧ ∀ H : Subgroup G, H ≤ L → Nat.card ↥H = 3 → ∃ i, H = K i := by
  classical
  obtain ⟨φ⟩ := hL
  let K : Fin 4 → Subgroup G := fun i =>
    ((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
      φ.symm.toMonoidHom).map L.subtype
  haveI hLfin : Finite ↥L :=
    Finite.of_equiv (Multiplicative (Fin 2 → ZMod 3)) φ.symm.toEquiv
  have hKle : ∀ i, K i ≤ L := by
    intro i
    change (((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
      φ.symm.toMonoidHom).map L.subtype) ≤ L
    exact Subgroup.map_subtype_le _
  have hKcard : ∀ i, Nat.card ↥(K i) = 3 := by
    intro i
    change Nat.card ↥(((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
      φ.symm.toMonoidHom).map L.subtype) = 3
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L),
      Subgroup.card_map_of_injective φ.symm.injective,
      Nat.card_zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i)),
      s16e_d5_orderOf_ofAdd (s16e_d5_lineVec i) (s16e_d5_lineVec_ne_zero i)]
  have hinj : Function.Injective K := by
    intro i j hij
    by_contra hne
    have hP : Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i)) =
        Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec j)) := by
      change (((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
          φ.symm.toMonoidHom).map L.subtype) =
        (((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec j))).map
          φ.symm.toMonoidHom).map L.subtype) at hij
      exact Subgroup.map_injective φ.symm.injective
        (Subgroup.map_injective (Subgroup.subtype_injective L) hij)
    have hmem : Multiplicative.ofAdd (s16e_d5_lineVec i) ∈
        Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec j)) :=
      hP ▸ Subgroup.mem_zpowers _
    rw [mem_zpowers_iff_mem_range_orderOf] at hmem
    obtain ⟨n, hn, hk⟩ := Finset.mem_image.mp hmem
    have hk' : n • s16e_d5_lineVec j = s16e_d5_lineVec i := by
      apply Multiplicative.ofAdd.injective
      rw [ofAdd_nsmul]
      exact hk
    have hn3 : n < 3 := by
      have hn' := Finset.mem_range.mp hn
      rwa [s16e_d5_orderOf_ofAdd (s16e_d5_lineVec j) (s16e_d5_lineVec_ne_zero j)] at hn'
    exact (s16e_d5_line_distinct j i (Ne.symm hne) ⟨n, hn3⟩) hk'
  have hcov : ∀ H : Subgroup G, H ≤ L → Nat.card ↥H = 3 → ∃ i, H = K i := by
    intro H hH hHcard
    have hHne : H ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hHcard
      exact absurd hHcard (by decide)
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
    have hxG : (x : G) ∈ H := x.2
    have hx : (x : G) ≠ 1 := by
      intro h
      exact hx1 (Subtype.ext h)
    have hLx : (x : G) ∈ L := hH hxG
    have hphi : φ ⟨(x : G), hLx⟩ ≠ 1 := by
      intro h
      exact hx (congrArg Subtype.val (φ.injective (h.trans φ.map_one.symm)))
    let w : Fin 2 → ZMod 3 := (φ ⟨(x : G), hLx⟩).toAdd
    have hw : w ≠ 0 := fun h0 => hphi (toAdd_eq_zero.mp h0)
    obtain ⟨i, m, hm⟩ := s16e_d5_line_cover w hw
    have hpow : Multiplicative.ofAdd w ∈
        Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i)) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨(m.val : ℤ), ?_⟩
      rw [zpow_natCast, ← s16e_d5_ofAdd_smul i m, hm]
    have hmemL : (⟨(x : G), hLx⟩ : ↥L) ∈
        (Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
          φ.symm.toMonoidHom := by
      rw [Subgroup.mem_map]
      refine ⟨Multiplicative.ofAdd w, hpow, ?_⟩
      have hwphi : Multiplicative.ofAdd w = φ ⟨(x : G), hLx⟩ := by
        simp [w]
      rw [hwphi]
      exact MulEquiv.symm_apply_apply φ _
    have hxKi : (x : G) ∈ K i := by
      change (x : G) ∈ (((Subgroup.zpowers (Multiplicative.ofAdd (s16e_d5_lineVec i))).map
        φ.symm.toMonoidHom).map L.subtype)
      rw [Subgroup.mem_map]
      exact ⟨⟨(x : G), hLx⟩, hmemL, rfl⟩
    have horder : orderOf (x : G) = 3 := by
      have hdvd : orderOf (x : G) ∣ 3 := by
        simpa [hHcard] using Subgroup.orderOf_dvd_natCard H hxG
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hx
      · exact h3
    have hcard_zp : Nat.card ↥(Subgroup.zpowers (x : G)) = 3 := by
      rw [Nat.card_zpowers (x : G), horder]
    haveI hHfin : Finite ↥H :=
      Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
    have h1 : Subgroup.zpowers (x : G) = H :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxG)
        (by rw [hHcard, hcard_zp])
    haveI hKifin : Finite ↥(K i) :=
      Nat.finite_of_card_ne_zero (by rw [hKcard i]; decide)
    have h2 : Subgroup.zpowers (x : G) = K i :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxKi)
        (by rw [hKcard i, hcard_zp])
    exact ⟨i, h1.symm.trans h2⟩
  exact ⟨K, hKle, hKcard, hinj, hcov⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
