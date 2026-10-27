module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMFrameC_negFix_card_le {m : ℕ} {π : Equiv.Perm (Fin m)} (hπ : π * π = 1) :
    Nat.card {f : ↥(sumZero m 3) // permAutV π f = f⁻¹} ≤ 3 ^ (m / 2) := by
  have hπinv : π⁻¹ = π := inv_eq_of_mul_eq_one_right hπ
  have hππ : ∀ k : Fin m, π (π k) = k := fun k => by
    have h := congrArg (fun σ : Equiv.Perm (Fin m) => σ k) hπ
    simpa [Equiv.Perm.mul_apply] using h
  have hzero : ∀ a : ZMod 3, a = -a → a = 0 := by decide
  have hneg : ∀ (f : ↥(sumZero m 3)), permAutV π f = f⁻¹ →
      ∀ k : Fin m, crd f (π k) = -crd f k := by
    intro f hf k
    have h1 := congrArg (fun g => crd g k) hf
    rw [crd_permAutV, crd_inv, hπinv] at h1
    exact h1
  have hfix : ∀ (f : ↥(sumZero m 3)), permAutV π f = f⁻¹ →
      ∀ k : Fin m, π k = k → crd f k = 0 := by
    intro f hf k hk
    have h1 := hneg f hf k
    rw [hk] at h1
    exact hzero _ h1
  let S : Finset (Fin m) := Finset.univ.filter (fun i => i < π i)
  have hS_image : S.image π ⊆ Finset.univ \ S := by
    intro x hx
    obtain ⟨i, hiS, hix⟩ := Finset.mem_image.mp hx
    rw [← hix]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    have h1 : i < π i := (Finset.mem_filter.mp hiS).2
    have h2 : π i < π (π i) := (Finset.mem_filter.mp hmem).2
    rw [hππ] at h2
    omega
  have hS_card : S.card ≤ (Finset.univ \ S).card := by
    rw [← Finset.card_image_of_injective S π.injective]
    exact Finset.card_le_card hS_image
  have hS_compl : (Finset.univ \ S).card = m - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin]
  have hS_le : 2 * S.card ≤ m := by
    have h := hS_card
    rw [hS_compl] at h
    omega
  have hS_half : S.card ≤ m / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hcardK : Nat.card {f : ↥(sumZero m 3) // permAutV π f = f⁻¹} ≤ 3 ^ S.card := by
    have hinj : Function.Injective
        (fun f : {f : ↥(sumZero m 3) // permAutV π f = f⁻¹} =>
          fun i : ↥S => crd f.1 i.1) := by
      intro f g hfg
      apply Subtype.ext
      apply ext_crd
      intro k
      by_cases hk : π k = k
      · rw [hfix f.1 f.2 k hk, hfix g.1 g.2 k hk]
      · rcases lt_or_gt_of_ne hk with hpk | hkp
        · have hkS : π k ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hππ]; exact hpk⟩
          have h1 : crd f.1 (π k) = crd g.1 (π k) := congrFun hfg ⟨π k, hkS⟩
          have hf' : crd f.1 k = -crd f.1 (π k) := by
            rw [hneg f.1 f.2 k]
            exact (neg_neg _).symm
          have hg' : crd g.1 k = -crd g.1 (π k) := by
            rw [hneg g.1 g.2 k]
            exact (neg_neg _).symm
          rw [hf', hg', h1]
        · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkp⟩
          exact congrFun hfg ⟨k, hkS⟩
    calc Nat.card {f : ↥(sumZero m 3) // permAutV π f = f⁻¹}
        ≤ Nat.card (↥S → ZMod 3) := Nat.card_le_card_of_injective _ hinj
      _ = 3 ^ S.card := by
          rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact hcardK.trans (Nat.pow_le_pow_right (by norm_num : 0 < 3) hS_half)

theorem qTwoLMFrameC_negFix_card_le_VT {m : ℕ} {VT : Type} [Group VT]
    {ρ : Equiv.Perm (Fin m) →* MulAut VT} (hVT : IsAugModel m VT ρ) {π : Equiv.Perm (Fin m)}
    (hπ : π * π = 1) : Nat.card {v : VT // ρ π v = v⁻¹} ≤ 3 ^ (m / 2) := by
  obtain ⟨e, he⟩ := hVT.ex
  have hiff : ∀ f : ↥(sumZero m 3),
      (permAutV π f = f⁻¹) ↔ (ρ π (e f) = (e f)⁻¹) := by
    intro f
    constructor
    · intro h
      rw [← he π f, h, map_inv]
    · intro h
      rw [← he π f, ← map_inv] at h
      exact e.injective h
  have hcard : Nat.card {f : ↥(sumZero m 3) // permAutV π f = f⁻¹} =
      Nat.card {v : VT // ρ π v = v⁻¹} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hiff)
  rw [← hcard]
  exact qTwoLMFrameC_negFix_card_le hπ

end CFSG.StandardType.QTwo

end
