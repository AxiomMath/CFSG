module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxRank

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2d_sigma_pm {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n)
    (c : Fin n → ZMod p) (c₀ : ZMod p) (a : Fin n) :
    levTwoS2d_sigma n hn c c₀ a = 1 ∨ levTwoS2d_sigma n hn c c₀ a = -1 := by
  unfold levTwoS2d_sigma
  split_ifs <;> simp

theorem levTwoS2d_sigma_root_zero {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)} {c₀ : ZMod p} (hc₀ : c₀ ≠ 0) {β : Fin n → ℤ}
    (hβ : β ∈ Φ) (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {u v : Fin n} {su tv : ℤ}
    (_huv : u ≠ v) (hsu : su = 1 ∨ su = -1) (htv : tv = 1 ∨ tv = -1)
    (hβuv : toStdD n β = Pi.single u su + Pi.single v tv)
    (hQu : levTwoS2d_d n hn c u = c₀ ∨ levTwoS2d_d n hn c u = -c₀)
    (hQv : levTwoS2d_d n hn c v = c₀ ∨ levTwoS2d_d n hn c v = -c₀) :
    (su : ℚ) * (levTwoS2d_sigma n hn c c₀ u : ℚ) +
      (tv : ℚ) * (levTwoS2d_sigma n hn c c₀ v : ℚ) = 0 := by
  set m : ℤ := su * levTwoS2d_sigma n hn c c₀ u + tv * levTwoS2d_sigma n hn c c₀ v with hm
  have hm_zmod : (m : ZMod p) = 0 := by
    have hcu : ((levTwoS2d_sigma n hn c c₀ u : ℤ) : ZMod p) * c₀ = levTwoS2d_d n hn c u :=
      levTwoS2d_sigma_spec n hn c hQu
    have hcv : ((levTwoS2d_sigma n hn c c₀ v : ℤ) : ZMod p) * c₀ = levTwoS2d_d n hn c v :=
      levTwoS2d_sigma_spec n hn c hQv
    have hlam := hΦ.fix β hβ
    rw [levTwoS2d_lam_eps n hn hp2 c hβuv] at hlam
    have hmul : (m : ZMod p) * c₀ = 0 := by
      rw [hm]
      push_cast
      rw [add_mul, mul_assoc ((su : ℤ) : ZMod p) ((levTwoS2d_sigma n hn c c₀ u : ℤ) : ZMod p) c₀,
        mul_assoc ((tv : ℤ) : ZMod p) ((levTwoS2d_sigma n hn c c₀ v : ℤ) : ZMod p) c₀,
        hcu, hcv]
      exact hlam
    exact (mul_eq_zero.mp hmul).resolve_right hc₀
  have hm_abs : m = -2 ∨ m = 0 ∨ m = 2 := by
    rcases levTwoS2d_sigma_pm n hn c c₀ u with hu | hu <;>
      rcases levTwoS2d_sigma_pm n hn c c₀ v with hv | hv <;>
      rcases hsu with rfl | rfl <;> rcases htv with rfl | rfl <;>
      rw [hm, hu, hv] <;> norm_num
  have hm_zero : m = 0 := levTwoS2d_intCast_eq_zero_of_abs_two hp2 hm_abs hm_zmod
  have : (m : ℚ) = 0 := by rw [hm_zero]; norm_num
  rw [hm] at this
  push_cast at this
  linarith


theorem levTwoS2d_card_le_Supp {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {s : Finset (Fin n → ℤ)}
    (hsΦ : (s : Set (Fin n → ℤ)) ⊆ Φ)
    (hlin : LinearIndependent ℚ (fun v : s => toRat (v : Fin n → ℤ)))
    (hSupp : levTwoS2d_Supp n hn c Φ ⊆ (levTwoS2d_Z n hn c)ᶜ) :
    s.card ≤ Nat.card (levTwoS2d_Supp n hn c Φ) - 1 := by
  classical
  rcases Nat.eq_zero_or_pos s.card with hs0 | hspos
  · rw [hs0]; exact Nat.zero_le _
  · rcases levTwoS2d_Phi_side_abs n hn hp2 c hΦ with hZ | ⟨c₀, hc₀, hQ⟩
    · exfalso
      obtain ⟨β, hβs⟩ := Finset.card_pos.mp hspos
      have hβΦ : β ∈ Φ := hsΦ (Finset.mem_coe.mpr hβs)
      obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
        (levTwoS2d_isRt_iff n (by omega) β).1 (hΦ.isRt β hβΦ)
      have hi : toStdD n β i ≠ 0 := by
        rw [hcoord]; simp only [Pi.add_apply, Pi.single_apply]
        rcases hsi with rfl | rfl <;> simp [hij]
      exact hSupp ⟨β, hβΦ, hi⟩ (hZ β hβΦ i hi)
    · set Supp := levTwoS2d_Supp n hn c Φ with hSuppdef
      set S : Finset (Fin n) := Finset.univ.filter (fun a => a ∈ Supp) with hSdef
      have hSmem : ∀ a, a ∈ S ↔ a ∈ Supp := by intro a; simp [hSdef]
      have hSupp_ne : Supp.Nonempty := by
        obtain ⟨β, hβs⟩ := Finset.card_pos.mp hspos
        have hβΦ : β ∈ Φ := hsΦ (Finset.mem_coe.mpr hβs)
        obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
          (levTwoS2d_isRt_iff n (by omega) β).1 (hΦ.isRt β hβΦ)
        refine ⟨i, β, hβΦ, ?_⟩
        rw [hcoord]; simp only [Pi.add_apply, Pi.single_apply]
        rcases hsi with rfl | rfl <;> simp [hij]
      obtain ⟨a₀, ha₀⟩ := hSupp_ne
      let σ : Fin n → ℚ := fun a => (levTwoS2d_sigma n hn c c₀ a : ℚ)
      have hσ_pm : ∀ a, σ a = 1 ∨ σ a = -1 := by
        intro a
        have h := levTwoS2d_sigma_pm n hn c c₀ a
        rcases h with h | h <;> [left; right] <;> simp [σ, h]
      have hσ_ne : σ a₀ ≠ 0 := by
        rcases hσ_pm a₀ with h | h <;> rw [h] <;> norm_num
      have hsupport : ∀ β ∈ s, ∀ a, a ∉ Supp → levTwoS2d_toStdDQ n (toRat β) a = 0 := by
        intro β hβs a ha
        rw [levTwoS2d_toStdDQ_toRat, toRat_apply]
        by_contra hne
        exact ha ⟨β, hsΦ (Finset.mem_coe.mpr hβs),
          fun h0 => hne (by rw [h0]; norm_num)⟩
      have hsupp_u : ∀ β ∈ s, ∀ a, toStdD n β a ≠ 0 → a ∈ Supp := by
        intro β hβs a ha
        exact ⟨β, hsΦ (Finset.mem_coe.mpr hβs), ha⟩
      have hg : ∀ β ∈ s, ∑ a ∈ S, σ a * levTwoS2d_toStdDQ n (toRat β) a = 0 := by
        intro β hβs
        have hβΦ : β ∈ Φ := hsΦ (Finset.mem_coe.mpr hβs)
        obtain ⟨u, v, su, tv, huv, hsu, htv, hβuv⟩ :=
          (levTwoS2d_isRt_iff n (by omega) β).1 (hΦ.isRt β hβΦ)
        have hβu : toStdD n β u ≠ 0 := by
          rw [hβuv]; simp only [Pi.add_apply, Pi.single_apply]
          rcases hsu with rfl | rfl <;> simp [huv]
        have hβv : toStdD n β v ≠ 0 := by
          rw [hβuv]; simp only [Pi.add_apply, Pi.single_apply]
          rcases htv with rfl | rfl <;> simp [Ne.symm huv]
        have hQu := hQ β hβΦ u hβu
        have hQv := hQ β hβΦ v hβv
        have hsr := levTwoS2d_sigma_root_zero n hn hp2 c hc₀ hβΦ hΦ huv hsu htv hβuv hQu hQv
        have hsum : ∑ a ∈ S, σ a * levTwoS2d_toStdDQ n (toRat β) a =
            σ u * (su : ℚ) + σ v * (tv : ℚ) := by
          rw [levTwoS2d_toStdDQ_toRat]
          simp only [toRat_apply]
          have hsubset : ({u, v} : Finset (Fin n)) ⊆ S := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with h | h
            · rw [h]; exact (hSmem u).mpr (hsupp_u β hβs u hβu)
            · rw [h]; exact (hSmem v).mpr (hsupp_u β hβs v hβv)
          have hzero : ∀ a ∈ S, a ∉ ({u, v} : Finset (Fin n)) →
              σ a * ((toStdD n β) a : ℚ) = 0 := by
            intro a _ ha
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
            rw [hβuv]
            simp only [Pi.add_apply, Pi.single_apply]
            rw [if_neg ha.1, if_neg ha.2, add_zero]
            ring
          rw [← Finset.sum_subset hsubset hzero, Finset.sum_pair huv, hβuv]
          simp [huv, Ne.symm huv]
        rw [hsum]
        linarith [hsr]
      have hind : LinearIndependent ℚ
          (fun β : s => fun a : S.erase a₀ =>
            levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a.1) := by
        rw [linearIndependent_iff']
        intro t g hsum β hβ
        have hV : (∑ β ∈ t, g β • levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ))) = 0 := by
          funext a
          rw [Finset.sum_apply, Pi.zero_apply]
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a ∈ Supp
          · by_cases ha0 : a = a₀
            · rw [ha0]
              have hv : ∀ β : s, levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a₀ =
                  -(σ a₀)⁻¹ * ∑ b ∈ S.erase a₀, σ b *
                    levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b := by
                intro β
                have h := hg β.1 β.2
                rw [← Finset.sum_erase_add _ _ ((hSmem a₀).mpr ha₀)] at h
                have hmul : σ a₀ * levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a₀ =
                    -∑ b ∈ S.erase a₀, σ b *
                      levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b := by linarith
                rw [show levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a₀ =
                    (σ a₀)⁻¹ * (σ a₀ * levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a₀) by
                      rw [← mul_assoc, inv_mul_cancel₀ hσ_ne, one_mul]]
                rw [hmul]; ring
              simp_rw [hv]
              calc ∑ β ∈ t, g β * (-(σ a₀)⁻¹ * ∑ b ∈ S.erase a₀, σ b *
                      levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b)
                  = -(σ a₀)⁻¹ * ∑ β ∈ t, ∑ b ∈ S.erase a₀, g β * (σ b *
                      levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b) := by
                    simp_rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl; intro β _
                    apply Finset.sum_congr rfl; intro b _
                    ring
                _ = -(σ a₀)⁻¹ * ∑ b ∈ S.erase a₀, σ b *
                      (∑ β ∈ t, g β * levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b) := by
                    congr 1
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl; intro b _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl; intro β _; ring
                _ = 0 := by
                    rw [show (∑ b ∈ S.erase a₀, σ b *
                        (∑ β ∈ t, g β * levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) b)) = 0 from by
                      apply Finset.sum_eq_zero; intro b hb
                      have := congrFun hsum ⟨b, hb⟩
                      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
                      rw [this]; ring]
                    ring
            · have ha' : a ∈ S.erase a₀ := by
                rw [Finset.mem_erase]; exact ⟨ha0, (hSmem a).mpr ha⟩
              have := congrFun hsum ⟨a, ha'⟩
              simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
          · have : ∀ β : s, levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a = 0 := by
              intro β; exact hsupport β.1 β.2 a ha
            simp [this]
        have hV' : levTwoS2d_toStdDQ n (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 := by
          rw [map_sum]
          rw [show (∑ β ∈ t, levTwoS2d_toStdDQ n (g β • toRat (β : Fin n → ℤ))) =
              ∑ β ∈ t, g β • levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) from by
            apply Finset.sum_congr rfl; intro β _; rw [map_smul]]
          exact hV
        have hzero2 : (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 :=
          levTwoS2d_toStdDQ_eq_zero n hn hV'
        exact (linearIndependent_iff'.mp hlin) t g hzero2 β hβ
      have hle := LinearIndependent.fintype_card_le_finrank hind
      rw [Module.finrank_fintype_fun_eq_card] at hle
      have hScard : S.card = Nat.card Supp := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hcard : Fintype.card (S.erase a₀) = Nat.card Supp - 1 := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem ((hSmem a₀).mpr ha₀), hScard]
      rw [hcard] at hle
      simpa using hle

end CFSG.StandardType.LevTwo

