module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenOpp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

@[expose] def Eleven11Closing (M V Q : Subgroup G) : Prop :=
  ∀ U L X : Subgroup G, ∀ hd : Eleven11Data M V Q U L X,
    Nat.card (autI hd.setting.isElemAbelian M) = 21 →
    Nat.card (autI hd.setting.isElemAbelian X) = 3 → Nat.card V = 8 → False

theorem mem_gammaEleven_inf_conj {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X)
    {g : G}
    (hopp : Opp 2 (M ⊓ Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G)) ≤
      Subgroup.centralizer (V : Set G))
    (hne : U ⊓ conjSubgroup U g ≠ ⊥) : U ⊓ conjSubgroup U g ∈ gammaEleven M V := by
  obtain ⟨hUV, hU0, hCU, -⟩ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  exact ⟨inf_le_left.trans hUV, hne, fun h => hCU
    ((Subgroup.centralizer_le (inf_le_left : U ⊓ conjSubgroup U g ≤ U)).trans h), hopp⟩

theorem eleven_eleven_factors_of_eq_bot {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) {g : G} (hgM : g ∈ M) {j₀ : Fin s}
    (hj₀ : (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)⁻¹).toMonoidHom = Y j₀)
    (hbot : U ⊓ conjSubgroup U g = ⊥) : ∀ k, k = i₀ ∨ k = j₀ := by
  intro k
  by_contra hk
  obtain ⟨hk1, hk2⟩ := not_or.1 hk
  apply hdec.vs_ne_bot k
  rw [eq_bot_iff]
  intro v hv
  have h1 := vs_val_mem_inf hV hd hdec hgM hj₀ hk1 hk2 hv
  rw [hbot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact IntMod.val_injective (h1.trans IntMod.val_one.symm)

theorem eleven_eleven_of_eq {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) (hX : autI hV X = Y i₀) {g : G} (hgM : g ∈ M) :
    U ⊓ conjSubgroup U g ∈ gammaEleven M V := by
  have hgY : ¬ autI hV X = Y i₀ →
      (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)).toMonoidHom = Y i₀ :=
    fun h => absurd hX h
  have hopp := eleven_eleven_opp hV hd hdec hgM hgY
  by_cases hne : U ⊓ conjSubgroup U g = ⊥
  · exfalso
    have hMC : M ⊓ Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G) = M := by
      rw [hne]
      refine inf_eq_left.2 fun x _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := hh
      rw [this, one_mul, mul_one]
    rw [hMC] at hopp
    have hodd : Odd (Nat.card (autI hV M)) := odd_card_autI_of_opp_le hV hd.setting.normal hopp
    obtain ⟨j₀, hj₀, -⟩ := exists_conj_index hV hd hdec hgM hgY
    have hall := eleven_eleven_factors_of_eq_bot hV hd hdec hgM hj₀ hne
    obtain ⟨⟨hYsup, hYind, hcommY⟩, -, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, -⟩ := hdec.body
    by_cases hji : j₀ = i₀
    ·
      have hallk : ∀ k, k = i₀ := fun k => (hall k).elim id fun h => h.trans hji
      have hV1 : Vs i₀ = ⊤ := by
        rw [eq_top_iff, ← hdec.vs_sup]
        exact iSup_le fun k => by rw [hallk k]
      have h2 : commSub ⊤ (autI hV X) = ⊤ := by
        rw [hX, (hVi i₀).1, hV1]
      have h3 : fixV (autI hV X) = ⊥ := by
        have := Asc81c.fixV_inf_commSub_eq_bot' (IntMod.sq_eq_one) hdec.odd_X
        rwa [h2, inf_top_eq] at this
      have hU1 : U = ⊥ := by rw [← hdec.fixV_map, h3, Subgroup.map_bot]
      exact (deltaEleven_subset_gammaEleven M V hd.mem_delta).2.1 hU1
    ·
      have hne' : Y i₀ ≠ Y j₀ := fun h => hji (hYind.injective hdec.Y_ne_bot h).symm
      have hgN := hd.setting.normal hgM
      have hφ : convI hV ⟨g, hgN⟩ ∈ autI hV M := convI_mem_autI hV hgM hgN
      have hev := even_card_of_two_factors hperm hall hne'
        ((autI hV M).inv_mem hφ) hj₀
      exact (Nat.not_even_iff_odd.2 hodd) hev
  · exact mem_gammaEleven_inf_conj hd hopp hne

theorem eleven_eleven_of_frob {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) (hclose : Eleven11Closing M V Q) {s : ℕ}
    {Y : Fin s → Subgroup (MulAut (IntMod V hV))} {Vs : Fin s → Subgroup (IntMod V hV)}
    {i₀ : Fin s} (hdec : Eleven11Decomp hV M X U s Y Vs i₀) (hX : ¬ autI hV X = Y i₀) {g : G}
    (hgM : g ∈ M)
    (hgY : (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)).toMonoidHom = Y i₀) :
    U ⊓ conjSubgroup U g ∈ gammaEleven M V := by
  have hgY' : ¬ autI hV X = Y i₀ →
      (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)).toMonoidHom = Y i₀ :=
    fun _ => hgY
  have hopp := eleven_eleven_opp hV hd hdec hgM hgY'
  by_cases hne : U ⊓ conjSubgroup U g = ⊥
  · exfalso
    have hMC : M ⊓ Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G) = M := by
      rw [hne]
      refine inf_eq_left.2 fun x _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := hh
      rw [this, one_mul, mul_one]
    rw [hMC] at hopp
    have hModd : Odd (Nat.card (autI hV M)) :=
      odd_card_autI_of_opp_le hV hd.setting.normal hopp
    obtain ⟨j₀, hj₀, hj₀'⟩ := exists_conj_index hV hd hdec hgM hgY'
    have hj : j₀ = i₀ := hj₀' hX
    have hall := eleven_eleven_factors_of_eq_bot hV hd hdec hgM hj₀ hne
    obtain ⟨h3, -, h21, -, h8⟩ : Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y i₀ ∧
        Nat.card (Y i₀) = 21 ∧ (∃ a ∈ Y i₀, ∃ b ∈ Y i₀, a * b ≠ b * a) ∧
        ∀ j, Nat.card (Vs j) = 8 := by
      rcases hdec.case with h | h
      · exact absurd h hX
      · exact h
    have hallk : ∀ k, k = i₀ := fun k => (hall k).elim id fun h => h.trans hj
    have hV1 : Vs i₀ = ⊤ := by
      rw [eq_top_iff, ← hdec.vs_sup]
      exact iSup_le fun k => by rw [hallk k]
    have hcardW : Nat.card (IntMod V hV) = 8 := by
      have := h8 i₀
      rw [hV1, Subgroup.card_top] at this
      exact this
    have hYM : Y i₀ ≤ autI hV M := hdec.Y_le i₀
    have hM21 : Nat.card (autI hV M) = 21 := by
      have h168 := E6.card_mulAut_eight' (W := IntMod V hV) (fun a b => mul_comm a b)
        IntMod.sq_eq_one hcardW
      have hdvd : Nat.card (autI hV M) ∣ 21 * 8 := by
        rw [show 21 * 8 = 168 by norm_num, ← h168]
        exact Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ : 21 ∣ Nat.card (autI hV M) := h21 ▸ Subgroup.card_dvd_of_le hYM
      rw [hk] at hdvd hModd
      have hk8 : k ∣ 8 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show k ∣ 2 ^ 3 by simpa using hk8)
      have hj0 : j = 0 := by
        by_contra hj0
        apply (Nat.not_even_iff_odd.2 hModd)
        exact (Nat.even_pow.2 ⟨even_two, hj0⟩).mul_left 21
      rw [hk, hj0, pow_zero, mul_one]
    exact hclose U L X hd hM21 h3 hcardW
  · exact mem_gammaEleven_inf_conj hd hopp hne

end CFSG.LocalAnalysis.WeakClosure81
