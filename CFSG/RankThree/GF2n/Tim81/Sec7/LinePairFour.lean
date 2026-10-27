module

public import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairFrame
import CFSG.Timmesfeld.Transvection.ModelSUFour
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.Quasithin.MS93.PUEquiv

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
open scoped MatrixGroups commutatorElement

namespace SUTrans

section Four

variable {F : Type} [Field F] {σ : F ≃+* F} {K : Type} [Group K]

private theorem exists_swap_conjSub {T₀ T₁ T₂ T₃ : Subgroup (SU σ 4)}
    (hT₀ : IsUTransGroup σ (Pi.single (0 : Fin 4) 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (1 : Fin 4) 1) T₁)
    (hT₂ : IsUTransGroup σ (Pi.single (2 : Fin 4) 1) T₂)
    (hT₃ : IsUTransGroup σ (Pi.single (3 : Fin 4) 1) T₃) :
    ∃ w : SU σ 4, conjSubgroup w T₀ = T₁ ∧ conjSubgroup w T₃ = T₂ ∧
      conjSubgroup w T₁ = T₀ ∧ conjSubgroup w T₂ = T₃ := by
  obtain ⟨w, hw⟩ := exists_swap_SU_four σ
  have hw0 : suMat σ 4 w *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 1 1 := by
    rw [hw]
    funext i
    fin_cases i <;> simp
  have hw1 : suMat σ 4 w *ᵥ Pi.single (1 : Fin 4) 1 = Pi.single 0 1 := by
    rw [hw]
    funext i
    fin_cases i <;> simp
  have hw2 : suMat σ 4 w *ᵥ Pi.single (2 : Fin 4) 1 = Pi.single 3 1 := by
    rw [hw]
    funext i
    fin_cases i <;> simp
  have hw3 : suMat σ 4 w *ᵥ Pi.single (3 : Fin 4) 1 = Pi.single 2 1 := by
    rw [hw]
    funext i
    fin_cases i <;> simp
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have h := hT₀.conjSub w
    rw [hw0] at h
    exact h.eq hT₁
  · have h := hT₃.conjSub w
    rw [hw3] at h
    exact h.eq hT₂
  · have h := hT₁.conjSub w
    rw [hw1] at h
    exact h.eq hT₀
  · have h := hT₂.conjSub w
    rw [hw2] at h
    exact h.eq hT₃

private theorem perpRoots_eq_middle [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (hm : 2 ≤ 4)
    {Φ : SU σ 4 →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ 4))
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup σ hσ 4
      (unitaryLongRoot 4 hm)) x).map Φ)
    {T₀ T₁ T₂ T₃ : Subgroup (SU σ 4)}
    (hT₀ : IsUTransGroup σ (Pi.single (0 : Fin 4) 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (1 : Fin 4) 1) T₁)
    (hT₂ : IsUTransGroup σ (Pi.single (2 : Fin 4) 1) T₂)
    (hT₃ : IsUTransGroup σ (Pi.single (3 : Fin 4) 1) T₃) :
    perpRoots Δ (T₀.map Φ ⊔ T₃.map Φ) = T₁.map Φ ⊔ T₂.map Φ := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨u, T, hu, huu, hT, hUeq⟩ :=
      exists_eq_map_of_mem (m := 4) hσ hm hΔ hU.1
    have hP : u ∈ perpPair σ (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1) :=
      mem_perpPair_of_map_le_centralizer (m := 2) hσ hker hT hu huu hT₀ hT₃ (hUeq ▸ hU.2)
    obtain ⟨h3, h0⟩ := (mem_perpPair_ends (m := 2)).1 hP
    have h0' : u 0 = 0 := h0
    have h3' : u 3 = 0 := h3
    rcases eq_smul_of_perp_four hu h0' h3' huu with ⟨c, hc, hue⟩ | ⟨c, s, hc, hs, hue⟩
    · have hT' : IsUTransGroup σ (Pi.single (2 : Fin 4) 1) T :=
        IsUTransGroup.of_smul hσ hc (hue ▸ hT)
      rw [hUeq, hT'.eq hT₂]
      exact le_sup_right
    · have hsc : s + σ s = 0 := by rw [hs, CharTwo.add_self_eq_zero]
      obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans (σ := σ) hσ (v := Pi.single (2 : Fin 4) 1)
        (uForm_single_self (by decide)) hsc
      have htmem : t ∈ T₂ := (hT₂.1 t).2 ⟨s, hsc, ht⟩
      have hvec : suMat σ 4 t *ᵥ Pi.single (1 : Fin 4) 1 =
          Pi.single 1 1 + s • Pi.single (2 : Fin 4) 1 := by
        rw [ht, uTrans_mulVec_single_one_four]
      have hTt : IsUTransGroup σ (Pi.single 1 1 + s • Pi.single 2 1)
          (conjSubgroup t T₁) := by
        have h := hT₁.conjSub t
        rwa [hvec] at h
      have hTeq : T = conjSubgroup t T₁ := by
        have h1 : IsUTransGroup σ (c • (Pi.single 1 1 + s • Pi.single 2 1)) T := hue ▸ hT
        exact (IsUTransGroup.of_smul hσ hc h1).eq hTt
      rw [hUeq, hTeq, map_conjSubgroup Φ t T₁]
      exact Subgroup.conj_smul_le_of_le le_sup_left
        ⟨Φ t, Subgroup.mem_sup_right (Subgroup.mem_map_of_mem Φ htmem)⟩
  · refine map_le_perpRoots (m := 2) hσ htr hm hΔ hT₁ (single_one_ne_zero 1)
      (uForm_single_self (by decide)) hT₀ hT₃ ?_
    rw [mem_perpPair_ends]
    exact ⟨by simp, by simp⟩
  · refine map_le_perpRoots (m := 2) hσ htr hm hΔ hT₂ (single_one_ne_zero 2)
      (uForm_single_self (by decide)) hT₀ hT₃ ?_
    rw [mem_perpPair_ends]
    exact ⟨by simp, by simp⟩

private theorem natCard_range_inf_centralizer [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {Φ : SU (unitaryInvolution F 2 f) 4 →* K} (hinj : Function.Injective Φ)
    {T₀ T₁ T₂ T₃ : Subgroup (SU (unitaryInvolution F 2 f) 4)}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (0 : Fin 4) 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (1 : Fin 4) 1) T₁)
    (hT₂ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (2 : Fin 4) 1) T₂)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (3 : Fin 4) 1) T₃) :
    Nat.card ↥(Φ.range ⊓ Subgroup.centralizer
      (((T₀.map Φ ⊔ T₃.map Φ ⊔ (T₁.map Φ ⊔ T₂.map Φ)) : Subgroup K) : Set K)) =
      2 ^ f + 1 := by
  have hsup : (T₀.map Φ ⊔ T₃.map Φ ⊔ (T₁.map Φ ⊔ T₂.map Φ) : Subgroup K) =
      (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)).map Φ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup]
  rw [hsup, CFSG.Quasithin.MS93.PU.range_inf_centralizer_map hinj (T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂)),
    Subgroup.card_map_of_injective (K := Subgroup.centralizer
      ((T₀ ⊔ T₃ ⊔ (T₁ ⊔ T₂) : Subgroup (SU (unitaryInvolution F 2 f) 4)) : Set _))
      (f := Φ) hinj]
  exact natCard_centralizer_coord_SU_four hF hf hT₀ hT₁ hT₂ hT₃

private theorem exists_swap_sup_four (Φ : SU σ 4 →* K) {T₀ T₁ T₂ T₃ : Subgroup (SU σ 4)}
    (hT₀ : IsUTransGroup σ (Pi.single (0 : Fin 4) 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (1 : Fin 4) 1) T₁)
    (hT₂ : IsUTransGroup σ (Pi.single (2 : Fin 4) 1) T₂)
    (hT₃ : IsUTransGroup σ (Pi.single (3 : Fin 4) 1) T₃) :
    ∃ w : SU σ 4, conjSubgroup (Φ w) (T₀.map Φ ⊔ T₃.map Φ) = T₁.map Φ ⊔ T₂.map Φ ∧
      conjSubgroup (Φ w) (T₁.map Φ ⊔ T₂.map Φ) = T₀.map Φ ⊔ T₃.map Φ := by
  obtain ⟨w, h0, h3, h1, h2⟩ := exists_swap_conjSub hT₀ hT₁ hT₂ hT₃
  refine ⟨w, ?_, ?_⟩
  · change Subgroup.map (MulAut.conj (Φ w)).toMonoidHom (T₀.map Φ ⊔ T₃.map Φ) =
      T₁.map Φ ⊔ T₂.map Φ
    rw [Subgroup.map_sup]
    change conjSubgroup (Φ w) (T₀.map Φ) ⊔ conjSubgroup (Φ w) (T₃.map Φ) =
      T₁.map Φ ⊔ T₂.map Φ
    rw [← map_conjSubgroup Φ w T₀, ← map_conjSubgroup Φ w T₃, h0, h3]
  · change Subgroup.map (MulAut.conj (Φ w)).toMonoidHom (T₁.map Φ ⊔ T₂.map Φ) =
      T₀.map Φ ⊔ T₃.map Φ
    rw [Subgroup.map_sup]
    change conjSubgroup (Φ w) (T₁.map Φ) ⊔ conjSubgroup (Φ w) (T₂.map Φ) =
      T₀.map Φ ⊔ T₃.map Φ
    rw [← map_conjSubgroup Φ w T₁, ← map_conjSubgroup Φ w T₂, h1, h2]

end Four

theorem exists_linePair_four_of_frame {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    {K : Type} [Group K] {Φ : SU (unitaryInvolution F 2 f) 4 →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) 4)) (hm : 2 ≤ 4)
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f) hσ 4
      (unitaryLongRoot 4 hm)) x).map Φ)
    {T₀ T₃ : Subgroup (SU (unitaryInvolution F 2 f) 4)}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hAB : IsL2Gen (T₀.map Φ) (T₃.map Φ)) :
    ∃ C ∈ Δ, ∃ D ∈ Δ, IsL2Gen C D ∧ perpRoots Δ (T₀.map Φ ⊔ T₃.map Φ) = C ⊔ D ∧
      Nat.card ↥(Φ.range ⊓ Subgroup.centralizer
        ((T₀.map Φ ⊔ T₃.map Φ ⊔ (C ⊔ D) : Subgroup K) : Set K)) = 2 ^ f + 1 ∧
      ∃ g ∈ Φ.range, conjSubgroup g (T₀.map Φ ⊔ T₃.map Φ) = C ⊔ D ∧
        conjSubgroup g (C ⊔ D) = T₀.map Φ ⊔ T₃.map Φ := by
  have htr : ∀ a, unitaryInvolution F 2 f a = a → ∃ c, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hF ha
  have hkerbot : Φ.ker = ⊥ := by
    rw [eq_bot_iff]
    exact hker.trans (le_of_eq (center_SU_four_eq_bot hσ))
  have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).1 hkerbot
  obtain ⟨T₁, hT₁⟩ := exists_isUTransGroup hσ (v := Pi.single (1 : Fin 4) 1)
    (uForm_single_self (by decide))
  obtain ⟨T₂, hT₂⟩ := exists_isUTransGroup hσ (v := Pi.single (2 : Fin 4) 1)
    (uForm_single_self (by decide))
  have hCD : IsL2Gen (T₁.map Φ) (T₂.map Φ) := by
    obtain ⟨w, h0, h3, -, -⟩ := exists_swap_conjSub hT₀ hT₁ hT₂ hT₃
    have h := hAB.conj (Φ w)
    rw [← map_conjSubgroup Φ w T₀, ← map_conjSubgroup Φ w T₃, h0, h3] at h
    exact h
  refine ⟨T₁.map Φ, map_mem hσ htr hm hΔ (single_one_ne_zero 1)
      (uForm_single_self (by decide)) hT₁, T₂.map Φ, map_mem hσ htr hm hΔ
      (single_one_ne_zero 2) (uForm_single_self (by decide)) hT₂, hCD,
    perpRoots_eq_middle hσ htr hm hker hΔ hT₀ hT₁ hT₂ hT₃,
    natCard_range_inf_centralizer hF hf hinj hT₀ hT₁ hT₂ hT₃, ?_⟩
  obtain ⟨w, hswap1, hswap2⟩ := exists_swap_sup_four Φ hT₀ hT₁ hT₂ hT₃
  exact ⟨Φ w, ⟨w, rfl⟩, hswap1, hswap2⟩

end SUTrans

theorem IsSUImage.exists_linePair_four {K : Type} [Group K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} {f : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ 4}
    (hX : IsSUImage X₀ Δ f 4 hf hm)
    {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : IsL2Gen A B) :
    ∃ C ∈ Δ, ∃ D ∈ Δ, IsL2Gen C D ∧ perpRoots Δ (A ⊔ B) = C ⊔ D ∧
      Nat.card ↥(X₀ ⊓ Subgroup.centralizer ((A ⊔ B ⊔ (C ⊔ D) : Subgroup K) : Set K)) =
        2 ^ f + 1 ∧
      ∃ g ∈ X₀, conjSubgroup g (A ⊔ B) = C ⊔ D ∧ conjSubgroup g (C ⊔ D) = A ⊔ B := by
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨Ψ, hkerΨ, hrangeΨ, hΔΨ, T₀, T₃, hT₀, hT₃, hAΨ, hBΨ⟩ :=
    hX.exists_frame (m := 2) hA hB hAB.commutator_ne_bot
  have hAB' : IsL2Gen (T₀.map Ψ) (T₃.map Ψ) := by
    rw [← hAΨ, ← hBΨ]
    exact hAB
  obtain ⟨C, hC, D, hD, hCD, hperp, hcard, g, hg, hswap1, hswap2⟩ :=
    SUTrans.exists_linePair_four_of_frame hF hf hσ hkerΨ hm hΔΨ hT₀ hT₃ hAB'
  exact ⟨C, hC, D, hD, hCD, by simpa only [hAΨ, hBΨ] using hperp,
    by simpa only [hAΨ, hBΨ, hrangeΨ] using hcard, g, by simpa only [hrangeΨ] using hg,
    by simpa only [hAΨ, hBΨ] using hswap1, by simpa only [hAΨ, hBΨ] using hswap2⟩

end CFSG.RankThree.GF2n.Tim81
