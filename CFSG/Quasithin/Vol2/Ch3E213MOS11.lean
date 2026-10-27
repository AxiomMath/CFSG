module

public import CFSG.Quasithin.Vol2.Ch3E213MOS10

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

theorem false_of_asHyp (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    {K T M V : Subgroup X} (hX : E2P.ASHyp K T M) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : f = 1 ∨ f = 2) (hpsl : IsPSL 2 p f ↥K)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X))
    (hAut : 8 < E2.autCard T K) (hVT : V ≤ T) (hVn : T ≤ Subgroup.normalizer (V : Set X))
    (hsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ≤ Nat.card V) (hVM : V ≤ pCoreOf 2 M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.normal
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := hpsl
  have hf0 : f ≠ 0 := by omega
  have hFL : L2Field F := by
    refine ⟨by rw [hcard]; exact (hp.odd_of_ne_two (by omega)).pow, ?_⟩
    rw [hcard]
    exact lt_of_lt_of_le hp3 (Nat.le_self_pow hf0 p)
  have hιinj := conjNormal_injective hX.cent
  have hKinn : K.map (MulAut.conjNormal : X →* MulAut ↥K) = innAut ↥K := map_conjNormal_eq
  have hidx : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hX.minPar.isSylow.2.2
  obtain ⟨e, N, hTN, hNP⟩ := h12 F hFL X K ⟨e₀⟩ (hX.minPar.isSylow.2.1.toSylow hidx)
  generalize hι : (MulAut.conjNormal : X →* MulAut ↥K) = ι at hTN hNP hιinj hKinn
  have hTN' : T.map ι ≤ N.T := hTN
  have hNP' : (T ⊓ K).map ι = N.P := hNP
  have hPT : N.P ≤ T.map ι := by
    rw [← hNP']
    exact Subgroup.map_mono inf_le_left
  have hautT : E2.autCard T K = Nat.card T := by
    unfold E2.autCard
    rw [Subgroup.normalizer_eq_top_iff.mpr hX.normal, hX.cent, inf_top_eq, inf_bot_eq,
      Subgroup.relIndex_bot_left]
  have h8 : 8 < Nat.card (T.map ι) := by
    rw [Subgroup.card_map_of_injective hιinj, ← hautT]
    exact hAut
  have hVT' : V.map ι ≤ T.map ι := Subgroup.map_mono hVT
  have hVn' : T.map ι ≤ Subgroup.normalizer (V.map ι : Set (MulAut ↥K)) :=
    (Subgroup.map_mono hVn).trans (Subgroup.le_normalizer_map ι)
  have hsq' : ∀ v ∈ V.map ι, v * v = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, hsq v hv, map_one]
  have hV4' : 4 ≤ Nat.card (V.map ι) := by
    rw [Subgroup.card_map_of_injective hιinj]
    exact hV4
  have hVM' : V.map ι ≤ pCoreOf 2 (M.map ι) :=
    (Subgroup.map_mono hVM).trans (CFSG.LieType.BorelTits.map_pCoreOf_le _ _)
  have hD' : M.map ι ⊓ innAut ↥K =
      innAut ↥K ⊓ Subgroup.centralizer (E2P.zOf N.P : Set (MulAut ↥K)) := by
    rw [← hKinn, ← hNP', ← map_zOf hιinj]
    exact map_inf_eq_centralizer hιinj hMK
  have uniq : ∀ Y : Subgroup (MulAut ↥K), Y ≤ innAut ↥K → N.P ≤ Y → Y ≠ innAut ↥K →
      T.map ι ≤ Subgroup.normalizer (Y : Set (MulAut ↥K)) → Y ≤ M.map ι := by
    intro Y hYI hPY hYne hTY
    have hIr : innAut ↥K ≤ ι.range := by
      rw [← hKinn]
      exact Subgroup.map_le_range ι K
    have hmapY : (Y.comap ι).map ι = Y := Subgroup.map_comap_eq_self (hYI.trans hIr)
    have hY'K : Y.comap ι ≤ K := by
      intro y hy
      have hyI : ι y ∈ K.map ι := by
        rw [hKinn]
        exact hYI hy
      obtain ⟨k, hk, hky⟩ := hyI
      rw [← hιinj hky]
      exact hk
    have hSY : T ⊓ K ≤ Y.comap ι := fun s hs => hPY (by rw [← hNP']; exact ⟨s, hs, rfl⟩)
    have hYne' : Y.comap ι ≠ K := by
      intro h
      apply hYne
      calc Y = (Y.comap ι).map ι := hmapY.symm
        _ = K.map ι := by rw [h]
        _ = innAut ↥K := hKinn
    have hTY' : T ≤ Subgroup.normalizer (Y.comap ι : Set X) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp (hTY ⟨t, ht, rfl⟩) (ι y)
      show ι y ∈ Y ↔ ι (t * y * t⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact h1
    rw [← hmapY]
    exact Subgroup.map_mono (hX.le_M_of_normalized hY'K hSY hYne' hTY')
  exact false_of_aut h13a h13b hFL e N hp hp3 hf hcard hPT hTN' h8 hVT' hVn' hsq' hV4' hVM' hD'
    uniq (fun h11 u hu => hcoat F hFL h11 ↥K e u hu)

end CFSG.Quasithin.Ch3E213M.OS
