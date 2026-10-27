module

public import CFSG.Quasithin.H13.GoldschmidtC137CPt1
public import CFSG.Quasithin.H13.GoldschmidtC137DE
public import CFSG.Quasithin.H13.GoldschmidtC137Pt2Aux
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin4
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin5
public import CFSG.Quasithin.H13.GoldschmidtC137Tr

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem conjAut_map_ρ (c : Gp 6) (K : Subgroup (Gp 6)) :
    B1.conjAut (F.ρ c) (K.map F.ρ) = (cj c K).map F.ρ := by
  rw [conjAut_eq_map_gc, Subgroup.map_map]
  unfold cj
  rw [Subgroup.map_map]
  congr 1
  ext k
  simp [map_mul, map_inv]

theorem isElemAbelian2_mono_gc {W : Type*} [CommGroup W] {A B : Subgroup (MulAut W)} (h : B ≤ A)
    (hA : IsElemAbelian2 A) : IsElemAbelian2 B :=
  ⟨fun a ha b hb => hA.1 a (h ha) b (h hb), fun a ha => hA.2 a (h ha)⟩

theorem point_exists_A0 (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian (pCoreOf 2 P) A₀ ∧ autI h.hVe A₀ = Z1.map F.ρ := by
  set R := pCoreOf 2 P with hRdef
  have hRN : R ≤ normalizer (V : Set G) := h.R_le_N
  have hVR : V ≤ R := h.toBaum.hVR
  have hRX : R ≤ X := h.R_le_X
  obtain ⟨A, hA⟩ := h.exists_offender hJ
  have hB : autI h.hVe A ∈ offenderImages h.hVe R := ⟨A, hA, rfl⟩
  have hBoff := offenderImages_isFFStarOffender h.hVe hVR hRN hB
  have hBX : IsFFStarOffender (autI h.hVe X) (autI h.hVe A) :=
    isFFStarOffender_mono (autI_mono h.hVe hRX) hBoff
  have hAR : autI h.hVe A ≤ R1.map F.ρ := hR ▸ hBoff.1
  set B' := (autI h.hVe A).comap F.ρ with hB'
  have hB'map : B'.map F.ρ = autI h.hVe A := F.map_comap_eq (hAR.trans F.R1_map_le_X)
  have hoff : IsOffG 6 Mod.ut0 B' := (F.offender_ρ B').1 (by rw [hB'map]; exact hBX)
  obtain ⟨hB'ne, hB'F⟩ := offender_F_ge hoff
  have hB'R1 : B' ≤ R1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hAR hx
    rwa [← F.inj hyx]
  have hτ := R1_swap_mem hB'R1 hB'ne hB'F
  have hFle := R1_F_le hB'R1
  have hZB' : Z1 ≤ B' := by
    intro x hx
    rw [mem_Z1] at hx
    simp only [Z1l, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · have : x = 1 := tab_injective (by rw [hx, tab_one]; rfl)
      rw [this]
      exact B'.one_mem
    · have : x = Equiv.swap (4 : Fin 6) 5 := tab_injective (by rw [hx, tab_swap45]; rfl)
      rw [this]
      exact hτ
  have hZA : Z1.map F.ρ ≤ autI h.hVe A := hB'map ▸ Subgroup.map_mono hZB'
  have hffle : FFLe (autI h.hVe R) (Z1.map F.ρ) (autI h.hVe A) := by
    refine ⟨⟨?_, ?_, isElemAbelian2_mono_gc hZA hBoff.2.2.1⟩, hBoff.isA2, hZA, ?_⟩
    · rw [hR]
      exact Subgroup.map_mono Z1_le_R1
    · intro hb
      have := (Subgroup.map_eq_bot_iff_of_injective _ F.inj).1 hb
      have h1 : Equiv.swap (4 : Fin 6) 5 ∈ (⊥ : Subgroup (Gp 6)) := this ▸ swap45_mem_Z1
      exact absurd (Subgroup.mem_bot.1 h1) (by decide)
    · rw [F.card_ρ, F.card_fixV_ρ, card_Z1, card_fixV_Z1, ← hB'map, F.card_ρ, F.card_fixV_ρ]
      have := card_map_act B'
      rw [this] at hB'F hFle
      have h16 : Nat.card B' * Nat.card (fixV (B'.map (Mod.act 6 Mod.ut0))) = 16 := by omega
      calc 2 * (cK F.k * 8) = cK F.k * 16 := by ring
        _ = cK F.k * (Nat.card B' * Nat.card (fixV (B'.map (Mod.act 6 Mod.ut0)))) := by
          rw [h16]
        _ = _ := by ring
  obtain ⟨A₀, hA₀, hA₀eq⟩ := offenderImages_ffLe h.hVe hVR hRN hA hffle
  exact ⟨A₀, hA₀.1, hA₀eq.symm⟩

theorem point_hDE (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G))
    (hJR : autI h.hVe (thompsonJ (pCoreOf 2 P)) = autI h.hVe (pCoreOf 2 P)) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V h.hVe))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hVe L, B1.conjAut g (Y i) ≤ autI h.hVe (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hVe (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hVe (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hVe L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hVe L)) ∧
      ∀ A, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V h.hVe))),
          A = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hVe L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hVe (pCoreOf 2 P) := by
  obtain ⟨A₀, hA₀, hA₀eq⟩ := F.point_exists_A0 hR hJ
  have hc : F.ρ cptP ∈ autI h.hVe L := by
    rw [← F.hA]
    exact ⟨cptP, cptP_even, rfl⟩
  refine hDE_of_pieces h.hVe h.hXN h.hLX h.R_le_X
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) h.toBaum.hA2 hJR (m := 1) (fun _ => A₀)
    (fun _ => hA₀) (fun _ => F.ρ cptP) (fun _ => hc) ?_ ?_
  · simp only [hA₀eq, iSup_const]
    rw [F.conjAut_map_ρ, hR, ← Subgroup.map_sup, R1_sup_eq_top, ← F.hA]
    exact Subgroup.map_mono le_top
  · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [hR, hA₀eq, ← F.hA, F.rkIdx_fixV_ρ, F.rkIdx_fixV_ρ, F.rkIdx_fixV_ρ, rank_R1.2,
      rank_Z1.2, rkIdx_A6]


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
