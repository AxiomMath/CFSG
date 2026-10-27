module

public import CFSG.Quasithin.Vol2.Ch10SecA312AH
public import CFSG.Quasithin.Vol2.Ch10SecA312AS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Main
public import CFSG.LieType.HighestRoot.CentTrialityMain
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.Quasithin.Vol2.Ch10SecA312LB
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

section Z6

open CFSG.Quasithin.A312M24 CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.M24
open scoped Pointwise

@[expose] def vW : List ℕ := [0, 3, 0, 3]

@[expose] def orbW : List (ℕ × List ℕ) :=
  [(7, [1]), (9, [0, 0]), (7, [0, 2, 0]), (7, [1, 0, 2, 0]), (9, [1, 0]), (9, [0]), (9, [4, 0]),
    (7, []), (9, [0, 1, 0]), (9, []), (7, [3, 0]), (7, [1, 0]), (9, [2, 1, 0]), (7, [2, 0]),
    (7, [2, 3]), (7, [0, 0]), (7, [0, 1]), (7, [1, 0, 0]), (9, [0, 0, 0]), (7, [2, 0, 1]),
    (7, [0]), (7, [4, 1]), (7, [3]), (7, [3, 1])]

theorem orbW_spec : ∀ q < 24, ((orbW.getD q (0, [])).1 = 7 ∨ (orbW.getD q (0, [])).1 = 9) ∧
    (∀ l ∈ (orbW.getD q (0, [])).2, l < 5) ∧
    (wordTab 24 gens6T (orbW.getD q (0, [])).2).getD (orbW.getD q (0, [])).1
      (orbW.getD q (0, [])).1 = q := by
  decide +kernel

theorem eq_one_of_comm_Z6 {z : G24} (hz6 : z ∈ Z6)
    (hz : ∀ g ∈ Z6, z * g = g * z) : z = 1 := by
  have hcomm : ∀ g ∈ Z6, ∀ p : ℕ, z • (g • p) = g • (z • p) := fun g hg p => by
    rw [← mul_smul, ← mul_smul, hz g hg]
  have h23 := Z6_inv23 z hz6 ([0, 2, 3, 7, 10, 15, 17, 21] : List ℕ).toFinset (by decide)
  simp only [O23, List.mem_cons, List.not_mem_nil, or_false] at h23
  rcases h23 with h2 | h3
  · have hfix : ∀ p ∈ ([0, 2, 3, 7, 10, 15, 17, 21] : List ℕ).toFinset,
        y6 • p = p → p = 7 := by
      intro p hp
      rw [smul_nat, tab_y6]
      revert p
      decide +kernel
    have hfixLO : ∀ p ∈ ([1, 4, 5, 6, 8, 9, 12, 18] : List ℕ).toFinset,
        y6 • p = p → p = 9 := by
      intro p hp
      rw [smul_nat, tab_y6]
      revert p
      decide +kernel
    have hy7 : y6 • (7 : ℕ) = 7 := by rw [smul_nat, tab_y6]; decide
    have hy9 : y6 • (9 : ℕ) = 9 := by rw [smul_nat, tab_y6]; decide
    have hLO := Z6_invLO z hz6 ([1, 4, 5, 6, 8, 9, 12, 18] : List ℕ).toFinset (by decide)
    simp only [LOl, List.mem_cons, List.not_mem_nil, or_false] at hLO
    have h7 : z • (7 : ℕ) = 7 := by
      refine hfix _ ?_ (by rw [← hcomm y6 y6_mem, hy7])
      rw [← h2]
      exact Finset.smul_mem_smul_finset (by decide)
    have h9 : z • (9 : ℕ) = 9 := by
      refine hfixLO _ ?_ (by rw [← hcomm y6 y6_mem, hy9])
      rw [← hLO]
      exact Finset.smul_mem_smul_finset (by decide)
    have hall : ∀ q < 24, z • q = q := by
      intro q hq
      obtain ⟨hr, hl, hw⟩ := orbW_spec q hq
      have hg6 : evalEltL gens6 (orbW.getD q (0, [])).2 ∈ Z6 :=
        evalEltL_mem gens6 gens6_mem _
      have hgr : evalEltL gens6 (orbW.getD q (0, [])).2 • (orbW.getD q (0, [])).1 = q := by
        rw [smul_nat, tab_evalEltL _ _ (by rw [gens6_length]; exact hl), gens6_tab]
        exact hw
      have hzr : z • (orbW.getD q (0, [])).1 = (orbW.getD q (0, [])).1 := by
        rcases hr with h | h <;> rw [h]
        · exact h7
        · exact h9
      rw [← hgr, hcomm _ hg6, hzr]
    refine base_of_faithful (n := 24) z fun b hb => ?_
    have hb' : b < 24 := List.mem_range.mp hb
    have hlen : b < (tab 24 z).length := by simp [tab, hb']
    have := hall b hb'
    rw [smul_nat, List.getD_eq_getElem _ _ hlen] at this
    show (tab 24 z).getD b 0 = b
    rw [List.getD_eq_getElem _ _ hlen, this]
  · exfalso
    have hv6 : evalEltL m24Sg vW ∈ Z6 :=
      evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) vW
    have htv : tab 24 (evalEltL m24Sg vW) = wordTab 24 sTL vW := by
      rw [tab_evalEltL _ _ (by simp only [m24Sg_length]; decide), m24Sg_tab]
    have hvfix : ∀ q ∈ ([0, 2, 3, 7, 10, 15, 17, 21] : List ℕ).toFinset,
        evalEltL m24Sg vW • q = q := by
      intro q hq
      rw [smul_nat, htv]
      revert q
      decide +kernel
    have hvmove : evalEltL m24Sg vW • (11 : ℕ) ≠ 11 := by
      rw [smul_nat, htv]
      decide +kernel
    have h11 : (11 : ℕ) ∈ z • ([0, 2, 3, 7, 10, 15, 17, 21] : List ℕ).toFinset := by
      rw [h3]
      decide
    obtain ⟨q, hq, hzq⟩ := Finset.mem_smul_finset.mp h11
    apply hvmove
    rw [← hzq, ← mul_smul, ← hz _ hv6, mul_smul, hvfix q hq]

theorem card_of_isE2 {n : ℕ} {V : Type} [Group V] (h : IsE2 n V) : Nat.card V = 2 ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod]
  simp

theorem false_of_e64_G24 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hBtop : B ≠ ⊤) (hSB : m24CtxE.S ≤ Subgroup.normalizer (B : Set G24))
    (hcardB : Nat.card ↥B = 10752) {z : G24} (hzS : z ∈ m24CtxE.S) (hz1 : z ≠ 1)
    (hzc : ∀ t ∈ m24CtxE.S, z * t = t * z) (hzB : ∀ b ∈ B, z * b = b * z) : False := by
  have hsup : B ⊔ m24CtxE.S ≠ ⊤ := by
    intro htop
    have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (htop ▸ sup_le Subgroup.le_normalizer hSB))
    have : IsSimpleGroup G24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := B) with h | h
    · rw [h, Subgroup.card_bot] at hcardB
      omega
    · exact hBtop h
  obtain ⟨j, hj, hY, hc⟩ := overgroup_member le_sup_right hsup
  have hdvd : 10752 ∣ memIdx[j]! * 2 ^ 10 := by
    rw [← hcardB, ← hc]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hj' : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by
    have key : ∀ j < 13, 10752 ∣ memIdx[j]! * 2 ^ 10 → j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by
      decide
    exact key j hj hdvd
  have hcardY : ∀ {W : Subgroup ↥B} {a b : ℕ}, Nat.card ↥W = a → Nat.card (↥B ⧸ W) = b →
      Nat.card ↥B = b * a := fun {W a b} hW hQ => by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W, hQ, hW]
  have hZ46 : ∀ i, i = 4 ∨ i = 6 → m24CtxE.Y i = Z4 ∨ m24CtxE.Y i = Z6 := by
    obtain ⟨-, a, ha, hZa⟩ := Z4_eq
    obtain ⟨-, b, hb, hZb⟩ := Z6_eq
    have hab : a ≠ b := fun h => Z4_ne_Z6 (hZa.trans (h ▸ hZb.symm))
    intro i hi
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hi with rfl | rfl <;>
      first
        | exact absurd rfl hab
        | with_reducible exact Or.inl hZa.symm
        | with_reducible exact Or.inr hZb.symm
  have hZ6 : B ⊔ m24CtxE.S = Z6 → False := fun h6 => by
    have hcz : ∀ g ∈ Z6, z * g = g * z := by
      have hle : B ⊔ m24CtxE.S ≤ Subgroup.centralizer ({z} : Set G24) :=
        sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hzB b hb).symm)
          (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzc t ht).symm)
      intro g hg
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (by rw [h6]; exact hg))).symm
    exact hz1 (eq_one_of_comm_Z6 (S_le_Z6 hzS) hcz)
  have hZ4 : B ⊔ m24CtxE.S = Z4 → False := fun h4 => by
    obtain ⟨W, hWn, hW, hQ⟩ := isExt_Z4 hB h4
    have h := hcardY hW.2 ((CFSG.Timmesfeld.card_statedClassicalModel_two hQ).1 rfl)
    rw [hcardB] at h
    revert h
    decide
  rcases hj' with rfl | rfl | rfl | rfl
  · obtain ⟨W, hWn, hW, hQ⟩ := isExt_Z1 hB (hY.trans Z1_eq_Y1.2.symm)
    have h := hcardY (card_of_isE2 hW) ((CFSG.Timmesfeld.card_statedClassicalModel_two hQ).1 rfl)
    rw [hcardB] at h
    revert h
    decide
  · exact false_Z2 hB (hY.trans Z2_eq_Y2.2.symm)
  · rcases hZ46 4 (Or.inl rfl) with h | h
    · exact hZ4 (hY.trans h)
    · exact hZ6 (hY.trans h)
  · rcases hZ46 6 (Or.inr rfl) with h | h
    · exact hZ4 (hY.trans h)
    · exact hZ6 (hY.trans h)

end Z6

theorem false_of_m24_e64 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hM24 : IsSporadic .M24 ↥(⊤ : Subgroup X)) (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T)
    (hBtop : B ≠ ⊤) (hTB : T ≤ Subgroup.normalizer (B : Set X))
    (hN : IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y)) {z : X} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, z * t = t * z) (hzB : ∀ b ∈ B, z * b = b * z) : False := by
  obtain ⟨e⟩ := hM24
  let ψ : X ≃* CFSG.Quasithin.A312M24.G24 :=
    (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).trans e
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf
    (A312.isSylowTwoOf_top_map ψ.toMonoidHom ψ.surjective hT) CFSG.Quasithin.A312M24.m24_S_sylow'
  let φ : X ≃* CFSG.Quasithin.A312M24.G24 := ψ.trans (MulAut.conj g)
  have hTφ : T.map φ.toMonoidHom = CFSG.Quasithin.A312M24.m24CtxE.S := by
    rw [← hg, Subgroup.map_map]
    exact congrArg (Subgroup.map · T) (MonoidHom.ext fun _ => rfl)
  have hB' := map_mem_lFamily_equiv φ hB
  rw [hTφ] at hB'
  obtain ⟨W, hWn, hW, hQ⟩ := hN
  have hcardB : Nat.card ↥(B.map φ.toMonoidHom) = 10752 := by
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective,
      Subgroup.card_eq_card_quotient_mul_card_subgroup W, card_of_isE2 hW,
      (CFSG.Timmesfeld.card_statedClassicalModel_two hQ).1 rfl]
    decide
  have hmapT : ∀ t ∈ CFSG.Quasithin.A312M24.m24CtxE.S, ∃ t₀ ∈ T, φ t₀ = t := fun t ht => by
    rw [← hTφ] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact ⟨t₀, ht₀, rfl⟩
  refine false_of_e64_G24 hB' (map_ne_top_equiv φ hBtop) ?_ hcardB (z := φ z)
    (by rw [← hTφ]; exact ⟨z, hzT, rfl⟩) (fun h => hz1 (φ.injective (by rw [h, map_one]))) ?_ ?_
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := hmapT t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    obtain ⟨x₀, rfl⟩ := φ.surjective x
    have h := Subgroup.mem_normalizer_iff.mp (hTB ht₀) x₀
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact h
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := hmapT t ht
    rw [← map_mul, ← map_mul, hzc t₀ ht₀]
  · rintro _ ⟨b, hb, rfl⟩
    show φ z * φ b = φ b * φ z
    rw [← map_mul, ← map_mul, hzB b hb]

theorem a312ZCentM24_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    A312ZCentM24 := by
  intro X _ _ T B hcase hc
  obtain ⟨-, -, -, hT, hB, hBtop, hTB, htypes, ⟨z, hzT, hz1, hzc, hzB⟩, V, hVB, hV, hBV, hcomm,
    hV1, hcV, -⟩ := hc
  obtain ⟨hcase, hM24⟩ := hcase
  rcases hcase with h1 | h2 | h3 | h4
  · exact false_of_c14_rest hB (Or.inl h1) htypes hVB hV hBV hcomm hV1 hcV
  · exact false_of_m24_e64 hM24 hT hB hBtop hTB h2 hzT hz1 hzc hzB
  · exact false_of_c14_rest hB (Or.inr (Or.inl h3)) htypes hVB hV hBV hcomm hV1 hcV
  · exact false_of_c14_rest hB (Or.inr (Or.inr h4)) htypes hVB hV hBV hcomm hV1 hcV

end CFSG.Quasithin.Vol2.Ch10.A312A
