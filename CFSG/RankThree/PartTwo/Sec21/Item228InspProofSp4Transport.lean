module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSp4Model
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4Transport
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four d8Comb2_four exists_conj_into_d8Tor_sp
  exists_d8ctx spRev spRevEquiv diagU_dvec4_mem_spRev d8Vec_four)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL embedOf mapL_le mapL_mono card_mapL mapL_sup
  mapL_inj mapL_perfectResidual_inf)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly (IsElemAbelian)

theorem sp4EvenTorus : Sp4EvenTorus := by
  intro G _ _ X T k hk0 hke ⟨eX⟩ hTX hTe hT9
  set K := GaloisField 2 k with hKdef
  have hK : Nat.card K = 2 ^ k := GaloisField.card 2 k hk0.ne'
  set e : X ≃* spRev K := eX.trans ((Sec4.Res417Six.projSpEquivSp K).trans (spRevEquiv K))
    with hedef
  set T₁ : Subgroup (spRev K) := (T.subgroupOf X).map e.toMonoidHom with hT₁
  have hT₁3 : ∀ x ∈ T₁, x ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hTe.2 _ (Subgroup.mem_subgroupOf.mp ht))
    rw [this, map_one]
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_two_pow_sub_one hke
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_sp Nat.prime_three (by norm_num) hdvd T₁ hT₁3
  set e' : X ≃* spRev K := e.trans (MulAut.conj g) with he'def
  have hζ := exists_primitiveRoot_three_of_dvd hdvd
  have hT4 : ∀ v : D8Mod 3 K, (CFSG.RankThree.PartOne.KFU.diagU
      (CFSG.RankThree.PartOne.KFU.d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP4 : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (CFSG.RankThree.PartOne.KFU.permGL τ : GL (Fin 4) K) ∈ spRev K :=
    fun τ hτ => CFSG.RankThree.PartOne.SP4C.hP_spRev τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four Nat.prime_three (by norm_num) hζ
    (spRev K) hT4 hP4
  have hT0card : Nat.card ((d8Tor 3 K 4).subgroupOf (spRev K)) = 3 ^ 2 :=
    SM.card_F (by norm_num) hζ
  have hT0le : d8Tor 3 K 4 ≤ spRev K := by
    rintro _ ⟨v, rfl⟩
    exact hT4 v
  have hT0card' : Nat.card (d8Tor 3 K 4) = 3 ^ 2 := by
    rw [← hT0card]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT0le).toEquiv).symm
  have hmapT : mapL e' T = d8Tor 3 K 4 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hT0card', card_mapL e' hTX, hT9])
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hg (e t) ⟨t, ht, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hmapT' : (T.subgroupOf X).map e'.toMonoidHom = (d8Tor 3 K 4).subgroupOf (spRev K) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hmapT ▸ ⟨t, ht, rfl⟩)
    · intro hx
      have hx' : (x : GL (Fin 4) K) ∈ mapL e' T := by
        rw [hmapT]
        exact Subgroup.mem_subgroupOf.mp hx
      obtain ⟨t, ht, hxt⟩ := hx'
      refine ⟨t, ht, ?_⟩
      exact Subtype.ext hxt
  have hline : ∀ ℓ : Subgroup G, ℓ ≤ T → mapL e' ℓ ≤ d8Tor 3 K 4 := fun ℓ hℓ =>
    hmapT ▸ mapL_mono e' hℓ
  have hperf : ∀ ℓ : Subgroup G, ℓ ≤ X →
      mapL e' (perfCent X ℓ) = perfCent (spRev K) (mapL e' ℓ) := fun ℓ hℓ =>
    mapL_perfectResidual_inf e' hℓ
  have hperfX : ∀ ℓ : Subgroup G, perfCent X ℓ ≤ X := fun ℓ =>
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hpairsM := model_Sp4 hk0 hke hK
  refine ⟨?_, fun ℓ₁ ℓ₂ c₁ c₂ h₁ h₂ hc₁ hc₂ h₁3 h₂3 hc₁3 hc₂3 hne hc₁S hc₂S => ?_⟩
  ·
    obtain ⟨φ₁⟩ := nonempty_starOf_mulEquiv_torusImage hTX
    obtain ⟨φ₂⟩ := Sec4.Res417Six.nonempty_autIn_mulEquiv_of_map_eq e' hmapT'
    rw [Sec4.Res417Six.autIn_eq_torusImage] at φ₂
    exact ⟨φ₁.trans (φ₂.trans (SM.weylEquiv Nat.prime_three (by norm_num) hζ))⟩
  ·
    have h₁X := h₁.trans hTX
    have h₂X := h₂.trans hTX
    have hc₁X := hc₁.trans hTX
    have hc₂X := hc₂.trans hTX
    obtain ⟨hM1, hM2⟩ := hpairsM (mapL e' ℓ₁) (mapL e' ℓ₂) (mapL e' c₁) (mapL e' c₂)
      (hline ℓ₁ h₁) (hline ℓ₂ h₂) (hline c₁ hc₁) (hline c₂ hc₂)
      (by rw [card_mapL e' h₁X, h₁3]) (by rw [card_mapL e' h₂X, h₂3])
      (by rw [card_mapL e' hc₁X, hc₁3]) (by rw [card_mapL e' hc₂X, hc₂3])
      (fun h => hne (mapL_inj e' h₁X h₂X h))
      (by rw [← hperf ℓ₁ h₁X]; exact mapL_mono e' hc₁S)
      (by rw [← hperf ℓ₂ h₂X]; exact mapL_mono e' hc₂S)
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨hc₂ℓ₁, hcomm⟩ := hM1 (by rw [hc])
      refine ⟨mapL_inj e' hc₂X h₁X hc₂ℓ₁, ?_⟩
      refine commutator_eq_bot_of_mapL e' (hperfX ℓ₁) (hperfX ℓ₂) ?_
      rw [hperf ℓ₁ h₁X, hperf ℓ₂ h₂X]
      exact hcomm
    · have h := hM2 fun h => hc (mapL_inj e' hc₁X h₂X h)
      refine mapL_inj e' (sup_le (hperfX ℓ₁) (hperfX ℓ₂)) le_rfl ?_
      rw [mapL_sup e' (hperfX ℓ₁) (hperfX ℓ₂), hperf ℓ₁ h₁X, hperf ℓ₂ h₂X, h, mapL_self]

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
