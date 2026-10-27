module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338
public import CFSG.Quasithin.Background.F918F3
public import CFSG.Quasithin.EmptyFaithful.LRed4Alt

public section

namespace CFSG.Quasithin.H13.Ln2

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem b51Hyp_of
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      B51Hyp (ffJ (autOn (L ⊔ T) (vPlus L T))) (autOn L (vPlus L T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨hVc, hFF⟩ := h.isFFModule h38 h39
  refine ⟨hVc, ?_⟩
  set V := vPlus L T with hVdef
  set Mp := mPlus L T with hMpdef
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) V) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  have hMH : Mp ≤ L ⊔ T := by
    rw [hMpdef, ← conjClosure_sup_eq]
    exact le_sup_left
  have hHM : L ⊔ T ≤ Subgroup.normalizer (Mp : Set G) := sup_le_normalizer_conjClosure L T
  have hMV : Mp ≤ Subgroup.normalizer (V : Set G) := hMH.trans hHV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hMpT : Mp ⊔ T = L ⊔ T := conjClosure_sup_eq L T
  obtain ⟨hKX, hXK, h2X, -⟩ := h.autOn_data
  set K := autOn Mp V with hKdef
  set X := autOn (L ⊔ T) V with hXdef
  have hOK : pCoreOf 2 K = ⊥ := le_bot_iff.mp (hO2 ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K X hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK))
  have hKL : K = autOn L V := by rw [hKdef, hMp]
  have hLV' : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have hq : CFSG.IsQuasisimple ↥K := by
    rw [hKL]
    rw [hKL] at hOK
    exact InternalSec.isQuasisimple_autOn hLV' h.Lq hOK (h.not_L_le_centralizer h38 h39)
  have hS : SQTKGroup ↥K := sqtkGroup_autOn
    (sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.toSetup331.pCoreOf_ne_bot)
    hMH hMV hq
  obtain ⟨A, hA⟩ := ((B1_4_5 hV2 X).out 1 2).1 hFF
  have hKA : ⁅K, A⁆ = K := Ch3Sec3.commutator_eq_of_two hXK h2X hO2 hq hA.1 hA.2.1
    fun a ha => hA.2.2.1.2 a ha
  have h2' : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ Mp ⊔ Subgroup.centralizer (V : Set G) := by
    intro y hy
    rw [← hMpT] at hy
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 (le_normalizer_conjClosure_right L T) y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  obtain ⟨hB51, -⟩ := InternalSec.b51Hyp_ffJ_autOn hHV hMH hHM h2' hO2 hq hS hA hKA
  have hKL' : autOn Mp V = autOn L V := hKL
  rw [hKL'] at hB51
  exact hB51

theorem card_specialLinear (n : ℕ) (hn : n = 4 ∨ n = 5) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = if n = 4 then 20160 else 9999360 := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rcases hn with rfl | rfl
  · rw [← Nat.card_congr (statedSLEquivZModTwo (n := 4) h2).toEquiv, card_statedSL_four_zmod1527d]
    rfl
  · rw [← Nat.card_congr (statedSLEquivZModTwo (n := 5) h2).toEquiv, card_statedSL_five_zmod1527d]
    rfl

theorem false_of_surjective {m n : ℕ} (hm : m = 4 ∨ m = 5) (hn : n = 4 ∨ n = 5) (hmn : m ≠ n)
    {K : Type} [Group K] [Finite K]
    (hK : Nat.card K = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    (π : ↥(StatedSL m (ZMod 2)) →* K) (hπ : Function.Surjective π) : False := by
  rw [card_specialLinear n hn] at hK
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · exact hmn rfl
  · have h1 := Nat.card_le_card_of_surjective π hπ
    rw [card_statedSL_four_zmod1527d, hK] at h1
    norm_num at h1
  · exact LRed4.no_epi_sl5 hK π hπ
  · exact hmn rfl

theorem commV_autOn_eq (h : Hyp331 G T M L D) [IsMulCommutative ↥(vPlus L T)] :
    commV (autOn L (vPlus L T)) = commVPlus L T L := by
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    le_sup_left.trans (Hyp331.vPlus_reduced h.toSetup331).2.2.2.1
  apply Subgroup.map_injective (vPlus L T).subtype_injective
  rw [map_commV_autOn hLV, Subgroup.map_subgroupOf_eq_of_le
    (commutator_le_left_of_le_normalizer hLV)]

theorem module_cases
    (h18 : Stmt3_3_18) (h51 : AsB51) (hI16 : AsI16Cover) (h : Hyp331 G T M L D)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      B51Hyp (ffJ (autOn (L ⊔ T) (vPlus L T))) (autOn L (vPlus L T)) ∧
      ((∃ Z : Subgroup ↥(vPlus L T),
          Z ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) ∧ Nat.card ↥Z ≤ 2 ∧
          (n = 5 → Z = ⊥) ∧
          SLExteriorTwo (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) Z n) ∨
        SumNatDual (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) n) := by
  obtain ⟨hVc, hB⟩ := b51Hyp_of h h38 h39 hTL
  refine ⟨hVc, hB, ?_⟩
  set K := autOn L (vPlus L T) with hKdef
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hn3 : 3 ≤ n := by omega
  have hK : IsPSL n 2 1 ↥K :=
    LRed4.isPSL_two_of_statedSL' hn3 (e.trans (statedSLEquivZModTwo (n := n) h2).symm)
  have hcard : Nat.card ↥K = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hV2 : ∀ v : ↥(vPlus L T), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hA := alt15127_of_b51 h51 hI16 asI16CoverA8_of hV2 hB
    (by rcases hn with rfl | rfl; exacts [Or.inl hK, Or.inr hK])
  rcases hA with ⟨Z, hZ, hZ2, hext⟩ | hext | ⟨n', hsnd⟩ | ⟨n', hn', k, hk1, -, hDS⟩
  ·
    obtain ⟨π, hπ⟩ := hext
    by_cases h4 : n = 4
    · subst h4
      exact Or.inl ⟨Z, hZ, hZ2, fun h5 => absurd h5 (by norm_num), π, hπ⟩
    · exact (false_of_surjective (Or.inl rfl) hn (Ne.symm h4) hcard π hπ.1).elim
  ·
    obtain ⟨π, hπ⟩ := hext
    by_cases h5 : n = 5
    · subst h5
      exact Or.inl ⟨⊥, bot_le, by rw [Subgroup.card_bot]; norm_num, fun _ => rfl, π, hπ⟩
    · exact (false_of_surjective (Or.inr rfl) hn (Ne.symm h5) hcard π hπ.1).elim
  ·
    by_cases hnn : n' = n
    · subst hnn
      exact Or.inr hsnd
    · obtain ⟨hn'', π, U₁, U₂, -, hR, -⟩ := hsnd
      exact (false_of_surjective hn'' hn hnn hcard π hR.1).elim
  ·
    by_cases hnn : n' = n
    · subst hnn
      exfalso
      obtain ⟨_, h18'⟩ := h18 G T M L D h n' hn ⟨e⟩
      apply h18'
      refine ⟨k, hk1, ?_⟩
      rw [← commV_autOn_eq h]
      exact hDS
    · obtain ⟨I, π, -, -, -, hR⟩ := hDS
      exact (false_of_surjective hn' hn hnn hcard π (hR ⟨0, hk1⟩).1).elim

end CFSG.Quasithin.H13.Ln2
