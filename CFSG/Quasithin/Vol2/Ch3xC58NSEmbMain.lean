module

public import CFSG.Quasithin.Vol2.Ch3xC58NSInputs
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbPU
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbCount
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbAlt7

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

theorem embedLocal_of_b113 (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (hodd : AltEvenExcluded) (hMB : MinParabolicBlocks)
    (hB42 : ∀ (G : Type) [Group G] [Finite G], L238.AltBlockStatementJCat (G := G))
    (h38 : Vol2Native.A38ForSQTKCat) : EmbedLocal := by
  intro G _ _ hsimple hnonab hqtke T K₁ N₁ t x _ hshort htyp _ _ _ _ _ hcharP ⟨M, hmin⟩ hNC _ _ _
    hT₁N₁ _ _ _ _ _ hXc hsylX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set X := N₁ ⊔ K₁ with hX
  set P := K₁ ⊔ T₁ with hP
  have hT₁K : T₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  have hKX : K₁ ≤ X := le_sup_right
  have hT₁X : T₁ ≤ X := hT₁N₁.trans le_sup_left
  have hPX : P ≤ X := sup_le hKX hT₁X
  have hTP : T₁ ≤ P := le_sup_right
  have hT₁2 : IsPGroup 2 T₁ := hsylX.2.1
  have hO2 : pCoreOf 2 X ≠ ⊥ := by
    intro h
    apply L238.not_isPGroup_two_of_isShort2 hshort
    have hXb : X ≤ ⊥ := by
      rw [← h]
      refine le_trans (le_inf le_rfl fun y _ => ?_) hXc
      rw [h, mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, mem_bot] at hz
      rw [hz, one_mul, mul_one]
    have hK1 : K₁ = ⊥ := le_bot_iff.mp (hKX.trans hXb)
    rw [hK1]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hSQ : IsSQTKTC X :=
    ⟨kGroup_of_pCoreOf_ne_bot hqtke hsimple hnonab hO2,
      stronglyQuasithin_of_pCoreOf_ne_bot hqtke hO2⟩
  have hSQX : CFSG.SectionRank.IsSQTKCat ↥X := by
    obtain ⟨h1, h2⟩ := C1GN.isSQTKTC_iff_sqtkGroup.mp hSQ
    exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr h1, h2⟩
  have h38X : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
    h38 _ (Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQX)
  have hKP : (K₁.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hT₁K)
  have hK : IsChi0Block P K₁ := by
    refine ⟨⟨hshort, le_sup_left, hKP.isSubnormal⟩, ?_⟩
    rcases htyp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hnc := Emb.noCharNormal_of_noCommonNormal hNC
  have hobs := Emb.pushUpObstruction_of hmin hcharP hPX hSQX hnc
  have hKJ := Emb.commutator_thompsonJ_eq_of_minParabolicBlocks hMB hshort hT₁K hobs
  have S : L246C127.Setting X T₁ P K₁ := ⟨hXc, hsylX, hPX, hTP, hK.1⟩
  have hKZ := Emb.not_le_centralizer_omega_of_noCharNormal hT₁2 S.T_ne_bot hnc
  have hV : IsElemAbelian 2 (VZ T₁ X) := S.hred.2.2.1
  have hN : X ⊓ normalizer (T₁ : Set G) ≤ normalizer (T₁ : Set G) := inf_le_right
  rcases L246C127.Emb.block_or_alt7 h113 hodd hXc hsylX hSQX hPX hTP hK htyp hKJ hKZ hV with
    hB | ⟨L, hL, hKL, hULV, -, ⟨eL⟩, ⟨eK⟩, hsylL⟩
  ·
    have h3 : 3 ∣ Nat.card K₁ :=
      C1GN.three_dvd_card_of_isChiBlock (C1GN.isChiBlock_of_isChi0Block hB hK)
    have hsylN : IsSylowTwoOf T₁ (X ⊓ normalizer (T₁ : Set G)) :=
      C1GN.isSylowTwoOf_of_le hsylX (le_inf hT₁X le_normalizer) inf_le_left
    have hNK := Emb.le_normalizer_of_isBlock2 hXc hSQ hB h3 inf_le_left hsylN hT₁K
    exact fun n hn => C1.mem_normalizer_blockU (hNK hn)
  ·
    exact L246C127.Emb.le_normalizer_blockU_of_alt7 (hB42 G) hXc hsylX hSQX h38X hPX hTP hK hKJ
      hKZ hV hL hKL hULV eL eK hsylL inf_le_left hN hT₁K

end CFSG.Quasithin.C58NS
