module

public import CFSG.Quasithin.H13.A6S1372L74g
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.H13.A6S1372L74a
public import CFSG.Quasithin.H13.A6S1372L74d
public import CFSG.Quasithin.H13.A6S1372L74f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1374One_of (hDiag : Lem1374OneDiag)
    (hOdd : Lem1374OneOdd) (hFinal : Lem1374OneFinal) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (h139 : Stmt13_3_9) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h1352 : Stmt13_5_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hF : A318Facts) (h36 : A36ForSQTK) : Lem1374One := by
  intro G _ _ T L V S hNS hNU hhat H hH hab h hh hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hhQ
  have hCQ : ¬ S.C74 H ≤ pCoreOf 2 H := fun hle => hhQ (hle ((S.mem_C74_iff).2 ⟨hh, hcomm⟩))
  have hL1C := Setting4.not_L1_le_C74 hNS h13315 h1356two hH h13314 hhat
  have hKCc : ∀ {K : Subgroup G}, K ≤ S.C74 H → ∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
      k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    fun hKC k hk => ((S.mem_C74_iff).1 (hKC hk)).2
  rcases A6L74.exists_comp_or_odd_of_le (Setting4.QH_le_C74 hNS h13315 h1356two hH)
      (S.C74_le H) (S.le_normalizer_C74 H) hCQ with ⟨K, hKc, hKC, hKQ⟩ |
      ⟨p, hp, hp2, K₁, hQK₁, hK₁C, hHK₁, hK₁Q, hexp, hcomm₁, hmin⟩
  ·
    have hKH : K ≤ H := le_of_mem_cComp hKc
    have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
    have hK2 : oTwoRes K = K := by
      rw [oTwoRes_eq_oTwoUpper]
      exact (eq_oTwoUpper_of_perfect hperf).symm
    have hKU := Setting4.not_le_centralizer_U0 hNS h13315 h1356two hH hab hKC hK2 hKQ
    have hLf := Setting4.isFaithfulLocal_of_cComp hNS h13315 h1356two hH hab hKc hKU
    obtain ⟨hlist, ⟨hTK, -⟩, -⟩ := h1352 G T L S.h13 hNS K hLf
    have hHK := Setting4.le_normalizer_of_T_le hH h37 h38 hKc hTK
    have hL1K : ¬ S.L1 ≤ K := fun hle => hL1C (hle.trans hKC)
    have hKM := Setting4.not_le_normalizer_L hH h139 hhat hKH hHK hK2
      (ne_bot_of_mem_cComp hKc) hL1K
    have h52 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 := by
      rcases hlist with h1 | h1 | h1 | ⟨hP, hZ, hE⟩
      · exact Or.inl h1
      · exact Or.inr h1
      · obtain ⟨E⟩ := h1
        exact absurd (S.L1_le_of_quotEquiv hF h36 h38 hH hKc E a318Exclusion_alt6) hL1K
      · exact absurd (Setting4.L1_le_of_hat hNS h13315 h1356two hH hF h36 h38 hhat hKc hHK hP
          hZ hE) hL1K
    have hKU' := Setting4.inf_centralizer_U0_le_of_simple hKH hHK
      (A6L74.isSimpleGroup_of_a5_or_l32 h52) hKU
    have hB := Setting4.not_isA6Block_of hNS h13315 h1356two hH h1222 h323 h13314 hhat hab hKH
      hHK hK2 hKC hKU' hKM
    by_cases hc : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K
    · exact hFinal G T L V S hNS hNU hhat H hH hab hB K hKH hHK hK2 (hKCc hKC) hKU hKU' hKM
        hL1K hc (Or.inr h52)
    · exact hDiag G T L V S hNS hNU hhat H hH hab hB K hKc hHK h52 hL1K hc
  ·
    obtain ⟨hKH, hHK, hK2, hKC, hKQ, hexpK, hcommK, hminK⟩ :=
      Setting4.pCase (S.C74_le H) hp hp2 hQK₁ hK₁C hHK₁ hK₁Q hexp hcomm₁ hmin
    have hKU := Setting4.not_le_centralizer_U0 hNS h13315 h1356two hH hab hKC hK2 hKQ
    have hKU' := Setting4.inf_centralizer_U0_le_of_minimal (S := S) hKH hHK hminK hKU
    have hL1K : ¬ S.L1 ≤ oTwoRes K₁ := fun hle => hL1C (hle.trans hKC)
    have hK1 : oTwoRes K₁ ≠ ⊥ := fun h1 => hKQ (h1 ▸ bot_le)
    have hKM := Setting4.not_le_normalizer_L hH h139 hhat hKH hHK hK2 hK1 hL1K
    have hB := Setting4.not_isA6Block_of hNS h13315 h1356two hH h1222 h323 h13314 hhat hab hKH
      hHK hK2 hKC hKU' hKM
    obtain ⟨-, h3⟩ := hOdd G T L V S hNS hNU hhat H hH hab hB p hp hp2 (oTwoRes K₁) hKH hHK hK2
      (hKCc hKC) hKU hKU' hKM hL1K hexpK hcommK hminK
    exact hFinal G T L V S hNS hNU hhat H hH hab hB (oTwoRes K₁) hKH hHK hK2 (hKCc hKC) hKU hKU'
      hKM hL1K (Setting4.comm_L1_mem_of_card_three hH hHK h3) (Or.inl h3)

end CFSG.Quasithin.H13.A6
