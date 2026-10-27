module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHS
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDA6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.QuasithinUnique.Vol2Native.L239

namespace GoldCMaxA

theorem hs_sylow_data :
    ∃ S : Subgroup (J hsData), Nat.card S = 2 ^ 9 ∧
      ∃ z : J hsData, orderOf z = 2 ∧ centerOf S = Subgroup.zpowers z := by
  have hc := cmax_center_of_baseCertS (n := hsData.n) hsB (base_lt hs_facts)
    (base_property hs_facts) (a hsData) (b hsData) hsProg hs_valid hsQp 164 202 206 204 208
    hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 hs_cert'
  have hcard := (CFSG.QuasithinUnique.Ch1.SporLat.sGens_of_baseCertS (n := hsData.n) hsB
    (base_lt hs_facts) (base_property hs_facts) (a hsData) (b hsData) hsProg hs_valid hsQp 164 202
    206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 hs_cert').2
  exact ⟨_, hcard, _, cmax_center_eq_zpowers (IsPGroup.of_card hcard)
    (Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)) hc⟩

theorem hs_centMaxProp_of_data
    {Γ : Type} [Group Γ] [Finite Γ]
    (e : Γ ≃* Carrier .HS) {S : Subgroup Γ} {z : Γ} (hScard : Nat.card S = 2 ^ 9)
    (hΓ : Nat.card Γ = 2 ^ 9 * 86625) (hz2 : orderOf z = 2)
    (hZ : centerOf S = Subgroup.zpowers z) : CentMaxProp Γ := by
  have hS2 : IsPGroup 2 ↥S := IsPGroup.of_card hScard
  have hSi : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hScard, hΓ] at h1
    have h2 : S.index = 86625 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    norm_num
  have hSsyl : IsSylowTwoOf S ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩
  have hC : Nat.card (Subgroup.centralizer ({z} : Set Γ)) = 7680 := by
    have hd := Subgroup.card_dvd_of_le (cmax_le_centralizer_of_center hZ)
    rw [hScard] at hd
    rcases CFSG.ComponentClassification.HSFLit.card_centralizer_of_HS e hz2 with h | h
    · exact h
    · rw [h] at hd
      omega
  refine cmax_centMaxProp_of_lattice hS2 hSi hz2 hZ [512, 7680, 10752, 1536] ?_ ?_ ?_
  · intro K hSK
    rcases hs_overgroups ⟨e⟩ hSsyl hSK with h | ⟨m, hm, hcard, -, -⟩
    · exact Or.inl h
    · right
      simp only [hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp [hcard]
  · intro m hm hd
    rw [hC] at hd ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega
  · rw [hC, hΓ]
    omega

theorem hs_centMaxProp :
    CentMaxProp (J hsData) := by
  obtain ⟨S, hScard, z, hz2, hZ⟩ := hs_sylow_data
  obtain ⟨e⟩ := HSPairs.hs_equiv
  exact hs_centMaxProp_of_data e.symm hScard hs_card hz2 hZ

end GoldCMaxA

open GoldCMaxA in
theorem centMax_hs :
    ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
      IsSporadic .HS Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
        IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  intro Q _ _ P hP2 hPi ⟨e⟩ W hW hW0
  obtain ⟨eJ⟩ := HSPairs.hs_equiv
  exact (hs_centMaxProp.of_mulEquiv (eJ.symm.trans e.symm)) P hP2 hPi W hW hW0

end CFSG.Quasithin
