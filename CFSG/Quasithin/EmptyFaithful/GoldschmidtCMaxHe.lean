module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.HeldB
open CFSG.Blueprint.NativeSporadic (Carrier)

namespace GoldCMaxA

theorem he_card_centralizer
    {Γ : Type} [Group Γ] (φ : Γ ≃* ↥heP) {t : Γ} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set Γ)) = 161280 ∨
      Nat.card (Subgroup.centralizer ({t} : Set Γ)) = 21504 := by
  have hτ2 : orderOf ((φ t : ↥heP) : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  rw [cmax_card_centralizer_equiv φ t, Nat.card_congr (heCentralizerEquiv (φ t)).toEquiv]
  rcases involution_conj_cases (φ t).2 hτ2 with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
  · left
    rw [hgx]
    exact (Nat.card_congr (infCentralizerConjEquiv hg _).toEquiv).trans card_heP_cent0
  · right
    rw [hgx]
    exact (Nat.card_congr (infCentralizerConjEquiv hg _).toEquiv).trans card_heP_cent1

theorem he_sylow_data :
    ∃ S : Subgroup CFSG.Sporadic.He.J, Nat.card S = 2 ^ 10 ∧
      ∃ z : CFSG.Sporadic.He.J, orderOf z = 2 ∧ centerOf S = Subgroup.zpowers z := by
  have hc := cmax_center_of_baseCertS (n := 8330) heB he_base_lt he_base_property
    CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg he_valid heQp 170 249 253 251 255
    heEnum.1 heEnum.2.1 heEnum.2.2 10 he_cert'
  have hcard := (CFSG.QuasithinUnique.Ch1.SporLat.sGens_of_baseCertS (n := 8330) heB
    he_base_lt he_base_property CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg he_valid heQp 170 249
    253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 he_cert').2
  exact ⟨_, hcard, _, cmax_center_eq_zpowers (IsPGroup.of_card hcard)
    (Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)) hc⟩

theorem he_centMaxProp_of_data
    {Γ : Type} [Group Γ] [Finite Γ] (e : Γ ≃* Carrier .He) (φ : Γ ≃* ↥heP) {S : Subgroup Γ}
    {z : Γ} (hScard : Nat.card S = 2 ^ 10) (hΓ : Nat.card Γ = 2 ^ 10 * 3935925)
    (hz2 : orderOf z = 2) (hZ : centerOf S = Subgroup.zpowers z) : CentMaxProp Γ := by
  have hS2 : IsPGroup 2 ↥S := IsPGroup.of_card hScard
  have hSi : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hScard, hΓ] at h1
    have h2 : S.index = 3935925 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    norm_num
  have hSsyl : IsSylowTwoOf S ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hS2, hSi⟩
  have hC : Nat.card (Subgroup.centralizer ({z} : Set Γ)) = 21504 := by
    have hd := Subgroup.card_dvd_of_le (cmax_le_centralizer_of_center hZ)
    rw [hScard] at hd
    rcases he_card_centralizer φ hz2 with h | h
    · rw [h] at hd
      omega
    · exact h
  refine cmax_centMaxProp_of_lattice hS2 hSi hz2 hZ [1024, 3072, 9216, 138240, 21504] ?_ ?_ ?_
  · intro K hSK
    rcases he_overgroups ⟨e⟩ hSsyl hSK with h | ⟨m, hm, hcard, -, -⟩
    · exact Or.inl h
    · right
      simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hcard]
  · intro m hm hd
    rw [hC] at hd ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [hC, hΓ]
    omega

theorem he_centMaxProp :
    CentMaxProp CFSG.Sporadic.He.J := by
  obtain ⟨S, hScard, z, hz2, hZ⟩ := he_sylow_data
  exact he_centMaxProp_of_data CFSG.Sporadic.He.heEquivJ.symm heJEquivP hScard he_card hz2 hZ

end GoldCMaxA

open GoldCMaxA in
theorem centMax_he :
    ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
      IsSporadic .He Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
        IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  intro Q _ _ P hP2 hPi ⟨e⟩ W hW hW0
  exact (he_centMaxProp.of_mulEquiv (e.trans CFSG.Sporadic.He.heEquivJ).symm) P hP2 hPi W hW hW0

end CFSG.Quasithin
