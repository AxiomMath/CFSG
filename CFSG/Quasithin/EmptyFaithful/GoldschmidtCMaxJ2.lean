module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxCen
public import CFSG.CGT.T75E.J2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2Check

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.J2Cover
  CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
  CFSG.Sporadic.Schreier
open CFSG.Blueprint.NativeSporadic (Carrier)

namespace GoldCMaxA

theorem j2_sylow_data :
    ∃ S : Subgroup XJ, Nat.card S = 2 ^ 7 ∧
      ∃ z : XJ, orderOf z = 2 ∧ centerOf S = Subgroup.zpowers z := by
  classical
  obtain ⟨hs0len, hs0sort, hs01, hs0gen, hs0pow⟩ := s0_facts
  obtain ⟨hA1len, -, -, -, -⟩ := a_facts
  have hsub0 := closureListH_subset tabX tabX_eq hkey s0gen 40
  have hS0nd : S0X.Nodup := nodup_of_strictAsc enc S0X hs0sort
  have hS0gen' : ∀ x ∈ S0X, ∀ g ∈ s0gen, x * g ∈ S0X := fun x hx g hg =>
    (mem_map_enc enc_injective).1 (hs0gen x hx g hg)
  set S₀ : Subgroup XJ := Subgroup.closure {g | g ∈ s0gen} with hS₀def
  have hS₀ : ∀ x, x ∈ S₀ ↔ x ∈ S0X := subgroupOfGens_exists s0gen S0X hsub0 hs01 hS0gen'
  have hS₀card : Nat.card ↥S₀ = 128 := by rw [card_of_list hS0nd hS₀, hs0len]
  have hS₀2 : IsPGroup 2 S₀ := by
    intro g
    exact ⟨3, Subtype.ext (hs0pow _ ((hS₀ _).1 g.2))⟩
  have hA₁ : ∀ y, y ∈ canonZ S₀ ↔ y ∈ A1X := by
    intro y
    rw [mem_canonZ, hS₀]
    simp only [A1X, List.mem_filter, List.all_eq_true, beq_iff_eq]
    refine and_congr_right fun hyS => ?_
    constructor
    · intro h s hs
      have hsS : s ∈ S₀ := Subgroup.subset_closure hs
      have := h s hsS
      rw [this]
    · intro h
      have hcomm : ∀ g ∈ s0gen, y * g = g * y := fun g hg => by
        have := h g hg
        exact (enc_injective this).symm
      have hle : S₀ ≤ Subgroup.centralizer {y} := by
        rw [hS₀def, Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h' hh'
        rw [Set.mem_singleton_iff] at hh'
        rw [hh']
        exact hcomm g hg
      intro s hs
      have := Subgroup.mem_centralizer_iff.1 (hle hs) y rfl
      exact this.symm
  have hA1nd : A1X.Nodup := hS0nd.filter _
  have h1A : (1 : XJ) ∈ A1X :=
    (hA₁ 1).1 (mem_canonZ.2 ⟨S₀.one_mem, fun s _ => by rw [mul_one, one_mul]⟩)
  obtain ⟨a₁, a₂, hl⟩ := List.length_eq_two.1 hA1len
  rw [hl] at hA1nd h1A
  have hne : a₁ ≠ a₂ := by simpa using hA1nd
  have hz : ∃ z : XJ, ∀ c ∈ A1X, c = 1 ∨ c = z := by
    rw [hl]
    rcases List.mem_pair.1 h1A with h | h
    · refine ⟨a₂, fun c hc => ?_⟩
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact Or.inl h.symm
      · exact Or.inr rfl
    · refine ⟨a₁, fun c hc => ?_⟩
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl h.symm
  obtain ⟨z, hz⟩ := hz
  have hnt : Nontrivial ↥S₀ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS₀card]; norm_num)
  have hc : ∀ c ∈ S₀, (∀ q ∈ S₀, c * q = q * c) → c = 1 ∨ c = z := fun c hcS hcc =>
    hz c ((hA₁ c).1 (mem_canonZ.2 ⟨hcS, fun s hs => (hcc s hs).symm⟩))
  exact ⟨S₀, by rw [hS₀card]; norm_num, z, cmax_center_eq_zpowers hS₀2 hnt hc⟩

theorem j2_centMaxProp_of_data
    {Γ : Type} [Group Γ] [Finite Γ] (φ : Γ ≃* ↥P) {S : Subgroup Γ} {z : Γ}
    (hScard : Nat.card S = 2 ^ 7) (hΓ : Nat.card Γ = 604800) (hz2 : orderOf z = 2)
    (hZ : centerOf S = Subgroup.zpowers z) : CentMaxProp Γ := by
  have hS2 : IsPGroup 2 ↥S := IsPGroup.of_card hScard
  have hSi : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hScard, hΓ] at h1
    have h2 : S.index = 4725 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    norm_num
  have hd := Subgroup.card_dvd_of_le (cmax_le_centralizer_of_center hZ)
  rw [hScard] at hd
  have hτ2 : orderOf ((φ z : ↥P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz2]
  obtain ⟨r, hr, c, hc, hτ⟩ := (inner_classes).1 _ (φ z).2 hτ2
  have hcard : Nat.card (Subgroup.centralizer ({z} : Set Γ)) =
      Nat.card (centralizerIn P r) := by
    rw [cmax_card_centralizer_equiv φ z,
      CFSG.ComponentClassification.M12Cover.card_centralizer_eq_centralizerIn P (φ z), hτ]
    exact (Nat.card_congr
      (CFSG.ComponentClassification.M12Cover.centralizerInConjEquiv P hc r).toEquiv).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    rw [hcard, (inner_classes).2.2.1, (cent2B_facts).2.1] at hd
    omega
  · have hφ : φ z = (⟨c, hc⟩ : ↥P) * CFSG.CGT.T75E.tP * (⟨c, hc⟩ : ↥P)⁻¹ := Subtype.ext hτ
    have hmax := cmax_isMaxSubgroupIn_centralizer_of_equiv φ (t := z)
      (by rw [hφ]; exact CFSG.CGT.T75E.isCoatom_centralizer_conj_tP ⟨c, hc⟩)
    exact centMaxProp_of_data hS2 hSi hz2 hZ hmax

theorem j2_centMaxProp :
    CentMaxProp XJ := by
  obtain ⟨S, hScard, z, hz2, hZ⟩ := j2_sylow_data
  exact j2_centMaxProp_of_data (MulEquiv.subgroupCongr PC_eq) hScard card_PC hz2 hZ

end GoldCMaxA

open GoldCMaxA in
theorem centMax_j2 :
    ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
      IsSporadic .J2 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
        IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  intro Q _ _ P hP2 hPi ⟨e⟩ W hW hW0
  exact (j2_centMaxProp.of_mulEquiv
    (((MulEquiv.subgroupCongr PC_eq).trans nativeEquivP.symm).trans e.symm)) P hP2 hPi W hW hW0

end CFSG.Quasithin
