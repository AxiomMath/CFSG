module

public import CFSG.RankThree.PartOne.S12.Sec138LocLinear
public import CFSG.RankThree.PartOne.S12.Sec138II
public import CFSG.RankThree.PartOne.S12.L2Borel
public import CFSG.RankThree.PartOne.S12.FourCommuting
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank

@[expose] def KF134Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → RowModel p L 9 → ThreeTranspD p E →
    TransitiveD p E →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G)

namespace Sec138Loc

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kfAt_of_transitive {p : ℕ} {E : Subgroup G} {f : ℕ} {t₀ : MulAut E}
    (ht₀ : t₀ ∈ reflectionSet p E) (hK : KFAt p E f t₀) (htrans : TransitiveD p E) :
    ∀ t ∈ reflectionSet p E, KFAt p E f t := by
  intro t ht
  obtain ⟨x, hx, hxt⟩ := htrans t₀ ht₀ t ht
  obtain ⟨w, hw, hwx⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl hx)
  have h := hK.conj hw
  rw [hwx, hxt] at h
  exact h

theorem exists_odd_prime_dvd_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hpos : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (g + 1) - 1 ≠ 1 := by
    rw [pow_succ]
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨r, hr, ?_, hrd⟩
  rintro rfl
  have hodd : (2 : ℕ) ∣ 2 ^ (g + 1) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (g + 1) := Nat.one_le_two_pow
  omega

theorem no_four_of_comm {p : ℕ} {E : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (he : CFSG.twoLocalOddRank G = 3) (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    (hC : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G)) :
    ∀ a ∈ reflectionSet p E, ∀ b ∈ reflectionSet p E, ∀ c ∈ reflectionSet p E,
      ∀ d ∈ reflectionSet p E, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      a * b = b * a → a * c = c * a → a * d = d * a → b * c = c * b → b * d = d * b →
      c * d = d * c → False := by
  intro a ha b hb c hc d hd hab hac had hbc hbd hcd cab cac cad cbc cbd ccd
  obtain ⟨r, hr, hr2, hrf⟩ := exists_odd_prime_dvd_two_pow_sub_one hf
  let K : Fin 4 → Subgroup G := ![kZero p E a, kZero p E b, kZero p E c, kZero p E d]
  have hcomm : ∀ i j, i ≠ j → K i ≤ Subgroup.centralizer (K j : Set G) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hC a ha b hb hab cab
    · exact hC a ha c hc hac cac
    · exact hC a ha d hd had cad
    · exact hC b hb a ha hab.symm cab.symm
    · exact absurd rfl hij
    · exact hC b hb c hc hbc cbc
    · exact hC b hb d hd hbd cbd
    · exact hC c hc a ha hac.symm cac.symm
    · exact hC c hc b hb hbc.symm cbc.symm
    · exact absurd rfl hij
    · exact hC c hc d hd hcd ccd
    · exact hC d hd a ha had.symm cad.symm
    · exact hC d hd b hb hbd.symm cbd.symm
    · exact hC d hd c hc hcd.symm ccd.symm
    · exact absurd rfl hij
  have hU : ∀ i, ∃ U : Subgroup (K i), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ Subgroup.normalizer (U : Set (K i)), orderOf x = r ∧ ∃ u ∈ U, x * u * x⁻¹ ≠ u := by
    intro i
    fin_cases i
    · exact exists_two_subgroup_normalized_by_odd_prime (hK a ha).2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime (hK b hb).2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime (hK c hc).2.1 hr hr2 hrf
    · exact exists_two_subgroup_normalized_by_odd_prime (hK d hd).2.1 hr hr2 hrf
  have h4 : 4 ≤ RankThreeEven.localRank r G := four_le_localRank_of_commuting hr K hcomm hU
  have hrG : r ∣ Nat.card G := prime_dvd_card_of_localRank_pos hr (by omega)
  have h3 := Theta.localRank_le_twoLocalOddRank hr hr2 hrG
  omega

end Sec138Loc

theorem node138Loc_of_comm (hKFU4 : KF126U4) (hComm : KF134Comm) : Node138Loc := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA hmodel hD3 htrans
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have : IsElementaryAbelian p E := h.E_elem
  have hC := hComm G p A c L E h hF12 hF13 hT hEA hmodel hD3 htrans
  obtain ⟨hclosure, r, -, hr12, -, hrw, hr8, hr9⟩ := hF12.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hcard : Nat.card E = p ^ 4 := hr9 hr9'
  obtain ⟨f, hf1, hpf, hmod⟩ := hmodel
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have h3 := Nat.le_of_dvd (by norm_num) hpf
    norm_num at h3
    omega
  have hLcard : 1 < Nat.card (torusImage E L) := by
    interval_cases r
    · obtain ⟨e⟩ := hrw
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    · obtain ⟨e⟩ := hrw
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
      have := Nat.card_pos (α := Multiplicative (ZMod 2))
      have h24 : Nat.factorial 4 = 24 := by decide
      rw [h24]
      omega
    · obtain ⟨e⟩ := hrw
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    · obtain ⟨e⟩ := hrw
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
  obtain ⟨t₀, ht₀D, ht₀L⟩ : ∃ t ∈ reflectionSet p E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    rw [hempty, Subgroup.closure_empty] at hclosure
    rw [hclosure, Subgroup.card_bot] at hLcard
    omega
  obtain ⟨hKat, -⟩ := hKFU4 G p A c L E f h hF12 hf1 hpf hmod hcard
  have hKall := Sec138Loc.kfAt_of_transitive ht₀D (hKat t₀ ht₀D ht₀L) htrans
  exact Sec138Loc.localSThree_of_no_four hcard hp5 hD3 htrans hF13.irreducible ⟨t₀, ht₀D⟩
    (Sec138Loc.no_four_of_comm hf2 h.setup.2.2.2.2.1 hKall hC)

end CFSG.RankThree.PartOne
