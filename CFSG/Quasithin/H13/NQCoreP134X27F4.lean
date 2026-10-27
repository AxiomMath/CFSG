module

public import CFSG.Quasithin.H13.NQCoreP134X27Borel
public import CFSG.Quasithin.Vol2.F134LieF4Borel
public import CFSG.LieType.BorelTits.Ree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Elem
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Embed
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5

public section

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieF4 CFSG.Quasithin.H13.NQCore

namespace CFSG.Quasithin.H13.NQCore.X27F4

theorem le_normalizer_of_card_eq27
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) {S H : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hSH : S ≤ H) (hH : Nat.card H = 27 * Nat.card S) :
    H ≤ Subgroup.normalizer (S : Set X) := by
  obtain ⟨b, K, _, _, _, φ, hb, hn, hK, hφi, hφr, hφS⟩ := F4.exists_embedding hX hS
  have hK' : Nat.card K = 2 ^ (2 * b + 1) := hn ▸ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hU' : IsSylowOf 2 S ⊤ := isSylowTwoOf_iff_isSylowOf.1 hS
  obtain ⟨E₀, hE₀U, hE₀2, hE₀c⟩ := F4.exists_elementaryAbelian_reeFixedPosUnipotent (a := b) hK'
  have hq8 : 8 ≤ Nat.card K := by
    rw [hK']
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE₀Γ : E₀ ≤ φ.range := hφr ▸ hE₀U.trans reeFixedPosUnipotent_le_reeGamma
  have hES : E₀.comap φ ≤ S := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ : φ x ∈ S.map φ := hφS ▸ hE₀U hx
    rwa [← hφi hsx]
  have hEcard : Nat.card (E₀.comap φ) = Nat.card E₀ := by
    rw [← Subgroup.card_map_of_injective hφi, Subgroup.map_comap_eq_self hE₀Γ]
  have hE2 : ∀ x ∈ E₀.comap φ, x ^ 2 = 1 := fun x hx => hφi (by
    rw [map_pow, map_one]
    exact hE₀2 _ hx)
  have hE16 : 16 ≤ Nat.card (E₀.comap φ) := by
    rw [hEcard]
    calc 16 ≤ 8 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq8 2
      _ ≤ Nat.card E₀ := hE₀c
  have hBT : CFSG.LieType.BorelTits.Holds X 2 :=
    CFSG.LieType.BorelTits.holds_of_reeTitsModel hX (by decide)
  obtain ⟨m, hm⟩ : ∃ m, Nat.card S = 2 ^ m := (IsPGroup.iff_card).1 hS.2.1
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := CFSG.Quasithin.H13.NQCore.S5.exists_proper_overgroup hBT hU' hSH
    (hES.trans hSH) hE2 hE16 Nat.prime_three (by norm_num) (m := m) (a := 3)
    (by rw [hH, hm, mul_comm]; norm_num) le_rfl
  have hBQ : F4.reeFixedBorel K b ≤ Q.map φ := by
    intro y hy
    obtain ⟨x, rfl⟩ : y ∈ φ.range := hφr ▸ reeFixedBorel_le_reeGamma hy
    exact ⟨x, hNQ ((F4.mem_normalizer_iff_mem_reeFixedBorel hφi hφr hφS x).2 hy), rfl⟩
  have hQΓ : Q.map φ ≤ F4.reeGamma K b := hφr ▸ Subgroup.map_le_range φ Q
  have hQne : Q.map φ ≠ F4.reeGamma K b := by
    intro h
    apply hQ
    apply Subgroup.map_injective hφi
    rw [h, ← MonoidHom.range_eq_map, hφr]
  obtain ⟨i, hi⟩ := exists_le_reeLocalParabolic hBQ hQΓ hQne
  have hUH : F4.reeFixedPosUnipotent K b ≤ H.map φ := hφS ▸ Subgroup.map_mono hSH
  rcases le_reeFixedBorel_or_dvd ((Subgroup.map_mono hHQ).trans hi) hUH with hB | hdvd
  · exact fun h hh => (F4.mem_normalizer_iff_mem_reeFixedBorel hφi hφr hφS h).2 (hB ⟨h, hh, rfl⟩)
  exfalso
  have hcardH : Nat.card (H.map φ) = 27 * Nat.card (F4.reeFixedPosUnipotent K b) := by
    rw [Subgroup.card_map_of_injective hφi, hH, ← hφS, Subgroup.card_map_of_injective hφi]
  have hrel : (F4.reeFixedPosUnipotent K b).relIndex (H.map φ) = 27 := by
    have hcardH : Nat.card (H.map φ) = 27 * Nat.card (F4.reeFixedPosUnipotent K b) := by
      rw [Subgroup.card_map_of_injective hφi, hH, ← hφS, Subgroup.card_map_of_injective hφi]
    have h := Subgroup.relIndex_mul_card (F4.reeFixedPosUnipotent K b) (H.map φ)
    rw [inf_eq_left.2 hUH, hcardH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hrel] at hdvd
  have hHP := (Subgroup.map_mono hHQ).trans hi
  obtain ⟨i, hi2⟩ := i
  have hi2' : i < 2 := hi2
  interval_cases i
  · rw [card_reeFixedOrbitUnipotent_zero hK', hK'] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain rfl : b = 1 := by
      by_contra hb1
      have : 2 ^ 5 ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hK8 : Nat.card K = 8 := hK'
    have hK3 : Nat.card K % 3 = 2 := by rw [hK8]
    have hBP : F4.reeFixedBorel K 1 ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩ :=
      reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
    have hidx : (F4.reeFixedBorel K 1).relIndex (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) =
        9 := by
      rw [← ncard_image_coset_eq_relIndex]
      change (F4.reeLocalCosets K 1 ⟨0, by decide⟩).ncard = 9
      rw [ncard_reeLocalCosets, card_reeFixedOrbitUnipotent_zero hK', hK8]
    have hcardP₀ : Nat.card (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) =
        9 * Nat.card (F4.reeFixedBorel K 1) := by
      have := Subgroup.relIndex_mul_card (F4.reeFixedBorel K 1)
        (F4.reeLocalParabolic K 1 ⟨0, by decide⟩)
      rw [inf_eq_left.2 hBP, hidx] at this
      exact this.symm
    have hB3 := not_three_dvd_card_reeFixedBorel (a := 1) hK3
    have hUB : Nat.card (F4.reeFixedPosUnipotent K 1) ∣ Nat.card (F4.reeFixedBorel K 1) :=
      Subgroup.card_dvd_of_le reeFixedPosUnipotent_le_reeFixedBorel
    have hdvdP : 27 * Nat.card (F4.reeFixedPosUnipotent K 1) ∣
        9 * Nat.card (F4.reeFixedBorel K 1) := by
      rw [← hcardH, ← hcardP₀]
      exact Subgroup.card_dvd_of_le hHP
    obtain ⟨c, hc⟩ := hUB
    rw [hc, show 9 * (Nat.card (F4.reeFixedPosUnipotent K 1) * c) =
      9 * c * Nat.card (F4.reeFixedPosUnipotent K 1) by ring] at hdvdP
    have h27 : 27 ∣ 9 * c := Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvdP
    have h3c : 3 ∣ c := by omega
    exact hB3 (hc ▸ Dvd.dvd.mul_left h3c _)
  · rw [card_reeFixedOrbitUnipotent_one hK', hK'] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 ^ 3 ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith

theorem noX27Simple_f4Even
    (n : ℕ) :
    NoX27Simple fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n := by
  intro A _ _ L P T hcfg h27 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (U : Subgroup ↥L) ⊤ :=
    ⟨le_top, U.isPGroup', by
      have := U.not_dvd_index
      rwa [← Subgroup.relIndex_top_right] at this⟩
  refine false_of_borel_data_x27 hcfg h27 (MulEquiv.refl ↥L) (U := (U : Subgroup ↥L))
    (B := Subgroup.normalizer ((U : Subgroup ↥L) : Set ↥L)) U.isPGroup' U.not_dvd_index
    (fun H hUH hH => le_normalizer_of_card_eq27 hL hU hUH hH) ?_
  intro x hx y hy
  exact F4.commutator_mem_of_isSylowTwoOf hL hU hx hy

theorem facts134X27_f4Even :
    ∀ f : ℕ, Odd f → 3 ≤ f →
      NoX27ConfigQ fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 f := fun f _ _ =>
  noX27ConfigQ_of_noCover (fun _ _ _ _ e h => CFSG.SectionRank.reeTitsModel_of_mulEquiv e.symm h)
    (noX27Simple_f4Even f) fun X _ _ hX h3 h => by
      have : Group.IsPerfect X := hX.1
      obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
      exact CFSG.QuasithinUnique.Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
        CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
          CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK π hπ hC hodd

end CFSG.Quasithin.H13.NQCore.X27F4
