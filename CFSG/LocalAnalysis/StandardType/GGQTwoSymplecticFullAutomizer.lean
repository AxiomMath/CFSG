module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponentBounds
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFrameDimensions
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticZeroBlock
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticMovingAutomizer

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix Polynomial Module CFSG.Open CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)


theorem four_dvd_fixed_of_full_frame
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2) (hn : 1 ≤ n)
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      WitSpNs.planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (t : ↥E) (ht3 : (t : StatedSp n K) ^ 3 = 1) (ht1 : (t : StatedSp n K) ≠ 1)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported (t : StatedSp n K) {X - 1},
      spSupported (t : StatedSp n K) {X - 1}⁆) :
    4 ∣ Nat.card (ggAutomizer
      ⁅spSupported (t : StatedSp n K) {X - 1}, spSupported (t : StatedSp n K) {X - 1}⁆ E) := by
  classical
  have h4 := fixedDim_ge_four_of_quasisimple_derived_fixed hK hn ht3 ht1 hQ
  have blocks := CFSG.LocalAnalysis.GLTheoremA.T173O.spPrimaryBlocks_of_order_three hK hn ht3 ht1
  change 4 ≤ finrank K (primaryComponent (spEnd (t : StatedSp n K)) (X - 1)) at h4
  rw [blocks.fixed_eq] at h4
  have heval : ∀ s : StatedSp n K, aeval (spEnd s) (X - 1 : K[X]) = spEnd s - 1 := by
    intro s
    rw [map_sub, aeval_X, map_one]
  have hdim0 := finrank_ker_aeval_conj (K := K) (n := n) A₀⁻¹
    (t : StatedSp n K) (X - 1 : K[X])
  rw [heval, heval] at hdim0
  have hdim : finrank K (LinearMap.ker (spEnd (A₀⁻¹ * (t : StatedSp n K) * A₀) - 1)) =
      finrank K (LinearMap.ker (spEnd (t : StatedSp n K) - 1)) := by
    have hAi : A₀⁻¹⁻¹ = A₀ := _root_.inv_inv A₀
    rw [hAi] at hdim0
    exact hdim0
  have hbound := finrank_fixed_le_two_mul_zero_card hK hdet hM (hframe t)
  let Z : Finset (Fin n) := Finset.univ.filter fun j => k j t = 1
  have hZ : 2 ≤ Z.card := by
    change _ ≤ 2 * Z.card at hbound
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < Z.card by omega)
  have hi0 : k i t = 1 := by simpa only [Z, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hj0 : k j t = 1 := by simpa only [Z, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  exact four_dvd_zeroBlock_of_full_planeFrame hK hdet hM hframe hsurj t hij hi0 hj0


theorem four_dvd_moving_of_full_frame
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2) (hn : 1 ≤ n)
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      WitSpNs.planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (t : ↥E) (ht3 : (t : StatedSp n K) ^ 3 = 1) (ht1 : (t : StatedSp n K) ≠ 1)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported (t : StatedSp n K) {X ^ 2 + X + 1},
      spSupported (t : StatedSp n K) {X ^ 2 + X + 1}⁆) :
    4 ∣ Nat.card (ggAutomizer
      ⁅spSupported (t : StatedSp n K) {X ^ 2 + X + 1},
        spSupported (t : StatedSp n K) {X ^ 2 + X + 1}⁆ E) := by
  classical
  have h4 := movingMultiplicity_ge_four_of_quasisimple_derived hK hn ht3 ht1 hQ
  letI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
  have hdim := finrank_primaryComponent (x := spEnd (t : StatedSp n K)) (a := SpFin.h3 K)
  rw [SpFin.h3_natDegree] at hdim
  change finrank K (primaryComponent (spEnd (t : StatedSp n K)) (X ^ 2 + X + 1)) =
    2 * primaryMultiplicity (spEnd (t : StatedSp n K)) (X ^ 2 + X + 1) at hdim
  have hconj0 := finrank_ker_aeval_conj (K := K) (n := n) A₀⁻¹ (t : StatedSp n K)
    (X ^ 2 + X + 1 : K[X])
  have hAi : A₀⁻¹⁻¹ = A₀ := _root_.inv_inv A₀
  rw [hAi] at hconj0
  have hconj : finrank K (primaryComponent (spEnd (A₀⁻¹ * (t : StatedSp n K) * A₀))
      (X ^ 2 + X + 1)) = finrank K (primaryComponent (spEnd (t : StatedSp n K))
      (X ^ 2 + X + 1)) := hconj0
  have hbound := finrank_quad_le_two_mul_moving_card (hframe t)
  let I : Finset (Fin n) := Finset.univ.filter fun j => k j t ≠ 1
  have hI : 4 ≤ I.card := by
    change _ ≤ 2 * I.card at hbound
    omega
  obtain ⟨S, hSI, hS4⟩ := Finset.exists_subset_card_eq hI
  let i : Fin 4 → Fin n := S.orderEmbOfFin hS4
  have hi : Function.Injective i := (S.orderEmbOfFin hS4).injective
  have hrange : Set.range i = S := Finset.range_orderEmbOfFin S hS4
  have hmoving : ∀ a, k (i a) t ≠ 1 := by
    intro a
    have ha : i a ∈ S := by
      change i a ∈ (S : Set (Fin n))
      rw [← hrange]
      exact ⟨a, rfl⟩
    have hb := hSI ha
    exact (Finset.mem_filter.mp hb).2
  exact four_dvd_movingBlock_of_full_planeFrame hK hdet hM hframe hsurj t ht3 i hi hmoving

theorem four_dvd_image_of_full_symplectic
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L)) (ggGamma L hN).range) := by
  obtain ⟨K, hField, hFinite, hK, θ, E, A₀, M, k, d, t, -, hdet, hM, hframe, -,
    hsurj, hmapE, hQJ, -, ht3, ht1, hJ⟩ :=
      exists_symplectic_full_component hS hq2 htag hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hK)
  have hr : 3 ≤ lab.rank := QTwoCav.three_le_exponent_of_beta_index hS Nat.prime_three θ hN hidx
  rcases hJ with hfixed | hmoving
  · have hQ := isQuasisimple_of_symplectic_projective_image hK hQJ hfixed
    have hfour := four_dvd_fixed_of_full_frame hK (by omega) hdet hM hframe hsurj t ht3 ht1 hQ
    rwa [card_automizer_symplectic_eq_original_image hmark.1 hN hK hr θ hfixed hmapE] at hfour
  · have hQ := isQuasisimple_of_symplectic_projective_image hK hQJ hmoving
    have hfour := four_dvd_moving_of_full_frame hK (by omega) hdet hM hframe hsurj t ht3 ht1 hQ
    rwa [card_automizer_symplectic_eq_original_image hmark.1 hN hK hr θ hmoving hmapE] at hfour

end CFSG.StandardType.QTwoSymplecticCav

end
