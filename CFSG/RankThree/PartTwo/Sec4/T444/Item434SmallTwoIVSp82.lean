module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Census.Symplectic46
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam commute_lam_lam)
open CFSG.RankThree.CentralCover (sl2Upper)
open Item434Kit Item434Alt
open scoped MatrixGroups

namespace Item434SmallTwoIV

theorem exists_elemAbelian_of_commuting {G : Type*} [Group G] [Finite G] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Ks : ι → Subgroup G)
    (hK : ∀ i j, i ≠ j → Ks j ≤ Subgroup.centralizer (Ks i : Set G)) (y : ι → G)
    (hyK : ∀ i, y i ∈ Ks i) (hy : ∀ i, y i ∉ Subgroup.centralizer (Ks i : Set G))
    (hy3 : ∀ i, y i ^ 3 = 1) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E ∧ 3 ^ Fintype.card ι ≤ Nat.card E := by
  have hpair : (Set.range y).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    exact Subgroup.mem_centralizer_iff.1 (hK i j hij' (hyK j)) (y i) (hyK i)
  set Y := Subgroup.closure (Set.range y)
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
  let y' : ι → Y := fun i => ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range y') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range y)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow y' hgen
    (fun i => (Subgroup.centralizer (Ks i : Set G)).subgroupOf Y)
    (fun i j hij => Subgroup.mem_subgroupOf.2 (hK i j hij (hyK j)))
    (fun i h => hy i (Subgroup.mem_subgroupOf.1 h))
    (fun i => Subgroup.mem_subgroupOf.2 (by
      change y i ^ 3 ∈ _
      rw [hy3 i]
      exact one_mem _))
  set Ω : Subgroup G := (powMonoidHom 3 : Y →* Y).ker.map Y.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card (powMonoidHom 3 : Y →* Y).ker :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hΩY : Ω ≤ Y := Subgroup.map_subtype_le _
  have hΩc : IsMulCommutative Ω := ⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from congrArg Subtype.val (hcomm ⟨a, hΩY a.2⟩ ⟨b, hΩY b.2⟩))⟩⟩
  have hΩq : ∀ w ∈ Ω, w ^ 3 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
  exact ⟨Ω, ⟨hΩc, hΩq⟩, hΩcard ▸ hbound⟩

theorem exists_card_eq_of_le {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {n : ℕ} (hn : 3 ^ n ≤ Nat.card E) :
    ∃ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hE).exists_card_eq
  have hkn : n ≤ k := by
    rw [hk] at hn
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hn
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := n)
    (by rw [hk]; exact pow_dvd_pow 3 hkn)
  refine ⟨K.map E.subtype, Source.isElemAbelian_of_le hE (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem exists_e81_projSp_four_two [Finite (projSp 4 (GaloisField 2 1))] :
    ∃ E : Subgroup (projSp 4 (GaloisField 2 1)), CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E := by
  set π := QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) (GaloisField 2 1)).subgroupOf
    (StatedSp 4 (GaloisField 2 1))) with hπ
  set ψ := Census.statedSpEquivProjSp 4 (GaloisField 2 1) with hψ
  let φ : Fin 4 → SL(2, GaloisField 2 1) →* projSp 4 (GaloisField 2 1) := fun i =>
    ψ.toMonoidHom.comp (π.comp (lam i))
  have hφinj : ∀ i, Function.Injective (φ i) := fun i =>
    ψ.injective.comp (Census.mk_lam_injective_of_ne (K := GaloisField 2 1) (j := i) (l := i + 1)
      (by fin_cases i <;> decide))
  have hφcomm : ∀ i j, i ≠ j → ∀ g g' : SL(2, GaloisField 2 1), φ i g * φ j g' = φ j g' * φ i g :=
    fun i j hij g g' => by
      change ψ (π (lam i g)) * ψ (π (lam j g')) = ψ (π (lam j g')) * ψ (π (lam i g))
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, (commute_lam_lam hij g g').eq]
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_of_commuting (fun i => (φ i).range)
    (fun i j hij => by
      rintro _ ⟨g', rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, rfl⟩
      exact hφcomm i j hij g g')
    (fun i => φ i (CFSG.RankThree.PartTwo.Census.Exceptional.sl2Three _)) (fun i => ⟨_, rfl⟩)
    (fun i h => by
      have h1 := Subgroup.mem_centralizer_iff.1 h (φ i (sl2Upper 1)) ⟨_, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact CFSG.RankThree.PartTwo.Census.Exceptional.sl2Three_not_commute _ ((hφinj i) h1).symm)
    (fun i => by
      rw [← map_pow, CFSG.RankThree.PartTwo.Census.Exceptional.sl2Three_pow_three, map_one])
  exact ⟨E, hE, by simpa using hcard⟩

theorem not_three_dvd_card_outer_projSp_four_two :
    ¬ 3 ∣ Nat.card (Outer (projSp 4 (GaloisField 2 1))) := by
  rw [Nat.card_congr (equivalence (projSpEquivStatedProj 4 (GaloisField 2 1))).toEquiv]
  have hK : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, GaloisField.card 2 1 one_ne_zero]
    norm_num
  have h1 := Sec19.Step1919EndProof.card_outer_statedSp_le (r := 4) (by norm_num) hK
  have h2 := Sec19.Step1919EndProof.card_ringEquiv_le (GaloisField 2 1)
  rw [GaloisField.card 2 1 one_ne_zero, pow_one] at h2
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp 4 (GaloisField 2 1)))) := Nat.card_pos
  intro h3
  have h4 := Nat.le_of_dvd hpos h3
  omega

theorem factorization_card_projSp_four_two :
    (Nat.card (projSp 4 (GaloisField 2 1))).factorization 3 = 5 := by
  rw [Sec19.Step1911Proof.card_projSp 4 le_rfl,
    show (2 ^ 1) ^ 4 ^ 2 * ∏ j ∈ Finset.Icc 1 4, ((2 ^ 1) ^ (2 * j) - 1) = 3 ^ 5 * 194969600 by
      decide]
  exact Item434AltPerm.factorization_three_pow_mul 5 (by norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_sp82 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 4 (GaloisField 2 1)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic hodd
    (e₀.trans (projSpEquivStatedProj 4 (GaloisField 2 1)))

theorem false_of_sp82_nine (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 4 (GaloisField 2 1))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False := by
  have : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨E, hE, hE81⟩ := exists_e81_projSp_four_two
  obtain ⟨D, hD, hD27⟩ := exists_card_eq_of_le hE (n := 3) (le_trans (by norm_num) hE81)
  exact Item434Spor.false_of_card_nine h (center_layer_eq_bot_of_sp82 h e₀) e₀ hD hD27 h9

theorem false_of_sp82_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 4 (GaloisField 2 1))
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨E, hE, hE81⟩ := exists_e81_projSp_four_two
  refine false_of_elemAbelian_index_three_of_outer h e₀ ?_ (center_eq_bot_of_layer_quotient h e₀)
    hE hE81 ?_ h27
  · exact not_three_dvd_card_outer_projSp_four_two
  · rw [factorization_card_projSp_four_two]
    omega

end Item434SmallTwoIV

section Families


theorem item434SmallTwoIV_Sp82_9 : Item434SecForCard IsSmallTwoSp82 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIV.false_of_sp82_nine hc e₀ h9).elim

theorem item434SmallTwoIV_Sp82_27 : Item434SecForCard IsSmallTwoSp82 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIV.false_of_sp82_27 hc e₀ h27).elim

theorem item434SmallTwoIV_Sp82 : Item434SmallTwoIV_Sp82 :=
  item434SecFor_of_card item434SmallTwoIV_Sp82_9 item434SmallTwoIV_Sp82_27

end Families

end CFSG.RankThree.PartTwo.Sec4
