module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec14.Wales149Direct
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofForms
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan149

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Inv

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [← Sec13.map_conj_eq_iff_mem_normalizer, Subgroup.map_sup,
    Sec13.map_conj_eq_iff_mem_normalizer.mpr hH, Sec13.map_conj_eq_iff_mem_normalizer.mpr hK]

theorem conj_mem_normalizer {X : Subgroup G} {s x : G}
    (hx : x ∈ Subgroup.normalizer
      ((X.map (MulAut.conj s⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    s * x * s⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
  have key : ∀ m : G, m ∈ X.map (MulAut.conj s⁻¹).toMonoidHom ↔ s * m * s⁻¹ ∈ X := by
    intro m
    constructor
    · rintro ⟨y, hy, rfl⟩
      change s * (s⁻¹ * y * s⁻¹⁻¹) * s⁻¹ ∈ X
      rwa [show s * (s⁻¹ * y * s⁻¹⁻¹) * s⁻¹ = y by group]
    · intro hm
      exact ⟨s * m * s⁻¹, hm, by
        change s⁻¹ * (s * m * s⁻¹) * s⁻¹⁻¹ = m
        group⟩
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro n
  have h1 := hx (s⁻¹ * n * s)
  rw [key, key] at h1
  rwa [show s * (s⁻¹ * n * s) * s⁻¹ = n by group,
    show s * (x * (s⁻¹ * n * s) * x⁻¹) * s⁻¹ = s * x * s⁻¹ * n * (s * x * s⁻¹)⁻¹ by group] at h1

theorem le_normalizer_of_inv (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G) {A : Subgroup G}
    (hA : Late.IsE27 A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a)
    (hN : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))
    {S : Subgroup G} (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer ({a} : Set G)) A
      (piCompl 3)) :
    S ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hSC, hSπ, hAS⟩ := hS
  have hS3 : ¬ 3 ∣ Nat.card S := (isPiSubgroup_piCompl_iff Nat.prime_three S).mp hSπ
  have hAC := Desc143X.le_centralizer_of_isE27 hA ha
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hON : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hAL : ∀ Z ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hA.1 ha ha1
  have hcomm : ⁅S, A⁆ ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_le]
    intro s hs x hx
    have hsC := hSC hs
    have hxC := hAC hx
    refine mem_normalizer_sup (hON ?_) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsC hxC)
        (Subgroup.inv_mem _ hsC)) (Subgroup.inv_mem _ hxC)
    · rw [commutatorElement_def]
      refine Subgroup.mul_mem _ (conj_mem_normalizer ?_) (Subgroup.inv_mem _ (hAL X hX hx))
      exact hAL _ (Sec6.map_conj_mem_thetaComponentsAt (Subgroup.inv_mem _ hsC) hX) hx
  have hcent : S ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
    fun g hg => hN ⟨hSC hg.1, Subgroup.centralizer_le_normalizer _ hg.2⟩
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A S hA3 hAS ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS3)
  rw [← hfac]
  exact sup_le hcomm hcent

theorem item143For1444S14_of_item143QS14 (h45 : Sec4.Item4_5)
    (h143Q : Ronan148Q.Item143QS14) : Item143For1444S14 := by
  intro G _ _ A c L h a ha ha1 hΩ
  have hAC := Desc143X.le_centralizer_of_isE27 h.isE27' ha
  have hON : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  rcases (h143Q G A c L h a ha ha1 hΩ Q₀ hQ₀).2 with hK | ⟨-, d, -, -, -, -, -, -, -, -, X, hX,
      hinv, -⟩
  · exact ⟨_, hK ▸ le_sup_left, hK, hAC.trans hON, fun S hS => hS.1.trans hON⟩
  · refine ⟨pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, ?_, ?_, ?_, ?_⟩
    · rw [hX]
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · rw [hX, sup_right_comm]
    · rcases hinv with hC | ⟨-, -, -, hNA⟩
      · exact hAC.trans hC
      · exact fun x hx => hNA ⟨hAC hx, Subgroup.le_normalizer hx⟩
    · rcases hinv with hC | ⟨-, hXa, -, hNA⟩
      · exact fun S hS => hS.1.trans hC
      · exact fun S hS =>
          le_normalizer_of_inv h45 h.toTheoremFourHyp h.isE27' ha ha1 hXa hNA hS

end Inv

theorem item1444S14_holds
    : Item1444S14 :=
  item1444S14_of_for1444 Ronan148M.concl142S14_holds Ronan148M.concl143S14_holds
    (item143For1444S14_of_item143QS14 Ronan148M.closedInputs.1 Ronan148M.item143QS14_holds)

theorem item145BotS14_holds
    : Item145BotS14 := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact item145BotS14_of h134 h48 h415

theorem item148NormalS14_holds
    : Item148NormalS14 :=
  item148NormalS14_of_item148S14 Ronan148M.item148S14_holds

theorem item149S14_holds
    : Sec16.Item149S14 :=
  item149S14_of_1444 item145BotS14_holds item1444S14_holds item148NormalS14_holds

theorem item148SmallS14_holds
    : Item148SmallS14 :=
  item148SmallS14_of_item148S14 Ronan148M.item148S14_holds

end CFSG.RankThree.PartTwo.Sec14.Ronan149
