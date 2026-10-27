module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace LayerPDiv

variable {G : Type} [Group G]

theorem dvd_card_of_isComponentOf_su_of_mem_suPairs_field [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ} (h : UnitaryFieldData 2 f F)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ m + 1)
    {ψ₁ : ↥(unitarySU 2 f F (m + 1)) →* G}
    (hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f F (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ₁)
    {L : Subgroup G} (hK : IsComponentOf L (ψ₁.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L := by
  classical
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f); omega)
  have hn3 : 3 ≤ m + 1 := by omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hodd : (Nat.card (SUTorus.inducedMatrices ψ₁ E) : F) ≠ 0 := by
    intro h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 ((CharP.cast_eq_zero_iff _ 2 _).mp h0)
    obtain ⟨e, he, hpe⟩ := SUTorus.mem_inducedMatrices.mp x.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (SUTorus.suPairs ψ₁).pow_mem hpe (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hq hqd hker₁ h1
    have hx2 : (x : GL (Fin (m + 1)) F) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
    have hxx : (x : GL (Fin (m + 1)) F) ^ (p ^ k) = x := by
      rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
    rw [hxx] at hc
    rw [hc] at hx2
    have hx1 : x = 1 := Subtype.ext (by simp [hc, LayerFacts.eq_one_of_scalar_sq_eq_one hx2])
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hnorm : SUTorus.inducedMatrices ψ₁ E ≤
      Subgroup.normalizer (unitarySU 2 f F (m + 1) : Set (GL (Fin (m + 1)) F)) := by
    intro B hB
    obtain ⟨e, -, hpe⟩ := SUTorus.mem_inducedMatrices.mp hB
    exact hpe.1
  have hpK : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact dvd_sq_sub_one hpq
  obtain ⟨β, S, ⟨hSC, hSn, hSq, hder, -⟩, hdvd⟩ := exists_coreFamily_su_pDiv h hodd hnorm hpK
  obtain ⟨c, rfl⟩ := exists_eq_map_of_isComponentOf ψ₁ hker₁ (LayerFacts.map_ggSUCent_le hEA)
    (LayerFacts.normal_map_ggSUCent hker₁) (LayerFacts.commutator_le_map_ggSUCent hker₁) S hSC
    hSn hSq hder hK
  exact dvd_card_map_of_perfect ψ₁ hker₁ (LayerFacts.ggCommutator_eq_of_isQuasisimple (hSq c)) hp
    (hdvd c)

theorem dvd_card_of_isComponentOf_su_of_mem_suPairs [Finite G] {f m : ℕ} (hf : 1 ≤ f)
    (hn : 4 ≤ m + 1)
    {ψ₁ : ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) →* G}
    (hker₁ : ψ₁.ker ≤
      Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ₁)
    {K : Subgroup G} (hK : IsComponentOf K (ψ₁.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card K := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  exact dvd_card_of_isComponentOf_su_of_mem_suPairs_field h hF hn hker₁ hp hp2 hpq hE hEA hK

theorem dvd_card_of_isComponentOf_su_family_field [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ} (h : UnitaryFieldData 2 f F)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Unitary.rootDatum hF (m + 1)) ψ e)
    {L : Subgroup G} (hK : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L := by
  classical
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution F 2 f) (m + 1) =
      unitarySU 2 f F (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f F (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  have hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ₁ := by
    intro e he
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker e⁻¹ (hdiag e⁻¹ (E.inv_mem he))
    refine ⟨P * A * P⁻¹, SUTorus.mem_suPairs_transfer P hP hSU hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  rw [← hr₁] at hK
  exact dvd_card_of_isComponentOf_su_of_mem_suPairs_field h hF hn hker₁ hp hp2 hpq hE hEA hK

theorem dvd_card_of_isComponentOf_su_family [Finite G] {f m : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E,
      GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ e)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card K := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  exact dvd_card_of_isComponentOf_su_family_field h hF hn hker hp hp2 hpq hE hdiag hK

theorem dvd_card_of_isComponentOf_su [Finite G] {f m : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) {y : G}
    (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ y)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y})) :
    p ∣ Nat.card K := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Finite (GaloisField 2 (2 * f)) := h.finite
  have : CharP (GaloisField 2 (2 * f)) 2 := h.charP
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) =
      unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  set E := Subgroup.zpowers y with hEdef
  have hE : IsPGroup p E := ggIsPGroup_zpowers_of_pow_eq_one hy
  obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker y hdiag
  have hpair : (y⁻¹, P * A * P⁻¹) ∈ SUTorus.suPairs ψ₁ :=
    SUTorus.mem_suPairs_transfer P hP hSU hA fun u => by
      rw [inv_inv]
      exact hAc u
  have hpair' : (y, (P * A * P⁻¹)⁻¹) ∈ SUTorus.suPairs ψ₁ := by
    have h' := (SUTorus.suPairs ψ₁).inv_mem hpair
    rwa [Prod.inv_mk, inv_inv] at h'
  have hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ₁ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨(P * A * P⁻¹)⁻¹ ^ k, (SUTorus.suPairs ψ₁).zpow_mem hpair' k⟩
  rw [← ggCentralizer_zpowers_eq, ← hr₁] at hK
  exact dvd_card_of_isComponentOf_su_of_mem_suPairs hf hn hker₁ hp hp2 hpq hE hEA hK

end LayerPDiv

section Tags

theorem ggLayerPDivTag_PSU : GGLayerPDivTag .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have hU : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hU]
    intro ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
    obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    have hn : 4 ≤ n := by
      have : 2 ≤ n / 2 := hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange] at hK
    exact LayerPDiv.dvd_card_of_isComponentOf_su hf hn hker hp hp2 hpq hy hdiag hK
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

theorem ggLayerPDivInput_of_remaining_seven (hPlus : GGLayerPDivTag .POmegaPlus)
    (hMinus : GGLayerPDivTag .POmegaMinus) (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6)
    (hE7 : GGLayerPDivTag .E7) (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6) :
    GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining_eight ggLayerPDivTag_PSU hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggSixLayerCXInput_of_pDivTags_seven (hPlus : GGLayerPDivTag .POmegaPlus)
    (hMinus : GGLayerPDivTag .POmegaMinus) (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6)
    (hE7 : GGLayerPDivTag .E7) (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6)
    (hNS : GGSixLayerCXNonsplitInput) : GGSixLayerCXInput :=
  ggSixLayerCXInput_of_split
    (ggLayerPDivInput_of_remaining_seven hPlus hMinus hF4 hE6 hE7 hE8 hTwE6) hNS

end Tags

end CFSG.StandardType
