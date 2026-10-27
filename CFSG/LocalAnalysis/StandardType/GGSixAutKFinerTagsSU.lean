module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace LayerExcThree

open LayerCores

variable {K : Type} [Field K] {f n : ℕ}

theorem exists_coreFamily_su_excThree (h : UnitaryFieldData 2 f K) (hK : 16 ≤ Nat.card K)
    {A : Subgroup (GL (Fin n) K)} (hA : (Nat.card A : K) ≠ 0)
    (hAN : A ≤ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))) :
    ∃ (β : Type) (S : β → Subgroup ↥(unitarySU 2 f K n)),
      IsCoreFamily ((Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
        (unitarySU 2 f K n).subtype) S ∧ ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hsymd : ∃ Y : Matrix (Fin n) (Fin n) K, (∀ g ∈ A, Y * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Y) ∧ Y + suAdj h Y = 1 := by
    obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
    refine ⟨c • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one], ?_⟩
    rw [suAdj_smul_one, ← add_smul, hc, one_smul]
  obtain ⟨β, S, hS, hgood⟩ := exists_coreFamily_adjCent_excThree hA (isInvol_suAdj (n := n) h)
    (fun X hX g hg => suAdj_mul_comm h hAN X hX hg) hsymd (by omega) (Or.inl hK)
  set H₀ : Subgroup (GL (Fin n) K) :=
    adjCent A (isInvol_suAdj (n := n) h) ⊓ (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, S c ≤ H₀ := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hS.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin n) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ (unitarySU 2 f K n).subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hC : H₀.comap (unitarySU 2 f K n).subtype =
      (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap (unitarySU 2 f K n).subtype := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    exact ⟨fun hx' => hx'.1.1, fun hx' => ⟨⟨hx', hx.1⟩, (hdet _).mpr hx.2⟩⟩
  have h2' := hS0.comap (unitarySU 2 f K n).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h2'
  refine ⟨β, fun c => (S c).comap (unitarySU 2 f K n).subtype, h2', fun c => ?_⟩
  rw [ggCQ_comap_of_injective _ (Subgroup.subtype_injective _) ((hSdet c).trans hle)]
  exact hgood c

end LayerExcThree

namespace LayerExcThree

variable {G : Type} [Group G]

theorem ggNotExcThree_of_isComponentOf_su [Finite G] {f m : ℕ} (hf : 2 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : G} (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f (by omega))
      (m + 1)) ψ y)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y})) :
    GGNotExcThreeOrder (ggCQ K) := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf1
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf1, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Finite (GaloisField 2 (2 * f)) := h.finite
  have : CharP (GaloisField 2 (2 * f)) 2 := h.charP
  have hK16 : 16 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [hF]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    nlinarith
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
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f); omega)
  have hn3 : 3 ≤ m + 1 := by omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hodd : (Nat.card (SUTorus.inducedMatrices ψ₁ E) : GaloisField 2 (2 * f)) ≠ 0 := by
    intro h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 ((CharP.cast_eq_zero_iff _ 2 _).mp h0)
    obtain ⟨e, he, hpe⟩ := SUTorus.mem_inducedMatrices.mp x.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (SUTorus.suPairs ψ₁).pow_mem hpe (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hq hqd hker₁ h1
    have hx2 : (x : GL (Fin (m + 1)) (GaloisField 2 (2 * f))) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
    have hxx : (x : GL (Fin (m + 1)) (GaloisField 2 (2 * f))) ^ (p ^ k) = x := by
      rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
    rw [hxx] at hc
    rw [hc] at hx2
    have hx1 : x = 1 := Subtype.ext (by simp [hc, LayerFacts.eq_one_of_scalar_sq_eq_one hx2])
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hnorm : SUTorus.inducedMatrices ψ₁ E ≤
      Subgroup.normalizer (unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) :
        Set (GL (Fin (m + 1)) (GaloisField 2 (2 * f)))) := by
    intro B hB
    obtain ⟨e, -, hpe⟩ := SUTorus.mem_inducedMatrices.mp hB
    exact hpe.1
  obtain ⟨β, S, ⟨hSC, hSn, hSq, hder, -⟩, hgood⟩ :=
    exists_coreFamily_su_excThree h hK16 hodd hnorm
  rw [← ggCentralizer_zpowers_eq, ← hr₁] at hK
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ₁ hker₁
    (LayerFacts.map_ggSUCent_le hEA) (LayerFacts.normal_map_ggSUCent hker₁)
    (LayerFacts.commutator_le_map_ggSUCent hker₁) S hSC hSn hSq hder hK
  rw [ggCQ_map_of_perfect ψ₁ hker₁ (hSq c).1]
  exact hgood c

end LayerExcThree

section Tags

theorem ggAKFG_excThree_PSU : ∀ (G : Type) [Group G] [Finite G] (n f : ℕ)
    (ψ : (ggU .PSU n f).K →* G) (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU .PSU n f).D .PSU n f ψ →
    2 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y : G, y ^ p = 1 →
      GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        GGNotExcThreeOrder (ggCQ C) := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have hU : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hU]
    intro ψ G₀ hpres hf2 p hp hp2 y hy hdiag C hC
    obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    have hn : 4 ≤ n := by
      have : 2 ≤ n / 2 := hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange] at hC
    exact LayerExcThree.ggNotExcThree_of_isComponentOf_su hf2 hn hker hp hp2 hy hdiag hC
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

theorem ggLayerNotDFourTwoTag_PSU : GGLayerNotDFourTwoTag .PSU := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree (ggAKFG_excThree_PSU G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C
    hC)).1

theorem ggLayerNotUFourAltSixTag_PSU : GGLayerNotUFourAltSixTag .PSU := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree (ggAKFG_excThree_PSU G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C
    hC)).2

end Tags

end CFSG.StandardType
