module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise


@[expose] def KF87UBComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
      ∀ t ∈ L ⊓ Subgroup.centralizer ({a} : Set G), (∃ k : ℕ, t ^ 2 ^ k = 1) →
        t ∈ ⁅L ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers b⁆

@[expose] def Pair87UnitarySyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
      ∀ Y ∈ thetaComponentsAt 3 a, sec8J X a ≤ Y →
        ∃ T : Sylow 2 (sec8I L a), (T : Subgroup (sec8I L a)).map (sec8I L a).subtype ≤ Y

namespace Item89Res2

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_thetaComponentsAt {a g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) :
    Y.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 a := by
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  let φ : Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({a} : Set G) :=
    MulAut.conj ⟨g, hg⟩
  refine ⟨Y₀.map φ.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three φ hY₀, ?_⟩
  show (Y₀.map φ.toMonoidHom).map (Subgroup.centralizer ({a} : Set G)).subtype =
    (Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem commutator_mem_normalizer {a g β : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hβ : ∀ Z ∈ thetaComponentsAt 3 a, β ∈ Subgroup.normalizer (Z : Set G)) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) : ⁅g, β⁆ ∈ Subgroup.normalizer (Y : Set G) := by
  have hg' : g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.inv_mem _ hg
  have h1 := hβ _ (map_conj_mem_thetaComponentsAt hg' hY)
  have h2 : g * β * g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    have hmem : ∀ z, z ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ Y := by
      intro z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hw
      · intro hz
        exact ⟨g * z * g⁻¹, hz, by simp [mul_assoc]⟩
    intro y
    have := h1 (g⁻¹ * y * g)
    rw [hmem, hmem] at this
    simpa [mul_assoc] using this
  have h4 : β⁻¹ ∈ Subgroup.normalizer (Y : Set G) := Subgroup.inv_mem _ (hβ Y hY)
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h2 h4

theorem mem_of_sylow_le {I Y : Subgroup G} (hIN : I ≤ Subgroup.normalizer (Y : Set G))
    (T : Sylow 2 I) (hT : (T : Subgroup I).map I.subtype ≤ Y) {t : G} (htI : t ∈ I)
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) : t ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := ht2
  set t' : I := ⟨t, htI⟩ with ht'
  have hk' : t' ^ 2 ^ k = 1 := Subtype.ext (by simpa [ht'] using hk)
  have hp : IsPGroup 2 (Subgroup.zpowers t') := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (t' ^ j) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq I T Q
  have htQ : t' ∈ ((h • T : Sylow 2 I) : Subgroup I) := hQ (Subgroup.mem_zpowers t')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ
  obtain ⟨s, hs, hst⟩ := htQ
  have hsY : ((s : I) : G) ∈ Y := hT ⟨s, hs, rfl⟩
  have hhN : ((h : I) : G) ∈ Subgroup.normalizer (Y : Set G) := hIN h.2
  have heq : t = (h : G) * (s : G) * (h : G)⁻¹ := by
    have := congrArg (fun x : I => (x : G)) hst
    simpa [MulAut.conj_apply] using this.symm
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp hhN _).mp hsY

end Item89Res2

theorem pair87UnitaryY_of (h45 : Sec4.Item4_5) (hC : KF87UBComm) (hS : Pair87UnitarySyl) :
    Pair87UnitaryY := by
  intro G _ _ A c L a b X n h hU Y hY hJY
  have hG := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) :=
    Item87Proof.le_centralizer_of_isElemAbelian hAel h.a_mem
  have hAfix : ∀ Z ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
      (hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG h.a_ne_one)) hAH hAel
      ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩
  have hcomm : ⁅L ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers b⁆ ≤
      Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.commutator_le]
    intro g hg β hβ
    have hβA : β ∈ A := (Subgroup.zpowers_le.mpr hbA) hβ
    exact Item89Res2.commutator_mem_normalizer (Subgroup.mem_inf.mp hg).2
      (fun Z hZ => hAfix Z hZ hβA) hY
  have hIdef : sec8I L a = Subgroup.closure
      {y | y ∈ L ⊓ Subgroup.centralizer {a} ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
    simp only [sec8I, hU, ↓reduceIte]
  have hIN : sec8I L a ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hIdef, Subgroup.closure_le]
    rintro t ⟨htL, ht2⟩
    exact hcomm (hC G A c L a b X n h hU t htL ht2)
  obtain ⟨T, hT⟩ := hS G A c L a b X n h hU Y hY hJY
  have hgen : ∀ t ∈ L ⊓ Subgroup.centralizer ({a} : Set G), (∃ k : ℕ, t ^ 2 ^ k = 1) → t ∈ Y := by
    intro t htL ht2
    have htI : t ∈ sec8I L a := by
      rw [hIdef]
      exact Subgroup.subset_closure ⟨htL, ht2⟩
    exact Item89Res2.mem_of_sylow_le hIN T hT htI ht2
  rw [hIdef, Subgroup.closure_le]
  rintro t ⟨htL, ht2⟩
  exact hgen t htL ht2

end CFSG.RankThree.PartTwo.Sec8
