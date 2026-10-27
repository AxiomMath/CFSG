module

public import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.RankThree.PartTwo.Sec20.Item208OneProof
public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step208S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
      CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) ≤ sTwenty M N c T

@[expose] def Step208XActs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N → ∀ x ∈ L ⊓ Subgroup.normalizer (T : Set G),
      x ∈ Subgroup.normalizer (sTwenty M N c T : Set G)

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N) : CFSG.Open.pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hN ▸ hTN
  have hTO : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have h2 : IsPGroup 2 ↥(T ⊔ CFSG.Open.pCoreOf 2 L) :=
    IsPGroup.to_sup_of_normal_right' hT.sylow.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hTO
  have heq := hT.sylow.eq_of_le le_sup_left (sup_le hT.sylow.le hO2L) h2
  rw [← heq]
  exact le_sup_right

theorem sTwenty_le_pCoreOf_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hTN : T ≤ N) :
    sTwenty M N c T ≤ CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL (mem_of_hyp201 hT.toHyp201)
  have hXle : normalClosureIn (kTwenty M c ⊓ N) c ⊔ T ≤ (kTwenty M c ⊔ T) ⊓ N := by
    refine sup_le ((normalClosureIn_le (M := kTwenty M c ⊓ N)
      (Subgroup.mem_inf.mpr ⟨self_mem_normalClosureIn M c, hcN⟩)).trans
      (inf_le_inf_right N le_sup_left)) (le_inf le_sup_right hTN)
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ((kTwenty M c ⊔ T) ⊓ N) :=
    hT.sylow.of_le (le_inf le_sup_right hTN) (inf_le_left.trans (sup_le hKM hT.sylow.le))
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le_of_isSylowOf hTsyl).trans le_sup_right)
    (hXle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem mem_normalizer_normalClosureIn_sup_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N) {x : G}
    (hx : x ∈ L ⊓ Subgroup.normalizer (T : Set G)) :
    x ∈ Subgroup.normalizer
      ((normalClosureIn (kTwenty M c ⊓ N) c ⊔ T : Subgroup G) : Set G) := by
  have hO2T := pCoreOf_le_core hT hN hO2L hTN
  have hcL : ∀ y ∈ L, c⁻¹ * y * c * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro y hy
    have hc : c⁻¹ ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
      rw [hT.centralizer_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
    have := hc.2 y hy
    rwa [inv_inv] at this
  apply mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkN : k ∈ Subgroup.normalizer (L : Set G) := hN ▸ hk.2
    have hy : k⁻¹ * x * k ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) x).mp hx.1
      simpa [mul_assoc] using this
    have hw : k * (c⁻¹ * (k⁻¹ * x * k) * c * (k⁻¹ * x * k)⁻¹) * k⁻¹ ∈ T :=
      hO2T ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hkN) _).mp (hcL _ hy))
    have hd : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    have heq : (MulAut.conj x).toMonoidHom (k * c * k⁻¹) =
        (k * c * k⁻¹) * (k * (c⁻¹ * (k⁻¹ * x * k) * c * (k⁻¹ * x * k)⁻¹) * k⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [SetLike.mem_coe, heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hw)
  · rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hx.2 t).mp ht)

theorem step208XActs_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N)
    (hS : CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) ≤ sTwenty M N c T)
    {x : G} (hx : x ∈ L ⊓ Subgroup.normalizer (T : Set G)) :
    x ∈ Subgroup.normalizer (sTwenty M N c T : Set G) := by
  have hSeq : sTwenty M N c T =
      CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) :=
    le_antisymm (sTwenty_le_pCoreOf_core hT hN hAL hTN) hS
  rw [hSeq]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (mem_normalizer_normalClosureIn_sup_core hT hN hO2L hTN hx)

theorem step208XActs_of_step208S (hS : Step208S) : Step208XActs := by
  intro G _ _ A M L N c T hT hTN x hx
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step208XActs_core hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One)
    (pCoreOf_le_of_hyp201One hT.hyp201One) hTN (hS G A M L N c T hT hTN) hx

theorem exists_two_element_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (h280 : (L ⊓ M).relIndex L = 280) (hTN : T ≤ N) :
    ∃ x ∈ L ⊓ Subgroup.normalizer (T : Set G), x ∉ M ∧ IsPGroup 2 (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hN ▸ hTN
  have hTM : T ≤ M := hT.sylow.le
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  have hnot : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T (T ⊔ L) := by
    intro hsyl
    have h1 := hsyl.inf_of_le_normalizer le_sup_right (sup_le hTL Subgroup.le_normalizer)
    have h2 := not_dvd_relIndex_of_isSylowOf_le h1 (le_inf inf_le_right (inf_le_left.trans hTM))
      inf_le_left
    rw [h280] at h2
    exact h2 (by norm_num)
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_le hT2 (le_sup_left : T ≤ T ⊔ L)
  have hlt : T < R := lt_of_le_of_ne hTR fun h => hnot (h ▸ hR)
  obtain ⟨y, hyR, hyT, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hR.isPGroup hlt
  have hyTL : y ∈ T ⊔ L := hR.le hyR
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T L hTL] at hyTL
  obtain ⟨t, ht, l, hl, rfl⟩ := Set.mem_mul.mp hyTL
  have hl' : l = t⁻¹ * (t * l) := by group
  have hlR : l ∈ R := by
    rw [hl']
    exact R.mul_mem (R.inv_mem (hTR ht)) hyR
  have hlN : l ∈ Subgroup.normalizer (T : Set G) := by
    rw [hl']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer ht)) hyN
  refine ⟨l, ⟨hl, hlN⟩, fun hlM => hyT ?_, hR.isPGroup.to_le (Subgroup.zpowers_le.mpr hlR)⟩
  have hyM : t * l ∈ M := M.mul_mem (hTM ht) hlM
  have heq := hT.sylow.eq_of_le le_sup_left (sup_le hTM (Subgroup.zpowers_le.mpr hyM))
    (hR.isPGroup.to_le (sup_le hTR (Subgroup.zpowers_le.mpr hyR)))
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem step208X_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M)
    (h280 : (L ⊓ M).relIndex L = 280) (hTN : T ≤ N)
    (hS : CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) ≤ sTwenty M N c T) :
    ∃ x ∈ L ⊓ Subgroup.normalizer (T : Set G), x ∉ M ∧ IsPGroup 2 (Subgroup.zpowers x) ∧
      x ∈ Subgroup.normalizer (sTwenty M N c T : Set G) := by
  obtain ⟨x, hx, hxM, hx2⟩ := exists_two_element_core hT hN h280 hTN
  exact ⟨x, hx, hxM, hx2, step208XActs_core hT hN hAL hO2L hTN hS hx⟩

section Certificates

theorem exists_two_element_of_ctx20One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (hTN : T ≤ N) :
    ∃ x ∈ L ⊓ Subgroup.normalizer (T : Set G), x ∉ M ∧ IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact exists_two_element_core hT.toCtx20 hN
    (relIndex_inf_eq_of_hyp201One h1812 h184 hT.hyp201One) hTN

theorem step208X_of (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (hA : Step208XActs) :
    Step208X := by
  intro G _ _ A M L N c T hT hTN
  obtain ⟨x, hx, hxM, hx2⟩ := exists_two_element_of_ctx20One h1812 h184 hT hTN
  exact ⟨x, hx, hxM, hx2, hA G A M L N c T hT hTN x hx⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec20
