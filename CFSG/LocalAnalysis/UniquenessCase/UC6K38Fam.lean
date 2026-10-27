module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K38AL
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LargeExtraspecial.Bender
import CFSG.Adapters.LinearCatalogStated
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.PSL2Odd
import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K38B

open Subgroup CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.OutStructure (OutPChain Inn)

structure BorelConfig {X : Type} [Group X] (q : ℕ) (Hb K : Subgroup X) (T : Sylow q K) :
    Prop where
  normal : K.Normal
  simple : IsSimpleGroup K
  nonabelian : ∃ a b : K, a * b ≠ b * a
  centralizer_eq_bot : centralizer (K : Set X) = ⊥
  stronglyEmbedded : IsStronglyPEmbedded q Hb
  sylow_le : (T : Subgroup K).map K.subtype ≤ Hb
  le_normalizer : Hb ≤ normalizer (((T : Subgroup K).map K.subtype : Subgroup X) : Set X)
  model : ∃ d : TauCeti.ValidLieTypeIndex,
    ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex q n d) ∨ (IsUnitaryIndex q d ∧ 2 ≤ d.1.fieldExponent) ∨
      IsReeGTwoIndex q d) ∧ Nonempty (K ≃* CatGroup d)

section Subgroup

variable {X : Type} [Group X] {K : Subgroup X}

theorem mem_normalizer_map_iff (S : Subgroup K) (k : K) :
    (k : X) ∈ normalizer ((S.map K.subtype : Subgroup X) : Set X) ↔
      k ∈ normalizer (S : Set K) := by
  have hmem : ∀ y : K, (y : X) ∈ S.map K.subtype ↔ y ∈ S := fun y =>
    mem_map_iff_mem K.subtype_injective
  simp only [mem_normalizer_iff, SetLike.mem_coe]
  constructor
  · intro h y
    rw [← hmem y, h, ← hmem]
    simp
  · intro h z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 := (h y).1 hy
      rw [← hmem] at h1
      simpa using h1
    · intro hz
      obtain ⟨y', hy', hy'z⟩ := hz
      have hzK : z ∈ K := by
        have : z = (k : X)⁻¹ * y' * k := by
          rw [show (y' : X) = (k : X) * z * (k : X)⁻¹ from hy'z]
          group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem k.2) y'.2) k.2
      have h1 : (⟨z, hzK⟩ : K) ∈ S := by
        rw [h]
        have : k * ⟨z, hzK⟩ * k⁻¹ = y' := Subtype.ext (by simpa using hy'z.symm)
        rw [this]
        exact hy'
      exact ⟨⟨z, hzK⟩, h1, rfl⟩

theorem conjNormal_injective [K.Normal] (hC : centralizer (K : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hC, mem_bot] at hxC
  exact hxC

end Subgroup

section TI

variable {X : Type} [Group X] [Finite X] {q : ℕ} [Fact q.Prime] {Hb K : Subgroup X}
  {T : Sylow q K}

theorem BorelConfig.ti (hB : BorelConfig q Hb K T) :
    ∀ P : Sylow q K, P = T ∨ (P : Subgroup K) ⊓ T = ⊥ := by
  intro P
  obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq K T P
  by_cases hk : k ∈ normalizer ((T : Subgroup K) : Set K)
  · exact Or.inl (Sylow.smul_eq_iff_mem_normalizer.2 hk)
  · right
    have hkH : (k : X) ∉ Hb := fun h => hk ((mem_normalizer_map_iff _ k).1 (hB.le_normalizer h))
    have hs := hB.stronglyEmbedded.2.2 k hkH
    have hsub : (((k • T : Sylow q K) : Subgroup K) ⊓ T).map K.subtype ≤
        Hb ⊓ Hb.map (MulAut.conj (k : X)).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨hB.sylow_le ⟨y, hy2, rfl⟩, ?_⟩
      have hy1' : y ∈ ((k • T : Sylow q K) : Subgroup K) := hy1
      rw [Sylow.smul_def, mem_smul_iff] at hy1'
      obtain ⟨t, ht, rfl⟩ := hy1'
      exact ⟨(t : X), hB.sylow_le ⟨t, ht, rfl⟩, by simp [MulAut.conj_apply]⟩
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hdvd
    have hp : IsPGroup q (((k • T : Sylow q K) : Subgroup K) ⊓ T : Subgroup K) :=
      T.isPGroup'.to_inf_right
    rcases hp.card_eq_or_dvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (h1.trans hdvd) hs

end TI

section Count

theorem card_sylow_eq_of_mulEquiv {L M : Type*} [Group L] [Group M] [Finite L] {q : ℕ}
    [Fact q.Prime] (e : L ≃* M) (T : Sylow q L) (S : Sylow q M) : Nat.card T = Nat.card S := by
  have : Finite M := Finite.of_equiv L e.toEquiv
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]

theorem statedClassicalModel_of_isLinTwoIndex {L : Type} [Group L] {p n : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d) (h : Nonempty (L ≃* CatGroup d)) :
    StatedClassicalModel L .PSL 2 p n := by
  obtain ⟨⟨x, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨r, hr, rfl, rfl⟩ := hd
  obtain rfl : x = .A 1 r := hr
  obtain ⟨e⟩ := h
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

theorem card_sylow_of_linTwo {L : Type} [Group L] [Finite L] {q n : ℕ} [Fact q.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex q n d) (he : Nonempty (L ≃* CatGroup d))
    (T : Sylow q L) : Nat.card (Sylow q L) = Nat.card T + 1 := by
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hn : 1 ≤ n := by
    obtain ⟨r, -, -, rfl⟩ := hd
    exact r.exponent_pos
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q (PSL2GF q n)))
  rw [CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 L q n
      (statedClassicalModel_of_isLinTwoIndex hd ⟨e⟩),
    card_sylow_eq_of_mulEquiv (e.trans e') T S, (psl2GF_sylow q n hn S).2]

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model in
theorem card_sylow_psu {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : 2 < p ^ f) (hF : Nat.card F = (p ^ f) ^ 2)
    (hfix : Nat.card {x : F // J.conj x = x} = p ^ f)
    (S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (Sylow p (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.card S + 1 := by
  obtain ⟨R, hR⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  have h2 := isMultiplyPretransitive_two J hJ (p ^ f) hF hfix
  haveI : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have h1 : Nat.card (Sylow p (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (normalizer (((R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)))).index :=
    Sylow.card_eq_index_normalizer R
  have hRc : Nat.card S = p ^ (3 * f) := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity R, hR,
      UnitaryModel.card_rootGroup_eq J hJ hF hfix]
  rw [h1, hR, UnitaryModel.normalizer_rootGroup_eq_stabilizer_pinf J hJ hF hfix hq,
    MulAction.index_stabilizer_of_transitive, card_isoPoint J hJ (p ^ f) hF hfix, hRc,
    ← pow_mul, mul_comm f 3]

theorem card_sylow_of_unitary {L : Type} [Group L] [Finite L] {q : ℕ} [Fact q.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex q d) (he : Nonempty (L ≃* CatGroup d))
    (T : Sylow q L) : Nat.card (Sylow q L) = Nat.card T + 1 := by
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd he)
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv L e.toEquiv
  obtain ⟨S⟩ := (inferInstance :
    Nonempty (Sylow q (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)))
  rw [CFSG.LargeExtraspecial.Bender.card_sylow_congr e q, card_sylow_eq_of_mulEquiv e T S]
  exact card_sylow_psu J hJ hf hq hF hfix S

variable {X : Type} [Group X] [Finite X] {q : ℕ} [Fact q.Prime] {Hb K : Subgroup X}
  {T : Sylow q K}

theorem BorelConfig.card_sylow (hq3 : q ≠ 3) (hB : BorelConfig q Hb K T) :
    Nat.card (Sylow q K) = Nat.card T + 1 := by
  obtain ⟨d, hd, he⟩ := hB.model
  rcases hd with ⟨n, -, hn⟩ | ⟨hu, -⟩ | hr
  · exact card_sylow_of_linTwo hn he T
  · exact card_sylow_of_unitary hu he T
  · exact absurd hr.1 hq3

end Count

section Out

theorem outPChain_of_linTwo {L : Type} [Group L] {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex q n d) (he : Nonempty (L ≃* CatGroup d)) :
    OutPChain q L :=
  (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_PSL_two_odd_all hq hq2 hq2
    (statedClassicalModel_of_isLinTwoIndex hd he)).toChain

theorem outPChain_of_unitary {L : Type} [Group L] {q : ℕ} (hq : q.Prime)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex q d) (hf : 1 ≤ d.1.fieldExponent)
    (he : Nonempty (L ≃* CatGroup d)) : OutPChain q L := by
  refine (CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd hq
    (UnitaryModel.statedClassicalModel hd he) fun hdvd => ?_).toChain
  have h1 : q ∣ q ^ d.1.fieldExponent + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
  have h2 : q ∣ q ^ d.1.fieldExponent := dvd_pow_self q (by omega)
  exact hq.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h1))

variable {X : Type} [Group X] [Finite X] {q : ℕ} [hq : Fact q.Prime]

theorem BorelConfig.outPChain {Hb K : Subgroup X} {T : Sylow q K} (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hB : BorelConfig q Hb K T) : OutPChain q K := by
  obtain ⟨d, hd, he⟩ := hB.model
  rcases hd with ⟨n, -, hn⟩ | ⟨hu, hf⟩ | hr
  · exact outPChain_of_linTwo hq.out hq2 hn he
  · exact outPChain_of_unitary hq.out hu (by omega) he
  · exact absurd hr.1 hq3

theorem inf_ne_bot_of_outPChain {K : Subgroup X} [K.Normal] (hO : OutPChain q K)
    (hC : centralizer (K : Set X) = ⊥) {A : Subgroup X} (hA : IsElemAbelian q A)
    (hcard : q < Nat.card A) : A ⊓ K ≠ ⊥ := by
  intro hbot
  set φ : X →* MulAut K := MulAut.conjNormal with hφdef
  have hφ : Function.Injective φ := conjNormal_injective hC
  have hinn : ∀ x ∈ A, φ x ∈ Inn K → x = 1 := by
    intro x hx hxi
    obtain ⟨k, hk⟩ := hxi
    have hxk : x = k := hφ (by rw [← hk, hφdef, MulAut.conjNormal_val])
    have hmem : x ∈ A ⊓ K := ⟨hx, hxk ▸ k.2⟩
    rwa [hbot, mem_bot] at hmem
  have hord : ∀ x ∈ A, x ≠ 1 → Nat.card (zpowers x) = q := fun x hx hx1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA.2 x hx) hx1
  have hA1 : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard (by have := hq.out.one_lt; omega)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨v, hv, hvu⟩ : ∃ v ∈ A, v ∉ zpowers u := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show A ≤ zpowers u from h)
    rw [hord u hu hu1'] at hle
    omega
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ one_mem _)
  have huv : u * v = v * u := congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcomm : φ u * φ v = φ v * φ u := by rw [← map_mul, ← map_mul, huv]
  have hpow : ∀ x ∈ A, φ x ^ (q ^ 1) ∈ Inn K := fun x hx => by
    rw [pow_one, ← map_pow, hA.2 x hx, map_one]
    exact one_mem _
  rcases hO.comparable hcomm (hpow u hu) (hpow v hv) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h1 : u * v ^ m = 1 :=
      hinn _ (A.mul_mem hu (A.zpow_mem hv m)) (by rwa [map_mul, map_zpow])
    have hu' : u ∈ zpowers v :=
      mem_zpowers_iff.2 ⟨-m, by rw [zpow_neg, ← eq_inv_of_mul_eq_one_left h1]⟩
    have heq : zpowers u = zpowers v :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hu')
        (by rw [hord u hu hu1', hord v hv hv1])
    exact hvu (heq ▸ mem_zpowers v)
  · have h1 : v * u ^ m = 1 :=
      hinn _ (A.mul_mem hv (A.zpow_mem hu m)) (by rwa [map_mul, map_zpow])
    exact hvu (mem_zpowers_iff.2 ⟨-m, by rw [zpow_neg, ← eq_inv_of_mul_eq_one_left h1]⟩)

end Out

end CFSG.LocalAnalysis.UniquenessCase.UCK.K38B
