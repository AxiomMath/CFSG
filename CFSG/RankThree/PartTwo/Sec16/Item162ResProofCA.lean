module

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162

open CFSG Equiv CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.KFacts.KP2
open scoped commutatorElement Pointwise

theorem isElemAbelian_eNine : CFSG.Assembly.IsElemAbelian 3 eNine := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, i, j, rfl⟩ := a
    obtain ⟨_, i', j', rfl⟩ := b
    exact eNineF_comm i j i' j'
  · rintro _ ⟨i, j, rfl⟩
    exact eNineF_pow_three i j

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizerSection_of_mem {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {t : G}
    (ht : t ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) :
    t ∈ CFSG.GH74.GLS.centralizerSection Y (CFSG.Open.pCoreOf 2 Y) := by
  obtain ⟨htA, ht⟩ := ht
  refine ⟨hAY htA,
    (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) htA,
    fun k hk => ?_⟩
  have e : ⁅k, t⁆ = (t * k * t⁻¹ * k⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact inv_mem (ht k hk)

open CFSG.RankThreeEvenClassification.Helpers in
theorem mem_zpowers_of_mem_sectionCentralizer {A Y : Subgroup G}
    (hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))
    {b b' : G} (hb : b ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) (hb1 : b ≠ 1)
    (hb' : b' ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) :
    b' ∈ Subgroup.zpowers b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hZ : Subgroup.center (↥Y ⧸ N) = ⊥ := (KFacts.KS14.a7_facts (↥Y ⧸ N) ⟨φ⟩).2.1
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1
  set C := CFSG.GH74.GLS.centralizerSection Y O with hC
  have hmemC : ∀ t ∈ Late.sectionCentralizer A Y O, t ∈ C := fun t ht =>
    mem_centralizerSection_of_mem hAY ht
  set D := A ⊓ C with hD
  have hbD : b ∈ D := ⟨hb.1, hmemC b hb⟩
  have hb'D : b' ∈ D := ⟨hb'.1, hmemC b' hb'⟩
  have hDY : ∀ x ∈ D, x ∈ Y → x = 1 := by
    intro x hxD hxY
    have hxO := Step163Alt.mem_pCoreOf_of_mem_centralizerSection hZ hxY hxD.2
    obtain ⟨m, hm⟩ := hOp ⟨x, hxO⟩
    have h2 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    exact Step163Alt.eq_one_of_two_three h2 (by rw [pow_one]; exact hA.2 x hxD.1)
  set B := Subgroup.zpowers b ⊔ Subgroup.zpowers b' with hBdef
  have hBD : B ≤ D := sup_le (Subgroup.zpowers_le.mpr hbD) (Subgroup.zpowers_le.mpr hb'D)
  have hBA : B ≤ A := hBD.trans inf_le_left
  have hBC : B ≤ C := hBD.trans inf_le_right
  have hB3 : IsPGroup 3 B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hA.2 x (hBA x.2)
  have hBN : B ≤ Subgroup.normalizer (Y : Set G) := hBA.trans hAY
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlift : ∀ y : ↥Y, ∃ y' : ↥Y,
      (y' : G) ∈ Subgroup.centralizer (B : Set G) ∧ π y' = π y := by
    intro y
    refine exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three B Y hB3 hBN π hker3 (fun member element => ?_) y
    have h := (hBC member.2).2.2 (element⁻¹ : ↥Y) (element⁻¹ : ↥Y).2
    rw [hπ, eq_comm, Step163Alt.mk_eq_mk_iff]
    simpa only [commutatorElement_def, Subgroup.coe_inv, mul_assoc, inv_inv] using h
  set K := Y ⊓ Subgroup.centralizer (B : Set G) with hK
  set κ : ↥Y →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (φ.toMonoidHom.comp π) with hκ
  set f : ↥K →* Perm (Fin 7) := κ.comp (Subgroup.inclusion inf_le_left) with hf
  have hfker : IsPGroup 2 f.ker := by
    rintro ⟨z, hz⟩
    have hz1 : π (Subgroup.inclusion inf_le_left z) = 1 := by
      have h1 : φ (π (Subgroup.inclusion inf_le_left z)) = 1 :=
        Subtype.ext (by simpa [hf, hκ] using hz)
      rw [← map_one φ] at h1
      exact φ.injective h1
    have hzO : (z : G) ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Step163Alt.mem_pCore_two_iff] at hz1
      exact hz1
    obtain ⟨n, hn⟩ := hOp ⟨z, hzO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hEf : eNine ≤ f.range := by
    intro z hz
    have hzA := eNine_le_alternatingGroup hz
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (φ.symm ⟨z, hzA⟩)
    obtain ⟨y', hy'C, hy'⟩ := hlift y
    refine ⟨⟨y', y'.2, hy'C⟩, ?_⟩
    change ((φ (π y') : alternatingGroup (Fin 7)) : Perm (Fin 7)) = z
    rw [hy', show π y = φ.symm ⟨z, hzA⟩ from hy, MulEquiv.apply_symm_apply]
  obtain ⟨F, hFK, hF, hF9⟩ := Step163Alt.exists_elemAbelian_lift f hfker isElemAbelian_eNine hEf
  rw [card_eNine] at hF9
  have hFY : F ≤ Y := hFK.trans inf_le_left
  have hFB : F ≤ Subgroup.centralizer (B : Set G) := hFK.trans inf_le_right
  have hFb : ∀ x ∈ F, x * b = b * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hFB hx) b
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))).symm
  have hFb' : ∀ x ∈ F, x * b' = b' * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hFB hx) b'
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))).symm
  have hb3 : b ^ 3 = 1 := hA.2 b hb.1
  have hb'3 : b' ^ 3 = 1 := hA.2 b' hb'.1
  set E := F ⊔ Subgroup.zpowers b with hEdef
  have hE : CFSG.Assembly.IsElemAbelian 3 E := Sec15.isElemAbelian_sup_zpowers hF hb3 hFb
  have hdisj : Disjoint F (Subgroup.zpowers b) := by
    rw [Subgroup.disjoint_def]
    intro x hxF hxb
    exact hDY x ((Subgroup.zpowers_le.mpr hbD) hxb) (hFY hxF)
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hFb))
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb3 hb1
  have hE27 : Nat.card E = 27 := by
    rw [hEdef, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer F _ hbN hdisj,
      hF9, hbcard]
  have hEE : E ∈ partTwoE G :=
    ⟨hE, hE27, O, hO, hOp, sup_le (hFY.trans hYO) (Subgroup.zpowers_le.mpr (hAO hb.1))⟩
  have hEb' : ∀ x ∈ E, x * b' = b' * x := by
    have hle : E ≤ Subgroup.centralizer ({b'} : Set G) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hFb' x hx)) ?_
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      exact Subgroup.mem_centralizer_iff.mp (hAC hb'.1) b hb.1
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hsup := hmax E hEE (E ⊔ Subgroup.zpowers b') (Sec15.isElemAbelian_sup_zpowers hE hb'3 hEb')
    le_sup_left
  have hb'E : b' ∈ E :=
    hsup ▸ (le_sup_right : Subgroup.zpowers b' ≤ E ⊔ Subgroup.zpowers b') (Subgroup.mem_zpowers b')
  have hb'mul : b' ∈ (F : Set G) * (Subgroup.zpowers b : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left F _ hbN]
    exact hb'E
  obtain ⟨x, hxF, y, hy, hxy⟩ := Set.mem_mul.mp hb'mul
  have hxD : x ∈ D := by
    have e : x = b' * y⁻¹ := by rw [← hxy]; group
    rw [e]
    exact D.mul_mem hb'D (D.inv_mem ((Subgroup.zpowers_le.mpr hbD) hy))
  have hx1 := hDY x hxD (hFY hxF)
  rw [← hxy, hx1, one_mul]
  exact hy

theorem sectionCentralizer_eq_zpowers_of_mem {A Y : Subgroup G}
    (hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))
    {c : G} (hc : c ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) (hc1 : c ≠ 1) :
    Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers c : Set G) := by
  ext t
  constructor
  · exact fun ht => mem_zpowers_of_mem_sectionCentralizer hmax hA hAY hO φ hc hc1 ht
  · intro ht
    have hcD : c ∈ A ⊓ CFSG.GH74.GLS.centralizerSection Y (CFSG.Open.pCoreOf 2 Y) :=
      ⟨hc.1, mem_centralizerSection_of_mem hAY hc⟩
    have htD := (Subgroup.zpowers_le.mpr hcD) ht
    refine ⟨htD.1, fun y hy => ?_⟩
    have h := htD.2.2.2 y hy
    have e : t * y * t⁻¹ * y⁻¹ = ⁅y, t⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h

end CFSG.RankThree.PartTwo.Sec16.Res162
