module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Quasithin.Recognition.HSType17m
public import CFSG.LargeExtraspecial.A2ModSLModel
public import CFSG.Walter.J1Props.Janko
public import CFSG.Walter.Models
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

scoped instance generalizedFitting_normal_inst (X : Type) [Group X] [Finite X] :
    (CFSG.generalizedFitting X).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic).2

@[expose] def IsHSType (G : Type) [Group G] [Finite G] : Prop :=
  ∃ (z : G) (V : Subgroup G), z ^ 2 = 1 ∧ z ≠ 1 ∧ IsElemAbelian 2 V ∧ Nat.card ↥V = 8 ∧
    (IsZ4StarQ8Sq ↥(CFSG.generalizedFitting ↥(Subgroup.centralizer ({z} : Set G))) ∧
      Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ⧸
        CFSG.generalizedFitting ↥(Subgroup.centralizer ({z} : Set G)) ≃* Equiv.Perm (Fin 5))) ∧
    (V ≤ (CFSG.generalizedFitting ↥(Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype ∧
      Nonempty (↥(CFSG.generalizedFitting ↥(Subgroup.normalizer (V : Set G))) ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      StatedClassicalModel (↥(Subgroup.normalizer (V : Set G)) ⧸
        CFSG.generalizedFitting ↥(Subgroup.normalizer (V : Set G))) .PSL 3 2 1)

@[expose] def IsJ1Type (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G ∧ ∃ z : G, IsTwoCentralInvolution z ∧
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
      (PSL(2, F4) × Multiplicative (ZMod 2)))

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsHSType G → NativeSporadic.IsSporadic G .HS

section BurnsideId

private theorem burnsideId_mul_aux {X : Type*} [Group X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
    (hba : b₁ * a₂ = a₂ * b₁) (hca : c₁ * a₂ = a₂ * c₁) (hcb : c₁ * b₂ = b₂ * c₁) :
    a₁ * a₂ * (b₁ * b₂) * (c₁ * c₂) = a₁ * b₁ * c₁ * (a₂ * b₂ * c₂) := by
  have h1 : b₁ * c₁ * a₂ = a₂ * (b₁ * c₁) := by
    rw [mul_assoc, hca, ← mul_assoc, hba, mul_assoc]
  have h2 : c₁ * b₂ = b₂ * c₁ := hcb
  calc a₁ * a₂ * (b₁ * b₂) * (c₁ * c₂)
      = a₁ * (a₂ * (b₁ * (b₂ * c₁))) * c₂ := by simp only [mul_assoc]
    _ = a₁ * (a₂ * (b₁ * (c₁ * b₂))) * c₂ := by rw [h2]
    _ = a₁ * (a₂ * (b₁ * c₁)) * b₂ * c₂ := by simp only [mul_assoc]
    _ = a₁ * (b₁ * c₁ * a₂) * b₂ * c₂ := by rw [h1]
    _ = a₁ * b₁ * c₁ * (a₂ * b₂ * c₂) := by simp only [mul_assoc]

private theorem burnsideId_eq_of_involution {X K : Type*} [Group X] [Group K] {S : Subgroup X}
    (e : S ≃* K) {t : K} (ht : ∀ k : K, k ^ 2 = 1 → k ≠ 1 → k = t) {w : X} (hw : w ∈ S)
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : w = (e.symm t : X) := by
  have hsq : (⟨w, hw⟩ : S) ^ 2 = 1 := Subtype.ext (by simpa using hw2)
  have hne : (⟨w, hw⟩ : S) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have h1 : e ⟨w, hw⟩ = t := ht _ (by rw [← map_pow, hsq, map_one])
    (fun h => hne (e.injective (h.trans (map_one e).symm)))
  rw [← h1]
  simp

open CFSG.Quasithin.HSType in
private theorem burnsideId_isZ4Q8Q8_of_isZ4StarQ8Sq {X : Type} [Group X]
    (h : CFSG.ASVolI.ChIJK.IsZ4StarQ8Sq X) : IsZ4Q8Q8 X := by
  obtain ⟨A, B, C, ⟨eA⟩, ⟨eB⟩, ⟨eC⟩, hABC, hAB, hAC, hBC, hcard, hAC', -⟩ := h
  let ψ : (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) →* X :=
    { toFun := fun t => (eA.symm t.1 : X) * (eB.symm t.2.1 : X) * (eC.symm t.2.2 : X)
      map_one' := by simp
      map_mul' := fun s t => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
        exact burnsideId_mul_aux
          (hAB _ (eA.symm t.1).2 _ (eB.symm s.2.1).2).symm
          (hAC _ (eA.symm t.1).2 _ (eC.symm s.2.2).2).symm
          (hBC _ (eB.symm t.2.1).2 _ (eC.symm s.2.2).2).symm }
  have hψ : ∀ t, ψ t = (eA.symm t.1 : X) * (eB.symm t.2.1 : X) * (eC.symm t.2.2 : X) :=
    fun t => rfl
  have hsurj : Function.Surjective ψ := by
    have hA : A ≤ ψ.range := fun x hx => ⟨(eA ⟨x, hx⟩, 1, 1), by simp [hψ]⟩
    have hB : B ≤ ψ.range := fun x hx => ⟨(1, eB ⟨x, hx⟩, 1), by simp [hψ]⟩
    have hC : C ≤ ψ.range := fun x hx => ⟨(1, 1, eC ⟨x, hx⟩), by simp [hψ]⟩
    have : (⊤ : Subgroup X) ≤ ψ.range := hABC ▸ sup_le (sup_le hA hB) hC
    exact MonoidHom.range_eq_top.mp (top_le_iff.mp this)
  have hne : A ⊓ B ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hw1' : w ≠ 1 := fun h0 => hw1 (Subtype.ext h0)
  have hw2 : w ^ 2 = 1 := by
    have h2 : (⟨w, hw⟩ : ↥(A ⊓ B)) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := (⟨w, hw⟩ : ↥(A ⊓ B)))
      rwa [hcard] at this
    simpa using congrArg Subtype.val h2
  have hwA : w ∈ A := (Subgroup.mem_inf.mp hw).1
  have hwB : w ∈ B := (Subgroup.mem_inf.mp hw).2
  have hwC : w ∈ C := (Subgroup.mem_inf.mp (hAC' ▸ hw)).2
  have hA2 : w = (eA.symm (Multiplicative.ofAdd 2) : X) :=
    burnsideId_eq_of_involution eA (by decide) hwA hw2 hw1'
  have hB2 : w = (eB.symm (QuaternionGroup.a 2) : X) :=
    burnsideId_eq_of_involution eB (by decide) hwB hw2 hw1'
  have hC2 : w = (eC.symm (QuaternionGroup.a 2) : X) :=
    burnsideId_eq_of_involution eC (by decide) hwC hw2 hw1'
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  have hle : z4Q8Q8Ident ≤ ψ.ker := by
    rw [z4Q8Q8Ident, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ]
      simp only [map_one, Subgroup.coe_one, mul_one]
      rw [← hA2, ← hB2, hww]
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ]
      simp only [map_one, Subgroup.coe_one, mul_one, one_mul]
      rw [← hA2, ← hC2, hww]
  have hker : ψ.ker ≤ z4Q8Q8Ident := by
    intro t ht
    rw [MonoidHom.mem_ker, hψ] at ht
    obtain ⟨s1, s2, s3⟩ := t
    dsimp only at ht
    have hB2eq : (eB.symm s2 : X) = (eA.symm s1 : X)⁻¹ * (eC.symm s3 : X)⁻¹ := by
      have : (eB.symm s2 : X) = (eA.symm s1 : X)⁻¹ *
          ((eA.symm s1 : X) * (eB.symm s2 : X) * (eC.symm s3 : X)) * (eC.symm s3 : X)⁻¹ := by
        group
      rw [ht, mul_one] at this
      exact this
    have hC3eq : (eC.symm s3 : X) = ((eA.symm s1 : X) * (eB.symm s2 : X))⁻¹ := by
      have : (eC.symm s3 : X) = ((eA.symm s1 : X) * (eB.symm s2 : X))⁻¹ *
          ((eA.symm s1 : X) * (eB.symm s2 : X) * (eC.symm s3 : X)) := by
        group
      rw [ht, mul_one] at this
      exact this
    have hc2 : ∀ q : QuaternionGroup 2, q * s2 = s2 * q := by
      intro q
      have hqA : Commute (eB.symm q : X) (eA.symm s1 : X) :=
        (hAB _ (eA.symm s1).2 _ (eB.symm q).2).symm
      have hqC : Commute (eB.symm q : X) (eC.symm s3 : X) :=
        hBC _ (eB.symm q).2 _ (eC.symm s3).2
      have hcomm : (eB.symm q : X) * (eB.symm s2 : X) = (eB.symm s2 : X) * (eB.symm q : X) := by
        rw [hB2eq]
        exact (hqA.inv_right.mul_right hqC.inv_right)
      apply eB.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (by simpa using hcomm)
    have hc3 : ∀ q : QuaternionGroup 2, q * s3 = s3 * q := by
      intro q
      have hqA : Commute (eC.symm q : X) (eA.symm s1 : X) :=
        (hAC _ (eA.symm s1).2 _ (eC.symm q).2).symm
      have hqB : Commute (eC.symm q : X) (eB.symm s2 : X) :=
        (hBC _ (eB.symm s2).2 _ (eC.symm q).2).symm
      have hcomm : (eC.symm q : X) * (eC.symm s3 : X) = (eC.symm s3 : X) * (eC.symm q : X) := by
        rw [hC3eq]
        exact (hqA.mul_right hqB).inv_right
      apply eC.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (by simpa using hcomm)
    have key : ∀ s : QuaternionGroup 2, (∀ q : QuaternionGroup 2, q * s = s * q) →
        s = 1 ∨ s = QuaternionGroup.a 2 := by decide
    have hs1 : ∀ t, (eA.symm s1 : X) = (eA.symm t : X) → s1 = t :=
      fun t h => eA.symm.injective (Subtype.ext h)
    have hone : (eA.symm (1 : Multiplicative (ZMod 4)) : X) = 1 := by simp
    have hone2 : (eB.symm (1 : QuaternionGroup 2) : X) = 1 := by simp
    have hone3 : (eC.symm (1 : QuaternionGroup 2) : X) = 1 := by simp
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hg12 : ((Multiplicative.ofAdd 2 : Multiplicative (ZMod 4)),
        (QuaternionGroup.a 2 : QuaternionGroup 2), (1 : QuaternionGroup 2)) *
        (Multiplicative.ofAdd 2, 1, (QuaternionGroup.a 2 : QuaternionGroup 2)) =
        ((1 : Multiplicative (ZMod 4)), (QuaternionGroup.a 2 : QuaternionGroup 2),
          (QuaternionGroup.a 2 : QuaternionGroup 2)) := by decide
    rcases key s2 hc2 with rfl | rfl <;> rcases key s3 hc3 with rfl | rfl
    · rw [hone2, hone3, mul_one, mul_one] at ht
      have : s1 = 1 := hs1 1 (by rw [ht, hone])
      subst this
      exact Subgroup.one_mem _
    · rw [← hC2, hone2, mul_one] at ht
      have h1 : (eA.symm s1 : X) = w := by
        rw [eq_inv_of_mul_eq_one_left ht, hwinv]
      have : s1 = Multiplicative.ofAdd 2 := hs1 _ (h1.trans hA2)
      subst this
      exact Subgroup.subset_closure (by simp)
    · rw [← hB2, hone3, mul_one] at ht
      have h1 : (eA.symm s1 : X) = w := by
        rw [eq_inv_of_mul_eq_one_left ht, hwinv]
      have : s1 = Multiplicative.ofAdd 2 := hs1 _ (h1.trans hA2)
      subst this
      exact Subgroup.subset_closure (by simp)
    · rw [← hB2, ← hC2, mul_assoc, hww, mul_one] at ht
      have : s1 = 1 := hs1 1 (by rw [ht, hone])
      subst this
      rw [← hg12]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hker' : z4Q8Q8Ident = ψ.ker := le_antisymm hle hker
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker'.symm)⟩

private theorem burnsideId_quasithinGenFitting_eq_map {B : Type*} [Group B] (Y : Subgroup B) :
    CFSG.Open.quasithinGenFitting Y = (CFSG.generalizedFitting ↥Y).map Y.subtype := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype,
    CFSG.generalizedFitting_eq_componentClassification]

private theorem burnsideId_equiv_genFitting {B : Type*} [Group B] (Y : Subgroup B) :
    Nonempty (↥(CFSG.generalizedFitting ↥Y) ≃* ↥(CFSG.Open.quasithinGenFitting Y)) :=
  ⟨(Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).trans
    (MulEquiv.subgroupCongr (burnsideId_quasithinGenFitting_eq_map Y).symm)⟩

private theorem burnsideId_exists_hom_of_equiv {X : Type*} [Group X] (F : Subgroup X) [F.Normal]
    {Y : Type*} [Group Y] (e : X ⧸ F ≃* Y) :
    ∃ φ : X →* Y, Function.Surjective φ ∧ φ.ker = F :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' F),
    e.surjective.comp (QuotientGroup.mk'_surjective F), by
      ext x
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideId_isTypeHS_of_isHSType {G : Type} [Group G] [Finite G] (h : IsHSType G) :
    CFSG.Quasithin.HSType.IsTypeHS G := by
  obtain ⟨z, V, hz2, hz1, hV, hVc, ⟨hZ, ⟨eQ⟩⟩, hle, ⟨eF⟩, hM⟩ := h
  have hmap := burnsideId_quasithinGenFitting_eq_map (Subgroup.centralizer ({z} : Set G))
  have hmapM := burnsideId_quasithinGenFitting_eq_map (Subgroup.normalizer (V : Set G))
  refine ⟨z, V, orderOf_eq_prime hz2 hz1, hV, hVc, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨e⟩ := burnsideId_equiv_genFitting (Subgroup.centralizer ({z} : Set G))
    obtain ⟨e'⟩ := burnsideId_isZ4Q8Q8_of_isZ4StarQ8Sq hZ
    exact ⟨e.symm.trans e'⟩
  · obtain ⟨φ, hφ, hker⟩ := burnsideId_exists_hom_of_equiv _ eQ
    refine ⟨φ, hφ, ?_⟩
    rw [hker, hmap]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  · rw [hmap]
    exact hle
  · obtain ⟨e⟩ := burnsideId_equiv_genFitting (Subgroup.normalizer (V : Set G))
    exact ⟨e.symm.trans eF⟩
  · obtain ⟨-, ⟨e⟩⟩ := CFSG.LargeExtraspecial.A2Mod.nonempty_mulEquiv_of_statedClassicalModel hM
    obtain ⟨θ, hθ, hker⟩ := burnsideId_exists_hom_of_equiv _ e
    refine ⟨θ, hθ, ?_⟩
    rw [hker, hmapM]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm


private theorem burnsideId_psl_four_equiv_alternating :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
      alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcard])
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four _ hcard)

private theorem burnsideId_exists_factor {G : Type} [Group G] {A : Type} [Group A]
    (hA : Subgroup.center A = ⊥) {z : G} (hz1 : z ≠ 1)
    (e : ↥(Subgroup.centralizer ({z} : Set G)) ≃* A × Multiplicative (ZMod 2)) :
    ∃ F : Subgroup G, F ≤ Subgroup.centralizer ({z} : Set G) ∧ z ∉ F ∧
      (∀ x ∈ Subgroup.centralizer ({z} : Set G), x ∈ F ∨ z * x ∈ F) ∧ Nonempty (F ≃* A) := by
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let ι : A →* G := (Subgroup.centralizer ({z} : Set G)).subtype.comp
    (e.symm.toMonoidHom.comp (MonoidHom.inl A (Multiplicative (ZMod 2))))
  have hι : Function.Injective ι := fun a b hab =>
    congrArg Prod.fst (e.symm.injective (Subtype.ext hab))
  have hιapp : ∀ a, ι a = ((e.symm (a, 1) : ↥(Subgroup.centralizer ({z} : Set G))) : G) :=
    fun a => rfl
  let ζ : ↥(Subgroup.centralizer ({z} : Set G)) := ⟨z, hzC⟩
  obtain ⟨⟨a₀, s₀⟩, h0⟩ : ∃ p : A × Multiplicative (ZMod 2), e ζ = p := ⟨_, rfl⟩
  have hcen : ∀ p : A × Multiplicative (ZMod 2), p * e ζ = e ζ * p := by
    intro p
    obtain ⟨y, rfl⟩ := e.surjective p
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  have ha₀ : a₀ = 1 := by
    have : a₀ ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro a
      have := congrArg Prod.fst (hcen (a, 1))
      rw [h0] at this
      simpa using this
    rw [hA] at this
    exact this
  have hs₀ : s₀ ≠ 1 := by
    intro hs
    apply hz1
    have : ζ = 1 := e.injective (by rw [h0, ha₀, hs, map_one]; rfl)
    exact congrArg Subtype.val this
  have hZ2 : ∀ s t : Multiplicative (ZMod 2), s ≠ 1 → t ≠ 1 → s = t := by decide
  have hsq : ∀ s : Multiplicative (ZMod 2), s * s = 1 := by decide
  refine ⟨ι.range, ?_, ?_, ?_, ⟨(MonoidHom.ofInjective hι).symm⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact (e.symm (a, 1)).2
  · rintro ⟨a, ha⟩
    have hζ : ζ = e.symm (a, 1) := Subtype.ext (by rw [← hιapp]; exact ha.symm)
    have : e ζ = (a, 1) := by rw [hζ, MulEquiv.apply_symm_apply]
    rw [h0] at this
    exact hs₀ (congrArg Prod.snd this)
  · intro x hx
    obtain ⟨⟨a, s⟩, hxe⟩ : ∃ p : A × Multiplicative (ZMod 2), e ⟨x, hx⟩ = p := ⟨_, rfl⟩
    by_cases hs : s = 1
    · left
      refine ⟨a, ?_⟩
      rw [hιapp]
      have : (⟨x, hx⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = e.symm (a, 1) := by
        rw [← hs, ← hxe, MulEquiv.symm_apply_apply]
      exact (congrArg Subtype.val this).symm
    · right
      refine ⟨a, ?_⟩
      rw [hιapp]
      have hss : s₀ = s := hZ2 _ _ hs₀ hs
      have : ζ * ⟨x, hx⟩ = e.symm (a, 1) := by
        apply e.injective
        rw [map_mul, h0, hxe, MulEquiv.apply_symm_apply, ha₀, ← hss]
        simp [hsq]
      exact (congrArg Subtype.val this).symm

private theorem burnsideId_sylow_comm {G : Type} [Group G] [Finite G] {z : G} (hz2 : z ^ 2 = 1)
    {F : Subgroup G}
    (hdec : ∀ x ∈ Subgroup.centralizer ({z} : Set G), x ∈ F ∨ z * x ∈ F)
    (hF60 : Nat.card F = 60) (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hTz : ∀ x ∈ (T : Subgroup G), x * z = z * x) :
    IsMulCommutative (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsMulCommutative ↥((T : Subgroup G) ⊓ F) := by
    have hp : IsPGroup 2 ↥((T : Subgroup G) ⊓ F) := T.isPGroup'.to_le inf_le_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card ↥((T : Subgroup G) ⊓ F) ∣ 60 :=
      hF60 ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hn] at hdvd
    have hn2 : n ≤ 2 := by
      by_contra hcon
      have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := h8.trans hdvd
      omega
    interval_cases n
    · haveI : Subsingleton ↥((T : Subgroup G) ⊓ F) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · haveI : IsCyclic ↥((T : Subgroup G) ⊓ F) := isCyclic_of_prime_card (by simpa using hn)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
  have hdecT : ∀ u : ↥(T : Subgroup G), ∃ u' ∈ (T : Subgroup G) ⊓ F,
      (u : G) = u' ∨ (u : G) = z * u' := by
    intro u
    have huC : (u : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hTz u u.2)
    rcases hdec u huC with h | h
    · exact ⟨u, ⟨u.2, h⟩, Or.inl rfl⟩
    · refine ⟨z * u, ⟨(T : Subgroup G).mul_mem hzT u.2, h⟩, Or.inr ?_⟩
      rw [← mul_assoc, ← pow_two, hz2, one_mul]
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨x', hx', hx⟩ := hdecT x
  obtain ⟨y', hy', hy⟩ := hdecT y
  have hxy : Commute x' y' :=
    congrArg Subtype.val (hQ.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
  have hzx : Commute z x' := (hTz x' hx'.1).symm
  have hzy : Commute z y' := (hTz y' hy'.1).symm
  apply Subtype.ext
  show (x : G) * y = y * x
  have key : Commute (x : G) (y : G) := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact hxy
    · exact hzx.symm.mul_right hxy
    · exact hzy.mul_left hxy
    · exact ((Commute.refl z).mul_right hzy).mul_left (hzx.symm.mul_right hxy)
  exact key

private theorem burnsideId_index_ne_two {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {C : Subgroup G} (hC : 120 ∣ Nat.card C) : ∀ H : Subgroup G, H.index ≠ 2 := by
  intro H hH
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hH
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hH
    have h1 : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
    rw [hH] at h1
    have := hC.trans h1
    omega
  · rw [h, Subgroup.index_top] at hH
    omega

end BurnsideId

section

theorem as_I_4_8 : I_4_8 := by
  intro G _ _ hG
  exact CFSG.Quasithin.HSType.statementI48_holds G (burnsideId_isTypeHS_of_isHSType hG)

end

@[expose] def I_4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsJ1Type G → NativeSporadic.IsSporadic G .J1

open CFSG.Walter.J1Props CFSG.ASVolI.ChIJK in
theorem as_I_4_9 : I_4_9 := by
  intro G _ _ hG
  obtain ⟨hs, z, ⟨hz2, hz1, T, hzT, hTc⟩, ⟨e⟩⟩ := hG
  obtain ⟨eA⟩ := burnsideId_psl_four_equiv_alternating
  let e' : ↥(Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5) ×
      Multiplicative (ZMod 2) := e.trans (MulEquiv.prodCongr eA (MulEquiv.refl _))
  have hA : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  obtain ⟨F, hFC, hzF, hdec, ⟨eF⟩⟩ := burnsideId_exists_factor hA hz1 e'
  have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hF60 : Nat.card F = 60 := by rw [Nat.card_congr eF.toEquiv, hA60]
  have hC120 : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 120 := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_prod, hA60]
    simp
  have hceq : Subgroup.centralizer ({z} : Set G) = Subgroup.zpowers z ⊔ F := by
    apply le_antisymm
    · intro x hx
      rcases hdec x hx with h | h
      · exact Subgroup.mem_sup_right h
      · have : x = z * (z * x) := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
        rw [this]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) h
    · refine sup_le ?_ hFC
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let h : JankoHyp₀ G :=
    { index_ne_two := burnsideId_index_ne_two (C := Subgroup.centralizer ({z} : Set G))
        (by rw [hC120])
      abelian_sylow := CFSG.Walter.hasAbelianSylowTwo_of_sylow T
        (burnsideId_sylow_comm hz2 hdec hF60 T hzT hTc)
      t := z
      orderOf_t := orderOf_eq_prime hz2 hz1
      F := F
      le_centralizer := hFC
      t_not_mem := hzF
      centralizer_eq := hceq
      iso := eF }
  obtain ⟨eJ⟩ := h.nonempty_mulEquiv_walterJ1
  exact CFSG.Walter.isSporadic_J1_of_mulEquiv eJ

end CFSG.ASVolI
