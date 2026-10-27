module

public import CFSG.Quasithin.Vol2.Asc94.HeNB1
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeInputs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS81NXKernel

public section

namespace CFSG.ComponentClassification.AS81.HeTriNB

section Sup

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.AS81.HeSylow

variable {G : Type} [Group G] [Finite G]

theorem sup_le_of_isSylowOf_normalizer {A R : Subgroup G} {g : G} {E F S₁ : Subgroup G}
    (hset : Sec4SettingNB G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) : E ⊔ F ≤ S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hSN
  have hP : IsPGroup 2 ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))) :=
    hset.frame.sylow.isPGroup.of_equiv (subgroupOfEquivOfLe le_normalizer).symm
  have : ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))).Normal :=
    normal_in_normalizer
  have hle := hP.le_sylow_of_normal T
  intro x hx
  rw [← hT]
  exact ⟨⟨x, le_normalizer hx⟩, hle (show (⟨x, le_normalizer hx⟩ : ↥(normalizer
    ((E ⊔ F : Subgroup G) : Set G))) ∈ (E ⊔ F).subgroupOf _ from hx), rfl⟩

end Sup

section Step42

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem step42_quot_of {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hS : Sec4SettingNB G A R g E F) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ((E ⊔ F).relIndex S₁ = 4 ∧ (∀ s ∈ S₁, s * s ∈ E ⊔ F) ∧ S₁ ≤ normalizer (E : Set G)) ∨
      ((∃ φ : ↥S₁ →* DihedralGroup 4, Function.Surjective φ ∧
          φ.ker = (E ⊔ F).subgroupOf S₁) ∧
        ∃ n ∈ normalizer (A : Set G), rightConjugate E n = F) :=
  (planeData_of hE16 h11 hS.frame hS.even).step42_quot
    (planeData_of hE16 h11 hS.frame.swap hS.even) hS₁

end Step42

section HeInputs

open Subgroup CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.ABGLocalTools CFSG.LargeExtraspecial
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem card_sylow_eq (hM : HeTri.HeModelFacts) (hQ : Sec4QNB G A R g E F S₁ Q z)
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2))))) :
    Nat.card S₁ = 1024 := by
  have hCz := HeTri.card_centralizer_eq hM hC
  have hcardS : Nat.card S₁ = 2 ^ (Nat.card G).factorization 2 := by
    have := hQ.sylow.card_eq
    rwa [card_top] at this
  set k := (Nat.card G).factorization 2 with hk
  have h1 : 2 ^ k ∣ 21504 := by
    rw [← hcardS, ← hCz]
    exact card_dvd_of_le hQ.le_centralizer
  have h2 : 2 ^ 10 ∣ Nat.card G := by
    have h := card_subgroup_dvd_card (centralizer ({z} : Set G))
    rw [hCz] at h
    exact (by norm_num : 2 ^ 10 ∣ 21504).trans h
  have h3 : 10 ≤ k :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  have h4 : k ≤ 10 := by
    by_contra h
    have : 2 ^ 11 ∣ 21504 := (Nat.pow_dvd_pow 2 (by omega)).trans h1
    omega
  rw [hcardS, show k = 10 by omega]
  norm_num

theorem sylow_le_normalizer_left {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hS : Sec4SettingNB G A R g E F)
    (hS₁N : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)))
    (hS₁ : Nat.card S₁ = 1024) : S₁ ≤ normalizer (E : Set G) := by
  rcases step42_quot_of hE16 h11 hS hS₁N with ⟨-, -, hle⟩ | ⟨⟨φ, hφ, hφk⟩, -⟩
  · exact hle
  · exfalso
    have hD := planeData_of hE16 h11 hS.frame hS.even
    have hEFS := sup_le_of_isSylowOf_normalizer hS hS₁N
    have h := card_eq_card_ker_mul φ hφ
    rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hEFS).toEquiv, hD.card_sup,
      DihedralGroup.nat_card, hS₁] at h
    norm_num at h

theorem sylow_le_normalizer {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hQ : Sec4QNB G A R g E F S₁ Q z) (hS₁ : Nat.card S₁ = 1024) :
    S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G) := by
  have hS := hQ.setting
  have hS' : Sec4SettingNB G A R g F E :=
    ⟨hS.frame.swap, hS.type, hS.even, hS.top⟩
  have hS₁N' : IsSylowOf 2 S₁ (normalizer ((F ⊔ E : Subgroup G) : Set G)) := by
    rw [sup_comm]
    exact hQ.sylowN
  exact le_inf (sylow_le_normalizer_left hE16 h11 hS hQ.sylowN hS₁)
    (sylow_le_normalizer_left hE16 h11 hS' hS₁N' hS₁)

theorem sylow_le_iX (hQ : Sec4QNB G A R g E F S₁ Q z) (hS₁ : Nat.card S₁ = 1024)
    (hN : S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G)) : S₁ ≤ iX z E ⊓ iX z F := by
  have hc : Nat.card S₁ = 2 ^ 10 := by rw [hS₁]; norm_num
  exact le_inf (le_oUpper_of_card (le_inf hQ.le_centralizer (hN.trans inf_le_left)) hc)
    (le_oUpper_of_card (le_inf hQ.le_centralizer (hN.trans inf_le_right)) hc)

theorem sec4He_inputs {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) (hM : HeTri.HeModelFacts)
    (hQ : Sec4QNB G A R g E F S₁ Q z)
    (h46 : ∀ X ∈ ({E, F} : Set (Subgroup G)),
      X ≤ iX z X ∧
        ∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
          Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X))
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2))))) :
    Nat.card S₁ = 1024 ∧ S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G) ∧ E ⊔ F ≤ S₁ ∧
      S₁ ≤ iX z E ⊓ iX z F ∧ Nat.card (iX z E) = 3072 ∧ Nat.card (iX z F) = 3072 := by
  have hS₁ := card_sylow_eq hM hQ hC
  have hN := sylow_le_normalizer hE16 h11 hQ hS₁
  have hF := hQ.setting.frame
  obtain ⟨hEI, φE, hφE, hφEk⟩ := h46 E (by simp)
  obtain ⟨hFI, φF, hφF, hφFk⟩ := h46 F (by simp)
  exact ⟨hS₁, hN, sup_le_of_isSylowOf_normalizer hQ.setting hQ.sylowN, sylow_le_iX hQ hS₁ hN,
    HeTri.card_iX_eq hEI hφE hφEk hF.cardE, HeTri.card_iX_eq hFI hφF hφFk hF.cardF⟩

end HeInputs

end CFSG.ComponentClassification.AS81.HeTriNB

namespace CFSG.ComponentClassification.AS81

section Step44iiDef

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Step44iiNB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4SettingNB G A R g E F →
      ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)) →
        (Nat.card S₁ = 2 ^ 10 ∧ ∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) ∨
        (Nat.card S₁ = 2 ^ 11 ∧
          ∃ (H : Type) (_ : Group H) (_ : Finite H) (K : Subgroup H), K.Normal ∧
            IsSporadic K .He ∧ K.index = 2 ∧ centralizer (K : Set H) = ⊥ ∧
            ∃ P : Sylow 2 H, Nonempty (S₁ ≃* P))

end Step44iiDef

section Step44Sylow

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.NativeSporadic HeSylow
open CFSG.Sporadic.HeldB

theorem step44_sylow_of_NB
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hset : Sec4SettingNB G A R g E F) (S₁ : Subgroup G)
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    (Nat.card S₁ = 2 ^ 10 ∧ ∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) ∨
      (Nat.card S₁ = 2 ^ 11 ∧
        ∃ (H : Type) (_ : Group H) (_ : Finite H) (K : Subgroup H), K.Normal ∧
          IsSporadic K .He ∧ K.index = 2 ∧ centralizer (K : Set H) = ⊥ ∧
          ∃ P : Sylow 2 H, Nonempty (S₁ ≃* P)) := by
  rcases sylow_equiv_model Hexa.hexa_check Hexa.hexaStab_check Hexa.step44_check
      (planeData_of hE16 h11 hset.frame hset.even)
      (planeData_of hE16 h11 hset.frame.swap hset.even) hS₁ with ⟨hc, ⟨e⟩⟩ | ⟨hc, ⟨e⟩⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (Carrier .He)))
    obtain ⟨e₀⟩ := nonempty_sylow_he_equiv P
    exact Or.inl ⟨hc, P, ⟨e.trans e₀.symm⟩⟩
  · have hK : IsSporadic (heP.subgroupOf heAutGroup) .He :=
      ⟨(subgroupOfEquivOfLe heP_le_heAutGroup).trans
        (heEquivP : Blueprint.NativeSporadic.Carrier .He ≃* ↥heP).symm⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥heAutGroup))
    obtain ⟨e₀⟩ := nonempty_sylow_aut_equiv heP_normal_heAutGroup hK heP_relIndex_heAutGroup
      centralizer_heP_eq_bot P
    exact Or.inr ⟨hc, ↥heAutGroup, inferInstance, inferInstance, heP.subgroupOf heAutGroup,
      heP_normal_heAutGroup, hK, heP_relIndex_heAutGroup, centralizer_heP_eq_bot, P,
      ⟨e.trans e₀.symm⟩⟩

theorem step44iiNB_of
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) : Step44iiNB :=
  fun _ _ _ _ _ _ _ _ hset S₁ hS₁ => step44_sylow_of_NB hE16 h11 hset S₁ hS₁

end Step44Sylow

section NXAct

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

@[expose] def Sec4NXKernelNB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4SettingNB G A R g E F → ∀ X ∈ ({E, F} : Set (Subgroup G)),
      AS76b.oUpperTwoPrime (normalizer (X : Set G)) ⊓
        AS76b.oddCoreIn (centralizer (A : Set G)) = ⊥

end NXAct

section NXKernel

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

theorem sec4NXKernelNB_of
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) :
    Sec4NXKernelNB := by
  intro G _ _ A R g E F hset X hX
  have hD := planeData_of hE16 h11 hset.frame hset.even
  have hD' := planeData_of hE16 h11 hset.frame.swap hset.even
  rcases hX with rfl | rfl
  · exact NXKernel.oUpper_inf_eq_bot_of_planeData h4 h34 hE16 hD' hD
  · exact NXKernel.oUpper_inf_eq_bot_of_planeData h4 h34 hE16 hD hD'

end NXKernel

section NXModel

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow Hexa CFSG.Monster.B.Co2

@[expose] def Sec4NXModelNB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4SettingNB G A R g E F → ∀ X ∈ ({E, F} : Set (Subgroup G)),
      ∃ (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM),
        Function.Surjective ψ ∧
        ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))) ∧
        (∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
          (y : G) = ℓ * x * (ℓ : G)⁻¹ →
            (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹) ∧
        ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0

end NXModel

section NXCheck

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

theorem sec4NXModelNB_of_check {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hc : hexaCheck = true) (hS : hexaStabCheck = true) (hK : Sec4NXKernelNB) :
    Sec4NXModelNB := by
  intro G _ _ A R g E F hset X hX
  have hD := planeData_of hE16 h11 hset.frame hset.even
  have hD' := planeData_of hE16 h11 hset.frame.swap hset.even
  have hKX := hK G A R g E F hset X hX
  rcases hX with rfl | rfl
  · obtain ⟨ι, ψ, hs, hk, he, hR⟩ := hD.nxModel hc hS hD'
    exact ⟨ι, ψ, hs, hk.trans (hD.centralizer_subgroupOf_oUpper hKX), he, hR⟩
  · obtain ⟨ι, ψ, hs, hk, he, hR⟩ := hD'.nxModel hc hS hD
    exact ⟨ι, ψ, hs, hk.trans (hD'.centralizer_subgroupOf_oUpper hKX), he, hR⟩

end NXCheck

theorem sec4NXModelNB_of
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) (hK : Sec4NXKernelNB) :
    Sec4NXModelNB :=
  sec4NXModelNB_of_check hE16 h11 Hexa.hexa_check Hexa.hexaStab_check hK

end CFSG.ComponentClassification.AS81
