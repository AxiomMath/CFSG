module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Quasithin.Recognition.St84.Gen.SL2InnerAut
import CFSG.Quasithin.EmptyFaithful.S153G93DSL2CMain
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_surjective_SL2_of_isL2Quot {L : Subgroup G} {n : ℕ}
    (hq : IsL2Quot n (oTwoQuot ↥L)) :
    ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective α ∧ α.ker = (pCoreOf 2 L).subgroupOf L := by
  obtain ⟨e0⟩ := hq
  let e : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e0.trans (CFSG.Quasithin.pslTwoGf2EquivSl n)
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  refine ⟨α, e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk',
    CFSG.openPCoreOf_subgroupOf]

private theorem map_subgroupOf_eq_map_subgroupOf_of_sup_pCore
    {L T A Q : Subgroup G} {H : Type*} [Group H] (α : ↥L →* H)
    (hker : α.ker = Q.subgroupOf L) (hAL : A ≤ L) (hQL : Q ≤ L)
    (hAT : A ⊔ Q = T) :
    (T.subgroupOf L).map α = (A.subgroupOf L).map α := by
  have hTsub : T.subgroupOf L = A.subgroupOf L ⊔ Q.subgroupOf L := by
    rw [← hAT, Subgroup.subgroupOf_sup hAL hQL]
  have hQmap : (Q.subgroupOf L).map α = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [hker]
    exact hx
  rw [hTsub, Subgroup.map_sup, hQmap, sup_bot_eq]

private theorem image_sylow_data {L T A Q : Subgroup G} {H : Type*} [Group H]
    (α : ↥L →* H) (hα : Function.Surjective α) (hker : α.ker = Q.subgroupOf L)
    (hT : IsSylowTwoOf T L) (hA : A ≤ T) (hQL : Q ≤ L) (hAT : A ⊔ Q = T) :
    IsPGroup 2 ((T.subgroupOf L).map α) ∧
      ¬ 2 ∣ ((T.subgroupOf L).map α).index ∧
      (T.subgroupOf L).map α = (A.subgroupOf L).map α := by
  have hTL : T ≤ L := hT.1
  have hAL : A ≤ L := hA.trans hTL
  have hQT : Q ≤ T := hAT ▸ le_sup_right
  have hS2 : IsPGroup 2 (T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hker_le : α.ker ≤ T.subgroupOf L := by
    rw [hker]
    exact Subgroup.subgroupOf_mono L hQT
  refine ⟨hS2.map α, ?_,
    map_subgroupOf_eq_map_subgroupOf_of_sup_pCore α hker hAL hQL hAT⟩
  rw [Subgroup.index_map_eq (H := T.subgroupOf L) hα hker_le]
  exact hT.2.2

private theorem fixes_image_of_centralizes_mod_pCore {L Q A : Subgroup G} {H : Type*} [Group H]
    {c : G} (α : ↥L →* H) (θ : H ≃* H)
    (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hθ : ∀ x y : ↥L, (y : G) = c * (x : G) * c⁻¹ → θ (α x) = α y)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q)
    (hQL : Q ≤ L) (hcA : ∀ a ∈ A, c * a * c⁻¹ * a⁻¹ ∈ Q) :
    ∀ x ∈ (A.subgroupOf L).map α, θ x = x := by
  rintro x ⟨a, ha, rfl⟩
  have haA : (a : G) ∈ A := ha
  let q : ↥L := ⟨c * (a : G) * c⁻¹ * (a : G)⁻¹, hQL (hcA (a : G) haA)⟩
  let y : ↥L := ⟨c * (a : G) * c⁻¹,
    (Subgroup.mem_normalizer_iff.mp hcL (a : G)).mp a.2⟩
  have hy : y = q * a := by
    apply Subtype.ext
    simp only [y, q, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  have hαq : α q = 1 := (hker q).mpr (by simpa [q] using hcA (a : G) haA)
  have h := hθ a y rfl
  rw [hy, map_mul, hαq, one_mul] at h
  exact h

theorem exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot_of_commutator_mem {L T A : Subgroup G}
    [Finite ↥L] {n : ℕ} (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hA : A ≤ T)
    (hAT : A ⊔ pCoreOf 2 L = T) {c : G} (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcA : ∀ a ∈ A, c * a * c⁻¹ * a⁻¹ ∈ pCoreOf 2 L) :
    ∃ a ∈ A, ∀ l ∈ L, ⁅c * a⁻¹, l⁆ ∈ pCoreOf 2 L := by
  classical
  let Q : Subgroup G := pCoreOf 2 L
  let F : Type := GaloisField 2 n
  obtain ⟨α, hα, hαker'⟩ := exists_surjective_SL2_of_isL2Quot hq
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    rw [hαker', CFSG.openPCoreOf_subgroupOf]
  have hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q := by
    intro x
    rw [← MonoidHom.mem_ker, hαker]
    exact (CFSG.mem_openPCoreOf_iff x).symm
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hcL
  obtain ⟨θ, hθ⟩ := exists_mulAut_of_normalizes α hα hker hcL hcQ
  obtain ⟨hPp, hidx, hPA⟩ :=
    image_sylow_data α hα (by simpa [Q] using hαker') hT hA hQL (by simpa [Q] using hAT)
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := (T.subgroupOf L).map α
  have hfix : ∀ x ∈ P, θ x = x := by
    intro x hx
    change x ∈ (T.subgroupOf L).map α at hx
    rw [hPA] at hx
    exact fixes_image_of_centralizes_mod_pCore α θ hcL hθ hker hQL hcA x hx
  obtain ⟨p, hpP, hpconj⟩ :=
    CFSG.Quasithin.S153G93D.SL2C.exists_inner_of_fixes_sylow hPp hidx θ hfix
  rw [hPA] at hpP
  obtain ⟨a, ha, haeq⟩ := hpP
  have haA : (a : G) ∈ A := ha
  refine ⟨(a : G), haA, fun l hl => ?_⟩
  let x : ↥L := ⟨l, hl⟩
  let z : ↥L := a⁻¹ * x * a
  let y : ↥L := ⟨c * (z : G) * c⁻¹,
    (Subgroup.mem_normalizer_iff.mp hcL (z : G)).mp z.2⟩
  have hyθ : (y : G) = c * (z : G) * c⁻¹ := rfl
  have hαy : α y = α x := by
    have h1 : θ (α z) = α y := hθ z y hyθ
    have hzα : α z = p⁻¹ * α x * p := by simp [z, haeq]
    have h2 : θ (α z) = α x := by
      rw [hpconj (α z), hzα]
      group
    rw [← h1, h2]
  have hmem : ((y * x⁻¹ : ↥L) : G) ∈ Q :=
    (hker (y * x⁻¹)).mp (by rw [map_mul, map_inv, hαy, mul_inv_cancel])
  have hval : ((y * x⁻¹ : ↥L) : G) = ⁅c * (a : G)⁻¹, l⁆ := by
    simp only [y, z, x, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      inv_inv, commutatorElement_def]
    group
  rw [hval] at hmem
  simpa [Q] using hmem

theorem exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot {L T A : Subgroup G} [Finite ↥L]
    {n : ℕ} (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hA : A ≤ T)
    (hAT : A ⊔ pCoreOf 2 L = T) {c : G} (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcA : ∀ a ∈ A, c * a = a * c) :
    ∃ a ∈ A, ∀ l ∈ L, ⁅c * a⁻¹, l⁆ ∈ pCoreOf 2 L := by
  refine exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot_of_commutator_mem hq hT hA hAT hcL
    (fun a ha => ?_)
  have h : c * a * c⁻¹ * a⁻¹ = 1 := by rw [hcA a ha]; group
  simpa [h] using (pCoreOf 2 L).one_mem

end CFSG.Quasithin.F112R.St84
