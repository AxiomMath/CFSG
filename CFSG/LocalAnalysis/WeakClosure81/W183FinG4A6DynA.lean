module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6S6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6
import CFSG.GH74.Generic.BProg.B3.S3T5L3P
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open Equiv

theorem w183finG4A6_not_acts_of_induced {Y : Type} [Group Y]
    [Finite Y] (L : Subgroup Y) [L.Normal] (e : ↥L ≃* alternatingGroup (Fin 6)) (y : Y)
    (h : (MulAut.conjNormal y : MulAut ↥L) ∈ w183finG4A6AutS6 e) :
    ¬ ActsOnDynkinMod ⊥ L y := by
  classical
  intro hAct
  obtain ⟨hτN, P, hPpar, hmove⟩ := hAct
  obtain ⟨-, hPL, hPmax, S, -, hSL, hSpow, hSidx, hNS⟩ := hPpar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowIn 2 S L := by
    refine ⟨hSL, fun g => ?_, hSidx⟩
    obtain ⟨k, hk⟩ := hSpow (g : Y) g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTsyl : IsSylowIn 2 (S.map (MulAut.conj y).toMonoidHom) L :=
    Ch1Sec3.isSylowIn_map_conj hSyl hτN
  obtain ⟨hh, hhL, hconjT⟩ := Ch1Sec3.exists_conj_of_isSylowIn hSyl hTsyl
  have hmemT : ∀ x : Y, x ∈ S.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * x * y ∈ S := by
    intro x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
    · intro hx
      exact ⟨y⁻¹ * x * y, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hτ'S : ∀ k : Y, k ∈ S ↔ (hh⁻¹ * y) * k * (hh⁻¹ * y)⁻¹ ∈ S := by
    intro k
    have h1 := hconjT (y * k * y⁻¹)
    rw [hmemT] at h1
    have e1 : y⁻¹ * (y * k * y⁻¹) * y = k := by group
    have e2 : hh⁻¹ * (y * k * y⁻¹) * hh = (hh⁻¹ * y) * k * (hh⁻¹ * y)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have hτ'N : (hh⁻¹ * y) ∈ Subgroup.normalizer (L : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hhL)) hτN
  obtain ⟨π₀, hπ₀⟩ := (w183finG4A6_mem_autS6_iff e _).1 h
  have hπ : ∀ k : ↥L,
      ((e ((MulAut.conjNormal (hh⁻¹ * y) : MulAut ↥L) k) : alternatingGroup (Fin 6)) :
      Perm (Fin 6)) = (((e ⟨hh, hhL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))⁻¹ * π₀) *
        ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) *
        (((e ⟨hh, hhL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))⁻¹ * π₀)⁻¹ := by
    intro k
    have e1 : (MulAut.conjNormal (hh⁻¹ * y) : MulAut ↥L) k =
        (⟨hh, hhL⟩ : ↥L)⁻¹ * (MulAut.conjNormal y : MulAut ↥L) k * ⟨hh, hhL⟩ := by
      apply Subtype.ext
      simp [MulAut.conjNormal_apply, mul_assoc]
    rw [e1, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hπ₀ k]
    group
  set π : Perm (Fin 6) :=
    ((e ⟨hh, hhL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))⁻¹ * π₀ with hπdef

  have hLcard : Nat.card ↥L = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact Unc25K1.A6Model.card_alt6
  have hScard : Nat.card S = 8 := by
    rw [hSyl.card_eq, hLcard, Unc25K1.A6Model.factorization_360]
    norm_num
  have hS'card : Nat.card (S.subgroupOf L) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv]
    exact hScard
  have hSP : S ≤ P := fun x hx => hNS (Subgroup.mem_inf.2 ⟨hSL hx, Subgroup.le_normalizer hx⟩)
  have hPstab : ∀ x : Y, x ∈ P ↔ (hh⁻¹ * y) * x * (hh⁻¹ * y)⁻¹ ∈ P := by
    by_cases hPS : P = S
    · subst hPS
      exact hτ'S
    · have hPX' : S.subgroupOf L ≤ P.subgroupOf L := fun k hk => hSP hk
      have hXP' : P.subgroupOf L ≠ S.subgroupOf L := by
        intro h
        apply hPS
        refine le_antisymm ?_ hSP
        intro x hx
        have hxK : x ∈ L := hPL.le hx
        have : (⟨x, hxK⟩ : ↥L) ∈ P.subgroupOf L := hx
        rw [h] at this
        exact this
      have hXtop : P.subgroupOf L ≠ ⊤ := by
        intro h
        apply hPL.ne
        refine le_antisymm hPL.le fun x hx => ?_
        have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := by rw [h]; trivial
        exact this
      have hγP : ∀ k : ↥L, k ∈ S.subgroupOf L ↔
          (MulAut.conjNormal (hh⁻¹ * y) : MulAut ↥L) k ∈ S.subgroupOf L := by
        intro k
        exact hτ'S (k : Y)
      have key := Unc25K1.A6Model.key_of_iso e (S.subgroupOf L) (P.subgroupOf L) hS'card hPX' hXP'
        hXtop (MulAut.conjNormal (hh⁻¹ * y)) π hπ hγP
      intro x
      by_cases hxL : x ∈ L
      · exact key ⟨x, hxL⟩
      · constructor
        · intro hx
          exact absurd (hPL.le hx) hxL
        · intro hx
          exact absurd ((Subgroup.mem_normalizer_iff.1 hτ'N x).2 (hPL.le hx)) hxL
  apply hmove hh hhL
  ext x
  rw [mem_conjSubgroup_iff]
  have h1 := hPstab ((y⁻¹ * hh) * x * (y⁻¹ * hh)⁻¹)
  have e3 : (hh⁻¹ * y) * ((y⁻¹ * hh) * x * (y⁻¹ * hh)⁻¹) * (hh⁻¹ * y)⁻¹ = x := by group
  rw [e3] at h1
  exact h1

theorem w183finG4A6_not_mem_autS6_of_acts {M : Type} [Group M]
    (e : M ≃* alternatingGroup (Fin 6)) (γ : MulAut M)
    (h : ActsOnDynkinMod ⊥ (innAutOf M) γ) : γ ∉ w183finG4A6AutS6 e := by
  intro hγ
  haveI : Finite M := Finite.of_equiv _ e.symm.toEquiv
  haveI : Finite (MulAut M) :=
    Finite.of_injective (fun α : MulAut M => (α : M → M)) DFunLike.coe_injective
  haveI : (innAutOf M).Normal := innAutOf_normal M
  have hZ : ∀ z : M, (∀ x, z * x = x * z) → z = 1 := fun z hz => by
    have hz' : z ∈ Subgroup.center M := Subgroup.mem_center_iff.2 (fun g => (hz g).symm)
    rw [w183finG4A6_center_eq_bot e] at hz'
    exact hz'
  let eL : ↥(innAutOf M) ≃* alternatingGroup (Fin 6) :=
    (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm.trans e
  refine w183finG4A6_not_acts_of_induced (innAutOf M) eL γ ?_ h
  obtain ⟨π, hπ⟩ := (w183finG4A6_mem_autS6_iff e γ).1 hγ
  rw [w183finG4A6_mem_autS6_iff]
  refine ⟨π, fun k => ?_⟩
  obtain ⟨m, rfl⟩ := (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).surjective k
  have h1 := CFSG.GH74.Generic.BProg.B3.S3T5L3.conjNormal_innEquiv hZ γ m
  change ((e ((CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm
      ((MulAut.conjNormal γ) (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m)))) :
        alternatingGroup (Fin 6)) =
    π * ((e ((CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ).symm
      (CFSG.GH74.Generic.BProg.B3.S3T5L3.innEquiv hZ m)) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) * π⁻¹
  rw [h1, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hπ m

end CFSG.LocalAnalysis.WeakClosure81

end
