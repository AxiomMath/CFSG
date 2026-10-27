module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import CFSG.Quasithin.Recognition.St84.Sp44DC

import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalExtend
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalBorelAut

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.Open
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2)
open CFSG.QuasithinUnique.Fin257.Sp4 (dSp)
open CFSG.Quasithin.F112R.St84.Sp44 (B0 dTor rootXa rootXb T0B A1B A2B HB dSp_mem_dTor
  dTor_le B0_le_normalizer_radA1 B0_le_normalizer_radA2 T0B_normal radA1_normal radA2_normal
  map_A1B)
open CFSG.RankThree.PartOne.KCRootAxis (frobAut)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private lemma exists_two_le_of_eight_le (hF : 8 ≤ Nat.card F) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card F = 2 ^ n := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hq
  have h8 : 8 ≤ 2 ^ (n : ℕ) := by rw [← hcard]; exact hF
  have hn : 2 ≤ (n : ℕ) := by
    by_contra h
    have hle : (n : ℕ) ≤ 1 := by omega
    have hle2 : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    norm_num at hle2
    omega
  exact ⟨(n : ℕ), hn, hcard⟩

private lemma map_conj_mul_of_normal {K : Subgroup ↥(B0 F)} [K.Normal]
    (σ : MulAut ↥(B0 F)) (g : ↥(B0 F)) (h : K.map σ.toMonoidHom = K) :
    K.map ((MulAut.conj g * σ).toMonoidHom) = K := by
  have hcomp : (MulAut.conj g * σ).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp σ.toMonoidHom := rfl
  rw [hcomp, ← Subgroup.map_map, h]
  exact Subgroup.Normal.map_conj_eq (H := K) g

private lemma exists_conj_frobAut_agree_of_map_A1B (hF : 8 ≤ Nat.card F)
    (σ : MulAut ↥(B0 F)) (hA1 : (A1B F).map σ.toMonoidHom = A1B F) :
    ∃ (e : ↥(B0 F)) (s t : Fˣ) (k : ℕ),
      ∀ b : ↥(B0 F), (e : antiSp F) * ((σ b : ↥(B0 F)) : antiSp F) *
        (e : antiSp F)⁻¹ =
        (MulAut.conj (dSp s t) * frobAut F ^ k) (b : antiSp F) := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have hA2 : (A2B F).map σ.toMonoidHom = A2B F := map_A2B_of_map_A1B σ hA1
  obtain ⟨e, -, hHe⟩ := exists_conj_map_HB σ
  let τ : MulAut ↥(B0 F) := MulAut.conj e * σ
  have hτe : ∀ b : ↥(B0 F), ((τ b : ↥(B0 F)) : antiSp F) =
      (e : antiSp F) * ((σ b : ↥(B0 F)) : antiSp F) * (e : antiSp F)⁻¹ := fun _ => rfl
  have hTτ : (T0B F).map τ.toMonoidHom = T0B F := map_T0B_eq τ
  have hA1τ : (A1B F).map τ.toMonoidHom = A1B F := by
    haveI : (A1B F).Normal := radA1_normal
    exact map_conj_mul_of_normal σ e hA1
  have hA2τ : (A2B F).map τ.toMonoidHom = A2B F := by
    haveI : (A2B F).Normal := radA2_normal
    exact map_conj_mul_of_normal σ e hA2
  obtain ⟨s, t, k, hag⟩ :=
    exists_eq_conj_frobAut_pow_of_eight_le hF τ hTτ hHe hA1τ hA2τ
  let Φ : MulAut (antiSp F) := MulAut.conj (dSp s t) * frobAut F ^ k
  have hgB0 : dSp s t ∈ B0 F := dTor_le (dSp_mem_dTor s t)
  have hΦB0 : ∀ x : antiSp F, x ∈ B0 F ↔ Φ x ∈ B0 F :=
    conj_frobAut_pow_mem_B0_iff hgB0 k
  have hΦB0map : (B0 F).map Φ.toMonoidHom = B0 F := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (hΦB0 x).mp hx
    · intro x hx
      refine ⟨Φ⁻¹ x, (hΦB0 (Φ⁻¹ x)).mpr (by simpa using hx), by simp⟩
  let Φ' : MulAut ↥(B0 F) :=
    (MulEquiv.subgroupMap Φ (B0 F)).trans (MulEquiv.subgroupCongr hΦB0map)
  have hΦ'coe : ∀ b : ↥(B0 F), ((Φ' b : ↥(B0 F)) : antiSp F) = Φ (b : antiSp F) :=
    fun _ => rfl
  have hτΦ : τ.toMonoidHom = Φ'.toMonoidHom := by
    refine B0_monoidHom_ext h4 ?_
    intro b hb
    apply Subtype.ext
    change ((τ b : ↥(B0 F)) : antiSp F) = ((Φ' b : ↥(B0 F)) : antiSp F)
    rw [hag b hb, hΦ'coe b]
  have hτΦb : ∀ b : ↥(B0 F), τ b = Φ' b := fun b => by
    simpa using DFunLike.congr_fun hτΦ b
  refine ⟨e, s, t, k, fun b => ?_⟩
  rw [← hτe b, hτΦb b, hΦ'coe b]

theorem exists_mulAut_extend_B0 (hF : 8 ≤ Nat.card F) (σ : MulAut ↥(B0 F))
    (hA1 : (A1B F).map σ.toMonoidHom = A1B F) :
    ∃ Ψ : MulAut (antiSp F),
      (∀ g : antiSp F, g ∈ Subgroup.normalizer (radA1 F : Set (antiSp F)) ↔
        Ψ g ∈ Subgroup.normalizer (radA1 F : Set (antiSp F))) ∧
      (∀ g : antiSp F, g ∈ Subgroup.normalizer (radA2 F : Set (antiSp F)) ↔
        Ψ g ∈ Subgroup.normalizer (radA2 F : Set (antiSp F))) ∧
      ∀ b : ↥(B0 F), Ψ (b : antiSp F) = ((σ b : ↥(B0 F)) : antiSp F) := by
  classical
  obtain ⟨e, s, t, k, hagree⟩ := exists_conj_frobAut_agree_of_map_A1B hF σ hA1
  have hgB0 : dSp s t ∈ B0 F := dTor_le (dSp_mem_dTor s t)
  let Φ : MulAut (antiSp F) := MulAut.conj (dSp s t) * frobAut F ^ k
  let Ψ : MulAut (antiSp F) := MulAut.conj ((e : antiSp F)⁻¹) * Φ
  have hΨe : ∀ g : antiSp F, Ψ g = (e : antiSp F)⁻¹ * Φ g * (e : antiSp F) := fun g => by
    simp [Ψ, MulAut.mul_apply, MulAut.conj_apply]
  have hΦb : ∀ b : ↥(B0 F), (e : antiSp F) * ((σ b : ↥(B0 F)) : antiSp F) *
      (e : antiSp F)⁻¹ = Φ (b : antiSp F) := fun b => hagree b
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro g
    have heN : (e : antiSp F) ∈ Subgroup.normalizer (radA1 F : Set (antiSp F)) :=
      B0_le_normalizer_radA1 e.2
    have hN := Subgroup.mem_normalizer_iff''.mp
      (Subgroup.le_normalizer
        (H := Subgroup.normalizer (radA1 F : Set (antiSp F))) heN)
    rw [hΨe g]
    exact (conj_frobAut_pow_mem_normalizer_radA1_iff hgB0 k g).trans (hN (Φ g))
  · intro g
    have heN : (e : antiSp F) ∈ Subgroup.normalizer (radA2 F : Set (antiSp F)) :=
      B0_le_normalizer_radA2 e.2
    have hN := Subgroup.mem_normalizer_iff''.mp
      (Subgroup.le_normalizer
        (H := Subgroup.normalizer (radA2 F : Set (antiSp F))) heN)
    rw [hΨe g]
    exact (conj_frobAut_pow_mem_normalizer_radA2_iff hgB0 k g).trans (hN (Φ g))
  · intro b
    rw [hΨe (b : antiSp F), ← hΦb b]
    group

theorem dcSp4_of_eight_le (hF : 8 ≤ Nat.card F) :
    DCProp (Subgroup.normalizer (radA1 F : Set (antiSp F)))
      (Subgroup.normalizer (radA2 F : Set (antiSp F))) := by
  classical
  obtain ⟨n, hn, hcard⟩ := exists_two_le_of_eight_le hF
  refine dcProp_of_forall_exists_extend ?_
  intro σ hσ
  have hInf : Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
      Subgroup.normalizer (radA2 F : Set (antiSp F)) = B0 F :=
    normalizer_radA1_inf_normalizer_radA2 hn hcard
  have hcore : pCoreOf 2 (Subgroup.normalizer (radA1 F : Set (antiSp F))) = radA1 F :=
    pCoreOf_normalizer_radA1 hn hcard
  let E : ↥(Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
      Subgroup.normalizer (radA2 F : Set (antiSp F))) ≃* ↥(B0 F) :=
    MulEquiv.subgroupCongr hInf
  have hE : ∀ x : ↥(Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
      Subgroup.normalizer (radA2 F : Set (antiSp F))),
      ((E x : ↥(B0 F)) : antiSp F) = (x : antiSp F) :=
    fun x => MulEquiv.subgroupCongr_apply hInf x
  have hEs : ∀ x : ↥(B0 F),
      ((E.symm x : ↥(Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
        Subgroup.normalizer (radA2 F : Set (antiSp F)))) : antiSp F) = (x : antiSp F) :=
    fun x => MulEquiv.subgroupCongr_symm_apply hInf x
  let σ' : MulAut ↥(B0 F) := (E.symm.trans σ).trans E
  have hσ'coe : ∀ x : ↥(B0 F), ((σ' x : ↥(B0 F)) : antiSp F) =
      ((σ (E.symm x) : ↥(Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
        Subgroup.normalizer (radA2 F : Set (antiSp F)))) : antiSp F) := by
    intro x
    rw [← hE (σ (E.symm x))]
    rfl
  have hσ1 := hσ
  rw [hcore] at hσ1
  have hσ' : ∀ b : ↥(B0 F), (b : antiSp F) ∈ radA1 F ↔ (σ' b : antiSp F) ∈ radA1 F := by
    intro b
    rw [hσ'coe b, ← hEs b]
    exact hσ1 (E.symm b)
  have hA1' : (A1B F).map σ'.toMonoidHom = A1B F := map_A1B σ' hσ'
  obtain ⟨Ψ, hN1, hN2, hΨ⟩ := exists_mulAut_extend_B0 hF σ' hA1'
  refine ⟨Ψ, hN1, hN2, ?_⟩
  intro b
  have h1 := hΨ (E b)
  rw [hE b] at h1
  have h2 : ((σ' (E b) : ↥(B0 F)) : antiSp F) =
      ((σ b : ↥(Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
        Subgroup.normalizer (radA2 F : Set (antiSp F)))) : antiSp F) := by
    rw [hσ'coe (E b), MulEquiv.symm_apply_apply]
  exact h1.trans h2

end CFSG.Quasithin.F112R.St84
