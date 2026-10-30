module

public import Certificates.Certificate188002
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport

public section

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model
open scoped LinearAlgebra.Projectivization Matrix

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

section Field


noncomputable instance instFieldGF64 : Field GF64 :=
  Field.ofMinimalAxioms GF64 Certificates.certificate188002.field.1 Certificates.certificate188002.field.2.1 Certificates.certificate188002.field.2.2.1 Certificates.certificate188002.field.2.2.2.1
    Certificates.certificate188002.field.2.2.2.2.1 Certificates.certificate188002.field.2.2.2.2.2.1 Certificates.certificate188002.field.2.2.2.2.2.2.1
    Certificates.certificate188002.field.2.2.2.2.2.2.2.1 Certificates.certificate188002.field.2.2.2.2.2.2.2.2.1 Certificates.certificate188002.field.2.2.2.2.2.2.2.2.2

theorem card_GF64 : Nat.card GF64 = (2 ^ 3) ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem conj8_eq_pow (x : GF64) : x.conj8 = x ^ 8 := by
  unfold GF64.conj8
  ring

noncomputable def J64 : HermitianForm 3 GF64 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Classical.choose (exists_standardHermitianForm (K := GF64) 2 3 card_GF64)

theorem J64_spec :
    J64.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧ (∀ x : GF64, J64.conj x = x ^ (2 ^ 3)) ∧
      Nat.card {x : GF64 // J64.conj x = x} = 2 ^ 3 :=
  Classical.choose_spec (exists_standardHermitianForm (K := GF64) 2 3 card_GF64)

theorem J64_form : J64.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  exact J64_spec.1

theorem J64_conj (x : GF64) : J64.conj x = x.conj8 := by
  calc J64.conj x = x ^ (2 ^ 3) := J64_spec.2.1 x
    _ = x ^ 8 := by norm_num
    _ = x.conj8 := (conj8_eq_pow x).symm

theorem J64_fix : Nat.card {x : GF64 // J64.conj x = x} = 2 ^ 3 := by
  exact J64_spec.2.2

theorem normalizedV_ne_zero {v : Fin 3 → GF64} (hv : NormalizedV v) : v ≠ 0 := by
  rintro rfl
  rcases hv with e | ⟨-, f⟩ | ⟨-, -, g⟩
  · exact zero_ne_one (show (0 : GF64) = 1 from e)
  · exact zero_ne_one (show (0 : GF64) = 1 from f)
  · exact zero_ne_one (show (0 : GF64) = 1 from g)

theorem normalizedV_smul_eq_one {v w : Fin 3 → GF64} (hv : NormalizedV v) (hw : NormalizedV w)
    {c : GF64} (h : c • v = w) : c = 1 := by
  have h0 : c * v 0 = w 0 := congrFun h 0
  have h1 : c * v 1 = w 1 := congrFun h 1
  have h2 : c * v 2 = w 2 := congrFun h 2
  rcases hv with e | ⟨e0, e1⟩ | ⟨e0, e1, e2⟩ <;>
    rcases hw with f | ⟨f0, f1⟩ | ⟨f0, f1, f2⟩ <;>
    simp_all

theorem ne_zero_coord_of_ne_zero {v : Fin 3 → GF64} (hv : v ≠ 0) :
    v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  funext i
  fin_cases i <;> simp [h.1, h.2.1, h.2.2]

theorem vec3_eq_cons (v : Fin 3 → GF64) : ![v 0, v 1, v 2] = v := by
  funext i
  fin_cases i <;> rfl

theorem normV3_eq_smul (a b c : GF64) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ s : GF64, s ≠ 0 ∧ normV3 a b c = s • ![a, b, c] := by
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb
      have hc : c ≠ 0 := by
        rcases h with h | h | h
        · exact (h rfl).elim
        · exact (h rfl).elim
        · exact h
      refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
      funext i
      fin_cases i <;> simp [normV3, hc]
    · refine ⟨b⁻¹, inv_ne_zero hb, ?_⟩
      funext i
      fin_cases i <;> simp [normV3, hb]
  · refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
    funext i
    fin_cases i <;> simp [normV3, ha]

theorem mem_isotropicSet_of_iso {v : Fin 3 → GF64} (hv : v ≠ 0)
    (h : Iso3 (v 0) (v 1) (v 2)) : Projectivization.mk GF64 v hv ∈ isotropicSet J64 := by
  have hpair : dotProduct (fun i => J64.conj (v i)) (J64.form *ᵥ v) = 0 := by
    rw [selfPairing_std J64 J64_form v]
    simp only [J64_conj]
    exact h
  simp only [isotropicSet, Set.mem_setOf_eq]
  exact ⟨v, hv, rfl, hpair⟩

noncomputable def ptsPt (j : Fin 513) : IsoPoint J64 :=
  ⟨Projectivization.mk GF64 (ptsV j) (normalizedV_ne_zero (Certificates.certificate188002.points.1 j).1),
    mem_isotropicSet_of_iso (normalizedV_ne_zero (Certificates.certificate188002.points.1 j).1) (Certificates.certificate188002.points.1 j).2⟩

theorem ptsPt_injective : Function.Injective ptsPt := by
  intro i j hij
  have hmk : Projectivization.mk GF64 (ptsV i) (normalizedV_ne_zero (Certificates.certificate188002.points.1 i).1) =
      Projectivization.mk GF64 (ptsV j) (normalizedV_ne_zero (Certificates.certificate188002.points.1 j).1) :=
    congrArg Subtype.val hij
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).1 hmk
  have hc1 : c = 1 := normalizedV_smul_eq_one (Certificates.certificate188002.points.1 j).1 (Certificates.certificate188002.points.1 i).1 hc
  rw [hc1, one_smul] at hc
  have hi := Certificates.certificate188002.points.2.1 i
  have hj := Certificates.certificate188002.points.2.1 j
  rw [hc] at hj
  exact Fin.ext (hi.symm.trans hj)

theorem ptsPt_surjective : Function.Surjective ptsPt := by
  rintro ⟨x, hx⟩
  obtain ⟨v, hv, rfl, hiso⟩ := hx
  have hiso' : Iso3 (v 0) (v 1) (v 2) := by
    rw [selfPairing_std J64 J64_form v] at hiso
    simp only [J64_conj] at hiso
    exact hiso
  obtain ⟨s, -, hsv⟩ := normV3_eq_smul (v 0) (v 1) (v 2) (ne_zero_coord_of_ne_zero hv)
  have hP3 := Certificates.certificate188002.points.2.2 (v 0) (v 1) (v 2) (ne_zero_coord_of_ne_zero hv) hiso'
  refine ⟨ptIdx idxTable[vcode (normV3 (v 0) (v 1) (v 2))]!, ?_⟩
  have hsv' : s • v = ptsV (ptIdx idxTable[vcode (normV3 (v 0) (v 1) (v 2))]!) := by
    rw [hP3, hsv, vec3_eq_cons v]
  exact Subtype.ext ((Projectivization.mk_eq_mk_iff' _ _ _ _ _).2 ⟨s, hsv'⟩)

noncomputable def ptsE : IsoPoint J64 ≃ Fin 513 := by
  exact (Equiv.ofBijective ptsPt ⟨ptsPt_injective, ptsPt_surjective⟩).symm

theorem ptsE_symm_coe (j : Fin 513) :
    ∃ hv : ptsV j ≠ 0,
      ((ptsE.symm j : IsoPoint J64) : ℙ GF64 (Fin 3 → GF64)) = Projectivization.mk GF64 (ptsV j) hv := by
  exact ⟨normalizedV_ne_zero (Certificates.certificate188002.points.1 j).1, rfl⟩

end Field

end CFSG.RankThree.PartTwo.Sec4.Item434U38
