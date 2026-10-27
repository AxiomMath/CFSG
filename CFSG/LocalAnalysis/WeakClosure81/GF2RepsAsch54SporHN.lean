module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.HN.Local.InvolutionClasses
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.PermV
public import Certificates.Certificate75346

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporHN

open Subgroup CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK CFSG.Sporadic.HN.Local

section Pair


noncomputable def pairT : Subgroup (J dHN) := Certificates.certificate75346.choose

theorem t_comm : ∀ p ∈ pairT, wG 13 * p = p * wG 13 :=
  Certificates.certificate75346.choose_spec.choose

theorem t_mul_self : wG 13 * wG 13 = 1 :=
  Certificates.certificate75346.choose_spec.choose_spec.choose

theorem pairT_spec : Nat.card pairT = 2 ^ 14 ∧ wG 13 ∈ pairT ∧ wG 13 ≠ 1 ∧
    (∀ x ∈ pairT, (∀ p ∈ pairT, x * p = p * x) → x = 1 ∨ x = wG 13) ∧
    Nat.card (zTwoOf pairT (wG 13) t_comm t_mul_self) = 4 ∧
    centralizer {wG 13} ⊔ normalizer (zTwoOf pairT (wG 13) t_comm t_mul_self : Set (J dHN)) = ⊤ :=
  Certificates.certificate75346.choose_spec.choose_spec.choose_spec

theorem t_mem : wG 13 ∈ pairT := pairT_spec.2.1

theorem t_ne_one : wG 13 ≠ 1 := pairT_spec.2.2.1

theorem center_pairT : ∀ x ∈ pairT, (∀ p ∈ pairT, x * p = p * x) → x = 1 ∨ x = wG 13 :=
  pairT_spec.2.2.2.1

@[expose] noncomputable def pairV : Subgroup (J dHN) := zTwoOf pairT (wG 13) t_comm t_mul_self

@[expose] noncomputable def pairA : Subgroup (J dHN) := centralizer {wG 13}

@[expose] noncomputable def pairB : Subgroup (J dHN) := normalizer (pairV : Set (J dHN))

theorem card_pairV : Nat.card pairV = 4 := pairT_spec.2.2.2.2.1

theorem pairA_sup_pairB : pairA ⊔ pairB = ⊤ := pairT_spec.2.2.2.2.2

theorem t_mem_pairV : wG 13 ∈ pairV := by
  rw [pairV, mem_zTwoOf]
  refine ⟨t_mem, fun p hp => Or.inl ?_⟩
  rw [commutatorElement_def, t_comm p hp]
  group

theorem isSylowIn_pairT : CFSG.Quasithin.IsSylowIn 2 pairT ⊤ := by
  have h := pairT.card_mul_index
  rw [pairT_spec.1, card_Jd] at h
  have hi : pairT.index = 16664484375 := by omega
  refine ⟨le_top, IsPGroup.of_card (n := 14) pairT_spec.1, ?_⟩
  rw [relIndex_top_right, hi]
  decide

theorem pairT_le_pairA : pairT ≤ pairA := fun x hx =>
  mem_centralizer_singleton_iff.2 (t_comm x hx).symm

theorem pairT_le_pairB : pairT ≤ pairB := le_normalizer_zTwoOf pairT (wG 13) t_comm t_mul_self

end Pair

theorem card_pairA :
    Nat.card pairA = 3686400 :=
  card_centralizer_t4

theorem card_pairB_dvd :
    Nat.card pairB ∣ 22118400 := by
  have h6 := CFSG.GH74.GLS.Stage1.Thm6.Sec13.relIndex_dvd_six card_pairV (le_refl pairB)
  have hle : centralizer (pairV : Set (J dHN)) ⊓ pairB ⊓ pairB ≤ pairA := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx.1.1 _ t_mem_pairV).symm
  rw [← relIndex_mul_card (H := centralizer (pairV : Set (J dHN)) ⊓ pairB) (K := pairB),
    show (22118400 : ℕ) = 6 * 3686400 by norm_num]
  exact Nat.mul_dvd_mul h6 ((card_dvd_of_le hle).trans (dvd_of_eq card_pairA))

section LPair


theorem isLPair_pair : IsLPair IsCalL0 pairT pairA pairB where
  le_left := pairT_le_pairA
  le_right := pairT_le_pairB
  ne_top_left h := by
    have h1 := card_pairA
    rw [h, card_top, card_Jd] at h1
    norm_num at h1
  ne_top_right h := by
    have h1 := card_pairB_dvd
    rw [h, card_top, card_Jd] at h1
    norm_num at h1
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 14) (N := 3686400)
    (by decide +kernel) (dvd_of_eq card_pairA)
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 15) (N := 22118400)
    (by decide +kernel) card_pairB_dvd
  sup_eq_top := pairA_sup_pairB

end LPair

theorem JH_eq : CFSG.Sporadic.HNSchreier.JH = J dHN := rfl

theorem card_outer_J_le :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (J dHN)) ≤ 2 := by
  rw [← JH_eq]
  exact CFSG.Sporadic.HNSchreier.card_outer.le

end CFSG.LocalAnalysis.WeakClosure81.SporHN

namespace CFSG.LocalAnalysis.WeakClosure81


open SporHN in
theorem asch54SporGenAt_hn :
    Asch54SporGenAt .HN :=
  asch54SporGenAt_of_isLPair_of_aut
    (CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv.map fun f =>
      f.symm.trans CFSG.Sporadic.Bridge.HN.nativeEquiv)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    card_outer_J_le isSylowIn_pairT isLPair_pair fun ψ hψ =>
      map_centralizer_normalizer_zTwoOf_eq t_mem t_ne_one t_comm t_mul_self center_pairT ψ hψ

end CFSG.LocalAnalysis.WeakClosure81

end
