module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Model
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.ComponentClassification.UnbalancedCatalog

private theorem w183finSp44_minorAut_pow_mem_inner_iff (m : ℕ) :
    SpChain.minorAut GF4 ^ m ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (SpChain.antiSp GF4) ↔ 4 ∣ m := by
  have hK : Nat.card GF4 = 2 ^ 2 := by rw [Nat.card_eq_fintype_card]; decide
  obtain ⟨Fr, hFr, hord, hzp⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data (K := GF4) (n := 2)
      (by norm_num) hK
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ :=
    SpChain.exceptionalAut_structure (K := GF4) (f := 2) (by norm_num) hFr hord hzp
  rw [← CFSG.QuasithinUnique.Setup.X7b.mem_inner_iff_autCongr,
    CFSG.QuasithinUnique.Setup.X7b.autCongr_pow,
    CFSG.QuasithinUnique.Setup.X7b.autCongr_minorAut]
  simpa using hmem m

private theorem w183finSp44_symp_encodeM (g : SpChain.antiSp GF4) :
    symp (encodeM ((g : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4)) = true := by
  rw [symp_iff, decodeM_encodeM]
  exact SpChain.mem_antiSp.mp g.2

private theorem w183finSp44_toS4_encodeM (g : SpChain.antiSp GF4)
    (h : symp (encodeM ((g : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4)) = true) :
    toS4 (encodeM ((g : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4)) h = g := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [toS4_val, decodeM_encodeM]

private theorem w183finSp44_validB_encodeM (g : SpChain.antiSp GF4) {j : ℕ} (hj : j < 4) :
    validB (encodeM ((g : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4), j) = true := by
  unfold validB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true_eq.mpr (encodeM_lt _), w183finSp44_symp_encodeM g⟩,
    decide_eq_true_eq.mpr hj⟩

theorem autOf_inj {x y : El} (hx : validB x = true) (hy : validB y = true)
    (h : autOf x = autOf y) : x = y := by
  have hx1 : x.1 < 4294967296 := (validB_iff.mp hx).1
  have hy1 : y.1 < 4294967296 := (validB_iff.mp hy).1
  have hx2 : x.2 < 4 := (validB_iff.mp hx).2.2
  have hy2 : y.2 < 4 := (validB_iff.mp hy).2.2
  obtain ⟨Fr, hFr, hord, hzp⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data (K := GF4) (n := 2)
      (by norm_num) (by rw [Nat.card_eq_fintype_card]; decide)
  have hstruct := SpChain.exceptionalAut_structure (K := GF4) (f := 2) (by norm_num) hFr hord hzp
  have huniq := hstruct.2.1
  have hc : CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf x) =
      CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf y) := by rw [h]
  have hxr : CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf x) =
      SpChain.spInner 2 GF4 (SpChain.antiSpEquiv GF4 (toS4 x.1 (validB_symp hx))) *
        SpChain.exceptionalAut GF4 ^ x.2 := by
    rw [autOf, dif_pos hx, map_mul, CFSG.QuasithinUnique.Setup.X7b.autCongr_conj,
      CFSG.QuasithinUnique.Setup.X7b.autCongr_pow,
      CFSG.QuasithinUnique.Setup.X7b.autCongr_minorAut]
  have hyr : CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf y) =
      SpChain.spInner 2 GF4 (SpChain.antiSpEquiv GF4 (toS4 y.1 (validB_symp hy))) *
        SpChain.exceptionalAut GF4 ^ y.2 := by
    rw [autOf, dif_pos hy, map_mul, CFSG.QuasithinUnique.Setup.X7b.autCongr_conj,
      CFSG.QuasithinUnique.Setup.X7b.autCongr_pow,
      CFSG.QuasithinUnique.Setup.X7b.autCongr_minorAut]
  let qx : StatedSp 2 GF4 × Fin (2 * 2) :=
    (SpChain.antiSpEquiv GF4 (toS4 x.1 (validB_symp hx)), ⟨x.2, by omega⟩)
  let qy : StatedSp 2 GF4 × Fin (2 * 2) :=
    (SpChain.antiSpEquiv GF4 (toS4 y.1 (validB_symp hy)), ⟨y.2, by omega⟩)
  have hqx : CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf x) =
      SpChain.spInner 2 GF4 qx.1 * SpChain.exceptionalAut GF4 ^ (qx.2 : ℕ) := by
    rw [hxr]
  have hqy : CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf y) =
      SpChain.spInner 2 GF4 qy.1 * SpChain.exceptionalAut GF4 ^ (qy.2 : ℕ) := by
    rw [hyr]
  obtain ⟨p, -, huniqp⟩ := huniq (CFSG.QuasithinUnique.Setup.X7b.autCongr GF4 (autOf x))
  have hqxy : qx = qy := (huniqp qx hqx).trans (huniqp qy (hc.trans hqy)).symm
  have h1 : qx.1 = qy.1 := congrArg Prod.fst hqxy
  have h2fin : qx.2 = qy.2 := congrArg Prod.snd hqxy
  have h2 : x.2 = y.2 := by simpa [qx, qy] using congrArg Fin.val h2fin
  have htoS4 : toS4 x.1 (validB_symp hx) = toS4 y.1 (validB_symp hy) :=
    (SpChain.antiSpEquiv GF4).injective (by simpa [qx, qy] using h1)
  have hmat : decodeM x.1 = decodeM y.1 := by
    have hz := congrArg (fun z : S4 => ((z : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4)) htoS4
    simpa only [toS4_val] using hz
  exact Prod.ext (decodeM_inj hx1 hy1 hmat) h2

private theorem w183finSp44_encodeM_decodeM {g : Nat} (hg : g < 4294967296) :
    encodeM (decodeM g) = g :=
  decodeM_inj (encodeM_lt _) hg (decodeM_encodeM (decodeM g))

private noncomputable def w183finSp44_validCodesEquiv :
    {x : El // validB x = true} ≃ (SpChain.antiSp GF4 × Fin 4) where
  toFun x := (toS4 x.1.1 (validB_symp x.2), ⟨x.1.2, (validB_iff.mp x.2).2.2⟩)
  invFun p := ⟨(encodeM ((p.1 : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4), p.2.1),
    w183finSp44_validB_encodeM p.1 p.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [toS4_val]
      exact w183finSp44_encodeM_decodeM (validB_iff.mp x.2).1
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact w183finSp44_toS4_encodeM p.1 (w183finSp44_symp_encodeM p.1)
    · exact Fin.ext rfl

private theorem w183finSp44_card_autS4 : Nat.card (MulAut S4) = 3916800 := by
  have hcardK : Nat.card GF4 = 4 := by rw [Nat.card_eq_fintype_card]; decide
  have hK : Nat.card GF4 = 2 ^ 2 := by rw [Nat.card_eq_fintype_card]; decide
  obtain ⟨Fr, hFr, hord, hzp⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data (K := GF4) (n := 2)
      (by norm_num) hK
  obtain ⟨-, -, -, -, -, hOut, -⟩ :=
    SpChain.exceptionalAut_structure (K := GF4) (f := 2) (by norm_num) hFr hord hzp
  have hOutAnti : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (SpChain.antiSp GF4)) = 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (CFSG.QuasithinUnique.Setup.X7b.antiProjEquiv GF4)).toEquiv]
    simpa using hOut
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (SpChain.antiSp GF4)) = Nat.card (SpChain.antiSp GF4) :=
    (Nat.card_congr (MonoidHom.ofInjective
      (CFSG.QuasithinUnique.Setup.X7b.conj_injective (K := GF4))).toEquiv).symm
  have hcard : Nat.card (MulAut (SpChain.antiSp GF4)) =
      Nat.card (SpChain.antiSp GF4) * 4 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (SpChain.antiSp GF4)),
      hOutAnti, hinner]
    ring
  change Nat.card (MulAut (SpChain.antiSp GF4)) = 3916800
  rw [hcard, SpChain.card_antiSp (K := GF4) (q := 4) hcardK]
  norm_num

theorem autOf_surj (α : MulAut S4) : ∃ x : El, validB x = true ∧ autOf x = α := by
  have hcardK : Nat.card GF4 = 4 := by rw [Nat.card_eq_fintype_card]; decide
  have hdom : Nat.card {x : El // validB x = true} = Nat.card (MulAut S4) := by
    rw [Nat.card_congr w183finSp44_validCodesEquiv, Nat.card_prod, Nat.card_fin,
      SpChain.card_antiSp (K := GF4) (q := 4) hcardK, w183finSp44_card_autS4]
    norm_num
  have hf : Function.Injective (fun x : {x : El // validB x = true} => autOf x.1) := by
    intro x y hxy
    exact Subtype.ext (autOf_inj x.2 y.2 hxy)
  have hbij : Function.Bijective (fun x : {x : El // validB x = true} => autOf x.1) :=
    hf.bijective_of_nat_card_le (le_of_eq hdom.symm)
  obtain ⟨x, hx⟩ := hbij.2 α
  exact ⟨x.1, x.2, hx⟩

theorem autOf_inner_iff {x : El} (hx : validB x = true) :
    autOf x ∈ innAutOf S4 ↔ x.2 = 0 := by
  have hsymp : symp x.1 = true := validB_symp hx
  have hx2 : x.2 < 4 := (validB_iff.mp hx).2.2
  have hconj : MulAut.conj (toS4 x.1 hsymp) ∈ innAutOf S4 := ⟨toS4 x.1 hsymp, rfl⟩
  rw [autOf, dif_pos hx]
  constructor
  · intro hmem
    have h2 : SpChain.minorAut GF4 ^ x.2 ∈ innAutOf S4 := by
      have h1 : (MulAut.conj (toS4 x.1 hsymp))⁻¹ *
          (MulAut.conj (toS4 x.1 hsymp) * SpChain.minorAut GF4 ^ x.2) ∈ innAutOf S4 :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hconj) hmem
      simpa only [inv_mul_cancel_left] using h1
    have h4 : 4 ∣ x.2 := (w183finSp44_minorAut_pow_mem_inner_iff x.2).mp h2
    obtain ⟨k, hk⟩ := h4
    omega
  · intro h0
    rw [h0, pow_zero, mul_one]
    exact hconj

theorem card_autS4 : Nat.card (MulAut S4) = 3916800 := w183finSp44_card_autS4

theorem isSp4_equiv_S4 {L : Type} [Group L] (h : IsSp4 L 2) : Nonempty (L ≃* S4) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK4 : Nat.card K = 4 := by simpa using hK
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK4]; norm_num)
  have e2 : K ≃+* GF4 := by
    have : Fintype K := Fintype.ofFinite K
    exact FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, hK4]
      exact (by decide : Fintype.card GF4 = 4).symm)
  exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.X7b.antiProjEquiv K).symm.trans
    (CFSG.QuasithinUnique.Setup.X7b.antiSpCongr e2))⟩

theorem validB_conjE {g x : El} (hg : validB g = true) (hx : validB x = true) :
    validB (conjE g x) = true :=
  validB_gmulE hg (validB_gmulE hx (validB_invE hg))

theorem autOf_conjE {g x : El} (hg : validB g = true) (hx : validB x = true) :
    autOf (conjE g x) = autOf g * autOf x * (autOf g)⁻¹ := by
  rw [conjE, autOf_gmulE hg (validB_gmulE hx (validB_invE hg)), autOf_gmulE hx (validB_invE hg),
    autOf_invE hg, mul_assoc]

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
