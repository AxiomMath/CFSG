module

public import CFSG.Quasithin.Background.SmithB45TorLift
public import CFSG.Quasithin.Background.SmithB42Tits
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2266
public import Certificates.Certificate2268
public import Certificates.Certificate260140
public import Certificates.Certificate260420
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.SmithB45TorCrit
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate8026Base

public noncomputable section

namespace CFSG.Quasithin.B45Tor

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.B42Disp CFSG.Quasithin.B42Tits
open scoped commutatorElement

theorem titsTor_check :
    titsTorWordsCheck = true ∧ titsTorPlaneCheck = true ∧ titsTorNormCheck = true ∧
      titsTorRelCheck = true ∧ titsTorClassCheck = true :=
  Certificates.certificate260420

theorem rep_titsTorPow {x : Array ℕ} {σ : Equiv.Perm (Fin 1755)} (hx : Rep 1755 x σ) (k : ℕ) :
    Rep 1755 (titsTorPow x k) (σ ^ k) := by
  induction k with
  | zero => simpa [titsTorPow] using (rep_idA (n := 1755))
  | succ k ih => rw [pow_succ']; exact rep_compA hx ih

@[expose] def titsTorWords : List (List ℤ) :=
  [titsWordR₁, titsWordR₂, titsWordI, titsWordJ, titsWordH, titsWordGy, titsWordG₁, titsWordG₂]

theorem mem_r₁ : titsWordR₁ ∈ titsTorWords := by simp [titsTorWords]
theorem mem_r₂ : titsWordR₂ ∈ titsTorWords := by simp [titsTorWords]
theorem mem_i : titsWordI ∈ titsTorWords := by simp [titsTorWords]
theorem mem_j : titsWordJ ∈ titsTorWords := by simp [titsTorWords]
theorem mem_h : titsWordH ∈ titsTorWords := by simp [titsTorWords]
theorem mem_gy : titsWordGy ∈ titsTorWords := by simp [titsTorWords]
theorem mem_g₁ : titsWordG₁ ∈ titsTorWords := by simp [titsTorWords]
theorem mem_g₂ : titsWordG₂ ∈ titsTorWords := by simp [titsTorWords]

section Elements

theorem titsTor_words {w : List ℤ} (hw : w ∈ titsTorWords) :
    lettersOK 13 w = true ∧ isInvA 1755 (titsTorArr w) (invCand 1755 (titsTorArr w)) = true := by
  have h := titsTor_check.1
  simp only [titsTorWordsCheck, List.all_eq_true, Bool.and_eq_true] at h
  exact h w hw

theorem rep_titsTorArr {w : List ℤ} (hw : w ∈ titsTorWords) :
    Rep 1755 (titsTorArr w) (wordIn 13 titsT w) :=
  rep_wordArr_titsT (titsTor_words hw).1

theorem rep_conj_titsTor {w : List ℤ} (hw : w ∈ titsTorWords) {x : Array ℕ}
    {σ : Equiv.Perm (Fin 1755)} (hx : Rep 1755 x σ) :
    Rep 1755 (conjArr (titsTorArr w) x) (wordIn 13 titsT w * σ * (wordIn 13 titsT w)⁻¹) :=
  rep_conjArr (rep_titsTorArr hw) (titsTor_words hw).2 hx

local notation "Rr₁" => wordIn 13 titsT titsWordR₁
local notation "Rr₂" => wordIn 13 titsT titsWordR₂
local notation "Ri" => wordIn 13 titsT titsWordI
local notation "Rj" => wordIn 13 titsT titsWordJ
local notation "Rh" => wordIn 13 titsT titsWordH

theorem rep_titsTorR (a b : ℕ) : Rep 1755 (titsTorR a b) (Rr₁ ^ a * Rr₂ ^ b) :=
  rep_compA (rep_titsTorPow (rep_titsTorArr mem_r₁) a) (rep_titsTorPow (rep_titsTorArr mem_r₂) b)

theorem titsTor_plane :
    Rr₁ ^ 5 = 1 ∧ Rr₂ ^ 5 = 1 ∧ Rr₁ * Rr₂ = Rr₂ * Rr₁ ∧
      ∀ a < 5, ∀ b < 5, Rr₁ ^ a * Rr₂ ^ b = 1 → a = 0 ∧ b = 0 := by
  have h := titsTor_check.2.1
  simp only [titsTorPlaneCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_eqA (rep_titsTorPow (rep_titsTorArr mem_r₁) 5) rep_idA h1,
    eq_of_eqA (rep_titsTorPow (rep_titsTorArr mem_r₂) 5) rep_idA h2,
    eq_of_eqA (rep_compA (rep_titsTorArr mem_r₁) (rep_titsTorArr mem_r₂))
      (rep_compA (rep_titsTorArr mem_r₂) (rep_titsTorArr mem_r₁)) h3, ?_⟩
  intro a ha b hb hab
  have h5 := allLt_spec (allLt_spec h4 ha) hb
  have h6 : eqA 1755 (titsTorR a b) (idA 1755) = true := (eqA_iff (rep_titsTorR a b) rep_idA).2 hab
  rw [h6] at h5
  simpa using h5

theorem titsTor_norm :
    Ri * Rr₁ * Ri⁻¹ = Rr₁ ^ 4 * Rr₂ ^ 2 ∧ Ri * Rr₂ * Ri⁻¹ = Rr₁ ^ 4 * Rr₂ ^ 1 ∧
      Rj * Rr₁ * Rj⁻¹ = Rr₁ ^ 2 * Rr₂ ^ 0 ∧ Rj * Rr₂ * Rj⁻¹ = Rr₁ ^ 2 * Rr₂ ^ 3 ∧
      Rh * Rr₁ * Rh⁻¹ = Rr₁ ^ 0 * Rr₂ ^ 2 ∧ Rh * Rr₂ * Rh⁻¹ = Rr₁ ^ 2 * Rr₂ ^ 4 := by
  have h := titsTor_check.2.2.1
  simp only [titsTorNormCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨eq_of_eqA (rep_conj_titsTor mem_i (rep_titsTorArr mem_r₁)) (rep_titsTorR 4 2) h1,
    eq_of_eqA (rep_conj_titsTor mem_i (rep_titsTorArr mem_r₂)) (rep_titsTorR 4 1) h2,
    eq_of_eqA (rep_conj_titsTor mem_j (rep_titsTorArr mem_r₁)) (rep_titsTorR 2 0) h3,
    eq_of_eqA (rep_conj_titsTor mem_j (rep_titsTorArr mem_r₂)) (rep_titsTorR 2 3) h4,
    eq_of_eqA (rep_conj_titsTor mem_h (rep_titsTorArr mem_r₁)) (rep_titsTorR 0 2) h5,
    eq_of_eqA (rep_conj_titsTor mem_h (rep_titsTorArr mem_r₂)) (rep_titsTorR 2 4) h6⟩

theorem titsTor_rel :
    Ri * Ri = Rj * Rj ∧ Ri * Rj * Ri⁻¹ * Rj⁻¹ = Ri * Ri ∧ Rh * Ri * Rh⁻¹ = Rj ∧
      Rh * Rj * Rh⁻¹ = Ri * Rj ∧ Ri * (Ri * Rr₁ * Ri⁻¹) * Ri⁻¹ * Rr₁ = 1 ∧
      Ri * (Ri * Rr₂ * Ri⁻¹) * Ri⁻¹ * Rr₂ = 1 ∧ Ri * Ri * (Ri * Ri) = 1 := by
  have h := titsTor_check.2.2.2.1
  simp only [titsTorRelCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have rI := rep_titsTorArr mem_i
  have rJ := rep_titsTorArr mem_j
  have rY : Rep 1755 titsTorY (Ri * Ri) := rep_compA rI rI
  exact ⟨eq_of_eqA rY (rep_compA rJ rJ) h1,
    eq_of_eqA (rep_compA (rep_conj_titsTor mem_i rJ) (rep_inv_of_isInvA rJ (titsTor_words mem_j).2))
      rY h2,
    eq_of_eqA (rep_conj_titsTor mem_h rI) rJ h3,
    eq_of_eqA (rep_conj_titsTor mem_h rJ) (rep_compA rI rJ) h4,
    eq_of_eqA (rep_compA (rep_conj_titsTor mem_i (rep_conj_titsTor mem_i
      (rep_titsTorArr mem_r₁))) (rep_titsTorArr mem_r₁)) rep_idA h5,
    eq_of_eqA (rep_compA (rep_conj_titsTor mem_i (rep_conj_titsTor mem_i
      (rep_titsTorArr mem_r₂))) (rep_titsTorArr mem_r₂)) rep_idA h6,
    eq_of_eqA (rep_compA rY rY) rep_idA h7⟩

theorem titsTor_class :
    wordIn 13 titsT titsWordGy * (Ri * Ri) * (wordIn 13 titsT titsWordGy)⁻¹ = titsTInv ∧
      wordIn 13 titsT titsWordG₁ * titsZ * (wordIn 13 titsT titsWordG₁)⁻¹ *
        (wordIn 13 titsT titsWordG₂ * titsZ * (wordIn 13 titsT titsWordG₂)⁻¹) = titsTInv := by
  have h := titsTor_check.2.2.2.2
  simp only [titsTorClassCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have rI := rep_titsTorArr mem_i
  exact ⟨eq_of_eqA (rep_conj_titsTor mem_gy (rep_compA rI rI)) titsTInv_rep h1,
    eq_of_eqA (rep_compA (rep_conj_titsTor mem_g₁ titsZ_rep) (rep_conj_titsTor mem_g₂ titsZ_rep))
      titsTInv_rep h2⟩

end Elements

section Plane

@[expose] def titsR₁ : titsD := ⟨wordIn 13 titsT titsWordR₁, wordIn_titsT_mem_titsD _⟩

@[expose] def titsR₂ : titsD := ⟨wordIn 13 titsT titsWordR₂, wordIn_titsT_mem_titsD _⟩

@[expose] def titsI : titsD := ⟨wordIn 13 titsT titsWordI, wordIn_titsT_mem_titsD _⟩

@[expose] def titsJ : titsD := ⟨wordIn 13 titsT titsWordJ, wordIn_titsT_mem_titsD _⟩

@[expose] def titsH : titsD := ⟨wordIn 13 titsT titsWordH, wordIn_titsT_mem_titsD _⟩

@[expose] def titsRParam (x : ZMod 5 × ZMod 5) : titsD := titsR₁ ^ x.1.val * titsR₂ ^ x.2.val

theorem titsR₁_pow : titsR₁ ^ 5 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact titsTor_plane.1)

theorem titsR₂_pow : titsR₂ ^ 5 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact titsTor_plane.2.1)

theorem titsR₁_commute : Commute titsR₁ titsR₂ := Subtype.ext titsTor_plane.2.2.1

theorem titsRParam_add (x y : ZMod 5 × ZMod 5) :
    titsRParam (x + y) = titsRParam x * titsRParam y := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [titsRParam, Prod.fst_add, Prod.snd_add]
  rw [pow_val_add titsR₁_pow, pow_val_add titsR₂_pow]
  exact (titsR₁_commute.pow_pow y.1.val x.2.val).mul_mul_mul_comm _ _

theorem titsRParam_zero : titsRParam 0 = 1 := by simp [titsRParam]

theorem titsRParam_nsmul (n : ℕ) (x : ZMod 5 × ZMod 5) :
    titsRParam (n • x) = titsRParam x ^ n := by
  induction n with
  | zero => rw [zero_smul, titsRParam_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, titsRParam_add, ih, pow_succ]

theorem titsRParam_injective : Function.Injective titsRParam := by
  intro x y hxy
  have h1 : titsRParam (x - y) = 1 := by
    have := titsRParam_add (x - y) y
    rw [sub_add_cancel, hxy] at this
    exact (mul_eq_right.1 this.symm)
  have h2 : wordIn 13 titsT titsWordR₁ ^ (x - y).1.val * wordIn 13 titsT titsWordR₂ ^ (x - y).2.val
      = 1 := congrArg Subtype.val h1
  obtain ⟨ha, hb⟩ := titsTor_plane.2.2.2 _ (ZMod.val_lt _) _ (ZMod.val_lt _) h2
  rw [← sub_eq_zero]
  exact Prod.ext ((ZMod.val_eq_zero _).1 ha) ((ZMod.val_eq_zero _).1 hb)

@[expose] def titsR : Subgroup titsD where
  carrier := Set.range titsRParam
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, titsRParam_add x y⟩
  one_mem' := ⟨0, titsRParam_zero⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    refine ⟨-x, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← titsRParam_add, neg_add_cancel, titsRParam_zero]

theorem card_titsR : Nat.card titsR = 5 ^ 2 := by
  have h := Nat.card_range_of_injective titsRParam_injective
  rw [Nat.card_prod, Nat.card_zmod] at h
  rw [sq]
  exact h

theorem titsR_comm : ∀ a ∈ titsR, ∀ b ∈ titsR, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← titsRParam_add, ← titsRParam_add, add_comm]

theorem titsR_pow : ∀ r ∈ titsR, r ^ 5 = 1 := by
  rintro _ ⟨x, rfl⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [← titsRParam_nsmul]
  have h5 : (5 : ℕ) • x = 0 := by
    ext <;> simp only [nsmul_eq_mul, Nat.cast_ofNat, Prod.fst_zero, Prod.snd_zero] <;>
      exact (mul_eq_zero_of_left (ZMod.natCast_self 5) _)
  rw [h5, titsRParam_zero]

theorem mem_normalizer_titsR {g : titsD} {u v : ZMod 5 × ZMod 5}
    (hu : g * titsR₁ * g⁻¹ = titsRParam u) (hv : g * titsR₂ * g⁻¹ = titsRParam v) :
    g ∈ Subgroup.normalizer (titsR : Set titsD) := by
  have hmap : ∀ x, g * titsRParam x * g⁻¹ = titsRParam (x.1.val • u + x.2.val • v) := by
    intro x
    rw [titsRParam_add, titsRParam_nsmul, titsRParam_nsmul, ← hu, ← hv, conj_pow, conj_pow,
      titsRParam]
    group
  have hfwd : ∀ r ∈ titsR, g * r * g⁻¹ ∈ titsR := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (hmap x).symm⟩
  have : Finite titsR := Nat.finite_of_card_ne_zero (by rw [card_titsR]; norm_num)
  refine Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => hfwd n hn, fun hn => ?_⟩
  let c : titsR → titsR := fun r => ⟨g * r * g⁻¹, hfwd r r.2⟩
  have hc : Function.Injective c := by
    intro r r' h
    have h1 : g * (r : titsD) * g⁻¹ = g * (r' : titsD) * g⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.1 hc) ⟨g * n * g⁻¹, hn⟩
  have h1 : g * (r : titsD) * g⁻¹ = g * n * g⁻¹ := congrArg Subtype.val hr
  have h2 : (r : titsD) = n := by simpa using h1
  exact h2 ▸ r.2

theorem invOn_titsR : InvOn titsR (titsI * titsI) := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := titsTor_rel
  have e1 : titsI * titsI * titsR₁ * (titsI * titsI)⁻¹ = titsR₁⁻¹ := Subtype.ext (by
    change wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordR₁ *
      (wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordI)⁻¹ = (wordIn 13 titsT titsWordR₁)⁻¹
    rw [← mul_eq_one_iff_eq_inv.1 h5]
    group)
  have e2 : titsI * titsI * titsR₂ * (titsI * titsI)⁻¹ = titsR₂⁻¹ := Subtype.ext (by
    change wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordR₂ *
      (wordIn 13 titsT titsWordI * wordIn 13 titsT titsWordI)⁻¹ = (wordIn 13 titsT titsWordR₂)⁻¹
    rw [← mul_eq_one_iff_eq_inv.1 h6]
    group)
  rintro _ ⟨x, rfl⟩
  have hc : titsI * titsI * (titsR₁ ^ x.1.val * titsR₂ ^ x.2.val) * (titsI * titsI)⁻¹ =
      (titsI * titsI * titsR₁ * (titsI * titsI)⁻¹) ^ x.1.val *
        (titsI * titsI * titsR₂ * (titsI * titsI)⁻¹) ^ x.2.val := by
    rw [conj_pow, conj_pow]
    group
  rw [titsRParam, hc, e1, e2, mul_inv_rev, ← inv_pow, ← inv_pow]
  exact (titsR₁_commute.inv_inv.pow_pow _ _).eq

theorem titsR_q8 : IsQ8Data titsR titsI titsJ titsH := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := titsTor_norm
  obtain ⟨r1, r2, r3, r4, -, -, -⟩ := titsTor_rel
  have hconj : ∀ {g : titsD} {a b : ℕ} (hab : a < 5 ∧ b < 5),
      (g : Equiv.Perm (Fin 1755)) * wordIn 13 titsT titsWordR₁ * (g : Equiv.Perm (Fin 1755))⁻¹ =
        wordIn 13 titsT titsWordR₁ ^ a * wordIn 13 titsT titsWordR₂ ^ b →
      g * titsR₁ * g⁻¹ = titsRParam ((a : ZMod 5), (b : ZMod 5)) := by
    intro g a b hab h
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, titsRParam, Subgroup.coe_pow]
    rw [ZMod.val_natCast_of_lt hab.1, ZMod.val_natCast_of_lt hab.2]
    exact h
  have hconj2 : ∀ {g : titsD} {a b : ℕ} (hab : a < 5 ∧ b < 5),
      (g : Equiv.Perm (Fin 1755)) * wordIn 13 titsT titsWordR₂ * (g : Equiv.Perm (Fin 1755))⁻¹ =
        wordIn 13 titsT titsWordR₁ ^ a * wordIn 13 titsT titsWordR₂ ^ b →
      g * titsR₂ * g⁻¹ = titsRParam ((a : ZMod 5), (b : ZMod 5)) := by
    intro g a b hab h
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, titsRParam, Subgroup.coe_pow]
    rw [ZMod.val_natCast_of_lt hab.1, ZMod.val_natCast_of_lt hab.2]
    exact h
  have eIJ : ⁅titsI, titsJ⁆ = titsI * titsI := Subtype.ext (by
    rw [commutatorElement_def]
    exact r2)
  have eJJ : titsJ * titsJ = titsI * titsI := Subtype.ext r1.symm
  have eHI : titsH * titsI * titsH⁻¹ = titsJ := Subtype.ext r3
  have eHJ : titsH * titsJ * titsH⁻¹ = titsI * titsJ := Subtype.ext r4
  refine ⟨mem_normalizer_titsR (hconj (by norm_num) n1) (hconj2 (by norm_num) n2),
    mem_normalizer_titsR (hconj (by norm_num) n3) (hconj2 (by norm_num) n4),
    mem_normalizer_titsR (hconj (by norm_num) n5) (hconj2 (by norm_num) n6),
    by rw [eIJ]; exact invOn_titsR, invOn_titsR, by rw [eJJ]; exact invOn_titsR,
    by rw [eHI]; exact AgreeOn.refl _, by rw [eHJ]; exact AgreeOn.refl _⟩

theorem titsI_pow_four : titsI * titsI * (titsI * titsI) = 1 :=
  Subtype.ext titsTor_rel.2.2.2.2.2.2

theorem isConj_titsTD :
    IsConj titsTD (titsI * titsI) := by
  refine (isConj_iff.2 ⟨⟨wordIn 13 titsT titsWordGy, wordIn_titsT_mem_titsD _⟩, ?_⟩).symm
  exact Subtype.ext titsTor_class.1

theorem titsTD_eq_conj_mul_conj :
    ∃ g₁ g₂ : titsD, titsTD = g₁ * titsZD * g₁⁻¹ * (g₂ * titsZD * g₂⁻¹) :=
  ⟨⟨wordIn 13 titsT titsWordG₁, wordIn_titsT_mem_titsD _⟩,
    ⟨wordIn 13 titsT titsWordG₂, wordIn_titsT_mem_titsD _⟩, Subtype.ext titsTor_class.2.symm⟩

end Plane

section Module

variable {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
  (L : Subgroup (MulAut V)) (hZL : Subgroup.center L = ⊥) (e : L ⧸ Subgroup.center L ≃* titsD)

include hV hZL in
theorem exists_titsT_index :
    ∃ y : L, IsConj titsTD (modelProj L e y) ∧
      2 ^ 12 ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  have hord : orderOf (2 : ZMod 5) = 4 := by
    refine (orderOf_eq_iff (by norm_num)).2 ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := modelProj_surjective L e (titsI * titsI)
  have hm : ∀ n : ℕ, 0 < n → orderOf (2 : ZMod 5) ∣ 2 * n → 2 ≤ n := by
    intro n hn hdvd
    rw [hord] at hdvd
    omega
  have hidx := two_pow_le_index_of_orbits hV L hZL e (by norm_num) titsR_comm titsR_pow card_titsR
    (closure_le_normalizer titsR_q8)
    (fun K hKR hK => six_le_orbit_of_eq_five rfl titsR_pow card_titsR titsR_q8 hKR hK)
    titsI_pow_four titsR_q8.inv_ii hm hy
  exact ⟨y, by rw [hy]; exact isConj_titsTD, by simpa using hidx⟩

include hV hZL in
theorem two_pow_le_index_titsT {x : L} (hx : IsConj titsTD (modelProj L e x)) :
    2 ^ 12 ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨y, hy, hidx⟩ := exists_titsT_index hV L hZL e
  obtain ⟨c, hc⟩ := isConj_iff.1 (hy.symm.trans hx)
  rw [index_eq_of_modelProj_conj L hZL e hc.symm]
  exact hidx

include hV hZL in
theorem two_pow_le_index_titsZ {x : L} (hx : IsConj titsZD (modelProj L e x)) :
    2 ^ 6 ≤ (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  obtain ⟨g₁, g₂, ht⟩ := titsTD_eq_conj_mul_conj
  obtain ⟨l₁, hl₁⟩ := modelProj_surjective L e (g₁ * c⁻¹)
  obtain ⟨l₂, hl₂⟩ := modelProj_surjective L e (g₂ * c⁻¹)
  set xt : L := l₁ * x * l₁⁻¹ * (l₂ * x * l₂⁻¹) with hxt
  have hxtT : IsConj titsTD (modelProj L e xt) := by
    refine isConj_iff.2 ⟨1, ?_⟩
    have e1 : modelProj L e x = c * titsZD * c⁻¹ := hc.symm
    rw [hxt, map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hl₁, hl₂, e1, ht]
    group
  have h1 := two_pow_le_index_titsT hV L hZL e hxtT
  have h2 : (fixV (Subgroup.zpowers (xt : MulAut V))).index ≤
      (fixV (Subgroup.zpowers (x : MulAut V))).index ^ 2 := by
    have hxtV : (xt : MulAut V) = (l₁ : MulAut V) * x * (l₁ : MulAut V)⁻¹ *
        ((l₂ : MulAut V) * x * (l₂ : MulAut V)⁻¹) := rfl
    rw [hxtV, sq]
    refine (CFSG.QuasithinUnique.Setup.X5.index_fixV_mul_le _ _).trans ?_
    rw [CFSG.QuasithinUnique.Setup.X5.index_fixV_conj,
      CFSG.QuasithinUnique.Setup.X5.index_fixV_conj]
  by_contra hlt
  push Not at hlt
  have h3 : (fixV (Subgroup.zpowers (x : MulAut V))).index ^ 2 < (2 ^ 6) ^ 2 :=
    Nat.pow_lt_pow_left hlt two_ne_zero
  omega

end Module

theorem classTests_titsD
    {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hZL : Subgroup.center L = ⊥) (e : L ⧸ Subgroup.center L ≃* titsD) :
    ClassTests V L e (fun ξ => IsConj titsTD ξ) 5 2 0 := by
  refine ⟨fun E hE => card_le_of_isElem2 E hE, fun E hE hpure => card_le_of_pure E hE hpure,
    ?_, ?_, ?_, ?_⟩
  · intro F hF
    have hle : F ≤ (MulAut.conj : titsD →* MulAut titsD).range := fun α hα =>
      mem_range_conj_of_mul_self α (by rw [← sq]; exact hF.2 α hα)
    rw [inf_of_le_left hle, pow_zero, one_mul]
  · intro x _ _ hxB
    exact lt_of_lt_of_le (by norm_num) (two_pow_le_index_titsT hV L hZL e hxB)
  · intro x hx2 hxo
    exfalso
    apply hxo
    apply mem_range_conj_of_mul_self
    rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]
  · intro E _ _ hpure
    left
    intro x hx2 hx1 hxE
    have hπ1 : modelProj L e x ≠ 1 := fun h =>
      hx1 (modelProj_injective L hZL e (h.trans (map_one _).symm))
    have h2 : orderOf (modelProj L e x) = 2 :=
      orderOf_eq_prime (by rw [sq, ← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]) hπ1
    rcases titsD_involution_conj _ h2 with hz | ht
    · exact lt_of_lt_of_le (by norm_num) (two_pow_le_index_titsZ hV L hZL e hz)
    · exact absurd ht (hpure _ hxE hπ1)

end CFSG.Quasithin.B45Tor
