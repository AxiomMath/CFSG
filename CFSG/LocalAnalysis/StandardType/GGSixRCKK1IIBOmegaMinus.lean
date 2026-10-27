module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCores
public import CFSG.CGT.Foote81L6.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
public import CFSG.CGT.Foote81L6.TStruct.DihSub
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.GH74.GLS.C3.Layer1.St1P89Transfer
public import CFSG.GH74.GLS.C3.Layer1.St1Prop810a
public import CFSG.GH74.GLS.IVK.Lifted.Rnormal4
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt75.Equivariance
public import CFSG.Goldschmidt75.Sig32Core
public import CFSG.Goldschmidt75.Sig3Four
public import CFSG.Goldschmidt75.Sig3Trans
public import CFSG.GroupTheory.OddOrderClosurePResidual
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.HighestRoot
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open scoped commutatorElement

private theorem rckp3_ht_le {m : ℕ} (hm : 1 ≤ m) {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB m) ∅) : ht γ ≤ 2 * (m : ℤ) - 1 := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht', h⟩ | ⟨i, s, hs, h⟩
  · rw [ht_of_toStdB_eq_add m h]
    rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      · have hi := i.isLt
        have hj := j.isLt
        omega
  · rw [ht_of_toStdB_eq_single m h]
    rcases hs with rfl | rfl <;> · have hi := i.isLt; omega

private theorem rckp3_rootForm_pos {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hdiv : D.divisible = ∅) {r γ δ : Fin D.rank → ℤ} (hr : IsHighestRoot D r)
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hsum : γ + δ = r) (hγr : γ ≠ r) (hδr : δ ≠ r)
    (hγht : 0 < ht γ) (hδht : 0 < ht δ) : 0 < rootForm D γ r := by
  have hr0 : toRat r ≠ 0 := fun e =>
    ne_zero_of_mem_roots D.isFiniteType D.divisible hr.mem_roots
      (toRat_injective (by simp [e]))
  have hrr : 0 < rootForm D r r := form_pos D.isFiniteType hr0
  have hγnn : 0 ≤ rootForm D γ r := rootForm_nonneg_of_ht_pos hr.dominant hγ hγht
  have hδnn : 0 ≤ rootForm D δ r := rootForm_nonneg_of_ht_pos hr.dominant hδ hδht
  obtain ⟨cγ, hcγ⟩ :=
    CFSG.StandardType.LieKnownR2.exists_pairing_int D hdiv (γ := γ) hr.mem_roots
  obtain ⟨cδ, hcδ⟩ :=
    CFSG.StandardType.LieKnownR2.exists_pairing_int D hdiv (γ := δ) hr.mem_roots
  have hcγ0 : (0 : ℤ) ≤ cγ := by
    have h : (0 : ℚ) ≤ (cγ : ℚ) := by
      have h2 : (0 : ℚ) ≤ (cγ : ℚ) * rootForm D r r := by rw [hcγ]; nlinarith
      exact (mul_nonneg_iff_of_pos_right hrr).mp h2
    exact_mod_cast h
  have hcδ0 : (0 : ℤ) ≤ cδ := by
    have h : (0 : ℚ) ≤ (cδ : ℚ) := by
      have h2 : (0 : ℚ) ≤ (cδ : ℚ) * rootForm D r r := by rw [hcδ]; nlinarith
      exact (mul_nonneg_iff_of_pos_right hrr).mp h2
    exact_mod_cast h
  have hcγ2 : cγ ≤ 2 := (CFSG.StandardType.LieKnownR2.pairing_le_two D hr hγ hcγ).1
  have hcδ2 : cδ ≤ 2 := (CFSG.StandardType.LieKnownR2.pairing_le_two D hr hδ hcδ).1
  have hcγne : cγ ≠ 2 := fun h =>
    hγr ((CFSG.StandardType.LieKnownR2.pairing_le_two D hr hγ hcγ).2 h)
  have hcδne : cδ ≠ 2 := fun h =>
    hδr ((CFSG.StandardType.LieKnownR2.pairing_le_two D hr hδ hcδ).2 h)
  have hsumR : rootForm D r r = rootForm D γ r + rootForm D δ r := by
    have h1 : rootForm D ((1 : ℕ) • γ + (1 : ℕ) • δ) r =
        (1 : ℕ) * rootForm D γ r + (1 : ℕ) * rootForm D δ r :=
      rootForm_nsmul_add_nsmul (D := D) 1 1 γ δ r
    simpa only [one_smul, Nat.cast_one, one_mul, hsum] using h1
  have hcsum : cγ + cδ = 2 := by
    have h : ((cγ : ℚ) + cδ) * rootForm D r r = (2 : ℚ) * rootForm D r r := by
      rw [add_mul, hcγ, hcδ, hsumR]
      ring
    have h' : ((cγ : ℚ) + cδ) = 2 := mul_right_cancel₀ hrr.ne' h
    exact_mod_cast h'
  have hcγ1 : cγ = 1 := by omega
  rw [hcγ1] at hcγ
  have h2 : (1 : ℚ) * rootForm D r r = 2 * rootForm D γ r := hcγ
  nlinarith [h2, hrr]

private theorem rckp3_pair_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F b c), Spin.Twisted.minusDatum n hirr⟩) :
    ∃ (β : Fin L.D.rank → ℤ) (x : L.K) (V : Subgroup L.K),
      β ∈ L.D.roots ∧ GGLongRoot L.D β ∧
      L.D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ pCoreOf 2 (Subgroup.normalizer (L.D.rootGroup β : Set L.K)) ∧
      ∀ v ∈ V, v ≠ 1 → ∃ j : L.K, v = j * x * j⁻¹ := by
  subst hL
  classical
  have hrank : (Spin.Twisted.minusDatum n hirr).rank = n - 1 := rfl
  let i0 : Fin (Spin.Twisted.minusDatum n hirr).rank := ⟨0, by rw [hrank]; omega⟩
  let i1 : Fin (Spin.Twisted.minusDatum n hirr).rank := ⟨1, by rw [hrank]; omega⟩
  let i2 : Fin (Spin.Twisted.minusDatum n hirr).rank := ⟨2, by rw [hrank]; omega⟩
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by simp [i0, i1])
  have h02 : i0 ≠ i2 := Fin.ne_of_val_ne (by simp [i0, i2])
  have h12 : i1 ≠ i2 := Fin.ne_of_val_ne (by simp [i1, i2])
  have h10 : i1 ≠ i0 := h01.symm
  have h20 : i2 ≠ i0 := h02.symm
  have h21 : i2 ≠ i1 := h12.symm
  let Fr : OddFrame (Spin.quadMinus n F b c) (n - 1) := Spin.Twisted.minusFrame n b c
  let β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ :=
    ofStdB (n - 1) (Pi.single i0 1 + Pi.single i1 1)
  let γ : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ :=
    ofStdB (n - 1) (Pi.single i0 1 + Pi.single i2 1)
  let δ : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ :=
    ofStdB (n - 1) (Pi.single i1 1 + Pi.single i2 (-1))
  let x : spinGroup (Spin.quadMinus n F b c) :=
    Fr.longRoot h01 true true (Multiplicative.ofAdd (1 : F))
  let y : spinGroup (Spin.quadMinus n F b c) :=
    Fr.longRoot h02 true true (Multiplicative.ofAdd (1 : F))
  let z : spinGroup (Spin.quadMinus n F b c) :=
    Fr.longRoot h21 true false (Multiplicative.ofAdd (1 : F))
  let nn : spinGroup (Spin.quadMinus n F b c) := Fr.longWeyl h12 true false
  let V : Subgroup (spinGroup (Spin.quadMinus n F b c)) :=
    Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hβstd : toStdB (n - 1) β =
      Pi.single i0 (boolSign true) + Pi.single i1 (boolSign true) := by
    rw [boolSign_true]; exact toStdB_ofStdB _ _
  have hγstd : toStdB (n - 1) γ =
      Pi.single i0 (boolSign true) + Pi.single i2 (boolSign true) := by
    rw [boolSign_true]; exact toStdB_ofStdB _ _
  have hδstd : toStdB (n - 1) δ =
      Pi.single i1 (boolSign true) + Pi.single i2 (boolSign false) := by
    rw [boolSign_true, boolSign_false]; exact toStdB_ofStdB _ _
  have hβstdR : toStdB (Spin.Twisted.minusDatum n hirr).rank β =
      Pi.single i0 (boolSign true) + Pi.single i1 (boolSign true) := hβstd
  have hγstdR : toStdB (Spin.Twisted.minusDatum n hirr).rank γ =
      Pi.single i0 (boolSign true) + Pi.single i2 (boolSign true) := hγstd
  have hδstdR : toStdB (Spin.Twisted.minusDatum n hirr).rank δ =
      Pi.single i1 (boolSign true) + Pi.single i2 (boolSign false) := hδstd
  have hβmem : β ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    rw [Spin.Twisted.minusDatum_roots]
    exact Spin.Twisted.mem_roots_of_toStdB_eq_long n h01 true true hβstd
  have hγmem : γ ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    rw [Spin.Twisted.minusDatum_roots]
    exact Spin.Twisted.mem_roots_of_toStdB_eq_long n h02 true true hγstd
  have hδmem : δ ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    rw [Spin.Twisted.minusDatum_roots]
    exact Spin.Twisted.mem_roots_of_toStdB_eq_long n h12 true false hδstd
  obtain ⟨hdiv, hirrB, r, hr, huniq⟩ :=
    CFSG.StandardType.LieKnownR2.POmega.Cores.spinMinus_highest hn hirr
  have hβht : ht β = 2 * (((Spin.Twisted.minusDatum n hirr).rank : ℕ) : ℤ) - 1 := by
    have h := ht_of_toStdB_eq_add (Spin.Twisted.minusDatum n hirr).rank hβstdR
    rw [h]
    simp [i0, i1, boolSign_true]
    ring
  have hrmax : ht r = 2 * (((Spin.Twisted.minusDatum n hirr).rank : ℕ) : ℤ) - 1 := by
    have h1 : ht β ≤ ht r := hr.height_le β hβmem
    have h2 : ht r ≤ 2 * ((n - 1 : ℕ) : ℤ) - 1 :=
      rckp3_ht_le (m := n - 1) (by omega) (by
        have h := hr.mem_roots
        rwa [Spin.Twisted.minusDatum_roots] at h)
    omega
  have hβeq : β = r := by
    apply huniq β hβmem
    intro ε hε
    have hb : ht ε ≤ 2 * ((n - 1 : ℕ) : ℤ) - 1 :=
      rckp3_ht_le (m := n - 1) (by omega) (by
        have h := hε
        rwa [Spin.Twisted.minusDatum_roots] at h)
    rw [hβht]
    omega
  have hrβ : IsHighestRoot (Spin.Twisted.minusDatum n hirr) β := by
    rw [hβeq]; exact hr
  have hβlong : GGLongRoot (Spin.Twisted.minusDatum n hirr) β := by
    refine ⟨1, β, hβmem, ?_, ?_⟩
    · intro ε hε; exact hrβ.height_le ε hε
    · rw [map_one]; rfl
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero F 2
  have hneg1 : (-1 : F) = 1 := by rw [neg_eq_iff_add_eq_zero]; exact h11
  have hx1 : x ≠ 1 := by
    intro hx
    have hinj := HypFrame.longRoot_injective Fr.toHypFrame h01 true true
    have heq : x = (Fr.longRoot h01 true true) (Multiplicative.ofAdd (0 : F)) := by
      rw [hx]; simp
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrArg Multiplicative.toAdd (hinj heq))
  have hx2 : x * x = 1 := by
    change (Fr.longRoot h01 true true) (Multiplicative.ofAdd (1 : F)) *
        (Fr.longRoot h01 true true) (Multiplicative.ofAdd (1 : F)) = 1
    rw [← map_mul]
    rw [show (Multiplicative.ofAdd (1 : F)) * (Multiplicative.ofAdd (1 : F)) =
        Multiplicative.ofAdd ((1 : F) + (1 : F)) from rfl, h11]
    exact map_one _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hcard_range : Nat.card (Fr.longRoot h01 true true).range = 2 := by
    have hinj := HypFrame.longRoot_injective Fr.toHypFrame h01 true true
    haveI : Finite ↥(Fr.longRoot h01 true true).range :=
      Finite.of_injective ((MonoidHom.ofInjective hinj).toEquiv.symm) (Equiv.injective _)
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact (Nat.card_congr Multiplicative.toAdd).trans hcard
  have heq_range :=
    (MonoidHom.ofInjective (HypFrame.longRoot_injective Fr.toHypFrame h01 true true)).toEquiv.symm
  haveI : Finite ↥(Fr.longRoot h01 true true).range :=
    Finite.of_injective heq_range heq_range.injective
  have hroot : (Spin.Twisted.minusDatum n hirr).rootGroup β = Subgroup.zpowers x := by
    have hrl : (Spin.Twisted.minusDatum n hirr).rootGroup β =
        (Fr.longRoot h01 true true).range :=
      Spin.Twisted.minusRootGroup_eq_long n hirr h01 true true hβstd
    rw [hrl]
    have hle : Subgroup.zpowers x ≤ (Fr.longRoot h01 true true).range :=
      Subgroup.zpowers_le.mpr ⟨Multiplicative.ofAdd (1 : F), rfl⟩
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard_range, Nat.card_zpowers, hxord])).symm
  have hx_beta : x ∈ (Spin.Twisted.minusDatum n hirr).rootGroup β := by
    rw [hroot]; exact Subgroup.mem_zpowers x
  have hy_beta : y ∈ (Spin.Twisted.minusDatum n hirr).rootGroup γ := by
    have hyr : (Spin.Twisted.minusDatum n hirr).rootGroup γ =
        (Fr.longRoot h02 true true).range :=
      Spin.Twisted.minusRootGroup_eq_long n hirr h02 true true hγstd
    rw [hyr]; exact ⟨Multiplicative.ofAdd (1 : F), rfl⟩
  have hy1 : y ≠ 1 := by
    intro hy
    have hinj := HypFrame.longRoot_injective Fr.toHypFrame h02 true true
    have heq : y = (Fr.longRoot h02 true true) (Multiplicative.ofAdd (0 : F)) := by
      rw [hy]; simp
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrArg Multiplicative.toAdd (hinj heq))
  have hy2 : y * y = 1 := by
    change (Fr.longRoot h02 true true) (Multiplicative.ofAdd (1 : F)) *
        (Fr.longRoot h02 true true) (Multiplicative.ofAdd (1 : F)) = 1
    rw [← map_mul]
    rw [show (Multiplicative.ofAdd (1 : F)) * (Multiplicative.ofAdd (1 : F)) =
        Multiplicative.ofAdd ((1 : F) + (1 : F)) from rfl, h11]
    exact map_one _
  have hcommxy : x * y = y * x :=
    (HypFrame.commute_longRoot_longRoot_left Fr.toHypFrame h01 h02 true true true
      (1 : F) (1 : F)).eq
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hy2
  have hxyne : x ≠ y := by
    intro h
    have hv : spinAction (Spin.quadMinus n F b c) x (Fr.vec i1 false) =
        spinAction (Spin.quadMinus n F b c) y (Fr.vec i1 false) := by rw [h]
    have hxact : spinAction (Spin.quadMinus n F b c) x (Fr.vec i1 false) =
        Fr.vec i1 false + Fr.vec i0 true := by
      simpa using HypFrame.spinAction_longRoot_vec_not_right Fr.toHypFrame (i := i0) (j := i1)
        h01 true true (1 : F)
    have hyact : spinAction (Spin.quadMinus n F b c) y (Fr.vec i1 false) = Fr.vec i1 false :=
      HypFrame.spinAction_longRoot_vec_of_ne Fr.toHypFrame (i := i0) (j := i2) (k := i1)
        h02 true true (1 : F) h10 h12 false
    rw [hxact, hyact] at hv
    have hv0 : Fr.vec i0 true = 0 := by
      have h' : Fr.vec i1 false + Fr.vec i0 true = Fr.vec i1 false + 0 := by
        simpa using hv
      exact add_left_cancel h'
    have hp := Fr.polar_vec_not i0 true
    rw [hv0] at hp
    exact (zero_ne_one : (0 : F) ≠ 1) (by simpa using hp)
  have hn_conj : nn * x * nn⁻¹ = y := by
    have h := HypFrame.conj_longRoot Fr.toHypFrame nn h01 true true h02 true true
      (l := (1 : F)) (m := (-1 : F))
      (by rw [HypFrame.spinAction_longWeyl_vec_of_ne Fr.toHypFrame h12 true false
          (show i0 ≠ i1 from h01) (show i0 ≠ i2 from h02) true, one_smul])
      (by rw [HypFrame.spinAction_longWeyl_vec_left Fr.toHypFrame h12 true false, Bool.not_false,
          neg_one_smul])
      (1 : F)
    rw [show (1 : F) * (-1) * 1 = (-1 : F) by ring, hneg1] at h
    exact h
  have hz_conj : z * x * z⁻¹ = x * y := by
    have hcomm : ⁅z, x⁆ = y := by
      have h := HypFrame.commutator_longRoot_longRoot Fr.toHypFrame (i := i2) (j := i1) (k := i0)
        h21 h10 h20 true false true (1 : F) (1 : F)
      simp only [Bool.not_false, one_mul] at h
      rw [HypFrame.longRoot_swap Fr.toHypFrame h10 true true (1 : F),
        hneg1, HypFrame.longRoot_swap Fr.toHypFrame h20 true true (1 : F), hneg1] at h
      simpa using h
    have h' : z * x * z⁻¹ * x⁻¹ = y := by
      rwa [commutatorElement_def] at hcomm
    calc z * x * z⁻¹ = z * x * z⁻¹ * x⁻¹ * x := by group
      _ = y * x := by rw [h']
      _ = x * y := hcommxy.symm
  have hxV : x ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hVcard : Nat.card V = 4 :=
    CFSG.GH74.GLS.C3.Layer1.P89.card_klein hx2' hy2' hcommxy hx1 hy1 hxyne
  have hVab : IsElemAbelian 2 V :=
    CFSG.GH74.GLS.C3.Layer1.P89.isElemAbelian_pair hx2' hy2' hcommxy
  have hct := Spin.Twisted.minusDatum_isCTGroupDatum n hirr hn
  have hext := Spin.Twisted.minusDatum_steinbergExtras n hirr
  have hX : ∀ ε ∈ (Spin.Twisted.minusDatum n hirr).roots,
      IsPGroup 2 ((Spin.Twisted.minusDatum n hirr).rootGroup ε) :=
    fun ε hε => isPGroup_minusRootGroup hirr hε
  obtain ⟨-, hQp, hQN, hNQ, -⟩ :=
    highestRootGen_of_isHighestRoot hct hext
      (divisibleNormalizes_of_divisible_eq_empty hdiv)
      (divisibleWeylMem_of_divisible_eq_empty hdiv) hirrB hX hrβ
  have hQle : highestRootRadical (Spin.Twisted.minusDatum n hirr) β ≤
      pCoreOf 2 (Subgroup.normalizer ((Spin.Twisted.minusDatum n hirr).rootGroup β :
        Set (spinGroup (Spin.quadMinus n F b c)))) :=
    GGRootNorm.le_pCoreOf_of_normalized hQN hQp (Subgroup.le_normalizer_iff.mp hNQ)
  have hβ0 : toRat β ≠ 0 := fun e =>
    ne_zero_of_mem_roots (Spin.Twisted.minusDatum n hirr).isFiniteType
      (Spin.Twisted.minusDatum n hirr).divisible hβmem
      (toRat_injective (by simp [e]))
  have hposβ : 0 < rootForm (Spin.Twisted.minusDatum n hirr) β β :=
    form_pos (Spin.Twisted.minusDatum n hirr).isFiniteType hβ0
  have hxQ : x ∈ highestRootRadical (Spin.Twisted.minusDatum n hirr) β :=
    rootGroup_le_highestRootRadical hβmem hposβ hx_beta
  have hγht : ht γ = 2 * (((Spin.Twisted.minusDatum n hirr).rank : ℕ) : ℤ) - 2 := by
    have h := ht_of_toStdB_eq_add (Spin.Twisted.minusDatum n hirr).rank hγstdR
    rw [h]
    simp [i0, i2, boolSign_true]
    ring
  have hδht : ht δ = 1 := by
    have h := ht_of_toStdB_eq_add (Spin.Twisted.minusDatum n hirr).rank hδstdR
    rw [h]
    simp [i1, i2, boolSign_true, boolSign_false]
  have hγδ : γ + δ = β := by
    apply toStdB_injective (Spin.Twisted.minusDatum n hirr).rank
    rw [toStdB_add, hγstdR, hδstdR, hβstdR]
    funext k
    simp only [Pi.add_apply, Pi.single_apply, boolSign_true, boolSign_false]
    split_ifs <;> omega
  have hγβ : γ ≠ β := by
    intro h
    rw [h] at hγht
    omega
  have hδβ : δ ≠ β := by
    intro h
    rw [h] at hδht
    omega
  have hposγ : 0 < rootForm (Spin.Twisted.minusDatum n hirr) γ β :=
    rckp3_rootForm_pos hdiv hrβ hγmem hδmem hγδ hγβ hδβ
      (by rw [hγht]; omega) (by rw [hδht]; norm_num)
  have hyQ : y ∈ highestRootRadical (Spin.Twisted.minusDatum n hirr) β :=
    rootGroup_le_highestRootRadical hγmem hposγ hy_beta
  have hVpc : V ≤ pCoreOf 2 (Subgroup.normalizer
      ((Spin.Twisted.minusDatum n hirr).rootGroup β :
        Set (spinGroup (Spin.quadMinus n F b c)))) :=
    (sup_le (Subgroup.zpowers_le.mpr hxQ) (Subgroup.zpowers_le.mpr hyQ)).trans hQle
  have hconj : ∀ v ∈ V, v ≠ 1 →
      ∃ j : spinGroup (Spin.quadMinus n F b c), v = j * x * j⁻¹ := by
    intro v hv hv1
    have hcommV : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      rcases CFSG.GH74.GLS.C3.Layer1.P89.mem_zpowers_of_sq hx2' ha with rfl | rfl <;>
        rcases CFSG.GH74.GLS.C3.Layer1.P89.mem_zpowers_of_sq hy2' hb with rfl | rfl <;>
        simp [hcommxy]
    obtain ⟨u, hu, w, hw, rfl⟩ :=
      (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer
        (CFSG.CGT.Foote81L6.le_normalizer_of_comm hcommV)).1 hv
    rcases CFSG.GH74.GLS.C3.Layer1.P89.mem_zpowers_of_sq hx2' hu with rfl | rfl <;>
      rcases CFSG.GH74.GLS.C3.Layer1.P89.mem_zpowers_of_sq hy2' hw with rfl | rfl
    · exact absurd (by simp) hv1
    · exact ⟨nn, by rw [one_mul]; exact hn_conj.symm⟩
    · exact ⟨1, by simp⟩
    · exact ⟨z, hz_conj.symm⟩
  exact ⟨β, x, V, hβmem, hβlong, hroot, hx2, hx1, hxV, hVab, hVcard, hVpc, hconj⟩

theorem rckIIPair_OmegaMinus
    (n : ℕ) (hn : 4 ≤ n) (hadm : StatedLieAdmissible .POmegaMinus n 2 1) :
      RCKIIPair .POmegaMinus n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have e : ggU .POmegaMinus n 1 =
      ⟨spinGroup (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr 2 1)⟩ := by
    simp only [ggU, lieUniversal]
  exact rckp3_pair_of_eq (n := n) hcard hn (minusCoeffs_irr 2 1)
    (ggU .POmegaMinus n 1) e

end CFSG.StandardType.RCKK1II
