module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSettingW
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCoreO2

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Cores

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.LieType.HighestRoot CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

private theorem com_ht_le {m : ℕ} (hm : 1 ≤ m) {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB m) ∅) : ht γ ≤ 2 * (m : ℤ) - 1 := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht', h⟩ | ⟨i, s, hs, h⟩
  · rw [ht_of_toStdB_eq_add m h]
    have hne : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
    rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      · have hi := i.isLt
        have hj := j.isLt
        omega
  · rw [ht_of_toStdB_eq_single m h]
    rcases hs with rfl | rfl <;> · have hi := i.isLt; omega

private theorem com_toStdB_eq_of_ht_eq {m : ℕ} (hm : 2 ≤ m) (zero one : Fin m)
    (hzero : zero.val = 0) (hone : one.val = 1)
    {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB m) ∅)
    (hht : ht γ = 2 * (m : ℤ) - 1) :
    toStdB m γ = Pi.single zero 1 + Pi.single one 1 := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht', h⟩ | ⟨i, s, hs, h⟩
  · rw [ht_of_toStdB_eq_add m h] at hht
    have hne : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
    rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl
    · rw [h]
      have hi := i.isLt
      have hj := j.isLt
      have hsum : i.val + j.val = 1 := by omega
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h1
      · have hieq : i = zero := Fin.ext (by rw [hzero]; omega)
        have hjeq : j = one := Fin.ext (by rw [hone]; omega)
        rw [hieq, hjeq]
      · have hieq : i = one := Fin.ext (by rw [hone]; exact h1)
        have hjeq : j = zero := Fin.ext (by rw [hzero]; omega)
        rw [hieq, hjeq, add_comm]
    · exfalso; have hi := i.isLt; have hj := j.isLt; omega
    · exfalso; have hi := i.isLt; have hj := j.isLt; omega
    · exfalso; have hi := i.isLt; have hj := j.isLt; omega
  · rw [ht_of_toStdB_eq_single m h] at hht
    rcases hs with rfl | rfl <;> · exfalso; have hi := i.isLt; omega

theorem spinMinus_highest {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (Spin.Twisted.minusDatum n hirr).divisible = ∅ ∧
      IsIrreducible (Spin.Twisted.minusDatum n hirr).cartan ∧
      ∃ r : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ,
        IsHighestRoot (Spin.Twisted.minusDatum n hirr) r ∧
        ∀ γ₀ ∈ (Spin.Twisted.minusDatum n hirr).roots,
          (∀ δ ∈ (Spin.Twisted.minusDatum n hirr).roots, ht δ ≤ ht γ₀) → γ₀ = r := by
  have hm : 0 < n - 1 := by omega
  have hm2 : 2 ≤ n - 1 := by omega
  have hirrB : IsIrreducible (cartanB (n - 1)) := isIrreducible_cartanB hm
  obtain ⟨r, hr⟩ := exists_isHighestRoot (D := Spin.Twisted.minusDatum n hirr) hirrB rfl hm
  let zero : Fin (n - 1) := ⟨0, by omega⟩
  let one : Fin (n - 1) := ⟨1, by omega⟩
  have hzero : zero.val = 0 := rfl
  have hone : one.val = 1 := rfl
  have hzero_int : (zero : ℤ) = 0 := by simp [zero]
  have hone_int : (one : ℤ) = 1 := by simp [one]
  set θ : Fin (n - 1) → ℤ := ofStdB (n - 1) (Pi.single zero 1 + Pi.single one 1) with hθdef
  have hθstd : toStdB (n - 1) θ = Pi.single zero 1 + Pi.single one 1 := by
    rw [hθdef]; exact toStdB_ofStdB _ _
  have h0ne : zero ≠ one := by
    intro h
    have := congrArg Fin.val h
    simp [hzero, hone] at this
  have hθmem : θ ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    have h : θ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ := by
      rw [hθdef]
      exact ofStdB_mem_rootsB (n - 1)
        (Or.inl ⟨zero, one, 1, 1, h0ne, Or.inl rfl, Or.inl rfl, rfl⟩)
    exact h
  have hθht : ht θ = 2 * ((n - 1 : ℕ) : ℤ) - 1 := by
    rw [ht_of_toStdB_eq_add (n - 1) hθstd, hzero_int, hone_int]
    ring_nf
  have hbound : ∀ γ ∈ (Spin.Twisted.minusDatum n hirr).roots,
      ht γ ≤ 2 * ((n - 1 : ℕ) : ℤ) - 1 :=
    fun γ hγ => com_ht_le (m := n - 1) (by omega) hγ
  have hrmax : ht r = 2 * ((n - 1 : ℕ) : ℤ) - 1 := by
    have h1 : ht θ ≤ ht r := hr.height_le θ hθmem
    have h2 := hbound r hr.mem_roots
    linarith [hθht, h1, h2]
  have hreq : r = θ := by
    apply toStdB_injective (n - 1)
    rw [com_toStdB_eq_of_ht_eq (m := n - 1) hm2 zero one hzero hone hr.mem_roots hrmax,
      hθstd]
  rw [hreq] at hr
  refine ⟨rfl, hirrB, θ, hr, ?_⟩
  intro γ₀ hγ₀ hmax
  have hγht : ht γ₀ = 2 * ((n - 1 : ℕ) : ℤ) - 1 := by
    have h1 : ht θ ≤ ht γ₀ := hmax θ hθmem
    have h2 := hbound γ₀ hγ₀
    linarith [hθht, h1, h2]
  apply toStdB_injective (n - 1)
  rw [com_toStdB_eq_of_ht_eq (m := n - 1) hm2 zero one hzero hone hγ₀ hγht, hθstd]

theorem spinMinus_coreOne {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c)))
    {Rr Rm Q : Subgroup ↥(spinGroup (Spin.quadMinus n F b c))}
    (hRr : Rr = ggRootSub (Spin.Twisted.minusDatum n hirr) (MonoidHom.id _) β u)
    (hRm : Rm = ggRootSub (Spin.Twisted.minusDatum n hirr) (MonoidHom.id _) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer
      (Rr : Set ↥(spinGroup (Spin.quadMinus n F b c))))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  obtain ⟨hdiv, hirrB, r, hr, hmax⟩ := spinMinus_highest hn hirr
  exact coreOne_long_of
    (Spin.Twisted.minusDatum_isCTGroupDatum n hirr hn)
    (Spin.Twisted.minusDatum_steinbergExtras n hirr)
    hdiv hirrB
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ)
    hr hmax hl u hRr hRm hQ

theorem spinMinus_coreFour {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c)))
    {Rr Q : Subgroup ↥(spinGroup (Spin.quadMinus n F b c))}
    (hRr : Rr = ggRootSub (Spin.Twisted.minusDatum n hirr) (MonoidHom.id _) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer
      (Rr : Set ↥(spinGroup (Spin.quadMinus n F b c))))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set ↥(spinGroup (Spin.quadMinus n F b c))) := by
  have hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hl
    exact CFSG.LieType.RootSystem.weylAction_mem_roots _ w hγ₀
  have hS : Radical.SpinOmegaData (Spin.quadMinus n F b c) :=
    Radical.spinOmegaData_quadMinus hn hirr
  obtain ⟨P, P', hOrth, hRoot, hW⟩ :=
    Radical.exists_frame_hW_of_root_minus hn hirr hS hβ hl u
  have hRrS : Rr = Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e := by
    rw [hRr, ggRootSub, Subgroup.map_id]
    exact hRoot
  have hQeq : Q = pCoreOf 2 (Subgroup.normalizer
      (Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e :
        Set ↥(spinGroup (Spin.quadMinus n F b c)))) := by
    rw [hQ, hRrS]
  have hV : 6 ≤ Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
    omega
  have hle : Q ≤ Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e := by
    rw [hQeq]
    exact Radical.siegelO2_le_orthSiegelCore hS hOrth hV hW
  have hcomm : ⁅Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e,
      Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e⁆ ≤
      Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e :=
    Radical.orthSiegelCore_commutator_le hOrth hS.nondeg hV
  have hcen : Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e ≤
      Subgroup.centralizer
        (Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e :
          Set ↥(spinGroup (Spin.quadMinus n F b c))) :=
    Radical.orthSiegelCore_le_centralizer hS hOrth
  refine ⟨?_, ?_⟩
  · calc ⁅Q, Q⁆ ≤ ⁅Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e,
        Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e⁆ :=
        Subgroup.commutator_mono hle hle
    _ ≤ Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e := hcomm
    _ = Rr := hRrS.symm
  · calc Q ≤ Radical.orthSiegelCore (Spin.quadMinus n F b c) P.e P'.e := hle
    _ ≤ Subgroup.centralizer
        (Radical.siegelRoot (Spin.quadMinus n F b c) P.e P'.e :
          Set ↥(spinGroup (Spin.quadMinus n F b c))) := hcen
    _ = Subgroup.centralizer (Rr : Set ↥(spinGroup (Spin.quadMinus n F b c))) := by rw [hRrS]

end CFSG.StandardType.LieKnownR2.POmega.Cores
