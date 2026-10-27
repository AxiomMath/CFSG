module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapLemmaR
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapThreeOne
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars
public import CFSG.HardMathSupport.Curtis.Proving.AlternatingElemAbelian

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lemmaRHyp_of_dispatchHyp {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {X : Type}
    [Group X] {φ : ↥(kGenIn V H) →* X} (hs : Function.Surjective φ)
    (hk : ∀ k : ↥(kGenIn V H), φ k = 1 ↔ (k : G) ∈ eCentSet V H T) :
    LemmaRHyp V (eSub V H T) (kGenIn V H) φ := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  exact
    { isTI := h83.isTI
      elemAbelian_V := h83.elemAbelian
      elemAbelian_E := h83.isElemAbelian_eSub
      inf_ne_bot := h83.inf_eSub_ne_bot
      le_K := le_kGenIn_self V H
      le_normalizer := fun k hk' =>
        le_normalizer_conjClosure (V ⊓ Subgroup.centralizer (T : Set G)) H
          (kGenIn_le_H h83.le_H hk')
      surjective := hs
      ker_iff := hk }

theorem exists_mem_V_map_ne_one {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {X : Type}
    [Group X] (e : X ≃* alternatingGroup (Fin 6)) {φ : ↥(kGenIn V H) →* X}
    (hs : Function.Surjective φ) (hk : ∀ k : ↥(kGenIn V H), φ k = 1 ↔ (k : G) ∈ eCentSet V H T) :
    ∃ v : ↥(kGenIn V H), (v : G) ∈ V ∧ φ v ≠ 1 := by
  by_contra hcon
  have hall : ∀ v : ↥(kGenIn V H), (v : G) ∈ V → φ v = 1 := by
    intro v hv
    by_contra hv1
    exact hcon ⟨v, hv, hv1⟩
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hVC : V ≤ Subgroup.centralizer (eSub V H T : Set G) := by
    intro v hv
    have h1 : φ ⟨v, le_kGenIn_self V H hv⟩ = 1 := hall ⟨v, le_kGenIn_self V H hv⟩ hv
    have h2 := (hk ⟨v, le_kGenIn_self V H hv⟩).1 h1
    simpa [eCentSet] using h2
  have hconj : conjClosure V H ≤ Subgroup.centralizer (eSub V H T : Set G) :=
    conjClosure_le fun g hg z hz => h83.conj_mem_centralizer_eSub hg (hVC hz)
  have hkC : ∀ k : ↥(kGenIn V H), φ k = 1 := fun k =>
    (hk k).2 (by simpa [eCentSet] using hconj (kGenIn_le_conjClosure V H k.2))
  haveI : Nontrivial (alternatingGroup (Fin 6)) :=
    alternatingGroup.nontrivial_of_three_le_card (α := Fin 6) (by simp)
  obtain ⟨y, hy⟩ := exists_ne (1 : alternatingGroup (Fin 6))
  have hx1 : e.symm y ≠ 1 := by
    intro hEq
    apply hy
    have := congrArg e hEq
    simpa using this
  obtain ⟨k, hk_eq⟩ := hs (e.symm y)
  exact hx1 (by rw [← hk_eq]; exact hkC k)

private def w85g_sigma : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 3 4

private def w85g_alpha : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def w85g_beta : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private lemma w85g_sigma_mem : w85g_sigma ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)

private lemma w85g_alpha_mem : w85g_alpha ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)

private lemma w85g_beta_mem : w85g_beta ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)

private lemma w85g_sigma_sq : w85g_sigma * w85g_sigma = 1 := by
  decide +kernel

private lemma w85g_sigma_ne_one : w85g_sigma ≠ 1 := by
  decide +kernel

private lemma w85g_alpha_cube : w85g_alpha ^ 3 = 1 := by
  decide +kernel

private lemma w85g_beta_cube : w85g_beta ^ 3 = 1 := by
  decide +kernel

private lemma w85g_alpha_ne_one : w85g_alpha ≠ 1 := by
  decide +kernel

private lemma w85g_beta_ne_one : w85g_beta ≠ 1 := by
  decide +kernel

private lemma w85g_disjoint : ∀ x : Fin 6, w85g_alpha x = x ∨ w85g_beta x = x := by
  decide +kernel

private lemma w85g_sigma_alpha :
    w85g_sigma * w85g_alpha * w85g_sigma⁻¹ = w85g_alpha⁻¹ := by
  decide +kernel

private lemma w85g_sigma_beta : w85g_sigma * w85g_beta * w85g_sigma⁻¹ = w85g_beta⁻¹ := by
  decide +kernel

private lemma w85g_alpha_beta_comm : w85g_alpha * w85g_beta = w85g_beta * w85g_alpha := by
  decide +kernel

theorem exists_elemAbelian_nine_inverted {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) {d : X} (hd2 : d * d = 1) (hd1 : d ≠ 1) :
    ∃ P : Subgroup X, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 2 ∧ ∀ x ∈ P, d * x * d⁻¹ = x⁻¹ := by
  let d' : alternatingGroup (Fin 6) := e d
  have hd'2 : d' * d' = 1 := by
    change e d * e d = 1
    rw [← map_mul, hd2, map_one]
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hd1
    have h' := congrArg (fun z : alternatingGroup (Fin 6) => e.symm z) h
    simpa [d'] using h'
  have hd'perm1 : (d' : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hd'1 (Subtype.ext h)
  have hd'perm2 : (d' : Equiv.Perm (Fin 6)) * (d' : Equiv.Perm (Fin 6)) = 1 := by
    simpa using congrArg Subtype.val hd'2
  obtain ⟨ρ, hρm, hρ⟩ :=
    CFSG.Quasithin.S143.alt6_invol_conj w85g_sigma (d' : Equiv.Perm (Fin 6))
      w85g_sigma_mem d'.2 w85g_sigma_ne_one hd'perm1 w85g_sigma_sq hd'perm2
  let a₁ : Equiv.Perm (Fin 6) := MulAut.conj ρ w85g_alpha
  let b₁ : Equiv.Perm (Fin 6) := MulAut.conj ρ w85g_beta
  have ha₁_mem : a₁ ∈ alternatingGroup (Fin 6) := by
    change ρ * w85g_alpha * ρ⁻¹ ∈ alternatingGroup (Fin 6)
    exact (alternatingGroup (Fin 6)).mul_mem
      ((alternatingGroup (Fin 6)).mul_mem hρm w85g_alpha_mem)
      ((alternatingGroup (Fin 6)).inv_mem hρm)
  have hb₁_mem : b₁ ∈ alternatingGroup (Fin 6) := by
    change ρ * w85g_beta * ρ⁻¹ ∈ alternatingGroup (Fin 6)
    exact (alternatingGroup (Fin 6)).mul_mem
      ((alternatingGroup (Fin 6)).mul_mem hρm w85g_beta_mem)
      ((alternatingGroup (Fin 6)).inv_mem hρm)
  have ha₁_cube : a₁ ^ 3 = 1 := by
    change (MulAut.conj ρ w85g_alpha) ^ 3 = 1
    rw [← map_pow, w85g_alpha_cube, map_one]
  have hb₁_cube : b₁ ^ 3 = 1 := by
    change (MulAut.conj ρ w85g_beta) ^ 3 = 1
    rw [← map_pow, w85g_beta_cube, map_one]
  have ha₁_ne : a₁ ≠ 1 := by
    intro h
    apply w85g_alpha_ne_one
    have h' : MulAut.conj ρ w85g_alpha = 1 := by simpa [a₁] using h
    exact (MulAut.conj ρ).injective (by rw [h', map_one])
  have hb₁_ne : b₁ ≠ 1 := by
    intro h
    apply w85g_beta_ne_one
    have h' : MulAut.conj ρ w85g_beta = 1 := by simpa [b₁] using h
    exact (MulAut.conj ρ).injective (by rw [h', map_one])
  have hdisj₁ : ∀ x : Fin 6, a₁ x = x ∨ b₁ x = x := by
    intro x
    rcases w85g_disjoint (ρ⁻¹ x) with h | h
    · left
      simpa [a₁, MulAut.conj_apply, Equiv.Perm.mul_apply] using congrArg ρ h
    · right
      simpa [b₁, MulAut.conj_apply, Equiv.Perm.mul_apply] using congrArg ρ h
  have hda : MulAut.conj (d' : Equiv.Perm (Fin 6)) a₁ = a₁⁻¹ := by
    rw [← hρ, show a₁ = ρ * w85g_alpha * ρ⁻¹ from rfl, MulAut.conj_apply]
    calc ρ * w85g_sigma * ρ⁻¹ * (ρ * w85g_alpha * ρ⁻¹) * (ρ * w85g_sigma * ρ⁻¹)⁻¹
        = ρ * (w85g_sigma * w85g_alpha * w85g_sigma⁻¹) * ρ⁻¹ := by group
      _ = ρ * w85g_alpha⁻¹ * ρ⁻¹ := by rw [w85g_sigma_alpha]
      _ = (ρ * w85g_alpha * ρ⁻¹)⁻¹ := by group
  have hdb : MulAut.conj (d' : Equiv.Perm (Fin 6)) b₁ = b₁⁻¹ := by
    rw [← hρ, show b₁ = ρ * w85g_beta * ρ⁻¹ from rfl, MulAut.conj_apply]
    calc ρ * w85g_sigma * ρ⁻¹ * (ρ * w85g_beta * ρ⁻¹) * (ρ * w85g_sigma * ρ⁻¹)⁻¹
        = ρ * (w85g_sigma * w85g_beta * w85g_sigma⁻¹) * ρ⁻¹ := by group
      _ = ρ * w85g_beta⁻¹ * ρ⁻¹ := by rw [w85g_sigma_beta]
      _ = (ρ * w85g_beta * ρ⁻¹)⁻¹ := by group
  have hab : Commute a₁ b₁ := by
    show a₁ * b₁ = b₁ * a₁
    rw [show a₁ = ρ * w85g_alpha * ρ⁻¹ from rfl,
      show b₁ = ρ * w85g_beta * ρ⁻¹ from rfl]
    calc ρ * w85g_alpha * ρ⁻¹ * (ρ * w85g_beta * ρ⁻¹)
        = ρ * (w85g_alpha * w85g_beta) * ρ⁻¹ := by group
      _ = ρ * (w85g_beta * w85g_alpha) * ρ⁻¹ := by rw [w85g_alpha_beta_comm]
      _ = ρ * w85g_beta * ρ⁻¹ * (ρ * w85g_alpha * ρ⁻¹) := by group
  have hmain : ∀ n k : ℕ,
      MulAut.conj (d' : Equiv.Perm (Fin 6)) (a₁ ^ n * b₁ ^ k) = (a₁ ^ n * b₁ ^ k)⁻¹ := by
    intro n k
    rw [map_mul, map_pow, map_pow, hda, hdb, mul_inv_rev, ← inv_pow, ← inv_pow]
    exact ((hab.inv_inv).pow_pow n k).eq
  let φ0 : X →* Equiv.Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
  have hφ0 : Function.Injective φ0 := by
    intro x y h
    apply e.injective
    exact Subtype.ext h
  let a : X := e.symm ⟨a₁, ha₁_mem⟩
  let b : X := e.symm ⟨b₁, hb₁_mem⟩
  have hea : e a = ⟨a₁, ha₁_mem⟩ := MulEquiv.apply_symm_apply e ⟨a₁, ha₁_mem⟩
  have heb : e b = ⟨b₁, hb₁_mem⟩ := MulEquiv.apply_symm_apply e ⟨b₁, hb₁_mem⟩
  have hφ0a : φ0 a = a₁ := by
    change ((e a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = a₁
    rw [hea]
  have hφ0b : φ0 b = b₁ := by
    change ((e b : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = b₁
    rw [heb]
  have hφ0d : φ0 d = (d' : Equiv.Perm (Fin 6)) := rfl
  have ha3 : a ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hea]
    apply Subtype.ext
    simpa using ha₁_cube
  have hb3 : b ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one, heb]
    apply Subtype.ext
    simpa using hb₁_cube
  have ha1 : a ≠ 1 := by
    intro h
    apply ha₁_ne
    have h2 : (⟨a₁, ha₁_mem⟩ : alternatingGroup (Fin 6)) = 1 := by
      rw [← hea, h, map_one]
    simpa using congrArg Subtype.val h2
  have hb1 : b ≠ 1 := by
    intro h
    apply hb₁_ne
    have h2 : (⟨b₁, hb₁_mem⟩ : alternatingGroup (Fin 6)) = 1 := by
      rw [← heb, h, map_one]
    simpa using congrArg Subtype.val h2
  have hdisj : ∀ x : Fin 6, φ0 a x = x ∨ φ0 b x = x := by
    intro x
    rw [hφ0a, hφ0b]
    exact hdisj₁ x
  obtain ⟨P, hPmem, hPa, hPcard⟩ :=
    CFSG.HardMathSupport.Curtis.Proving.exists_elemAbelian_of_disjoint
      (a := a) (b := b) φ0 hφ0 ha3 hb3 ha1 hb1 hdisj
  refine ⟨P, hPa, by rw [hPcard]; norm_num, ?_⟩
  intro x hx
  obtain ⟨n, k, rfl⟩ := (hPmem x).1 hx
  apply hφ0
  simp only [map_mul, map_pow, map_inv, hφ0a, hφ0b, hφ0d]
  exact hmain n k

theorem gap3_two_holds : ∀ V H T U : Subgroup G, DispatchHyp V H T U →
    ¬ KBarShape V H T (fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin 6))) := by
  rintro V H T U hD ⟨X, _, φ, hs, hk, ⟨e⟩⟩
  have hR := lemmaRHyp_of_dispatchHyp hD hs hk
  obtain ⟨v, hvV, hv1⟩ := exists_mem_V_map_ne_one hD e hs hk
  have hv2 : v * v = 1 := Subtype.ext (by simpa [pow_two] using hD.hyp7.1.2 (v : G) hvV)
  obtain ⟨P, hPa, hPc, hPinv⟩ :=
    exists_elemAbelian_nine_inverted e (d := φ v) (by rw [← map_mul, hv2, map_one]) hv1
  exact hR.false_of_inverted Nat.prime_three (by norm_num) hPa hPc hvV hPinv

theorem w3Lem85TwoGap3_holds : W3Lem85TwoGap3 G :=
  ⟨gap3_one_holds, gap3_two_holds⟩

end CFSG.LocalAnalysis.WeakClosure81

end
