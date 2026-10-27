module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartFour.WreathLine
import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open Matrix
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.RankOne
open CFSG.Timmesfeld.ARS.NaturalModule

section

variable {L : Type} [Group L] {m : ℕ}

private def diag (i j : Fin m) (a : L) : Fin m → L :=
  fun k => if k = i then a else if k = j then a else 1

@[simp] private theorem diag_apply (i j : Fin m) (a : L) (k : Fin m) :
    diag i j a k = if k = i then a else if k = j then a else 1 := rfl

private theorem diag_one (i j : Fin m) : diag i j (1 : L) = 1 := by
  funext k
  by_cases hk : k = i <;> by_cases hj : k = j <;> simp [hk, hj]

private theorem diag_mul (i j : Fin m) (a b : L) : diag i j (a * b) = diag i j a * diag i j b := by
  funext k
  by_cases hk : k = i <;> by_cases hj : k = j <;> simp [hk, hj]

private def diagHom (i j : Fin m) : L →* (Fin m → L) where
  toFun := diag i j
  map_one' := diag_one i j
  map_mul' := diag_mul i j

private def X (i j : Fin m) : L →* WreathSym L m :=
  (SemidirectProduct.inl : (Fin m → L) →* WreathSym L m).comp (diagHom i j)

private def Tau (i j : Fin m) : WreathSym L m := SemidirectProduct.inr (Equiv.swap i j)

private theorem X_def (i j : Fin m) (a : L) :
    X i j a = (SemidirectProduct.inl (diag i j a) : WreathSym L m) := rfl

private theorem Tau_def (i j : Fin m) :
    Tau i j = (SemidirectProduct.inr (Equiv.swap i j) : WreathSym L m) := rfl

private theorem wreathAct_swap_diag (i j : Fin m) (a : L) :
    wreathAct L m (Equiv.swap i j) (diag i j a) = diag i j a := by
  funext k
  simp only [wreathLine_act_apply, diag_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · by_cases hj : k = j
    · subst hj
      simp [hk]
    · have h1 : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hk hj
      simp [hk, hj, h1]

private theorem tau_mul_self (i j : Fin m) : Tau i j * Tau i j = (1 : WreathSym L m) := by
  apply SemidirectProduct.ext
  · simp [Tau_def]
  · simp [Tau_def, Equiv.swap_mul_self]

private theorem left_X (i j : Fin m) (a : L) : (X i j a).left = diag i j a := by
  simp [X_def]

private theorem right_X (i j : Fin m) (a : L) : (X i j a).right = (1 : Equiv.Perm (Fin m)) := by
  simp [X_def]

private theorem left_tau (i j : Fin m) : (Tau i j).left = (1 : Fin m → L) := by
  simp [Tau_def]

private theorem right_tau (i j : Fin m) :
    (Tau i j : WreathSym L m).right = (Equiv.swap i j : Equiv.Perm (Fin m)) := by
  simp [Tau_def]

private theorem X_mul_tau (i j : Fin m) (a : L) : X i j a * Tau i j = Tau i j * X i j a := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, right_X, right_tau,
      left_tau, left_X, wreathAct_swap_diag]
    simp
  · simp [right_X, right_tau]

private theorem X_mul_tau_left (i j : Fin m) (a : L) : (X i j a * Tau i j).left = diag i j a := by
  rw [SemidirectProduct.mul_left, left_X, right_X, left_tau]
  simp

private abbrev C2 := Multiplicative (ZMod 2)

private theorem C2_cases (ε : C2) : ε = 1 ∨ ε = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert ε
  decide

private def c2hom (i j : Fin m) : C2 →* WreathSym L m where
  toFun ε := if ε = 1 then 1 else Tau i j
  map_one' := by simp
  map_mul' := by
    intro ε δ
    rcases C2_cases ε with rfl | rfl <;> rcases C2_cases δ with rfl | rfl
    · simp
    · simp
    · simp
    · have h : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 : C2) = 1 := by
        decide
      simp [h, tau_mul_self]

private theorem c2hom_comm_X (i j : Fin m) (ε : C2) (a : L) :
    c2hom i j ε * X i j a = X i j a * c2hom i j ε := by
  rcases C2_cases ε with rfl | rfl
  · simp
  · rw [show c2hom i j (Multiplicative.ofAdd (1 : ZMod 2)) = Tau i j by simp [c2hom]]
    exact (X_mul_tau i j a).symm

private def Phi (i j : Fin m) : L × C2 →* WreathSym L m where
  toFun p := X i j p.1 * c2hom i j p.2
  map_one' := by simp
  map_mul' := by
    intro p q
    simp only [Prod.mul_def, map_mul]
    calc X i j p.1 * X i j q.1 * (c2hom i j p.2 * c2hom i j q.2)
        = X i j p.1 * (X i j q.1 * c2hom i j p.2) * c2hom i j q.2 := by group
      _ = X i j p.1 * (c2hom i j p.2 * X i j q.1) * c2hom i j q.2 := by
            rw [c2hom_comm_X]
      _ = X i j p.1 * c2hom i j p.2 * (X i j q.1 * c2hom i j q.2) := by group

private theorem phi_left (i j : Fin m) (p : L × C2) : (Phi i j p).left = diag i j p.1 := by
  rcases p with ⟨a, ε⟩
  rcases C2_cases ε with rfl | rfl
  · simp [Phi, c2hom, X_def]
  · change (X i j a * Tau i j).left = diag i j a
    rw [X_mul_tau_left]

end

section

open CFSG.LocalAnalysis.WeakClosure81

variable {L : Type} [Group L] {m : ℕ} {i j : Fin m}

private def Ksub : Subgroup (WreathSym L m) := (Phi i j).range

private def XK : L →* ↥(Ksub (i := i) (j := j) (L := L) (m := m)) where
  toFun a := ⟨X i j a, ⟨(a, 1), by simp [Phi]⟩⟩
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    apply SemidirectProduct.ext <;> simp [map_mul]

private def TauK : ↥(Ksub (i := i) (j := j) (L := L) (m := m)) :=
  ⟨Tau i j, ⟨(1, Multiplicative.ofAdd (1 : ZMod 2)), by simp [Phi, c2hom]⟩⟩

private def Tilde (b : L) : ↥(Ksub (i := i) (j := j) (L := L) (m := m)) :=
  ⟨X i j b * Tau i j, ⟨(b, Multiplicative.ofAdd (1 : ZMod 2)), by simp [Phi, c2hom]⟩⟩

private def rho : ↥(Ksub (i := i) (j := j) (L := L) (m := m)) →* L where
  toFun w := ((w : WreathSym L m).left) i
  map_one' := by simp
  map_mul' := by
    intro w w'
    obtain ⟨p, hp⟩ := w.2
    obtain ⟨q, hq⟩ := w'.2
    change (((w : WreathSym L m) * (w' : WreathSym L m)).left) i =
      (((w : WreathSym L m).left) i) * (((w' : WreathSym L m).left) i)
    rw [← hp, ← hq, ← map_mul, phi_left, phi_left, phi_left]
    simp [diag]

private theorem rho_XK (a : L) : rho (i := i) (j := j) (XK (i := i) (j := j) a) = a := by
  change (X i j a).left i = a
  rw [left_X]
  simp [diag]

private theorem rho_surjective : Function.Surjective (rho (i := i) (j := j) (L := L) (m := m)) :=
  fun a => ⟨XK a, rho_XK a⟩

private theorem rho_ker_le_zpowers :
    (rho (i := i) (j := j) (L := L) (m := m)).ker ≤
      Subgroup.zpowers (TauK (i := i) (j := j) (L := L) (m := m)) := by
  intro w hw
  obtain ⟨⟨a, ε⟩, hp⟩ := w.2
  rw [MonoidHom.mem_ker] at hw
  have hleft : ((w : WreathSym L m).left) i = 1 := by
    simpa [rho] using hw
  have hleft' : (Phi i j (a, ε)).left i = 1 := by
    simpa [hp] using hleft
  have hp1 : a = 1 := by
    rw [phi_left] at hleft'
    simpa [diag] using hleft'
  have hw_eq : (w : WreathSym L m) = c2hom i j ε := by
    rw [← hp]
    simp [Phi, hp1]
  have hmem : (w : WreathSym L m) ∈ Subgroup.zpowers (Tau i j) := by
    rcases C2_cases ε with h | h
    · rw [hw_eq, h]
      simp [c2hom]
    · rw [hw_eq, h]
      exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hn⟩

private theorem TauK_central :
    TauK (i := i) (j := j) (L := L) (m := m) ∈
      Subgroup.center ↥(Ksub (i := i) (j := j) (L := L) (m := m)) := by
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  obtain ⟨⟨a, ε⟩, hp⟩ := w.2
  have hw : w = ⟨Phi i j (a, ε), ⟨(a, ε), rfl⟩⟩ := (Subtype.ext hp).symm
  rw [hw]
  simp only [Subgroup.coe_mul]
  change (Phi i j (a, ε) : WreathSym L m) * Tau i j =
    Tau i j * Phi i j (a, ε)
  rcases C2_cases ε with h | h
  · subst h
    simp [Phi, c2hom, X_mul_tau]
  · subst h
    rw [show Phi i j (a, Multiplicative.ofAdd (1 : ZMod 2)) = X i j a * Tau i j by
      simp [Phi, c2hom]]
    have h1 : (X i j a * Tau i j) * Tau i j = X i j a := by
      rw [mul_assoc, tau_mul_self, mul_one]
    have h2 : Tau i j * (X i j a * Tau i j) = X i j a := by
      calc Tau i j * (X i j a * Tau i j)
          = (Tau i j * X i j a) * Tau i j := by group
        _ = (X i j a * Tau i j) * Tau i j := by rw [← X_mul_tau i j a]
        _ = X i j a := h1
    rw [h1, h2]

end

section

open CFSG.LocalAnalysis.WeakClosure81

variable {L : Type} [Group L] {m : ℕ} {i j : Fin m}

private theorem TauK_mul_self : TauK (i := i) (j := j) (L := L) (m := m) *
    TauK (i := i) (j := j) (L := L) (m := m) =
    (1 : ↥(Ksub (i := i) (j := j) (L := L) (m := m))) := by
  apply Subtype.ext
  exact tau_mul_self i j

private theorem XK_comm_TauK (a : L) :
    XK (i := i) (j := j) a * TauK (i := i) (j := j) =
      TauK (i := i) (j := j) * XK (i := i) (j := j) a := by
  apply Subtype.ext
  exact X_mul_tau i j a

private theorem XK_inv {a : L} (ha2 : a * a = 1) :
    (XK (i := i) (j := j) a)⁻¹ = XK (i := i) (j := j) a := by
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, ha2, map_one])

private theorem TauK_inv : (TauK (i := i) (j := j) (L := L) (m := m))⁻¹ =
    TauK (i := i) (j := j) (L := L) (m := m) :=
  inv_eq_of_mul_eq_one_right TauK_mul_self

private theorem Tilde_eq_XK_mul_TauK (b : L) :
    Tilde (i := i) (j := j) b = XK (i := i) (j := j) b * TauK (i := i) (j := j) := by
  apply Subtype.ext
  rfl

private theorem conj_prod_eq {a b : L} (ha2 : a * a = 1) (hb2 : b * b = 1) :
    XK (i := i) (j := j) a * Tilde (i := i) (j := j) b *
        (XK (i := i) (j := j) a)⁻¹ * (Tilde (i := i) (j := j) b)⁻¹ =
      XK (i := i) (j := j) (a * b * a * b) := by
  rw [Tilde_eq_XK_mul_TauK, XK_inv ha2, _root_.mul_inv_rev, TauK_inv, XK_inv hb2]
  calc XK (i := i) (j := j) a * (XK (i := i) (j := j) b * TauK) *
        XK (i := i) (j := j) a * (TauK * XK (i := i) (j := j) b)
      = XK (i := i) (j := j) a * XK (i := i) (j := j) b *
          (TauK * XK (i := i) (j := j) a) * TauK *
          XK (i := i) (j := j) b := by group
    _ = XK (i := i) (j := j) a * XK (i := i) (j := j) b *
          (XK (i := i) (j := j) a * TauK) * TauK *
          XK (i := i) (j := j) b := by
          rw [← XK_comm_TauK a]
    _ = (XK (i := i) (j := j) a * XK (i := i) (j := j) b *
          XK (i := i) (j := j) a) * (TauK * TauK) *
          XK (i := i) (j := j) b := by group
    _ = (XK (i := i) (j := j) a * XK (i := i) (j := j) b *
          XK (i := i) (j := j) a) * XK (i := i) (j := j) b := by
          rw [TauK_mul_self, mul_one]
    _ = XK (i := i) (j := j) (a * b * a * b) := by
          rw [← map_mul, ← map_mul, ← map_mul]

private theorem normalClosure_Tilde_eq_top [IsSimpleGroup L] {a b : L} (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hc : a * b * a * b ≠ 1) :
    Subgroup.normalClosure
      ({Tilde (i := i) (j := j) b} :
        Set ↥(Ksub (i := i) (j := j) (L := L) (m := m))) = ⊤ := by
  let N : Subgroup ↥(Ksub (i := i) (j := j) (L := L) (m := m)) :=
    Subgroup.normalClosure ({Tilde (i := i) (j := j) b} : Set _)
  have hNnormal : N.Normal := Subgroup.normalClosure_normal
  have htN : Tilde (i := i) (j := j) b ∈ N := Subgroup.subset_normalClosure rfl
  let H : Subgroup L := N.comap (XK (i := i) (j := j))
  have hHnormal : H.Normal := Subgroup.Normal.comap hNnormal _
  have hcH : a * b * a * b ∈ H := by
    have hconj : XK (i := i) (j := j) a * Tilde (i := i) (j := j) b *
        (XK (i := i) (j := j) a)⁻¹ ∈ N :=
      hNnormal.conj_mem _ htN _
    have hprod : XK (i := i) (j := j) a * Tilde (i := i) (j := j) b *
        (XK (i := i) (j := j) a)⁻¹ * (Tilde (i := i) (j := j) b)⁻¹ ∈ N :=
      N.mul_mem hconj (N.inv_mem htN)
    rw [conj_prod_eq ha2 hb2] at hprod
    exact Subgroup.mem_comap.mpr hprod
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hmem : a * b * a * b ∈ (⊥ : Subgroup L) := hbot ▸ hcH
    exact hc (Subgroup.mem_bot.mp hmem)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact absurd h hHne
  · rw [eq_top_iff]
    intro w _
    have hxN : ∀ c : L, XK (i := i) (j := j) c ∈ N := by
      intro c
      have hcH' : c ∈ H := by rw [h]; exact Subgroup.mem_top c
      exact Subgroup.mem_comap.mp hcH'
    have hτN : TauK (i := i) (j := j) ∈ N := by
      have hxb : XK (i := i) (j := j) b ∈ N := hxN b
      have hcalc : (XK (i := i) (j := j) b)⁻¹ * Tilde (i := i) (j := j) b =
          TauK (i := i) (j := j) := by
        rw [Tilde_eq_XK_mul_TauK]
        group
      have hmem := N.mul_mem (N.inv_mem hxb) htN
      rwa [hcalc] at hmem
    obtain ⟨⟨c, ε⟩, hp⟩ := w.2
    have hw : w = ⟨Phi i j (c, ε), ⟨(c, ε), rfl⟩⟩ := (Subtype.ext hp).symm
    rw [hw]
    rcases C2_cases ε with hε | hε
    · have hw' : (⟨Phi i j (c, ε), ⟨(c, ε), rfl⟩⟩ :
          ↥(Ksub (i := i) (j := j) (L := L) (m := m))) = XK (i := i) (j := j) c := by
        apply Subtype.ext
        subst hε
        simp [Phi, c2hom, XK]
      rw [hw']
      exact hxN c
    · have hw' : (⟨Phi i j (c, ε), ⟨(c, ε), rfl⟩⟩ :
          ↥(Ksub (i := i) (j := j) (L := L) (m := m))) =
          XK (i := i) (j := j) c * TauK (i := i) (j := j) := by
        apply Subtype.ext
        subst hε
        simp [Phi, c2hom, XK, TauK]
      rw [hw']
      exact N.mul_mem (hxN c) hτN

end

section

open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.CoreRadical
open CFSG.OddTranspositions.PartFour

variable {L : Type} [Group L] {m : ℕ} {i j : Fin m}

private theorem Tilde_coe_eq_wreathLine_sigma (hij : i ≠ j) {b : L} (hb2 : b * b = 1) :
    ((Tilde (i := i) (j := j) (L := L) (m := m) b :
        ↥(Ksub (i := i) (j := j) (L := L) (m := m))) : WreathSym L m) =
      wreathLine_sigma i j b := by
  apply SemidirectProduct.ext
  · funext p
    change (X i j b * Tau i j).left p = _
    rw [X_mul_tau_left, diag_apply]
    by_cases hpi : p = i
    · subst hpi
      rw [if_pos rfl, wreathLine_sigma_left_self hij b]
    · by_cases hpj : p = j
      · subst hpj
        rw [if_neg hpi, if_pos rfl, wreathLine_sigma_left_right hij b]
        exact (inv_eq_of_mul_eq_one_right hb2).symm
      · rw [if_neg hpi, if_neg hpj, wreathLine_sigma_left_ne hij b hpi hpj]
  · change (X i j b * Tau i j).right = _
    rw [SemidirectProduct.mul_right, right_X, right_tau, wreathLine_sigma_right]
    simp

private theorem isConj_tau_Tilde (hij : i ≠ j) {b : L} (hb2 : b * b = 1) :
    IsConj (Tau i j) ((Tilde (i := i) (j := j) (L := L) (m := m) b :
        ↥(Ksub (i := i) (j := j) (L := L) (m := m))) : WreathSym L m) := by
  rw [Tilde_coe_eq_wreathLine_sigma hij hb2]
  simpa [Tau] using
    wreathLine_sigma_isConj (L := L) (a := i) (b := j) (k := i) (l := j) hij hij b

end

section

open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.CoreRadical
open CFSG.Timmesfeld.RankOne
open CFSG.Timmesfeld.ARS.NaturalModule

private theorem radicalOutcome_Tilde {F : Type} [Field F] [Finite F] [CharP F 2]
    [IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F)] {n m : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) {i j : Fin m}
    {a b : Matrix.SpecialLinearGroup (Fin 2) F} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hc : a * b * a * b ≠ 1) :
    RadicalOutcome (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m)
      ((Tilde (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) b :
        ↥(Ksub (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m))) :
        WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) := by
  let K := Ksub (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)
  let t : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m :=
    (Tilde (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) b : ↥K)
  have ht : t ∈ K :=
    (Tilde (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) b).2
  have hncl : Subgroup.normalClosure ({⟨t, ht⟩} : Set ↥K) = ⊤ := by
    have h := normalClosure_Tilde_eq_top (L := Matrix.SpecialLinearGroup (Fin 2) F)
      (m := m) (i := i) (j := j) (a := a) (b := b) ha2 hb2 hc
    simpa [K, t] using h
  have hker : (rho (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F)
      (m := m)).ker ≤ Subgroup.center ↥K := by
    refine (rho_ker_le_zpowers (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)
      (i := i) (j := j)).trans ?_
    exact Subgroup.zpowers_le.mpr
      (TauK_central (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) (i := i) (j := j))
  have hker2 : Nat.card ↥((rho (i := i) (j := j)
      (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)).ker) ∣ 2 := by
    have hcard' : Nat.card ↥((rho (i := i) (j := j)
        (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)).ker) ∣
        Nat.card ↥(Subgroup.zpowers (TauK (L := Matrix.SpecialLinearGroup (Fin 2) F)
          (m := m) (i := i) (j := j))) :=
      Subgroup.card_dvd_of_le
        (rho_ker_le_zpowers (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)
          (i := i) (j := j))
    have horder : Nat.card ↥(Subgroup.zpowers (TauK
        (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) (i := i) (j := j))) =
        orderOf (TauK (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)
          (i := i) (j := j)) :=
      Nat.card_zpowers _
    have hdvd : orderOf (TauK (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)
        (i := i) (j := j)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by
        simpa [pow_two] using TauK_mul_self (L := Matrix.SpecialLinearGroup (Fin 2) F)
          (m := m) (i := i) (j := j))
    rw [horder] at hcard'
    exact hcard'.trans hdvd
  exact RadicalOutcome.of_surjective_sl2 (L := K) (t := t) ht hncl hcard hn
    (rho (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m))
    (rho_surjective (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) (i := i) (j := j))
    hker hker2

end

section

variable {Y : Type} [Group Y] {t : Y}

theorem radicalOutcome_of_isWreathTransposition (hZ : Subgroup.center Y = ⊥) {n m : ℕ}
    (h : IsWreathTransposition Y n m t) : RadicalOutcome Y t := by
  obtain ⟨hn, F, hF, hFin, hcard, e, i, j, hij, hconj⟩ := h
  let : Field F := hF
  let : Finite F := hFin
  have : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.E1.RootLift.isSimpleGroup_SL2 h4
  let e' : (Y ⧸ Subgroup.center Y) ≃* WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m := e
  let b : Matrix.SpecialLinearGroup (Fin 2) F := lowerElt F 1
  let a : Matrix.SpecialLinearGroup (Fin 2) F := upperElt F 1
  have ha2 : a * a = 1 := by
    change upperElt F 1 * upperElt F 1 = 1
    exact upperElt_mul_self (K := F) 1
  have hb2 : b * b = 1 := by
    change lowerElt F 1 * lowerElt F 1 = 1
    rw [lowerElt_mul, CharTwo.add_self_eq_zero, lowerElt_zero]
  have hc : a * b * a * b ≠ 1 := by
    change upperElt F 1 * lowerElt F 1 * upperElt F 1 * lowerElt F 1 ≠ 1
    rw [upperElt_one_mul_lowerElt_one_mul_upperElt_one]
    intro h1
    have h11 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((g : Matrix (Fin 2) (Fin 2) F) 1 1)) h1
    simp [coe_weylElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] at h11
  have hTilde : RadicalOutcome (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m)
      ((Tilde (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) b :
        ↥(Ksub (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m))) :
        WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) :=
    radicalOutcome_Tilde hcard hn ha2 hb2 hc
  have hConj : IsConj (Tau (i := i) (j := j)
      (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m))
      ((Tilde (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m) b :
        ↥(Ksub (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m))) :
        WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) :=
    isConj_tau_Tilde hij hb2
  have hτ : RadicalOutcome (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m)
      (Tau (i := i) (j := j) (L := Matrix.SpecialLinearGroup (Fin 2) F) (m := m)) :=
    RadicalOutcome.of_isConj hConj hTilde
  have hW : RadicalOutcome _ (e' (QuotientGroup.mk t)) :=
    RadicalOutcome.of_isConj hconj (by simpa [Tau] using hτ)
  have hquot : RadicalOutcome (Y ⧸ Subgroup.center Y) (QuotientGroup.mk t) :=
    RadicalOutcome.of_mulEquiv e' hW
  exact RadicalOutcome.of_center_eq_bot hZ hquot

end

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
