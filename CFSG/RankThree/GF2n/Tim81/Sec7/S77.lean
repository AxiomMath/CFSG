module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic
import CFSG.GroupTheory.CoprimeCovering
import CFSG.RankThree.GF2n.Tim81.Recog.GR
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport
import CFSG.Timmesfeld.Bridge.RootStructR2Incidence
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem Sec7Hyp.exists_l2Datum_of_centralizes (hS : Sec7Hyp M V n f)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hLP : UnitaryLinePair)
    {A₁ A₂ B : Subgroup G} (hA₁ : A₁ ∈ gammaAt V) (hA₂ : A₂ ∈ gammaAt V)
    (hA : IsL2Gen A₁ A₂) (hB : B ∈ omegaSet V) (hBΓ : B ∉ gammaAt V)
    (hBc : B ≤ cenOf (A₁ ⊔ A₂)) :
    ∃ (A₁' A₂' : Subgroup G) (h g : G), L2Datum M V A₁' A₂' h ∧
      conjSubgroup g V ∉ gammaAt V ∧ conjSubgroup g V ≤ cenOf (A₁' ⊔ A₂') := by
  obtain ⟨b, -, hb⟩ := hB
  have hA17 := hS.isSUImage_gammaL h76U
  have hSUperp := (hLP G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have h := hS.four_le; omega) hS.two_le
    hA17 A₁ hA₁ A₂ hA₂ hA).2.1 (by have h := hS.four_le; omega)
  obtain ⟨C, hCΓ, hCc⟩ := IsSUImage.nonempty hSUperp
  obtain ⟨k, -, hk⟩ := gammaAt_subset_omegaSet V hCΓ
  have hkY : k ∈ gammaStab V :=
    (hS.toSec6Hyp.mem_gammaStab_iff h75).mpr (hk ▸ hCΓ)
  have hCc' : conjSubgroup k V ≤ cenOf (A₁ ⊔ A₂) := hk ▸ hCc
  have hkY' : k⁻¹ ∈ gammaStab V := (gammaStab V).inv_mem hkY
  have hA₁'Γ : conjSubgroup k⁻¹ A₁ ∈ gammaAt V :=
    CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet hkY' hA₁
  have hA₂'Γ : conjSubgroup k⁻¹ A₂ ∈ gammaAt V :=
    CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet hkY' hA₂
  have hpairC : A₁ ⊔ A₂ ≤ cenOf (conjSubgroup k V) := Subgroup.le_centralizer_iff.mpr hCc'
  have hcen : conjSubgroup k⁻¹ (cenOf (conjSubgroup k V)) = cenOf V := by
    rw [← centralizer_conjSubgroup_eq, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  have hA₁'c : conjSubgroup k⁻¹ A₁ ≤ cenOf V := by
    calc conjSubgroup k⁻¹ A₁ ≤ conjSubgroup k⁻¹ (cenOf (conjSubgroup k V)) :=
          conjSubgroup_mono ((le_sup_left : A₁ ≤ A₁ ⊔ A₂).trans hpairC)
      _ = cenOf V := hcen
  have hA₂'c : conjSubgroup k⁻¹ A₂ ≤ cenOf V := by
    calc conjSubgroup k⁻¹ A₂ ≤ conjSubgroup k⁻¹ (cenOf (conjSubgroup k V)) :=
          conjSubgroup_mono ((le_sup_right : A₂ ≤ A₁ ⊔ A₂).trans hpairC)
      _ = cenOf V := hcen
  have hA₁'ne : conjSubgroup k⁻¹ A₁ ≠ V := by
    intro hEq
    have hle : conjSubgroup k⁻¹ A₂ ≤ cenOf (conjSubgroup k⁻¹ A₁) := hEq ▸ hA₂'c
    have hbot : ⁅conjSubgroup k⁻¹ A₂, conjSubgroup k⁻¹ A₁⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm] at hbot
    exact (hA.conj k⁻¹).commutator_ne_bot hbot
  have hA₂'ne : conjSubgroup k⁻¹ A₂ ≠ V := by
    intro hEq
    have hle : conjSubgroup k⁻¹ A₁ ≤ cenOf (conjSubgroup k⁻¹ A₂) := hEq ▸ hA₁'c
    have hbot : ⁅conjSubgroup k⁻¹ A₁, conjSubgroup k⁻¹ A₂⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    exact (hA.conj k⁻¹).commutator_ne_bot hbot
  have hcommV₁ : ⁅V, conjSubgroup k⁻¹ A₁⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hA₁'c)
  have hcommV₂ : ⁅V, conjSubgroup k⁻¹ A₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hA₂'c)
  have hA₁'sig : conjSubgroup k⁻¹ A₁ ∈ sigmaSet M V :=
    hS.toSec6Hyp.mem_sigmaSet_of_mem_gammaAt hA₁'Γ hA₁'ne hcommV₁
  have hA₂'sig : conjSubgroup k⁻¹ A₂ ∈ sigmaSet M V :=
    hS.toSec6Hyp.mem_sigmaSet_of_mem_gammaAt hA₂'Γ hA₂'ne hcommV₂
  obtain ⟨h, hD⟩ := exists_l2Datum hA₁'sig hA₂'sig (hA.conj k⁻¹)
  have hCg : conjSubgroup (k⁻¹ * b) V = conjSubgroup k⁻¹ B := by
    rw [hb]
    exact (conjSubgroup_conjSubgroup k⁻¹ b V).symm
  have hcentral : conjSubgroup (k⁻¹ * b) V ≤
      cenOf (conjSubgroup k⁻¹ A₁ ⊔ conjSubgroup k⁻¹ A₂) := by
    calc conjSubgroup (k⁻¹ * b) V = conjSubgroup k⁻¹ B := hCg
      _ ≤ conjSubgroup k⁻¹ (cenOf (A₁ ⊔ A₂)) := conjSubgroup_mono hBc
      _ = cenOf (conjSubgroup k⁻¹ (A₁ ⊔ A₂)) :=
            (centralizer_conjSubgroup_eq k⁻¹ (A₁ ⊔ A₂)).symm
      _ = cenOf (conjSubgroup k⁻¹ A₁ ⊔ conjSubgroup k⁻¹ A₂) := by rw [conjSubgroup_sup]
  have hnot : conjSubgroup (k⁻¹ * b) V ∉ gammaAt V := by
    intro hmem
    have h1 : conjSubgroup k (conjSubgroup (k⁻¹ * b) V) ∈ gammaAt V :=
      CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet hkY hmem
    rw [conjSubgroup_conjSubgroup, show k * (k⁻¹ * b) = b by group, ← hb] at h1
    exact hBΓ h1
  exact ⟨conjSubgroup k⁻¹ A₁, conjSubgroup k⁻¹ A₂, h, k⁻¹ * b, hD, hnot, hcentral⟩

theorem Sec7Hyp.commutator_mem_gammaStab (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    (hSR : UnitarySylowRoots) {A : Subgroup G} (hA : A ∈ gammaAt V) {g : G}
    (hAc : A ≤ cenOf (conjSubgroup g V)) {x a : G} (hx : x ∈ conjSubgroup g (Pc M V))
    (ha : a ∈ A) : ⁅x, a⁆ ∈ gammaStab V ⊓ conjSubgroup g (Pc M V) := by
  have hVc : V ≤ cenOf (conjSubgroup g⁻¹ A) := by
    calc V = conjSubgroup g⁻¹ (conjSubgroup g V) := by
          rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      _ ≤ conjSubgroup g⁻¹ (cenOf A) :=
          conjSubgroup_mono (Subgroup.le_centralizer_iff.mp hAc)
      _ = cenOf (conjSubgroup g⁻¹ A) := (centralizer_conjSubgroup_eq g⁻¹ A).symm
  have hTE : ⁅V, conjSubgroup g⁻¹ A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc
  have hE : conjSubgroup g⁻¹ A ∈ omegaSet V :=
    Tim79a.conjSubgroup_mem_omegaOf_of_mem (gammaAt_subset_omegaSet V hA)
      (Subgroup.mem_top g⁻¹)
  obtain ⟨S, hES, hVS⟩ :=
    hS.exists_sylowRoots_of_commute h74 h75 h76U hRTS hE hS.toSec6Hyp.mem_gammaAt_self hTE
  have hA17 := hS.isSUImage_gammaL h76U
  have hSyl := hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have h := hS.four_le; omega) hS.two_le hA17 S
  have hSylComm : ∀ u ∈ sylowRoots (gammaL V) (gammaAt V) S,
      ∀ v ∈ sylowRoots (gammaL V) (gammaAt V) S, u * v = v * u := hSyl.1
  have hPnorm : Pc M V ≤
      Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S : Set G) :=
    hS.Pc_le_normalizer_sylowRoots h74 h76U hSR hVS
  have hPgNorm : conjSubgroup g (Pc M V) ≤
      Subgroup.normalizer (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) : Set G) := by
    rw [normalizer_conjSubgroup]
    exact conjSubgroup_mono hPnorm
  have hW'ab : ∀ u ∈ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S),
      ∀ v ∈ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S), u * v = v * u := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    exact (map_mul (MulAut.conj g).toMonoidHom u' v').symm.trans
      ((congrArg (MulAut.conj g) (hSylComm u' hu' v' hv')).trans
        (map_mul (MulAut.conj g).toMonoidHom v' u'))
  have hAW' : A ≤ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) := by
    have h := conjSubgroup_mono (g := g) hES
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
  have haW' : a ∈ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) := hAW' ha
  have hxN : x ∈ Subgroup.normalizer
      (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) : Set G) := hPgNorm hx
  have hmemW' : ⁅x, a⁆ ∈ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) := by
    have hxax : x * a * x⁻¹ ∈ conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) :=
      (Subgroup.mem_normalizer_iff.mp hxN a).mp haW'
    rw [commutatorElement_def]
    exact (conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S)).mul_mem hxax
      ((conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S)).inv_mem haW')
  have hW'C : conjSubgroup g (sylowRoots (gammaL V) (gammaAt V) S) ≤ cenOf A := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hW'ab u hu v (hAW' hv)).symm
  have hcommY : ⁅x, a⁆ ∈ gammaStab V :=
    hS.toSec6Hyp.normalizer_le_gammaStab h75 hA
      (Subgroup.centralizer_le_normalizer (A : Set G) (hW'C hmemW'))
  have haN : a ∈ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) :=
    hS.toSec6Hyp.sec5.mem_normalizer_conj_Pc g (hAc ha)
  have hcommP : ⁅a, x⁆ ∈ conjSubgroup g (Pc M V) := by
    rw [commutatorElement_def]
    exact (conjSubgroup g (Pc M V)).mul_mem
      ((Subgroup.mem_normalizer_iff.mp haN x).mp hx)
      ((conjSubgroup g (Pc M V)).inv_mem hx)
  have hcommP' : ⁅x, a⁆ ∈ conjSubgroup g (Pc M V) := by
    have h := (conjSubgroup g (Pc M V)).inv_mem hcommP
    rwa [commutatorElement_inv] at h
  exact ⟨hcommY, hcommP'⟩

private theorem normal_inf_gammaStab_conj_Pc (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    {A : Subgroup G} (hA : A ∈ gammaAt V) {g : G}
    (hAc : A ≤ cenOf (conjSubgroup g V)) :
    ((gammaStab V ⊓ conjSubgroup g (Pc M V)).subgroupOf
      (conjSubgroup g (Pc M V))).Normal := by
  have hB_Y : conjSubgroup g V ≤ gammaStab V :=
    (Subgroup.le_centralizer_iff.mp hAc).trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans
        (hS.toSec6Hyp.normalizer_le_gammaStab h75 hA))
  have hXX : ⁅conjSubgroup g (Pc M V), conjSubgroup g (Pc M V)⁆ = conjSubgroup g V := by
    have h := (hS.toSec6Hyp.sec5.conj g).commutator_Pc_eq_V (hS.toSec6Hyp.conj g).ne
    rwa [Pc_conjSubgroup] at h
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rintro ⟨hdY, hdX⟩
    have hc : ⁅x, d⁆ ∈ conjSubgroup g V :=
      hXX ▸ Subgroup.commutator_mem_commutator hx hdX
    refine ⟨?_, (conjSubgroup g (Pc M V)).mul_mem
      ((conjSubgroup g (Pc M V)).mul_mem hx hdX)
      ((conjSubgroup g (Pc M V)).inv_mem hx)⟩
    have heq : x * d * x⁻¹ = ⁅x, d⁆ * d := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (gammaStab V).mul_mem (hB_Y hc) hdY
  · rintro ⟨hdY, hdX⟩
    have hdX' : d ∈ conjSubgroup g (Pc M V) := by
      rw [show d = x⁻¹ * (x * d * x⁻¹) * x by group]
      exact (conjSubgroup g (Pc M V)).mul_mem
        ((conjSubgroup g (Pc M V)).mul_mem
          ((conjSubgroup g (Pc M V)).inv_mem hx) hdX) hx
    have hc : ⁅x, d⁆ ∈ conjSubgroup g V :=
      hXX ▸ Subgroup.commutator_mem_commutator hx hdX'
    have heq : d = ⁅x, d⁆⁻¹ * (x * d * x⁻¹) := by
      rw [commutatorElement_def]
      group
    exact ⟨by
      rw [heq]
      exact (gammaStab V).mul_mem ((gammaStab V).inv_mem (hB_Y hc)) hdY, hdX'⟩

private theorem le_normalizer_inf_gammaStab_conj_Pc (hS : Sec7Hyp M V n f)
    (h75 : Sec7.Stmt75 V) {A : Subgroup G} (hA : A ∈ gammaAt V) {g : G}
    (hAc : A ≤ cenOf (conjSubgroup g V)) :
    A ≤ Subgroup.normalizer
      ((gammaStab V ⊓ conjSubgroup g (Pc M V) : Subgroup G) : Set G) := by
  intro a ha
  have haY : a ∈ gammaStab V :=
    hS.toSec6Hyp.normalizer_le_gammaStab h75 hA (Subgroup.le_normalizer ha)
  have haN : a ∈ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) :=
    hS.toSec6Hyp.sec5.mem_normalizer_conj_Pc g (hAc ha)
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rintro ⟨hdY, hdX⟩
    exact ⟨(gammaStab V).mul_mem ((gammaStab V).mul_mem haY hdY) ((gammaStab V).inv_mem haY),
      (Subgroup.mem_normalizer_iff.mp haN d).mp hdX⟩
  · rintro ⟨hdY, hdX⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp haN d).mpr hdX⟩
    rw [show d = a⁻¹ * (a * d * a⁻¹) * a by group]
    exact (gammaStab V).mul_mem ((gammaStab V).mul_mem ((gammaStab V).inv_mem haY) hdY) haY

private theorem commutator_mem_of_mem_sup {D : Subgroup G} {x h : G} {A₁ A₂ : Subgroup G}
    (hA₁N : A₁ ≤ Subgroup.normalizer (D : Set G))
    (hA₂N : A₂ ≤ Subgroup.normalizer (D : Set G))
    (hA₁c : ∀ a ∈ A₁, ⁅x, a⁆ ∈ D) (hA₂c : ∀ a ∈ A₂, ⁅x, a⁆ ∈ D)
    (hmem : h ∈ A₁ ⊔ A₂) : ∀ r ∈ Subgroup.zpowers h, ⁅x, r⁆ ∈ D := by
  have hsup : A₁ ⊔ A₂ ≤ CFSG.GroupTheory.commMemSubgroup
      (Subgroup.normalizer (D : Set G)) D le_rfl x := by
    refine sup_le (fun a ha => ⟨hA₁N ha, ?_⟩) (fun a ha => ⟨hA₂N ha, ?_⟩)
    · simpa only [commutatorElement_inv] using D.inv_mem (hA₁c a ha)
    · simpa only [commutatorElement_inv] using D.inv_mem (hA₂c a ha)
  intro r hr
  simpa only [commutatorElement_inv] using
    D.inv_mem (Subgroup.zpowers_le.mpr (hsup hmem) hr).2

theorem Sec7Hyp.conj_Pc_le_gammaStab (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    (hSR : UnitarySylowRoots) (h73 : Sec7.Stmt73 M V n f) {A₁ A₂ : Subgroup G}
    {h g : G} (hD : L2Datum M V A₁ A₂ h)
    (hBc : conjSubgroup g V ≤ cenOf (A₁ ⊔ A₂)) :
    conjSubgroup g (Pc M V) ≤ gammaStab V := by
  let X : Subgroup G := conjSubgroup g (Pc M V)
  let D : Subgroup G := gammaStab V ⊓ X
  have hpairC : A₁ ⊔ A₂ ≤ cenOf (conjSubgroup g V) := Subgroup.le_centralizer_iff.mpr hBc
  have hA₁c : A₁ ≤ cenOf (conjSubgroup g V) := le_sup_left.trans hpairC
  have hA₂c : A₂ ≤ cenOf (conjSubgroup g V) := le_sup_right.trans hpairC
  have hA₁Γ : A₁ ∈ gammaAt V := hS.toSec6Hyp.sigmaSet_subset_gammaAt hD.memA
  have hA₂Γ : A₂ ∈ gammaAt V := hS.toSec6Hyp.sigmaSet_subset_gammaAt hD.memB
  have hA₁ND : A₁ ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using le_normalizer_inf_gammaStab_conj_Pc hS h75 hA₁Γ hA₁c
  have hA₂ND : A₂ ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using le_normalizer_inf_gammaStab_conj_Pc hS h75 hA₂Γ hA₂c
  have hXD : (D.subgroupOf X).Normal := by
    simpa [D, X] using normal_inf_gammaStab_conj_Pc hS h75 hA₁Γ hA₁c
  have hhND : h ∈ Subgroup.normalizer (D : Set G) := (sup_le hA₁ND hA₂ND) hD.mem
  have hRN : Subgroup.zpowers h ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.mpr hhND
  have hD2 : IsPGroup 2 D :=
    (isPGroup_conj_Pc M V g).to_le (by simpa [D, X] using inf_le_right)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥D := hD2.isNilpotent
  have hsolv : Group.IsSolvable ↥D := inferInstance
  have hodd : Odd (Nat.card (Subgroup.zpowers h)) := by
    rw [Nat.card_zpowers, hD.order, hS.card_V]
    have hpow : Even (2 ^ f) := by
      obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by have := hS.one_le; omega⟩
      rw [hk, pow_succ']
      exact even_two.mul_right _
    exact hpow.add_one
  have hcop : Nat.Coprime (Nat.card D) (Nat.card (Subgroup.zpowers h)) := by
    obtain ⟨k, hk⟩ := hD2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  intro x hx
  have hxr : ∀ r ∈ Subgroup.zpowers h, ⁅x, r⁆ ∈ D :=
    commutator_mem_of_mem_sup hA₁ND hA₂ND
      (fun a ha => hS.commutator_mem_gammaStab h74 h75 h76U hRTS hSR hA₁Γ hA₁c hx ha)
      (fun a ha => hS.commutator_mem_gammaStab h74 h75 h76U hRTS hSR hA₂Γ hA₂c hx ha)
      hD.mem
  obtain ⟨n, hn, hxn⟩ := CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem
    (X := X) (N := D) (R := Subgroup.zpowers h) (by simpa [D] using inf_le_right)
    hXD hRN hsolv hcop hx hxr
  have hxnY : x * n ∈ gammaStab V := hS.yOf_le_gammaStab h73 h75 hD hxn.2
  have hxY : x ∈ gammaStab V := by
    have h := (gammaStab V).mul_mem hxnY ((gammaStab V).inv_mem hn.1)
    simpa using h
  exact hxY

theorem Sec7Hyp.false_of_centralizes_pair (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    (hSR : UnitarySylowRoots) (h73 : Sec7.Stmt73 M V n f) {A₁ A₂ : Subgroup G}
    {h g : G} (hD : L2Datum M V A₁ A₂ h) (hB : conjSubgroup g V ∉ gammaAt V)
    (hBc : conjSubgroup g V ≤ cenOf (A₁ ⊔ A₂)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPY : conjSubgroup g (Pc M V) ≤ gammaStab V :=
    hS.conj_Pc_le_gammaStab h74 h75 h76U hRTS hSR h73 hD hBc
  have hP2 : IsPGroup 2 (conjSubgroup g (Pc M V)) := isPGroup_conj_Pc M V g
  have hodd : Odd (gammaAt V).ncard := hS.toSec6Hyp.odd_ncard_gammaAt
  have hstab : ∀ x ∈ conjSubgroup g (Pc M V), ∀ H ∈ gammaAt V,
      H.map (MulAut.conj x).toMonoidHom ∈ gammaAt V := by
    intro x hx H hH
    exact CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet (hPY hx) hH
  obtain ⟨E, hEΓ, hEfix⟩ :=
    CFSG.Timmesfeld.Bridge.exists_map_conj_eq_of_isPGroup hP2 hstab
      (Odd.not_two_dvd_nat hodd)
  have hPN : conjSubgroup g (Pc M V) ≤ Subgroup.normalizer (E : Set G) := by
    intro x hx
    exact mem_normalizer_iff_conjSubgroup_eq.mpr (hEfix x hx)
  have hEeq : E = conjSubgroup g V := by
    have hEω : E ∈ omegaSet (conjSubgroup g V) := by
      rw [omegaSet_conjSubgroup]
      exact gammaAt_subset_omegaSet V hEΓ
    have hP : Pc (conjSubgroup g M) (conjSubgroup g V) ≤
        Subgroup.normalizer (E : Set G) := by
      rwa [Pc_conjSubgroup]
    exact (hS.toSec6Hyp.sec5.conj g).eq_of_Pc_le_normalizer hEω hP
  exact hB (hEeq ▸ hEΓ)

theorem Sec7Hyp.stmt77 (hS : Sec7Hyp M V n f) (h77a : Sec7.Stmt77a V)
    (h77b : Sec7.Stmt77b V) (h73 : Sec7.Stmt73 M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hLP : UnitaryLinePair)
    (hRTS : UnitaryRootTypeSylow) (hSR : UnitarySylowRoots) : Sec7.Stmt77 V := by
  change omegaSet V = gammaAt V
  by_contra hne
  obtain ⟨B, hBΩ, hBΓ, hVB⟩ := h77a hne
  obtain ⟨B, hBΩ, hBΓ, -, A₁, hA₁, A₂, hA₂, hA, hBc⟩ := h77b ⟨B, hBΩ, hBΓ, hVB⟩
  obtain ⟨A₁', A₂', h, g, hD, hgΓ, hgc⟩ :=
    hS.exists_l2Datum_of_centralizes h75 h76U hLP hA₁ hA₂ hA hBΩ hBΓ hBc
  exact hS.false_of_centralizes_pair h74 h75 h76U hRTS hSR h73 hD hgΓ hgc

theorem Sec7Hyp.unitaryConclusion (hS : Sec7Hyp M V n f) (h76U : Sec7.Stmt76U V n f)
    (h77 : Sec7.Stmt77 V) : UnitaryConclusion V := by
  obtain ⟨Φ, hker, hrange, hmem⟩ := h76U hS.one_le
  unfold UnitaryConclusion
  refine ⟨f, hS.two_le, hS.card_V,
    hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60, n + 2,
    (by have := hS.four_le; omega), Φ, ?_, hker, ?_⟩
  · rw [hrange, Quasithin.MS93.normalClosure_eq_iSup_map_conj]
    apply le_antisymm
    · refine iSup₂_le fun A hA => ?_
      have hAω : A ∈ omegaSet V := by rwa [← h77] at hA
      obtain ⟨g, -, hAg⟩ := hAω
      rw [hAg]
      exact le_iSup (fun g => V.map (MulAut.conj g).toMonoidHom) g
    · refine iSup_le fun g => ?_
      exact le_iSup₂ (f := fun A (_ : A ∈ gammaAt V) => A) (conjSubgroup g V) (by
        rw [← h77]
        exact ⟨g, Subgroup.mem_top g, rfl⟩)
  · intro U
    have hX : (∃ g, U = conjSubgroup g V) ↔ U ∈ omegaSet V := by
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, Subgroup.mem_top g, rfl⟩
      · rintro ⟨g, -, hg⟩
        exact ⟨g, hg⟩
    rw [hX, h77]
    exact hmem U

