module

import CFSG.GH74.GLS.IVK.Proofs2.Lemma17Tori
import CFSG.Walter.W67.Section6.Core62A
import CFSG.Walter.W67.W1Prop24C
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped MatrixGroups

theorem eq_one_of_commute_of_card_eight {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hT8 : Nat.card T = 8) (hBT : B ≤ normalizer (T : Set X)) (hB7 : Nat.card B = 7)
    (hBC : ¬ B ≤ centralizer (T : Set X)) {t : X} (ht : t ∈ T)
    (htB : ∀ b ∈ B, b * t = t * b) : t = 1 := by
  classical
  have hfact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let act : MulAction ↥B ↥T :=
    MulAction.compHom ↥T ((Subgroup.normalizerMonoidHom T).comp (Subgroup.inclusion hBT))
  have hBpg : IsPGroup 7 ↥B := IsPGroup.of_card (p := 7) (n := 1) (by simpa using hB7)
  have hsmul : ∀ (b : ↥B) (x : ↥T),
      ((b • x : ↥T) : X) = (b : X) * (x : X) * (b : X)⁻¹ := by
    intro b x
    change ((Subgroup.normalizerMonoidHom T (Subgroup.inclusion hBT b)) x : X) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have h1fix : (⟨1, T.one_mem⟩ : ↥T) ∈ MulAction.fixedPoints ↥B ↥T := by
    rw [MulAction.mem_fixedPoints]
    intro b
    apply Subtype.ext
    rw [hsmul]
    simp
  have hfix : ∀ b : ↥B, b • (⟨t, ht⟩ : ↥T) = ⟨t, ht⟩ := by
    intro b
    apply Subtype.ext
    rw [hsmul, htB (b : X) b.2, mul_assoc, mul_inv_cancel, mul_one]
  have htfix : (⟨t, ht⟩ : ↥T) ∈ MulAction.fixedPoints ↥B ↥T :=
    MulAction.mem_fixedPoints.mpr hfix
  have hcong : Nat.card ↥T ≡ (MulAction.fixedPoints ↥B ↥T).ncard [MOD 7] := by
    have h := IsPGroup.card_modEq_card_fixedPoints (p := 7) (G := ↥B) hBpg (α := ↥T)
    rwa [Nat.card_coe_set_eq] at h
  by_cases ht1 : t = 1
  · exact ht1
  · exfalso
    have hcle : (MulAction.fixedPoints ↥B ↥T).ncard ≤ 8 := by
      have h := Nat.card_le_card_of_injective
        (fun x : MulAction.fixedPoints ↥B ↥T => (x : ↥T)) Subtype.coe_injective
      rw [Nat.card_coe_set_eq, hT8] at h
      exact h
    have hc2 : 2 ≤ (MulAction.fixedPoints ↥B ↥T).ncard := by
      have hinj : Function.Injective (fun i : Fin 2 =>
          if i = 0 then (⟨⟨1, T.one_mem⟩, h1fix⟩ : MulAction.fixedPoints ↥B ↥T)
          else ⟨⟨t, ht⟩, htfix⟩) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have h := Nat.card_le_card_of_injective _ hinj
      rw [show Nat.card (Fin 2) = 2 from by simp, Nat.card_coe_set_eq] at h
      exact h
    have hmod : (MulAction.fixedPoints ↥B ↥T).ncard % 7 = 1 := by
      have h8 := hcong
      rw [hT8, Nat.ModEq] at h8
      omega
    have hc8 : (MulAction.fixedPoints ↥B ↥T).ncard = 8 := by omega
    have hall : MulAction.fixedPoints ↥B ↥T = ⊤ := by
      apply Set.eq_top_of_card_le_of_finite
      rw [hT8, Nat.card_coe_set_eq, hc8]
    apply hBC
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxfix : (⟨x, hx⟩ : ↥T) ∈ MulAction.fixedPoints ↥B ↥T := by
      rw [hall]
      exact trivial
    have h := (MulAction.mem_fixedPoints.mp hxfix) ⟨b, hb⟩
    have hbx : (b : X) * x * (b : X)⁻¹ = x := by
      rw [← hsmul ⟨b, hb⟩ ⟨x, hx⟩]
      exact congrArg Subtype.val h
    have h2 := congrArg (fun y => y * (b : X)) hbx
    simpa [mul_assoc] using h2.symm

theorem normalizer_le_of_index_eq_twentyOne {X : Type} [Group X] [Finite X]
    {T B M : Subgroup X} (hT8 : Nat.card T = 8)
    (hidx : (T.subgroupOf (normalizer (T : Set X))).index = 21)
    (hBT : B ≤ normalizer (T : Set X)) (hB7 : Nat.card B = 7) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g : X, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) : normalizer (T : Set X) ≤ M := by
  classical
  set N : Subgroup X := normalizer (T : Set X) with hNdef
  have hBN : B ≤ N := hBT
  change N ≤ M
  intro g hg
  let Tn : Subgroup N := T.subgroupOf N
  have hTnn : Tn.Normal := Subgroup.normal_in_normalizer
  let π : N →* N ⧸ Tn := QuotientGroup.mk' Tn
  have hQ : Nat.card (N ⧸ Tn) = 21 := by
    rw [← Subgroup.index_eq_card]
    simpa [Tn, hNdef] using hidx
  obtain ⟨P, hPnorm, hPcard⟩ := CFSG.Walter.W67.exists_normal_card_seven hQ
  let B' : Subgroup (N ⧸ Tn) := (B.subgroupOf N).map π
  let φ : ↥(B.subgroupOf N) →* N ⧸ Tn := π.comp (B.subgroupOf N).subtype
  have hcop : Nat.Coprime (Nat.card T) (Nat.card B) := by
    rw [hT8, hB7]
    norm_num
  have hTB : T ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : (QuotientGroup.mk' Tn) (x : N) = (QuotientGroup.mk' Tn) (y : N) := hxy
    have hmem : ((x⁻¹ * y : ↥(B.subgroupOf N)) : N) ∈ Tn := by
      have h := QuotientGroup.eq.mp hxy'
      simpa using h
    have hmemX : ((x⁻¹ * y : ↥(B.subgroupOf N)) : X) ∈ T ⊓ B := by
      refine ⟨?_, (x⁻¹ * y).2⟩
      show (((x⁻¹ * y : ↥(B.subgroupOf N)) : N) : X) ∈ T
      exact hmem
    have hone : ((x⁻¹ * y : ↥(B.subgroupOf N)) : X) = 1 := by
      have hbot : ((x⁻¹ * y : ↥(B.subgroupOf N)) : X) ∈ (⊥ : Subgroup X) := hTB ▸ hmemX
      simpa using hbot
    have h1 : x⁻¹ * y = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hone
    exact inv_mul_eq_one.mp h1
  have hsub : Subgroup.map (B.subgroupOf N).subtype (⊤ : Subgroup ↥(B.subgroupOf N)) =
      B.subgroupOf N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : φ.range = B' := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, hsub]
  have hB'card : Nat.card B' = 7 := by
    have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hrange] at hcard
    rw [← hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, hB7]
  have hidxP : P.index = 3 := by
    have h := Subgroup.index_mul_card P
    rw [hQ, hPcard] at h
    omega
  have hcardQP : Nat.card ((N ⧸ Tn) ⧸ P) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidxP
  have hB'P : B' = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro b hb
      have hb7 : orderOf (QuotientGroup.mk' P b) ∣ 7 := by
        have h1 := orderOf_map_dvd (QuotientGroup.mk' P) b
        have h2 : orderOf b ∣ 7 := by
          have h := Subgroup.orderOf_dvd_natCard B' hb
          rwa [hB'card] at h
        exact h1.trans h2
      have hb3 : orderOf (QuotientGroup.mk' P b) ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup ((N ⧸ Tn) ⧸ P))
          (x := QuotientGroup.mk' P b) (Subgroup.mem_top _)
        rwa [show Nat.card ↥(⊤ : Subgroup ((N ⧸ Tn) ⧸ P)) = 3 from by simpa using hcardQP] at h
      have h1 : orderOf (QuotientGroup.mk' P b) = 1 := by
        have h := Nat.dvd_gcd hb7 hb3
        rw [show Nat.gcd 7 3 = 1 from by norm_num] at h
        exact Nat.dvd_one.mp h
      have hker : QuotientGroup.mk' P b = 1 := orderOf_eq_one_iff.mp h1
      exact (QuotientGroup.eq_one_iff b).mp hker
    · rw [hPcard, hB'card]
  have hbM : ∀ b ∈ B, g⁻¹ * b * g ∈ M := by
    intro b hb
    have hbN : b ∈ N := hBN hb
    have hgN : g ∈ N := hg
    have hmemN : g⁻¹ * b * g ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hgN) hbN) hgN
    let k : N := ⟨g⁻¹ * b * g, hmemN⟩
    have hkB : ((k : N) : X) = g⁻¹ * b * g := rfl
    have hmemB' : π k ∈ B' := by
      rw [hB'P]
      have hpb : π ⟨b, hbN⟩ ∈ P := by
        rw [← hB'P]
        exact Subgroup.mem_map.mpr ⟨⟨b, hbN⟩, hb, rfl⟩
      have heq : k = (⟨g, hgN⟩ : N)⁻¹ * ⟨b, hbN⟩ * ⟨g, hgN⟩ := rfl
      rw [heq]
      simp only [map_mul, map_inv]
      simpa using hPnorm.conj_mem _ hpb (π ⟨g, hgN⟩)⁻¹
    obtain ⟨b', hb'B, hb'eq⟩ := Subgroup.mem_map.mp
      (show π k ∈ Subgroup.map π (B.subgroupOf N) from hmemB')
    have hquot : π (b'⁻¹ * k) = 1 := by
      rw [map_mul, map_inv, hb'eq, inv_mul_cancel]
    have hmemT : ((b' : N) : X)⁻¹ * (g⁻¹ * b * g) ∈ T := by
      have h := (QuotientGroup.eq_one_iff (b'⁻¹ * k)).mp hquot
      have h' : ((b'⁻¹ * k : N) : X) ∈ T := h
      have e1 : ((b'⁻¹ * k : N) : X) = ((b' : N) : X)⁻¹ * ((k : N) : X) := by
        simp
      rw [e1, hkB] at h'
      exact h'
    have hEq : g⁻¹ * b * g = ((b' : N) : X) * (((b' : N) : X)⁻¹ * (g⁻¹ * b * g)) := by
      group
    rw [hEq]
    exact M.mul_mem (hBM hb'B) (hTM hmemT)
  exact hstar g hbM

theorem psl2_eq_top_of_normalizer_le {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n) (hq7 : p ^ n ≠ 7) (hq9 : p ^ n ≠ 9) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hrq : ¬ r ∣ p ^ n - 1)
    {R H : Subgroup PSL(2, GaloisField p n)} (hR : Nat.card R = r)
    (hRH : normalizer (R : Set PSL(2, GaloisField p n)) ≤ H) {w : PSL(2, GaloisField p n)}
    (hwH : w ∈ H) (hw : ¬ orderOf w ∣ p ^ n + 1) : H = ⊤ := by
  classical
  let F := GaloisField p n
  have hFintype : Fintype F := Fintype.ofFinite F
  have hFdec : DecidableEq F := Classical.decEq F
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq5
    omega
  have hcardF : Nat.card F = p ^ n := GaloisField.card p n hn
  have hqcard : Fintype.card F = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardF
  have hq5F : 5 ≤ Fintype.card F := by rw [hqcard]; exact hq5
  have hring : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := F) hring
  have hRne : R ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card R = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hR] at h1
    exact hr.ne_one h1
  have hRodd : Odd (Nat.card R) := by
    rw [hR]
    exact hr.odd_of_ne_two hr2
  have hRcop : Nat.Coprime p (Nat.card R) := by
    rw [hR]
    exact (Nat.coprime_primes ‹Fact p.Prime›.out hr).mpr (Ne.symm hrp)
  rcases CFSG.GH74.GLS.IVK.Proofs2.exists_conj_mem_torus (F := F) hcardF hp2 hring hq5F hν
      R hRne hRodd hRcop with ⟨c, hc⟩ | ⟨c, hc⟩
  · exfalso
    have hle : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ PSL2Table.splitTorus F := by
      rintro x ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hc y hy
    have hcard : Nat.card (R.map (MulAut.conj c⁻¹).toMonoidHom) = r := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hR]
    have hdvd : r ∣ Nat.card (PSL2Table.splitTorus F) := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hring
    have hsp := PSL2Table.card_splitTorus (F := F) h2
    apply hrq
    have h : r ∣ Nat.card (PSL2Table.splitTorus F) * 2 := dvd_mul_of_dvd_left hdvd 2
    rw [hsp, hqcard] at h
    exact h
  · let C : Subgroup PSL(2, F) := PSL2Table.nonsplitTorus ν
    let R' : Subgroup PSL(2, F) := R.map (MulAut.conj c⁻¹).toMonoidHom
    have hR'C : R' ≤ C := by
      rintro x ⟨y, hy, rfl⟩
      simpa [C, MulAut.conj_apply] using hc y hy
    have hR'card : Nat.card R' = r := by
      rw [show R' = R.map (MulAut.conj c⁻¹).toMonoidHom from rfl,
        Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hR]
    have hNC : normalizer (C : Set PSL(2, F)) ≤ normalizer (R' : Set PSL(2, F)) := by
      intro y hy
      have hmapC : R'.map (MulAut.conj y).toMonoidHom ≤ C := by
        rintro z ⟨x, hx, rfl⟩
        have hx' : x ∈ C := hR'C hx
        exact (Subgroup.mem_normalizer_iff.mp hy x).mp hx'
      have hcardImg : Nat.card (R'.map (MulAut.conj y).toMonoidHom) = Nat.card R' :=
        Subgroup.card_map_of_injective (MulAut.conj y).injective
      have heq : R'.map (MulAut.conj y).toMonoidHom = R' :=
        CFSG.Walter.W67.Sec6.eq_of_le_cyclic
          (CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν)
          hmapC hR'C (by rw [hcardImg])
      have himg : ∀ z, (MulAut.conj y) z ∈ R' ↔ z ∈ R' := by
        intro z
        constructor
        · intro hz
          rw [← heq] at hz
          obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.mp hz
          rwa [(MulAut.conj y).injective huz] at hu
        · intro hz
          rw [← heq]
          exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [← MulAut.conj_apply]
      exact (himg z).symm
    have hNmap : (normalizer (R : Set PSL(2, F))).map (MulAut.conj c⁻¹).toMonoidHom =
        normalizer (R' : Set PSL(2, F)) := by
      have h := Subgroup.map_equiv_normalizer_eq (G := PSL(2, F)) R (MulAut.conj c⁻¹)
      simpa [R'] using h
    let H' : Subgroup PSL(2, F) := H.map (MulAut.conj c⁻¹).toMonoidHom
    have hH' : normalizer (C : Set PSL(2, F)) ≤ H' := by
      intro y hy
      have hy' : y ∈ normalizer (R' : Set PSL(2, F)) := hNC hy
      rw [← hNmap] at hy'
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hy'
      rw [← hme]
      exact Subgroup.mem_map.mpr ⟨m, hRH hm, rfl⟩
    have hw'H : (MulAut.conj c⁻¹) w ∈ H' :=
      Subgroup.mem_map.mpr ⟨w, hwH, rfl⟩
    have hw'not : (MulAut.conj c⁻¹) w ∉ normalizer (C : Set PSL(2, F)) := by
      intro hmem
      have hdvd : orderOf ((MulAut.conj c⁻¹) w) ∣
          Nat.card (normalizer (C : Set PSL(2, F))) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      have hcard : Nat.card (normalizer (C : Set PSL(2, F))) = p ^ n + 1 := by
        change Nat.card (normalizer (PSL2Table.nonsplitTorus ν : Set PSL(2, F))) = p ^ n + 1
        have h1 := PSL2Table.card_normalizer_nonsplitTorus (F := F) hring hq5F hν
        have h2 := PSL2Table.card_nonsplitTorus (F := F) hring hν
        omega
      rw [hcard] at hdvd
      apply hw
      have ho : orderOf ((MulAut.conj c⁻¹) w) = orderOf w :=
        MulEquiv.orderOf_eq (MulAut.conj c⁻¹) w
      rw [ho] at hdvd
      exact hdvd
    have hcoatom : IsCoatom (normalizer (C : Set PSL(2, F))) :=
      CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_nonsplitTorus (F := F) (p := p) (f := n)
        hcardF hp2 hq5 hq7 hq9 hν
    have hne : normalizer (C : Set PSL(2, F)) ≠ H' := by
      intro heq
      exact hw'not (heq ▸ hw'H)
    have hlt : normalizer (C : Set PSL(2, F)) < H' := lt_of_le_of_ne hH' hne
    have hH'top : H' = ⊤ := (IsCoatom.lt_iff hcoatom).mp hlt
    rw [eq_top_iff]
    intro x _
    have hx' : (MulAut.conj c⁻¹) x ∈ H' := by rw [hH'top]; exact trivial
    rw [show H' = H.map (MulAut.conj c⁻¹).toMonoidHom from rfl] at hx'
    obtain ⟨h, hhH, hhx⟩ := Subgroup.mem_map.mp hx'
    have hhx' : h = x := (MulAut.conj c⁻¹).injective hhx
    rwa [← hhx']

theorem not_seven_dvd_of_mul_eq {q i : ℕ} (hq : 2 ≤ q) (h7 : 7 ∣ q + 1)
    (h : i * (q * (q ^ 2 - 1)) = q ^ 3 * (q ^ 3 + 1) * (q - 1)) : ¬ 7 ∣ i := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have hi : i = q ^ 2 * (q ^ 2 - q + 1) := by
    have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h]
    have h3 : 1 ≤ q := by omega
    have h4 : 1 ≤ q ^ 2 := by omega
    zify [h1, h3, h4]
    ring
  have e : q ^ 2 - q + 1 = (q + 1) * (q - 2) + 3 := by
    zify [h1, hq]
    ring
  rw [hi, e]
  intro hd
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp hd with hd | hd
  · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) hd)
    omega
  · have := (Nat.dvd_add_right (dvd_mul_of_dvd_left h7 _)).mp hd
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
