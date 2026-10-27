module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPComp
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPStepCentral
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPStepDecomp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc813pstep_exists_sq_not_comm {J : Subgroup Q} (hJ : IsComponentOf J ⊤) :
    ∃ x ∈ J, ∃ l ∈ J, x * x * l ≠ l * x * x := by
  by_contra hcon
  push Not at hcon
  have hsq_center : ∀ x : ↥J, x * x ∈ Subgroup.center ↥J := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by
      simpa [Subgroup.coe_mul, mul_assoc] using (hcon (x : Q) x.2 (y : Q) y.2).symm)
  have hexp : ∀ z : ↥J ⧸ Subgroup.center ↥J, z * z = 1 := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) z
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hsq_center x
  have hcomm : IsMulCommutative (↥J ⧸ Subgroup.center ↥J) := by
    refine isMulCommutative_iff.mpr fun a b => ?_
    have hab : (a * b) * (a * b) = 1 := hexp (a * b)
    have ha : a * a = 1 := hexp a
    have hb : b * b = 1 := hexp b
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hab
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [show a⁻¹ = a from (eq_inv_of_mul_eq_one_right ha).symm,
            show b⁻¹ = b from (eq_inv_of_mul_eq_one_right hb).symm]
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  haveI : Group.IsPerfect (↥J ⧸ Subgroup.center ↥J) := inferInstance
  exact Group.IsPerfect.not_isMulCommutative (↥J ⧸ Subgroup.center ↥J) hcomm

private theorem wc813pstep_conjSubgroup_eq_iff {J : Subgroup Q} {c d : Q} :
    conjSubgroup J c = conjSubgroup J d ↔ c * d⁻¹ ∈ normalizer (J : Set Q) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  constructor
  · intro heq
    have h := congrArg (fun K => conjSubgroup K d⁻¹) heq
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using h
  · intro heq
    have h := congrArg (fun K => conjSubgroup K d) heq
    rw [conjSubgroup_conjSubgroup] at h
    simpa using h

theorem Cfg813.exists_normalizing_of_moved (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) {a : Q} (ha : a ∈ A) (hmoved : conjSubgroup J a ≠ J) :
    ∃ b ∈ A, b ≠ 1 ∧ b ∈ normalizer (J : Set Q) := by
  classical
  by_contra hcon
  have hnoN : ∀ c ∈ A, c ≠ 1 → c ∉ normalizer (J : Set Q) := by
    intro c hc hc1 hcN
    exact hcon ⟨c, hc, hc1, hcN⟩
  have ha1 : a ≠ 1 := by
    intro h1; exact hmoved (by rw [h1, conjSubgroup_one])
  have ha2 : a * a = 1 := by simpa [pow_two] using h.A_elem.2 a ha
  have hbexists : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra hbcon
    push Not at hbcon
    have hsub : (A : Set Q) ⊆ ({1, a} : Set Q) := by
      intro c hc
      by_cases hc1 : c = 1
      · rw [hc1]; exact Set.mem_insert _ _
      · rw [hbcon c hc hc1]; exact Set.mem_insert_of_mem _ rfl
    have hcard : Nat.card A ≤ 2 := by
      change (A : Set Q).ncard ≤ 2
      calc (A : Set Q).ncard ≤ ({1, a} : Set Q).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 2 := Set.ncard_pair (Ne.symm ha1)
    rw [h.A_card] at hcard
    omega
  obtain ⟨b, hbA, hb1, hba⟩ := hbexists
  have hb2 : b * b = 1 := by simpa [pow_two] using h.A_elem.2 b hbA
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_right ha2).symm
  have hbi : b⁻¹ = b := (eq_inv_of_mul_eq_one_right hb2).symm
  have habA : a * b ∈ A := A.mul_mem ha hbA
  have hab1 : a * b ≠ 1 := by
    intro h1
    have h1' : a = b := by
      calc a = a * (b * b) := by rw [hb2, mul_one]
        _ = (a * b) * b := by group
        _ = 1 * b := by rw [h1]
        _ = b := one_mul b
    exact hba h1'.symm
  have hJcomp : ∀ c : Q, IsComponentOf (conjSubgroup J c) ⊤ := by
    intro c
    have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
      (MulAut.conj c⁻¹) J).mpr hJ
    simpa [conjSubgroup] using hh
  have hcent : ∀ c : Q, conjSubgroup J c ≠ J →
      J ≤ centralizer (conjSubgroup J c : Set Q) := by
    intro c hc
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne J _
      hJ (hJcomp c) (Ne.symm hc)
  have hcent' : ∀ c d : Q, conjSubgroup J c ≠ conjSubgroup J d →
      conjSubgroup J c ≤ centralizer (conjSubgroup J d : Set Q) := by
    intro c d hcd
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (hJcomp c) (hJcomp d) hcd
  have hJ_ne_Ja : conjSubgroup J a ≠ J := hmoved
  have hJ_ne_Jb : conjSubgroup J b ≠ J := fun heq =>
    hnoN b hbA hb1 (conjSubgroup_eq_iff_mem_normalizer.mp heq)
  have hJ_ne_Jab : conjSubgroup J (a*b) ≠ J := fun heq =>
    hnoN (a*b) habA hab1 (conjSubgroup_eq_iff_mem_normalizer.mp heq)
  have hdistinct : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → conjSubgroup J c ≠ conjSubgroup J d := by
    intro c hc d hd hcd heq
    have hmem : c * d⁻¹ ∈ normalizer (J : Set Q) := wc813pstep_conjSubgroup_eq_iff.mp heq
    have hne1 : c * d⁻¹ ≠ 1 := by
      intro h1
      have h1' : c = d := by
        have := congrArg (fun t => t * d) h1
        simpa [mul_assoc] using this
      exact hcd h1'
    exact hnoN (c * d⁻¹) (A.mul_mem hc (A.inv_mem hd)) hne1 hmem
  have hJa_ne_Jb : conjSubgroup J a ≠ conjSubgroup J b :=
    hdistinct a ha b hbA (Ne.symm hba)
  have hJa_ne_Jab : conjSubgroup J a ≠ conjSubgroup J (a*b) :=
    hdistinct a ha (a*b) habA (by
      intro h1
      have h1' : 1 = b := by
        have := congrArg (fun t => a⁻¹ * t) h1
        simpa [mul_assoc] using this
      exact hb1 h1'.symm)
  have hJb_ne_Jab : conjSubgroup J b ≠ conjSubgroup J (a*b) :=
    hdistinct b hbA (a*b) habA (by
      intro h1
      have hcomm : a * b = b * a := IsElemAbelian.comm h.A_elem ha hbA
      have h1' : 1 = a := by
        have h2 := congrArg (fun t => b⁻¹ * t) h1
        rw [show b⁻¹ * (a * b) = a by
          calc b⁻¹ * (a * b) = b⁻¹ * (b * a) := by rw [hcomm]
            _ = a := by group] at h2
        simpa using h2
      exact ha1 h1'.symm)
  have hx2 : ∀ x : ↥J, x * x ∈ Subgroup.center ↥J := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro l
    have hxq : (x : Q) ∈ J := x.2
    have hlq : (l : Q) ∈ J := l.2
    set xb : Q := b * (x : Q) * b⁻¹ with hxbdef
    have hxb_mem : xb ∈ conjSubgroup J b := by
      rw [hxbdef, mem_conjSubgroup_iff]
      have h1 : b * (b * (x : Q) * b⁻¹) * b⁻¹ = (x : Q) := by
        calc b * (b * (x : Q) * b⁻¹) * b⁻¹ = (b * b) * (x : Q) * (b⁻¹ * b⁻¹) := by group
          _ = (x : Q) := by rw [hbi, hb2]; group
      rw [h1]; exact x.2
    set y : Q := (x : Q) * xb with hydef
    have hxbx : xb * (x : Q) = (x : Q) * xb :=
      Subgroup.mem_centralizer_iff.mp (hcent b hJ_ne_Jb x.2) xb hxb_mem
    have hyb : y * b = b * y := by
      have h1 : b * y * b⁻¹ = y := by
        rw [hydef, hxbdef]
        calc b * ((x : Q) * (b * (x : Q) * b⁻¹)) * b⁻¹
            = (b * (x : Q) * b⁻¹) * (b * (b * (x : Q) * b⁻¹) * b⁻¹) := by group
          _ = (b * (x : Q) * b⁻¹) * (x : Q) := by
              congr 1
              calc b * (b * (x : Q) * b⁻¹) * b⁻¹ = (b * b) * (x : Q) * (b⁻¹ * b⁻¹) := by group
                _ = (x : Q) := by rw [hbi, hb2]; group
          _ = (x : Q) * (b * (x : Q) * b⁻¹) := hxbx
      have h2 := congrArg (fun t => t * b) h1
      simpa [mul_assoc] using h2.symm
    set W : Set Q := {γ | ∃ z ∈ (⊤ : Subgroup Q) ⊓ centralizer ({b} : Set Q),
      γ = z * a * z⁻¹} with hWdef
    have hK1 : IsElemAbelian 2 (Subgroup.closure W) := h.K1 a ha b hbA hb1
    have hyC : y ∈ (⊤ : Subgroup Q) ⊓ centralizer ({b} : Set Q) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact hyb⟩
    have haW : a ∈ Subgroup.closure W :=
      Subgroup.subset_closure ⟨1, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_top 1, (centralizer _).one_mem⟩, by simp⟩
    have hyaW : y * a * y⁻¹ ∈ Subgroup.closure W :=
      Subgroup.subset_closure ⟨y, hyC, rfl⟩
    have hw1 : (a * (y * a * y⁻¹)) * (a * (y * a * y⁻¹)) = 1 :=
      IsElemAbelian.mul_self_eq_one hK1 ((Subgroup.closure W).mul_mem haW hyaW)
    set q1 : Q := a * (x : Q) * a⁻¹ with hq1def
    set q2 : Q := a * xb * a⁻¹ with hq2def
    set q3 : Q := xb⁻¹ with hq3def
    set q4 : Q := (x : Q)⁻¹ with hq4def
    have hw_eq : a * (y * a * y⁻¹) = q1 * q2 * q3 * q4 := by
      rw [hydef, hq1def, hq2def, hq3def, hq4def, hxbdef, hai, hbi]
      rw [mul_inv_rev]
      rw [show a * (x : Q) * a * (a * (b * (x : Q) * b) * a) *
            (b * (x : Q) * b)⁻¹ * ((x : Q))⁻¹ =
          a * (x : Q) * (a*a) * (b * (x : Q) * b) * a *
            (b * (x : Q) * b)⁻¹ * ((x : Q))⁻¹ by group]
      rw [ha2]
      group
    have hq1_mem : q1 ∈ conjSubgroup J a := by
      rw [hq1def, mem_conjSubgroup_iff]
      have h1 : a * (a * (x : Q) * a⁻¹) * a⁻¹ = (x : Q) := by
        calc a * (a * (x : Q) * a⁻¹) * a⁻¹ = (a * a) * (x : Q) * (a⁻¹ * a⁻¹) := by group
          _ = (x : Q) := by rw [hai, ha2]; group
      rw [h1]; exact x.2
    have hq2_mem : q2 ∈ conjSubgroup J (a * b) := by
      rw [hq2def, hxbdef, mem_conjSubgroup_iff]
      have hab2 : (a*b) * (a*b) = 1 := by simpa [pow_two] using h.A_elem.2 (a*b) habA
      have h1 : (a * b) * (a * (b * (x : Q) * b⁻¹) * a⁻¹) * (a * b)⁻¹ = (x : Q) := by
        calc (a * b) * (a * (b * (x : Q) * b⁻¹) * a⁻¹) * (a * b)⁻¹
            = ((a*b) * (a*b)) * (x : Q) * ((a*b)⁻¹ * (a*b)⁻¹) := by group
          _ = (x : Q) := by
              rw [show (a*b)⁻¹ = a*b from (eq_inv_of_mul_eq_one_right hab2).symm, hab2]; group
      rw [h1]; exact x.2
    have hq3_mem : q3 ∈ conjSubgroup J b := by
      rw [hq3def]; exact (conjSubgroup J b).inv_mem hxb_mem
    have hq4_mem : q4 ∈ J := by rw [hq4def]; exact J.inv_mem x.2
    have h12 : q1 * q2 = q2 * q1 :=
      (Subgroup.mem_centralizer_iff.mp (hcent' a (a*b) hJa_ne_Jab hq1_mem) q2 hq2_mem).symm
    have h13 : q1 * q3 = q3 * q1 :=
      (Subgroup.mem_centralizer_iff.mp (hcent' a b hJa_ne_Jb hq1_mem) q3 hq3_mem).symm
    have h14 : q1 * q4 = q4 * q1 :=
      Subgroup.mem_centralizer_iff.mp (hcent a hJ_ne_Ja hq4_mem) q1 hq1_mem
    have h23 : q2 * q3 = q3 * q2 :=
      (Subgroup.mem_centralizer_iff.mp (hcent' (a*b) b hJb_ne_Jab.symm hq2_mem) q3 hq3_mem).symm
    have h24 : q2 * q4 = q4 * q2 :=
      Subgroup.mem_centralizer_iff.mp (hcent (a*b) hJ_ne_Jab hq4_mem) q2 hq2_mem
    have h34 : q3 * q4 = q4 * q3 :=
      Subgroup.mem_centralizer_iff.mp (hcent b hJ_ne_Jb hq4_mem) q3 hq3_mem
    have hc14 : Commute q1 q4 := h14
    have hc24 : Commute q2 q4 := h24
    have hc34 : Commute q3 q4 := h34
    have h1234 : Commute (q1*q2*q3) q4 := (hc14.mul_left hc24).mul_left hc34
    have hw2 : (q1*q2*q3*q4) * (q1*q2*q3*q4) = 1 := by rw [← hw_eq]; exact hw1
    have hw2' : (q1*q2*q3*q4) * (q1*q2*q3*q4) =
        (q1*q2*q3) * (q1*q2*q3) * (q4*q4) := by
      calc (q1*q2*q3*q4)*(q1*q2*q3*q4) = ((q1*q2*q3)*q4)*((q1*q2*q3)*q4) := by group
        _ = (q1*q2*q3) * (q4 * (q1*q2*q3)) * q4 := by group
        _ = (q1*q2*q3) * ((q1*q2*q3) * q4) * q4 := by rw [← h1234.eq]
        _ = ((q1*q2*q3)*(q1*q2*q3)) * (q4*q4) := by group
    have h1 : (q1*q2*q3) * (q1*q2*q3) * ((x : Q)⁻¹ * (x : Q)⁻¹) = 1 := by
      have := hw2
      rw [hw2'] at this
      rwa [hq4def] at this
    have hx2eq : (x : Q) * (x : Q) = (q1*q2*q3) * (q1*q2*q3) := by
      have h2 := congrArg (fun t => t * ((x : Q) * (x : Q))) h1
      rw [one_mul] at h2
      have h4 : (q1*q2*q3) * (q1*q2*q3) * ((x : Q)⁻¹ * (x : Q)⁻¹) *
          ((x : Q) * (x : Q)) = (q1*q2*q3) * (q1*q2*q3) := by group
      rw [h4] at h2
      exact h2.symm
    have hc1l : Commute q1 (l : Q) :=
      Subgroup.mem_centralizer_iff.mp (hcent a hJ_ne_Ja hlq) q1 hq1_mem
    have hc2l : Commute q2 (l : Q) :=
      Subgroup.mem_centralizer_iff.mp (hcent (a*b) hJ_ne_Jab hlq) q2 hq2_mem
    have hc3l : Commute q3 (l : Q) :=
      Subgroup.mem_centralizer_iff.mp (hcent b hJ_ne_Jb hlq) q3 hq3_mem
    have hq123l : Commute (q1*q2*q3) (l : Q) := (hc1l.mul_left hc2l).mul_left hc3l
    have hx2_l : Commute ((x : Q) * (x : Q)) (l : Q) := by
      rw [hx2eq]
      simpa [pow_two] using hq123l.pow_left 2
    exact Subtype.ext hx2_l.symm
  obtain ⟨x, hxJ, l, hlJ, hne'⟩ := wc813pstep_exists_sq_not_comm hJ
  have hcenter := hx2 ⟨x, hxJ⟩
  rw [Subgroup.mem_center_iff] at hcenter
  exact hne' (by
    simpa [Subgroup.coe_mul, mul_assoc] using
      (congrArg Subtype.val (hcenter ⟨l, hlJ⟩)).symm)

private theorem wc813pstep_sq_central_of_commute (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) {a b : Q} (ha : a ∈ A) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hmoved : conjSubgroup J a ≠ J) :
    ∀ x ∈ J, x * b = b * x → ∀ l ∈ J, (x * x) * l = l * (x * x) := by
  intro x hx hxb l hl
  have ha2 : a * a = 1 := by simpa [pow_two] using h.A_elem.2 a ha
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_right ha2).symm
  have hJcomp : IsComponentOf (conjSubgroup J a) ⊤ := by
    have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
      (MulAut.conj a⁻¹) J).mpr hJ
    simpa [conjSubgroup] using hh
  have hcent : J ≤ centralizer (conjSubgroup J a : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne J _
      hJ hJcomp (Ne.symm hmoved)
  have hx'_mem : a * x * a⁻¹ ∈ conjSubgroup J a := by
    rw [mem_conjSubgroup_iff]
    have h1 : a * (a * x * a⁻¹) * a⁻¹ = x := by
      calc a * (a * x * a⁻¹) * a⁻¹ = (a*a) * x * (a⁻¹*a⁻¹) := by group
        _ = x := by rw [hai, ha2]; group
    rw [h1]; exact hx
  have hx'l : (a * x * a⁻¹) * l = l * (a * x * a⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hcent hl) (a * x * a⁻¹) hx'_mem
  have hxx' : Commute x (a * x * a⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (hcent hx) (a * x * a⁻¹) hx'_mem).symm
  have hxmem : x ∈ (⊤ : Subgroup Q) ⊓ centralizer ({b} : Set Q) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hxb⟩
  set W : Set Q := {γ | ∃ z ∈ (⊤ : Subgroup Q) ⊓ centralizer ({b} : Set Q),
    γ = z * a * z⁻¹} with hWdef
  have hK1 : IsElemAbelian 2 (Subgroup.closure W) := h.K1 a ha b hb hb1
  have haW : a ∈ Subgroup.closure W :=
    Subgroup.subset_closure ⟨1, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_top 1, (centralizer _).one_mem⟩, by simp⟩
  have hxW : x * a * x⁻¹ ∈ Subgroup.closure W :=
    Subgroup.subset_closure ⟨x, hxmem, rfl⟩
  have hw1 : (a * (x * a * x⁻¹)) * (a * (x * a * x⁻¹)) = 1 :=
    IsElemAbelian.mul_self_eq_one hK1 ((Subgroup.closure W).mul_mem haW hxW)
  have hw_eq : a * (x * a * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by
    rw [hai]; group
  have hx'2 : ((a * x * a⁻¹) * x⁻¹) * ((a * x * a⁻¹) * x⁻¹) = 1 := by
    rw [← hw_eq]; exact hw1
  have hcx : Commute x⁻¹ (a * x * a⁻¹) := hxx'.inv_left
  have hx'2' : (a * x * a⁻¹) * (a * x * a⁻¹) * (x⁻¹ * x⁻¹) = 1 := by
    have h1 : ((a * x * a⁻¹) * x⁻¹) * ((a * x * a⁻¹) * x⁻¹) =
        (a * x * a⁻¹) * (a * x * a⁻¹) * (x⁻¹ * x⁻¹) := by
      calc ((a * x * a⁻¹) * x⁻¹) * ((a * x * a⁻¹) * x⁻¹)
          = (a * x * a⁻¹) * (x⁻¹ * (a * x * a⁻¹)) * x⁻¹ := by group
        _ = (a * x * a⁻¹) * ((a * x * a⁻¹) * x⁻¹) * x⁻¹ := by rw [hcx.eq]
        _ = (a * x * a⁻¹) * (a * x * a⁻¹) * (x⁻¹ * x⁻¹) := by group
    rw [← h1]; exact hx'2
  have hx2eq : x * x = (a * x * a⁻¹) * (a * x * a⁻¹) := by
    have h2 := congrArg (fun t => t * (x * x)) hx'2'
    rw [one_mul] at h2
    have h4 : (a * x * a⁻¹) * (a * x * a⁻¹) * (x⁻¹ * x⁻¹) * (x * x) =
        (a * x * a⁻¹) * (a * x * a⁻¹) := by group
    rw [h4] at h2
    exact h2.symm
  rw [hx2eq]
  have hcx'l : Commute (a * x * a⁻¹) l := hx'l
  have hpow := hcx'l.pow_left 2
  rw [pow_two] at hpow
  exact hpow

private theorem wc813pstep_sq_central_of_decomp (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) {a b s c : Q} (ha : a ∈ A) (hb : b ∈ A)
    (hmoved : conjSubgroup J a ≠ J) (hsJ : s ∈ J) (hs : s * s = 1)
    (hc : c ∈ centralizer (J : Set Q)) (hbsc : b = s * c) :
    ∀ w ∈ J, ∀ l ∈ J, ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) * l =
      l * ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) :=
  sq_central_of_decomp_of_k1 h.K1 h.A_elem hJ ha hb hmoved hsJ hs hc hbsc

private theorem wc813pstep_central_of_commuting_conjugates {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) {s : Q} (hsJ : s ∈ J) (hs : s * s = 1)
    (h : ∀ w ∈ J, ∀ l ∈ J, ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) * l =
      l * ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹)))) :
    ∀ l ∈ J, s * l = l * s :=
  central_of_commuting_conjugates hJ hsJ hs h

theorem Cfg813.false_of_normalizing_of_moved (hF1 : InvolutionCentralizerFact)
    (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) (hJ5 : OddShape5 J)
    {a b : Q} (ha : a ∈ A) (hb : b ∈ A) (hb1 : b ≠ 1) (hbJ : b ∈ normalizer (J : Set Q))
    (hmoved : conjSubgroup J a ≠ J) : False := by
  classical
  have hbb : b * b = 1 := by simpa [pow_two] using h.A_elem.2 b hb
  have hx : ∀ x ∈ J, x * b = b * x → ∀ l ∈ J, (x * x) * l = l * (x * x) :=
    wc813pstep_sq_central_of_commute h hJ ha hb hb1 hmoved
  obtain ⟨s, hsJ, hs, c, hc, hbsc⟩ := hF1 Q J b hJ5 hbJ hbb hx
  have h2 : ∀ w ∈ J, ∀ l ∈ J, ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) * l =
      l * ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) :=
    wc813pstep_sq_central_of_decomp h hJ ha hb hmoved hsJ hs hc hbsc
  have hs_cent : ∀ l ∈ J, s * l = l * s :=
    wc813pstep_central_of_commuting_conjugates hJ hsJ hs h2
  have hs1 : s = 1 := by
    have hmem : (⟨s, hsJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hs_cent l l.2).symm
    have hdvd1 : orderOf (⟨s, hsJ⟩ : ↥J) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa [pow_two] using hs)
    have hdvd2 : orderOf (⟨s, hsJ⟩ : ↥J) ∣ Nat.card (Subgroup.center ↥J) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have hodd : Odd (Nat.card (Subgroup.center ↥J)) := hJ5.2.1
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center ↥J)) := Nat.coprime_two_left.mpr hodd
    have h1 : orderOf (⟨s, hsJ⟩ : ↥J) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd1 hdvd2)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have hbC : b ∈ centralizer (J : Set Q) := by
    rw [hbsc, hs1, one_mul]; exact hc
  obtain ⟨x, hxJ, l, hlJ, hne⟩ := wc813pstep_exists_sq_not_comm hJ
  have hxx : x * x * l = l * x * x := by
    simpa [mul_assoc] using hx x hxJ (Subgroup.mem_centralizer_iff.mp hbC x hxJ) l hlJ
  exact hne hxx

theorem Cfg813.A_le_normalizer (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) :
    A ≤ normalizer (J : Set Q) := by
  intro a ha
  by_contra hna
  have hmoved : conjSubgroup J a ≠ J := fun hEq =>
    hna (conjSubgroup_eq_iff_mem_normalizer.mp hEq)
  obtain ⟨b, hbA, hb1, hbJ⟩ := h.exists_normalizing_of_moved hJ ha hmoved
  exact h.false_of_normalizing_of_moved hF1 hJ (h.oddShape5 hF0 hJ) ha hbA hb1 hbJ hmoved

private theorem wc813pstep_eq_bot_of_isPGroup_odd {H : Subgroup Q} (h2 : IsPGroup 2 H)
    (hodd : Odd (Nat.card ↥H)) : H = ⊥ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := by
      rw [Nat.even_pow]
      exact ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (hk.symm ▸ heven)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq H hk

private theorem wc813pstep_inf_centralizer_odd (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q))) := by
  have hmap : J ⊓ centralizer (J : Set Q) =
      (Subgroup.center ↥J).map J.subtype := by
    ext x
    constructor
    · rintro ⟨hxJ, hxC⟩
      refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
      exact Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩))
  rw [hmap]
  have hcard : Nat.card ((Subgroup.center ↥J).map J.subtype) = Nat.card (Subgroup.center ↥J) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥J) J.subtype
      J.subtype_injective).toEquiv.symm
  rw [hcard]
  exact h.center_odd hJ

theorem Cfg813.inf_centralizer_eq_bot (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hJ5 : OddShape5 J) (hAJ : A ≤ normalizer (J : Set Q))
    (hne : ¬ A ≤ centralizer (J : Set Q)) : A ⊓ centralizer (J : Set Q) = ⊥ := by
  classical
  rcases Subgroup.bot_or_exists_ne_one (A ⊓ centralizer (J : Set Q)) with hbot | ⟨b, hb, hb1⟩
  · exact hbot
  · exfalso
    have hbA : b ∈ A := (Subgroup.mem_inf.mp hb).1
    have hbC : b ∈ centralizer (J : Set Q) := (Subgroup.mem_inf.mp hb).2
    apply hne
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let W : Set Q := {γ | ∃ y ∈ (⊤ : Subgroup Q) ⊓ centralizer ({b} : Set Q), γ = y * a * y⁻¹}
    have hW : IsElemAbelian 2 (Subgroup.closure W) := h.K1 a ha b hbA hb1
    have haW : a ∈ W :=
      ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top 1, (centralizer _).one_mem⟩, by simp⟩
    have hgen : ∀ y ∈ J, y * a * y⁻¹ ∈ W := by
      intro y hy
      refine ⟨y, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hbC y hy
    have hJW : J ≤ Subgroup.normalizer (W : Set Q) := by
      intro j hj
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        have hy'b : y' * b = b * y' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy').2
        have hjb : j * b = b * j := Subgroup.mem_centralizer_iff.mp hbC j hj
        refine ⟨j * y', Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩, by group⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [mul_assoc, hy'b, ← mul_assoc, hjb, mul_assoc]
      · rintro ⟨y', hy', hyeq⟩
        have hy'b : y' * b = b * y' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy').2
        have hjb : j⁻¹ * b = b * j⁻¹ := Subgroup.mem_centralizer_iff.mp hbC j⁻¹ (J.inv_mem hj)
        refine ⟨j⁻¹ * y', Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          rw [mul_assoc, hy'b, ← mul_assoc, hjb, mul_assoc]
        · calc y = j⁻¹ * (j * y * j⁻¹) * j := by group
            _ = j⁻¹ * (y' * a * y'⁻¹) * j := by rw [hyeq]
            _ = (j⁻¹ * y') * a * (j⁻¹ * y')⁻¹ := by group
    have hJWc : J ≤ Subgroup.normalizer (Subgroup.closure W : Set Q) :=
      hJW.trans (Subgroup.normalizer_le_normalizer_closure W)
    have hnorm : ((Subgroup.closure W ⊓ J).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        ((le_inf hJWc Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
    have hWc2 : IsPGroup 2 (Subgroup.closure W) := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro y
      exact ⟨1, by
        rw [pow_one]
        exact orderOf_dvd_iff_pow_eq_one.mpr
          (Subtype.ext (by simpa using hW.2 (y : Q) y.2))⟩
    have hoddJ : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q))) :=
      wc813pstep_inf_centralizer_odd h hJ
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hJ.2.2
        ((Subgroup.closure W ⊓ J).subgroupOf J) with hcenter | htop
    · have hleC : Subgroup.closure W ⊓ J ≤ centralizer (J : Set Q) := by
        rintro y ⟨hyW, hyJ⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hmem : (⟨y, hyJ⟩ : ↥J) ∈ (Subgroup.closure W ⊓ J).subgroupOf J := by
          rw [Subgroup.mem_subgroupOf]; exact ⟨hyW, hyJ⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcenter hmem) ⟨z, hz⟩)
      have hbotWJ : Subgroup.closure W ⊓ J = ⊥ :=
        wc813pstep_eq_bot_of_isPGroup_odd (hWc2.to_le inf_le_left)
          (hoddJ.of_dvd_nat (Subgroup.card_dvd_of_le (le_inf inf_le_right hleC)))
      have hcW : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.closure W :=
        (Subgroup.closure W).mul_mem (Subgroup.subset_closure (hgen x hx))
          ((Subgroup.closure W).inv_mem (Subgroup.subset_closure haW))
      have hcJ : x * a * x⁻¹ * a⁻¹ ∈ J := by
        have haJ : a * x⁻¹ * a⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp (hAJ ha) x⁻¹).1 (J.inv_mem hx)
        have : x * (a * x⁻¹ * a⁻¹) ∈ J := J.mul_mem hx haJ
        simpa [mul_assoc] using this
      have hc : x * a * x⁻¹ * a⁻¹ = 1 := by
        have : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.closure W ⊓ J := ⟨hcW, hcJ⟩
        rw [hbotWJ] at this
        exact Subgroup.mem_bot.mp this
      have h1 : x * a * x⁻¹ = a := by
        have := congrArg (fun t => t * a) hc
        simpa [mul_assoc] using this
      calc x * a = (x * a * x⁻¹) * x := by group
        _ = a * x := by rw [h1]
    · have hJleW : J ≤ Subgroup.closure W := by
        intro y hy
        have : (⟨y, hy⟩ : ↥J) ∈ (Subgroup.closure W ⊓ J).subgroupOf J := by
          rw [htop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1
      haveI : IsMulCommutative ↥J := isMulCommutative_iff.mpr fun y z =>
        Subtype.ext (IsElemAbelian.comm hW (hJleW y.2) (hJleW z.2))
      haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
      haveI : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
      exact (Group.IsPerfect.not_isMulCommutative ↥J inferInstance).elim

theorem Cfg813.A_le_sup_centralizer (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤)
    (hne : ¬ A ≤ centralizer (J : Set Q)) : A ≤ J ⊔ centralizer (J : Set Q) :=
  hF2 Q J A (h.oddShape5 hF0 hJ) (h.A_le_normalizer hF0 hF1 hJ) h.A_elem h.A_card
    (h.inf_centralizer_eq_bot hJ (h.oddShape5 hF0 hJ) (h.A_le_normalizer hF0 hF1 hJ) hne)
    (K1In.of_top J h.K1)

private theorem wc813pstep_relIndex_inf_eq_of_sup_eq {B R S : Subgroup Q} (hBS : B ≤ S)
    (hRS : R ≤ S) (hsup : B ⊔ R = S) (hRn : (R.subgroupOf S).Normal) :
    (B ⊓ R).relIndex B = R.relIndex S := by
  haveI : (R.subgroupOf S).Normal := hRn
  have hsup' : (B.subgroupOf S) ⊔ (R.subgroupOf S) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBS hRS, hsup]
    exact Subgroup.subgroupOf_self S
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf S) (K := R.subgroupOf S)
  rw [hsup', Subgroup.relIndex_top_right] at h1
  have h2 : (R.subgroupOf S).relIndex (B.subgroupOf S) = R.relIndex B :=
    Subgroup.relIndex_subgroupOf hBS
  calc (B ⊓ R).relIndex B = R.relIndex B := Subgroup.inf_relIndex_left (H := B) (K := R)
    _ = (R.subgroupOf S).relIndex (B.subgroupOf S) := h2.symm
    _ = (R.subgroupOf S).index := h1.symm
    _ = R.relIndex S := rfl

private theorem wc813pstep_card_sup_mul_card_inf {A B : Subgroup Q}
    (hAB : A ≤ normalizer (B : Set Q)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hBn : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hAB Subgroup.le_normalizer)
  have hrel : (A ⊓ B).relIndex A = B.relIndex (A ⊔ B) :=
    wc813pstep_relIndex_inf_eq_of_sup_eq le_sup_left le_sup_right rfl hBn
  have hA := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := A)
  have hB := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  rw [inf_of_le_left (inf_le_left : A ⊓ B ≤ A)] at hA
  rw [inf_of_le_left le_sup_right] at hB
  rw [hrel] at hA
  rw [← hB, ← hA]
  ring

private theorem wc813pstep_normalizer_le_normalizer_centralizer {J : Subgroup Q} :
    normalizer (J : Set Q) ≤ normalizer ((centralizer (J : Set Q) : Subgroup Q) : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro j hj
    have hg' : g⁻¹ ∈ normalizer (J : Set Q) := (normalizer (J : Set Q)).inv_mem hg
    have hconj : g⁻¹ * j * g ∈ J := by
      simpa using (Subgroup.mem_normalizer_iff.mp hg' j).1 hj
    have h1 := hx (g⁻¹ * j * g) hconj
    calc j * (g * x * g⁻¹) = g * ((g⁻¹ * j * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * j := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro j hj
    have hconj : g * j * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hg j).1 hj
    have h1 := hx (g * j * g⁻¹) hconj
    calc j * x = g⁻¹ * ((g * j * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * j * g⁻¹)) * g := by rw [h1]
      _ = x * j := by group

private theorem wc813pstep_sylow_eq_sup {J C P : Subgroup Q} (hJC : J ≤ centralizer (C : Set Q))
    (hCJ : C ≤ normalizer (J : Set Q)) (hodd : Odd (Nat.card ↥(J ⊓ C)))
    (hP : IsSylowIn 2 P (J ⊔ C)) :
    (P ⊓ J) ⊔ (P ⊓ C) = P := by
  have hJD : J ≤ J ⊔ C := le_sup_left
  have hCD : C ≤ J ⊔ C := le_sup_right
  have hJnorm : J ≤ normalizer (C : Set Q) := hJC.trans (Subgroup.centralizer_le_normalizer _)
  have hD_le : J ⊔ C ≤ normalizer (J : Set Q) := sup_le Subgroup.le_normalizer hCJ
  have hPJ : IsSylowIn 2 (P ⊓ J) J :=
    IsSylowIn.inf_normal hP hJD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJD).mpr hD_le)
  have hPC : IsSylowIn 2 (P ⊓ C) C :=
    IsSylowIn.inf_normal hP hCD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCD).mpr
        (sup_le hJnorm Subgroup.le_normalizer))
  have hbot : (P ⊓ J) ⊓ (P ⊓ C) = ⊥ := by
    have hleZ : (P ⊓ J) ⊓ (P ⊓ C) ≤ J ⊓ C :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    exact wc813pstep_eq_bot_of_isPGroup_odd
      (hP.isPGroup.to_le (inf_le_left.trans inf_le_left))
      (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hleZ))
  have hP'card : Nat.card ↥((P ⊓ J) ⊔ (P ⊓ C)) =
      Nat.card ↥(P ⊓ J) * Nat.card ↥(P ⊓ C) := by
    have hAB : P ⊓ J ≤ normalizer ((P ⊓ C : Subgroup Q) : Set Q) :=
      (inf_le_right : P ⊓ J ≤ J).trans (hJC.trans
        ((Subgroup.centralizer_le (inf_le_right : P ⊓ C ≤ C)).trans
          (Subgroup.centralizer_le_normalizer _)))
    have hform := wc813pstep_card_sup_mul_card_inf hAB
    rw [hbot, Subgroup.card_bot, mul_one] at hform
    exact hform
  have hfac : (Nat.card ↥(J ⊔ C)).factorization 2 =
      (Nat.card ↥J).factorization 2 + (Nat.card ↥C).factorization 2 := by
    have hform : Nat.card ↥(J ⊔ C) * Nat.card ↥(J ⊓ C) = Nat.card ↥J * Nat.card ↥C :=
      wc813pstep_card_sup_mul_card_inf hJnorm
    have hZfac : (Nat.card ↥(J ⊓ C)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
    have h1 := congrArg (fun n : ℕ => n.factorization 2) hform
    rw [Nat.factorization_mul (Nat.card_pos.ne' : Nat.card ↥(J ⊔ C) ≠ 0)
        (Nat.card_pos.ne' : Nat.card ↥(J ⊓ C) ≠ 0),
      Nat.factorization_mul (Nat.card_pos.ne' : Nat.card ↥J ≠ 0)
        (Nat.card_pos.ne' : Nat.card ↥C ≠ 0)] at h1
    simp only [Finsupp.coe_add, Pi.add_apply, hZfac, add_zero] at h1
    exact h1
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  rw [hP'card]
  exact le_of_eq (by
    calc Nat.card ↥P = 2 ^ (Nat.card ↥(J ⊔ C)).factorization 2 := hP.card_eq
      _ = 2 ^ ((Nat.card ↥J).factorization 2 + (Nat.card ↥C).factorization 2) := by rw [hfac]
      _ = 2 ^ (Nat.card ↥J).factorization 2 * 2 ^ (Nat.card ↥C).factorization 2 :=
          pow_add _ _ _
      _ = Nat.card ↥(P ⊓ J) * Nat.card ↥(P ⊓ C) := by rw [← hPJ.card_eq, ← hPC.card_eq])

private theorem wc813pstep_conjAct_smul (q : Q) (J : Subgroup Q) :
    ConjAct.toConjAct q • J = conjSubgroup J q⁻¹ := by
  rw [show ConjAct.toConjAct q • J = J.map (MulAut.conj q) from rfl]
  simp [conjSubgroup]

theorem Cfg813.isSylowIn_inf_normalizer (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) :
    IsSylowIn 2 (T ⊓ normalizer (J : Set Q)) (normalizer (J : Set Q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Q := normalizer (J : Set Q) with hN
  have hstabQ : MulAction.stabilizer (ConjAct Q) J =
      N.comap ConjAct.ofConjAct.toMonoidHom := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    change g • J = J ↔ ConjAct.ofConjAct g ∈ N
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  letI : MulAction T (Subgroup Q) :=
    MulAction.compHom (α := Subgroup Q) (ConjAct.toConjAct.toMonoidHom.comp T.subtype)
  have hstabT : MulAction.stabilizer T J = (N ⊓ T).subgroupOf T := by
    ext t
    rw [MulAction.mem_stabilizer_iff]
    change ConjAct.toConjAct (t : Q) • J = J ↔ (t : Q) ∈ N ⊓ T
    rw [Subgroup.mem_inf]
    constructor
    · intro ht
      exact ⟨by
        have h1 : ConjAct.toConjAct (t : Q) ∈ MulAction.stabilizer (ConjAct Q) J := ht
        rwa [hstabQ] at h1, t.2⟩
    · rintro ⟨hNt, -⟩
      exact show ConjAct.toConjAct (t : Q) ∈ MulAction.stabilizer (ConjAct Q) J from by
        rwa [hstabQ]
  have horbit : MulAction.orbit T J = MulAction.orbit (ConjAct Q) J := by
    ext K
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨ConjAct.toConjAct (t : Q), rfl⟩
    · rintro ⟨g, rfl⟩
      have hg : g • J = conjSubgroup J (ConjAct.ofConjAct g)⁻¹ := by
        simpa using wc813pstep_conjAct_smul (ConjAct.ofConjAct g) J
      have hcomp : IsComponentOf (conjSubgroup J (ConjAct.ofConjAct g)⁻¹) ⊤ := by
        have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
          (MulAut.conj (ConjAct.ofConjAct g)) J).mpr hJ
        simpa [conjSubgroup, inv_inv] using hh
      obtain ⟨t, ht, htJ⟩ := h.component_conj hJ hcomp
      refine ⟨⟨t⁻¹, T.inv_mem ht⟩, ?_⟩
      show ConjAct.toConjAct (t⁻¹) • J = g • J
      rw [wc813pstep_conjAct_smul, hg]
      rw [show (t⁻¹ : Q)⁻¹ = t by simp]
      exact htJ.symm
  have hidxQ : (MulAction.stabilizer (ConjAct Q) J).index = N.index := by
    rw [hstabQ]
    exact Subgroup.index_comap_of_surjective (H := N)
      (f := ConjAct.ofConjAct.toMonoidHom) ConjAct.ofConjAct.surjective
  have hidxT : (MulAction.stabilizer T J).index = (N ⊓ T).relIndex T := by
    rw [hstabT]; rfl
  have hidx : N.index = (T ⊓ N).relIndex T := by
    have hQ : (MulAction.stabilizer (ConjAct Q) J).index =
        (MulAction.orbit (ConjAct Q) J).ncard := MulAction.index_stabilizer (ConjAct Q) J
    have hT : (MulAction.stabilizer T J).index = (MulAction.orbit T J).ncard :=
      MulAction.index_stabilizer T J
    rw [← hidxQ, hQ, ← horbit, ← hT, hidxT, inf_comm]
  have hrel : (T ⊓ N).relIndex N = T.index := by
    have h1 : (T ⊓ N).relIndex T * T.index = (T ⊓ N).index :=
      Subgroup.relIndex_mul_index inf_le_left
    have h2 : (T ⊓ N).relIndex N * N.index = (T ⊓ N).index :=
      Subgroup.relIndex_mul_index inf_le_right
    have ha : (T ⊓ N).relIndex T ≠ 0 := by
      intro hzero
      have hc := Subgroup.relIndex_mul_card (H := T ⊓ N) (K := T)
      rw [inf_of_le_left inf_le_left, hzero, zero_mul] at hc
      exact Nat.card_pos.ne' hc.symm
    have h3 : (T ⊓ N).relIndex T * T.index =
        (T ⊓ N).relIndex T * (T ⊓ N).relIndex N := by
      calc (T ⊓ N).relIndex T * T.index = (T ⊓ N).index := h1
        _ = (T ⊓ N).relIndex N * N.index := h2.symm
        _ = (T ⊓ N).relIndex N * (T ⊓ N).relIndex T := by rw [hidx]
        _ = (T ⊓ N).relIndex T * (T ⊓ N).relIndex N := mul_comm _ _
    exact (mul_left_cancel₀ ha h3).symm
  refine ⟨inf_le_right, h.sylow.isPGroup.to_le inf_le_left, ?_⟩
  rw [hrel, ← Subgroup.relIndex_top_right]
  exact h.sylow.not_dvd_relIndex

theorem Cfg813.isSylowIn_inf_component (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : IsSylowIn 2 (T ⊓ J) J := by
  have hN := IsSylowIn.inf_normal (h.isSylowIn_inf_normalizer hJ)
    (Subgroup.le_normalizer : J ≤ normalizer (J : Set Q)) Subgroup.normal_in_normalizer
  rwa [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer : J ≤ normalizer (J : Set Q))] at hN

theorem Cfg813.exists_decomp (hF0 : OddSchurMultiplierFact) (h : Cfg813 T A B R L₀)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤) {a : Q} (haT : a ∈ T)
    (haJ : a ∈ J ⊔ centralizer (J : Set Q)) :
    ∃ ℓ ∈ T ⊓ J, ∃ c ∈ T ⊓ centralizer (J : Set Q), a = ℓ * c := by
  classical
  set C : Subgroup Q := centralizer (J : Set Q) with hC
  set D : Subgroup Q := J ⊔ C with hD
  set P : Subgroup Q := T ⊓ D with hP
  have hJcent : J ≤ centralizer (C : Set Q) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc j hj).symm
  have hJnorm : J ≤ normalizer (C : Set Q) :=
    hJcent.trans (Subgroup.centralizer_le_normalizer (C : Set Q))
  have hCnorm : C ≤ normalizer (J : Set Q) := Subgroup.centralizer_le_normalizer _
  have hNJ : normalizer (J : Set Q) ≤ normalizer (C : Set Q) :=
    wc813pstep_normalizer_le_normalizer_centralizer
  have hD_le : D ≤ normalizer (J : Set Q) := by
    rw [hD]
    exact sup_le Subgroup.le_normalizer hCnorm
  have hDnorm : (D.subgroupOf (normalizer (J : Set Q))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD_le).mpr (by
      rw [hD]
      exact (le_inf le_rfl hNJ).trans (Subgroup.inf_normalizer_le_normalizer_sup J C))
  have hPD : IsSylowIn 2 P D := by
    have h0 := IsSylowIn.inf_normal (h.isSylowIn_inf_normalizer hJ) hD_le hDnorm
    rw [show (T ⊓ normalizer (J : Set Q)) ⊓ D = P by
      rw [hP, inf_assoc, inf_eq_right.mpr hD_le]] at h0
    exact h0
  have hZodd : Odd (Nat.card ↥(J ⊓ C)) := wc813pstep_inf_centralizer_odd h hJ
  have hPeq : (P ⊓ J) ⊔ (P ⊓ C) = P := wc813pstep_sylow_eq_sup hJcent hCnorm hZodd hPD
  have hAB : P ⊓ J ≤ normalizer ((P ⊓ C : Subgroup Q) : Set Q) :=
    (inf_le_right : P ⊓ J ≤ J).trans (hJcent.trans
      ((Subgroup.centralizer_le (inf_le_right : P ⊓ C ≤ C)).trans
        (Subgroup.centralizer_le_normalizer _)))
  have haP : a ∈ P := Subgroup.mem_inf.mpr ⟨haT, haJ⟩
  have hmem : a ∈ ((P ⊓ J : Subgroup Q) : Set Q) * ((P ⊓ C : Subgroup Q) : Set Q) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P ⊓ J) (P ⊓ C) hAB, hPeq]
    exact haP
  rw [Set.mem_mul] at hmem
  obtain ⟨ℓ, hℓ, c, hc, hlc⟩ := hmem
  exact ⟨ℓ, ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hℓ).1).1, (Subgroup.mem_inf.mp hℓ).2⟩,
    c, ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1, (Subgroup.mem_inf.mp hc).2⟩, hlc.symm⟩

private theorem wc813pstep_inf_inf_centralizer_eq_bot {J : Subgroup Q} (hT2 : IsPGroup 2 T)
    (hodd : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q)))) :
    T ⊓ (J ⊓ centralizer (J : Set Q)) = ⊥ :=
  wc813pstep_eq_bot_of_isPGroup_odd (hT2.to_le inf_le_left)
    (hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

private theorem wc813pstep_astar_unique {J : Subgroup Q} (hT2 : IsPGroup 2 T)
    (hodd : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q))))
    {ℓ ℓ' c c' : Q} (hℓ : ℓ ∈ Astar T J A) (hℓ' : ℓ' ∈ Astar T J A)
    (hc : c ∈ T ⊓ centralizer (J : Set Q)) (hc' : c' ∈ T ⊓ centralizer (J : Set Q))
    (heq : ℓ * c = ℓ' * c') : ℓ = ℓ' := by
  have hℓT : ℓ ∈ T := (mem_Astar.mp hℓ).1.1
  have hℓJ : ℓ ∈ J := (mem_Astar.mp hℓ).1.2
  have hℓ'T : ℓ' ∈ T := (mem_Astar.mp hℓ').1.1
  have hℓ'J : ℓ' ∈ J := (mem_Astar.mp hℓ').1.2
  have hcC : c ∈ centralizer (J : Set Q) := (Subgroup.mem_inf.mp hc).2
  have hc'C : c' ∈ centralizer (J : Set Q) := (Subgroup.mem_inf.mp hc').2
  have hmem : ℓ'⁻¹ * ℓ ∈ T ⊓ (J ⊓ centralizer (J : Set Q)) := by
    refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.inv_mem hℓ'T) hℓT, ?_⟩
    refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.inv_mem hℓ'J) hℓJ, ?_⟩
    have h1 : ℓ'⁻¹ * ℓ = c' * c⁻¹ := by
      have h := congrArg (fun x => ℓ'⁻¹ * x * c⁻¹) heq
      simpa [mul_assoc] using h
    rw [h1]
    exact (centralizer (J : Set Q)).mul_mem hc'C
      ((centralizer (J : Set Q)).inv_mem hcC)
  have hbot : T ⊓ (J ⊓ centralizer (J : Set Q)) = ⊥ :=
    wc813pstep_eq_bot_of_isPGroup_odd (hT2.to_le inf_le_left)
      (hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  rw [hbot] at hmem
  have h1 : ℓ'⁻¹ * ℓ = 1 := Subgroup.mem_bot.mp hmem
  calc ℓ = ℓ' * (ℓ'⁻¹ * ℓ) := by group
    _ = ℓ' * 1 := by rw [h1]
    _ = ℓ' := mul_one ℓ'

theorem Cfg813.astar_facts (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hne : ¬ A ≤ centralizer (J : Set Q)) :
    Astar T J A ≤ T ⊓ J ∧ IsElemAbelian 2 (Astar T J A) ∧ Nat.card (Astar T J A) = 4 ∧
      ∀ a ∈ A, ∃ ℓ ∈ Astar T J A, ∃ c ∈ T ⊓ centralizer (J : Set Q), a = ℓ * c := by
  classical
  have hJ5 : OddShape5 J := h.oddShape5 hF0 hJ
  have hAJ : A ≤ normalizer (J : Set Q) := h.A_le_normalizer hF0 hF1 hJ
  have hAsup : A ≤ J ⊔ centralizer (J : Set Q) :=
    h.A_le_sup_centralizer hF0 hF1 hF2 hJ hne
  have hT2 : IsPGroup 2 T := h.sylow.isPGroup
  have hodd : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q))) :=
    wc813pstep_inf_centralizer_odd h hJ
  have hle : Astar T J A ≤ T ⊓ J := fun ℓ hℓ => (mem_Astar.mp hℓ).1
  have hdec : ∀ a ∈ A, ∃ ℓ ∈ Astar T J A, ∃ c ∈ T ⊓ centralizer (J : Set Q), a = ℓ * c := by
    intro a ha
    obtain ⟨ℓ, hℓ, c, hc, hlc⟩ := h.exists_decomp hF0 hJ (h.A_le ha) (hAsup ha)
    exact ⟨ℓ, mem_Astar.mpr ⟨hℓ, c, hc, hlc ▸ ha⟩, c, hc, hlc⟩
  have huniq : ∀ {ℓ ℓ' c c' : Q}, ℓ ∈ Astar T J A → ℓ' ∈ Astar T J A →
      c ∈ T ⊓ centralizer (J : Set Q) → c' ∈ T ⊓ centralizer (J : Set Q) →
      ℓ * c = ℓ' * c' → ℓ = ℓ' :=
    fun hℓ hℓ' hc hc' heq => wc813pstep_astar_unique hT2 hodd hℓ hℓ' hc hc' heq
  let projFun : ↥A → ↥(Astar T J A) := fun a =>
    ⟨Classical.choose (hdec a a.2), (Classical.choose_spec (hdec a a.2)).1⟩
  have proj_spec : ∀ a : ↥A, ∃ c ∈ T ⊓ centralizer (J : Set Q),
      (a : Q) = (projFun a : Q) * c := by
    intro a
    obtain ⟨c, hc, heq⟩ := (Classical.choose_spec (hdec a a.2)).2
    exact ⟨c, hc, heq⟩
  have proj_mul : ∀ a b : ↥A, projFun (a * b) = projFun a * projFun b := by
    intro a b
    obtain ⟨ca, hca, haeq⟩ := proj_spec a
    obtain ⟨cb, hcb, hbeq⟩ := proj_spec b
    obtain ⟨cab, hcab, habeq⟩ := proj_spec (a * b)
    have hcomm : (projFun b : Q) * ca = ca * (projFun b : Q) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hca).2 _
        (hle (projFun b).2).2
    have hmemc : ca * cb ∈ T ⊓ centralizer (J : Set Q) :=
      Subgroup.mem_inf.mpr
        ⟨T.mul_mem (Subgroup.mem_inf.mp hca).1 (Subgroup.mem_inf.mp hcb).1,
          (centralizer (J : Set Q)).mul_mem (Subgroup.mem_inf.mp hca).2
            (Subgroup.mem_inf.mp hcb).2⟩
    have hL : (projFun (a * b) : Q) * cab =
        ((projFun a : Q) * (projFun b : Q)) * (ca * cb) := by
      rw [← habeq]
      calc (a : Q) * (b : Q) = ((projFun a : Q) * ca) * ((projFun b : Q) * cb) := by
            rw [haeq, hbeq]
        _ = (projFun a : Q) * (ca * ((projFun b : Q) * cb)) := by group
        _ = (projFun a : Q) * ((ca * (projFun b : Q)) * cb) := by group
        _ = (projFun a : Q) * (((projFun b : Q) * ca) * cb) := by rw [← hcomm]
        _ = ((projFun a : Q) * (projFun b : Q)) * (ca * cb) := by group
    exact Subtype.ext (huniq (projFun (a * b)).2
      ((Astar T J A).mul_mem (projFun a).2 (projFun b).2) hcab hmemc hL)
  have proj_one : projFun 1 = 1 := by
    obtain ⟨c, hc, heq⟩ := proj_spec (1 : ↥A)
    have hmem1 : (1 : Q) ∈ T ⊓ centralizer (J : Set Q) :=
      Subgroup.mem_inf.mpr ⟨T.one_mem, (centralizer (J : Set Q)).one_mem⟩
    have hL : (projFun 1 : Q) * c = (1 : Q) * 1 := by
      rw [← heq]; simp
    exact Subtype.ext (huniq (projFun 1).2 (Astar T J A).one_mem hc hmem1 hL)
  let φ : ↥A →* ↥(Astar T J A) :=
    { toFun := projFun, map_one' := proj_one, map_mul' := proj_mul }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hab' : (projFun a : Q) = (projFun b : Q) := congrArg Subtype.val hab
    obtain ⟨ca, hca, haeq⟩ := proj_spec a
    obtain ⟨cb, hcb, hbeq⟩ := proj_spec b
    have hcaC : ca ∈ centralizer (J : Set Q) := (Subgroup.mem_inf.mp hca).2
    have hcbC : cb ∈ centralizer (J : Set Q) := (Subgroup.mem_inf.mp hcb).2
    have hℓJ : (projFun a : Q) ∈ J := (hle (projFun a).2).2
    have hcomm : (projFun a : Q) * (ca * cb⁻¹) = (ca * cb⁻¹) * (projFun a : Q) :=
      Subgroup.mem_centralizer_iff.mp
        ((centralizer (J : Set Q)).mul_mem hcaC ((centralizer (J : Set Q)).inv_mem hcbC))
        _ hℓJ
    have hprod : (a : Q) * (b : Q)⁻¹ = ca * cb⁻¹ := by
      calc (a : Q) * (b : Q)⁻¹ = (projFun a : Q) * ca * ((projFun b : Q) * cb)⁻¹ := by
            rw [haeq, hbeq]
        _ = (projFun a : Q) * ca * (cb⁻¹ * (projFun b : Q)⁻¹) := by rw [mul_inv_rev]
        _ = (projFun a : Q) * (ca * cb⁻¹) * (projFun a : Q)⁻¹ := by rw [hab']; group
        _ = ca * cb⁻¹ := by rw [hcomm]; group
    have hmem : (a : Q) * (b : Q)⁻¹ ∈ A ⊓ centralizer (J : Set Q) :=
      Subgroup.mem_inf.mpr ⟨A.mul_mem a.2 (A.inv_mem b.2), hprod ▸
        (centralizer (J : Set Q)).mul_mem hcaC ((centralizer (J : Set Q)).inv_mem hcbC)⟩
    have hbot : A ⊓ centralizer (J : Set Q) = ⊥ :=
      h.inf_centralizer_eq_bot hJ hJ5 hAJ hne
    rw [hbot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))
  have hφsurj : Function.Surjective φ := by
    intro ℓ
    obtain ⟨c, hc, hlc⟩ := (mem_Astar.mp ℓ.2).2
    refine ⟨⟨ℓ * c, hlc⟩, ?_⟩
    obtain ⟨c', hc', heq⟩ := proj_spec (⟨ℓ * c, hlc⟩ : ↥A)
    have hL : (projFun ⟨ℓ * c, hlc⟩ : Q) * c' = ℓ * c := by
      rw [← heq]
    exact Subtype.ext (huniq (projFun ⟨ℓ * c, hlc⟩).2 ℓ.2 hc' hc hL)
  let e : ↥A ≃* ↥(Astar T J A) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  refine ⟨hle, ?_, ?_, hdec⟩
  · refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm fun x y => ?_
      obtain ⟨a, rfl⟩ := e.toEquiv.surjective x
      obtain ⟨b, rfl⟩ := e.toEquiv.surjective y
      calc e a * e b = e (a * b) := (e.map_mul a b).symm
        _ = e (b * a) := congrArg e (h.A_elem.1.is_comm.comm a b)
        _ = e b * e a := e.map_mul b a
    · intro x hx
      obtain ⟨a, ha⟩ := e.toEquiv.surjective ⟨x, hx⟩
      have hx' : x = (e a : Q) := (congrArg Subtype.val ha).symm
      rw [hx']
      have haa : a * a = 1 := Subtype.ext (by
        simpa [Subgroup.coe_mul, Subgroup.coe_one, pow_two]
          using h.A_elem.2 (a : Q) a.2)
      change ((e a : ↥(Astar T J A)) : Q) ^ 2 = 1
      rw [pow_two, ← Subgroup.coe_mul, ← e.map_mul, haa, e.map_one, Subgroup.coe_one]
  · exact (Nat.card_congr e.toEquiv).symm.trans h.A_card

theorem Cfg813.astar_k1 (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hne : ¬ A ≤ centralizer (J : Set Q)) :
    K1In J (Astar T J A) := by
  classical
  obtain ⟨_, hAstarel, _, _⟩ := h.astar_facts hF0 hF1 hF2 hJ hne
  have hT2 : IsPGroup 2 T := h.sylow.isPGroup
  have hodd : Odd (Nat.card ↥(J ⊓ centralizer (J : Set Q))) :=
    wc813pstep_inf_centralizer_odd h hJ
  have hbot : T ⊓ (J ⊓ centralizer (J : Set Q)) = ⊥ :=
    wc813pstep_inf_inf_centralizer_eq_bot hT2 hodd
  intro α hα β hβ hβ1
  obtain ⟨hαTA, cα, hcα, hαA⟩ := mem_Astar.mp hα
  obtain ⟨hβTA, cβ, hcβ, hβA⟩ := mem_Astar.mp hβ
  have hβA_ne : β * cβ ≠ 1 := by
    intro hzero
    have hβC : β ∈ centralizer (J : Set Q) := by
      have hβeq : β = cβ⁻¹ := eq_inv_of_mul_eq_one_left hzero
      rw [hβeq]
      exact (centralizer (J : Set Q)).inv_mem (Subgroup.mem_inf.mp hcβ).2
    have hmem : β ∈ T ⊓ (J ⊓ centralizer (J : Set Q)) :=
      Subgroup.mem_inf.mpr ⟨hβTA.1, Subgroup.mem_inf.mpr ⟨hβTA.2, hβC⟩⟩
    rw [hbot] at hmem
    exact hβ1 (Subgroup.mem_bot.mp hmem)
  have hW : IsElemAbelian 2 (Subgroup.closure
      {γ : Q | ∃ x ∈ (⊤ : Subgroup Q) ⊓ centralizer ({β * cβ} : Set Q),
        γ = x * (α * cα) * x⁻¹}) :=
    h.K1 (α * cα) hαA (β * cβ) hβA hβA_ne
  have hcα_sq : cα * cα = 1 := by
    have hmem : α * cα ∈ {γ : Q | ∃ x ∈ (⊤ : Subgroup Q) ⊓ centralizer ({β * cβ} : Set Q),
        γ = x * (α * cα) * x⁻¹} :=
      ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top 1, (centralizer _).one_mem⟩, by simp⟩
    have hsq : (α * cα) * (α * cα) = 1 :=
      IsElemAbelian.mul_self_eq_one hW (Subgroup.subset_closure hmem)
    have hαα : α * α = 1 := by simpa [pow_two] using hAstarel.2 α hα
    have hcomm : α * cα = cα * α :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcα).2 α hαTA.2
    have hexp : (α * cα) * (α * cα) = (α * α) * (cα * cα) := by
      calc (α * cα) * (α * cα) = α * (cα * α) * cα := by group
        _ = α * (α * cα) * cα := by rw [hcomm]
        _ = (α * α) * (cα * cα) := by group
    calc cα * cα = (α * α) * (cα * cα) := by rw [hαα, one_mul]
      _ = (α * cα) * (α * cα) := hexp.symm
      _ = 1 := hsq
  have hgen : ∀ x ∈ J ⊓ centralizer ({β} : Set Q),
      x * α * x⁻¹ = (x * (α * cα) * x⁻¹) * cα := by
    intro x hx
    have hxJ : x ∈ J := (Subgroup.mem_inf.mp hx).1
    have hxc : x * cα = cα * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcα).2 x hxJ
    have hxc' : cα * x⁻¹ = x⁻¹ * cα := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) hxc
      simpa [mul_assoc] using h
    rw [show (x * (α * cα) * x⁻¹) * cα = (x * α * x⁻¹) * (cα * cα) by
        calc (x * (α * cα) * x⁻¹) * cα = x * α * (cα * x⁻¹) * cα := by group
          _ = x * α * (x⁻¹ * cα) * cα := by rw [hxc']
          _ = (x * α * x⁻¹) * (cα * cα) := by group,
      hcα_sq, mul_one]
  have hwx : ∀ x ∈ J ⊓ centralizer ({β} : Set Q),
      x * (α * cα) * x⁻¹ ∈ {γ : Q | ∃ x ∈ (⊤ : Subgroup Q) ⊓
        centralizer ({β * cβ} : Set Q), γ = x * (α * cα) * x⁻¹} := by
    intro x hx
    refine ⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxβ : x * β = β * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    have hxcβ : x * cβ = cβ * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcβ).2 x (Subgroup.mem_inf.mp hx).1
    rw [← mul_assoc, hxβ, mul_assoc, hxcβ, ← mul_assoc]
  have hcα_w : ∀ x ∈ J ⊓ centralizer ({β} : Set Q),
      cα * (x * (α * cα) * x⁻¹) = (x * (α * cα) * x⁻¹) * cα := by
    intro x hx
    have hxJ : x ∈ J := (Subgroup.mem_inf.mp hx).1
    have hxc : x * cα = cα * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcα).2 x hxJ
    have hxc' : cα * x⁻¹ = x⁻¹ * cα := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) hxc
      simpa [mul_assoc] using h
    have hgJ : x * α * x⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hxJ hαTA.2) (J.inv_mem hxJ)
    have hcg : cα * (x * α * x⁻¹) = (x * α * x⁻¹) * cα :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcα).2 _ hgJ).symm
    have hgx : x * (α * cα) * x⁻¹ = (x * α * x⁻¹) * cα := by
      calc x * (α * cα) * x⁻¹ = x * α * (cα * x⁻¹) := by group
        _ = x * α * (x⁻¹ * cα) := by rw [hxc']
        _ = (x * α * x⁻¹) * cα := by group
    rw [hgx]
    calc cα * ((x * α * x⁻¹) * cα) = (cα * (x * α * x⁻¹)) * cα := by group
      _ = ((x * α * x⁻¹) * cα) * cα := by rw [hcg]
  refine IsElemAbelian.closure_of_commute (p := 2) ?_ ?_
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    rw [hgen x hx, hgen y hy]
    have hcommW : (x * (α * cα) * x⁻¹) * (y * (α * cα) * y⁻¹) =
        (y * (α * cα) * y⁻¹) * (x * (α * cα) * x⁻¹) :=
      IsElemAbelian.comm hW (Subgroup.subset_closure (hwx x hx))
        (Subgroup.subset_closure (hwx y hy))
    have hcx := hcα_w x hx
    have hcy := hcα_w y hy
    have hmulx : ((x * (α * cα) * x⁻¹) * cα) * ((y * (α * cα) * y⁻¹) * cα) =
        (x * (α * cα) * x⁻¹) * (y * (α * cα) * y⁻¹) := by
      calc ((x * (α * cα) * x⁻¹) * cα) * ((y * (α * cα) * y⁻¹) * cα) =
            (x * (α * cα) * x⁻¹) * (cα * (y * (α * cα) * y⁻¹)) * cα := by group
        _ = (x * (α * cα) * x⁻¹) * ((y * (α * cα) * y⁻¹) * cα) * cα := by rw [hcy]
        _ = (x * (α * cα) * x⁻¹) * (y * (α * cα) * y⁻¹) * (cα * cα) := by group
        _ = (x * (α * cα) * x⁻¹) * (y * (α * cα) * y⁻¹) := by rw [hcα_sq, mul_one]
    have hmuly : ((y * (α * cα) * y⁻¹) * cα) * ((x * (α * cα) * x⁻¹) * cα) =
        (y * (α * cα) * y⁻¹) * (x * (α * cα) * x⁻¹) := by
      calc ((y * (α * cα) * y⁻¹) * cα) * ((x * (α * cα) * x⁻¹) * cα) =
            (y * (α * cα) * y⁻¹) * (cα * (x * (α * cα) * x⁻¹)) * cα := by group
        _ = (y * (α * cα) * y⁻¹) * ((x * (α * cα) * x⁻¹) * cα) * cα := by rw [hcx]
        _ = (y * (α * cα) * y⁻¹) * (x * (α * cα) * x⁻¹) * (cα * cα) := by group
        _ = (y * (α * cα) * y⁻¹) * (x * (α * cα) * x⁻¹) := by rw [hcα_sq, mul_one]
    rw [hmulx, hmuly, hcommW]
  · rintro a ⟨x, hx, rfl⟩
    rw [hgen x hx]
    have hsqW : (x * (α * cα) * x⁻¹) * (x * (α * cα) * x⁻¹) = 1 :=
      IsElemAbelian.mul_self_eq_one hW (Subgroup.subset_closure (hwx x hx))
    have hcx := hcα_w x hx
    have hmul : ((x * (α * cα) * x⁻¹) * cα) * ((x * (α * cα) * x⁻¹) * cα) =
        (x * (α * cα) * x⁻¹) * (x * (α * cα) * x⁻¹) := by
      calc ((x * (α * cα) * x⁻¹) * cα) * ((x * (α * cα) * x⁻¹) * cα) =
            (x * (α * cα) * x⁻¹) * (cα * (x * (α * cα) * x⁻¹)) * cα := by group
        _ = (x * (α * cα) * x⁻¹) * ((x * (α * cα) * x⁻¹) * cα) * cα := by rw [hcx]
        _ = (x * (α * cα) * x⁻¹) * (x * (α * cα) * x⁻¹) * (cα * cα) := by group
        _ = (x * (α * cα) * x⁻¹) * (x * (α * cα) * x⁻¹) := by rw [hcα_sq, mul_one]
    rw [pow_two, hmul, hsqW]

end CFSG.LocalAnalysis.WeakClosure81

end
