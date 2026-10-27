module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE

import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddL2Gen
import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Red
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieCore
import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient
import CFSG.LocalAnalysis.WeakClosure81.SecU1ElemAbelianPair
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsDihedral
import CFSG.GH74.GLS.Bg.TwoGroups.Free2
import CFSG.Quasithin.Vol2.Ch11SecU1Crit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup CFSG.GorensteinWalter

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} [L.Normal] {F : Type} [Field F] [Finite F]

theorem card_inf_centralizer_of_conjNormal_mem_innDiagSub
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hF : L2Field F) (e : ↥L ≃* L2 F) {ε : ℤ}
    (hε1 : ε = 1 ∨ ε = -1) (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {b : Q} (hb2 : orderOf b = 2)
    (hbL : b ∉ L) (hbD : MulAut.conjNormal b ∈ innDiagSub e) :
    (Nat.card ↥(L ⊓ Subgroup.centralizer {b}) : ℤ) = Nat.card F + ε := by
  have hb : b * b = 1 :=
    CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two hb2
  have hσ2 : (MulAut.conjNormal b : MulAut ↥L) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hb, map_one]
  have hinj : Function.Injective (MulAut.conjNormal : Q →* MulAut ↥L) :=
    CFSG.Wreathed.SimpleOddIndexQuotient.conjNormal_injective_of_centralizer_eq_bot
      (G := Q) L hC
  have hσ1 : (MulAut.conjNormal b : MulAut ↥L) ≠ 1 := by
    intro h1
    have hb1 : b = 1 := hinj (by rw [h1, map_one])
    rw [hb1, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  have hσI : (MulAut.conjNormal b : MulAut ↥L) ∉ innAut ↥L := by
    rintro ⟨l, hl⟩
    apply hbL
    have h1 : MulAut.conjNormal (H := L) b = MulAut.conjNormal (H := L) (l : Q) := by
      rw [MulAut.conjNormal_val, ← hl]
    have h2 : b = (l : Q) := hinj h1
    exact h2 ▸ l.2
  have hcard := L2Seitz.diag_type hF e hε1 hε hσ2 hσ1 hbD hσI
  have hfix : L ⊓ Subgroup.centralizer ({b} : Set Q) =
      (CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b)).map L.subtype := by
    ext x
    constructor
    · rintro ⟨hxL, hxc⟩
      exact ⟨⟨x, hxL⟩,
        (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.mem_fixedSubgroup_conjNormal_iff
          L b ⟨x, hxL⟩).2 hxc, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2,
        (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.mem_fixedSubgroup_conjNormal_iff
          L b y).1 hy⟩
  rw [hfix, Subgroup.card_map_of_injective L.subtype_injective]
  exact hcard

theorem l2Field_of_card_sq {F₀ : Type} [Field F₀] [Finite F₀]
    (hF : L2Field F) (h9 : Nat.card F ≠ 9) (hq : Nat.card F₀ ^ 2 = Nat.card F) :
    L2Field F₀ := by
  set q₀ : ℕ := Nat.card F₀ with hq₀def
  have hq₀ : q₀ ^ 2 = Nat.card F := hq
  have hq₀odd : Odd q₀ := by
    have h1 : Odd (q₀ ^ 2) := hq₀.symm ▸ hF.1
    exact (Nat.odd_pow_iff (by norm_num)).mp h1
  have hq₀2 : 2 ≤ q₀ := by
    by_contra h
    have hq1 : q₀ ≤ 1 := by omega
    have hle : q₀ ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hq1 2
    rw [hq₀] at hle
    norm_num at hle
    have h3 := hF.2
    omega
  have hq₀3 : 3 < q₀ := by
    rcases Nat.lt_or_ge 3 q₀ with h | h
    · exact h
    have hle : q₀ ≤ 3 := by omega
    have h3 := hF.2
    interval_cases q₀
    · obtain ⟨t, ht⟩ := hq₀odd
      omega
    · exfalso
      norm_num at hq₀
      exact h9 hq₀.symm
  exact ⟨hq₀odd, hq₀3⟩

theorem exists_involution_ne_centralizer_pgl2 {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : L2Field F₀) {A : PGL2 F₀} (hA2 : orderOf A = 2) :
    ∃ B : PGL2 F₀, B ∈ Subgroup.centralizer ({A} : Set (PGL2 F₀)) ∧ orderOf B = 2 ∧
      B ≠ A := by
  set q₀ : ℕ := Nat.card F₀ with hq₀def
  have hq₀odd : Odd q₀ := hF₀.1
  have hq₀3 : 3 < q₀ := hF₀.2
  have hoddPP : IsOddPrimePower q₀ := by
    rw [hq₀def]
    exact CFSG.GH74.GLS.IVK.isOddPrimePower_of_L2Field hF₀
  obtain ⟨ε₀, hε₀1, hε₀⟩ := L2Seitz.exists_eps hF₀
  obtain ⟨m, hm, ⟨eD⟩⟩ :
      ∃ m : ℕ, ((m : ℤ) = q₀ - ε₀ ∨ (m : ℤ) = q₀ + ε₀) ∧
        Nonempty (↥(Subgroup.centralizer ({A} : Set (PGL2 F₀))) ≃* DihedralGroup m) := by
    have hbranch := pgl2_involution_centralizer_dihedral hoddPP hq₀3 hε₀1 hε₀ hA2
    by_cases hAmem : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range
    · obtain ⟨m, hm, he⟩ := hbranch.1 hAmem
      exact ⟨m, Or.inl hm, he⟩
    · obtain ⟨m, hm, he⟩ := hbranch.2 hAmem
      exact ⟨m, Or.inr hm, he⟩
  have hm_nat : m = q₀ - 1 ∨ m = q₀ + 1 := by
    rcases hε₀1 with rfl | rfl
    · rcases hm with hm | hm
      · left; omega
      · right; omega
    · rcases hm with hm | hm
      · right; omega
      · left; omega
  have hmeven : Even m := by
    rcases hm_nat with rfl | rfl
    · obtain ⟨t, ht⟩ := hq₀odd
      exact ⟨t, by omega⟩
    · obtain ⟨t, ht⟩ := hq₀odd
      exact ⟨t + 1, by omega⟩
  have hm3 : 3 ≤ m := by
    rcases hm_nat with rfl | rfl <;> omega
  have haD2 : orderOf (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 2 := by
    calc orderOf (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) =
        orderOf (⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          ↥(Subgroup.centralizer ({A} : Set (PGL2 F₀)))) :=
          MulEquiv.orderOf_eq eD _
      _ = orderOf A := Subgroup.orderOf_mk A _
      _ = 2 := hA2
  have ha2 : (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) *
      (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 1 :=
    CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two haD2
  have ha1 : (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at haD2
    exact absurd haD2 (by norm_num)
  obtain ⟨c, hc2mul, hc1, hcne, -⟩ :=
    CFSG.ComponentClassification.AutL2Facts.dihedral_exists_commuting_involution hmeven
      (by omega : 2 ≤ m) (eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) ha2 ha1
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2mul) hc1
  refine ⟨(eD.symm c : PGL2 F₀), (eD.symm c).2, ?_, ?_⟩
  · calc orderOf (eD.symm c : PGL2 F₀) = orderOf (eD.symm c) := Subgroup.orderOf_coe _
      _ = orderOf c := MulEquiv.orderOf_eq eD.symm c
      _ = 2 := hc2
  · intro h
    apply hcne
    have h1 : eD.symm c = ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h
    calc c = eD (eD.symm c) := (eD.apply_symm_apply c).symm
      _ = eD ⟨A, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by rw [h1]

theorem exists_involution_commute_of_conjNormal_not_mem_innDiagSub
    (hF : L2Field F) (e : ↥L ≃* L2 F) (N : L2Notation e) (h9 : Nat.card F ≠ 9) {b : Q}
    (hb2 : orderOf b = 2) (hbD : MulAut.conjNormal b ∉ innDiagSub e)
    {x : Q} (hx : x ∈ L ⊓ Subgroup.centralizer {b}) (hx2 : orderOf x = 2) :
    ∃ y ∈ L ⊓ Subgroup.centralizer {b}, orderOf y = 2 ∧ y ≠ x ∧ x * y = y * x := by
  have hb : b * b = 1 :=
    CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two hb2
  have hσ2 : (MulAut.conjNormal b : MulAut ↥L) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hb, map_one]
  obtain ⟨F₀, _, _, hq₀, ⟨ψ⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.exists_equiv_pgl2_fixedSubgroup hF e N hσ2 hbD
  have hF₀ : L2Field F₀ := l2Field_of_card_sq hF h9 hq₀
  have hxfix : (⟨x, hx.1⟩ : ↥L) ∈ CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b) :=
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.mem_fixedSubgroup_conjNormal_iff
      L b ⟨x, hx.1⟩).2 hx.2
  set x' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b)) :=
    ⟨⟨x, hx.1⟩, hxfix⟩ with hx'def
  set A : PGL2 F₀ := ψ x' with hAdef
  have hA2 : orderOf A = 2 := by
    rw [hAdef, MulEquiv.orderOf_eq]
    calc orderOf x' = orderOf ((x' : ↥L)) := (Subgroup.orderOf_coe x').symm
      _ = orderOf (⟨x, hx.1⟩ : ↥L) := by rw [hx'def]
      _ = orderOf x := Subgroup.orderOf_mk x hx.1
      _ = 2 := hx2
  obtain ⟨B, hBmem, hB2, hBne⟩ := exists_involution_ne_centralizer_pgl2 hF₀ hA2
  have hBcomm : B * A = A * B := Subgroup.mem_centralizer_singleton_iff.mp hBmem
  set B' : ↥(Subgroup.centralizer ({A} : Set (PGL2 F₀))) := ⟨B, hBmem⟩ with hB'def
  set y' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b)) := ψ.symm B' with hy'def
  set y : Q := ((y' : ↥L) : Q) with hydef
  have hyL : y ∈ L := (y' : ↥L).2
  have hyfix : (y' : ↥L) ∈ CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b) := y'.2
  have hycommb : y ∈ Subgroup.centralizer ({b} : Set Q) :=
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.mem_fixedSubgroup_conjNormal_iff
      L b (y' : ↥L)).1 hyfix
  have hψy : ψ y' = B := by
    rw [hy'def, MulEquiv.apply_symm_apply, hB'def]
  have hψx : ψ x' = A := hAdef
  have hy2 : orderOf y = 2 := by
    change orderOf ((y' : ↥L) : Q) = 2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    calc orderOf y' = orderOf (ψ y') := (MulEquiv.orderOf_eq ψ y').symm
      _ = orderOf B := by rw [hψy]
      _ = 2 := hB2
  have hyne : y ≠ x := by
    intro h
    have h1 : (y' : ↥L) = ⟨x, hx.1⟩ := Subtype.ext h
    have h2 : y' = x' := Subtype.ext h1
    have h3 : B = A := by
      rw [← hψy, ← hψx, h2]
    exact hBne h3
  have hxy' : x' * y' = y' * x' := by
    apply ψ.injective
    rw [map_mul, map_mul, hψx, hψy]
    exact hBcomm.symm
  have hxyL : ((x' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b))) : ↥L) *
      ((y' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b))) : ↥L) =
      ((y' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b))) : ↥L) *
      ((x' : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b))) : ↥L) :=
    congrArg (fun z : ↥(CFSG.GH74.GLS.fixedSubgroup ↥L (MulAut.conjNormal b)) =>
      ((z : ↥L))) hxy'
  refine ⟨y, ⟨hyL, hycommb⟩, hy2, hyne, ?_⟩
  have := congrArg Subtype.val hxyL
  simpa [x', y', hydef] using this

private theorem exists_conj_mem_of_centralizing (hS : CFSG.Quasithin.Vol2.Ch11.SecU1.Setting L)
    {T : Subgroup Q} (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t)
    {Ω : Set (Subgroup Q)} (hΩ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaColl Ω)
    {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAel : CFSG.Open.IsElemAbelian 2 A)
    (hzA : z ∈ A) {y : Q} (hyL : y ∈ L) (hy2 : orderOf y = 2) (hyne : y ≠ z)
    (hyA : ∀ a ∈ A, a * y = y * a) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ a ∈ A', orderOf a = 2 ∧ a ∈ L ∧ a ≠ z := by
  have hyzpow : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers y) := by
    apply CFSG.Open.isElemAbelian_zpowers
    rw [← hy2]
    exact pow_orderOf_eq_one y
  have hcommAY : ∀ a ∈ A, ∀ c ∈ Subgroup.zpowers y, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hav : Commute a y := hyA a ha
    exact (hav.zpow_right k).eq
  have hE : CFSG.Open.IsElemAbelian 2 (A ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAel hyzpow hcommAY
  obtain ⟨l, hlL, hl⟩ := hS.inner_conj y hyL z hzL hy2 hz2
  obtain ⟨g, hgT, hgy⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.exists_conj_le_eq hT hzT hE
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hl
  have hA'Ω : CFSG.Quasithin.A1b.conjSub g A ∈ Ω := by
    have h1 := hΩ.conj A hAΩ g⁻¹
    rwa [CFSG.Quasithin.conjSubgroup_eq_conjSub A g⁻¹, inv_inv] at h1
  refine ⟨CFSG.Quasithin.A1b.conjSub g A, hA'Ω, ?_, g * z * g⁻¹, ?_, ?_, ?_, ?_⟩
  · exact (CFSG.Quasithin.A1b.conjSub_mono g le_sup_left).trans hgT
  · rw [CFSG.Quasithin.A1b.mem_conjSub_iff]
    have h : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [h]
    exact hzA
  · rw [CFSG.Quasithin.Vol2.Ch11.SecU1.orderOf_conj']
    exact hz2
  · exact (inferInstance : L.Normal).conj_mem z hzL g
  · intro he
    apply hyne
    have h1 : g * y * g⁻¹ = g * z * g⁻¹ := by rw [hgy, he]
    exact mul_left_cancel (mul_right_cancel h1)

theorem exists_mem_omega_inner_ne_or_diag
    (hS : CFSG.Quasithin.Vol2.Ch11.SecU1.Setting L) (hF : L2Field F) (e : ↥L ≃* L2 F)
    (N : L2Notation e) (h9 : Nat.card F ≠ 9) {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1)
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) {T : Subgroup Q} (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤)
    {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t)
    {Ω : Set (Subgroup Q)} (hΩ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaColl Ω)
    {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAT : A ≤ T) (hA4 : 4 ≤ Nat.card A) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ a ∈ A', orderOf a = 2 ∧
      ((a ∈ L ∧ a ≠ z) ∨
        (a ∉ L ∧ (Nat.card ↥(L ⊓ Subgroup.centralizer {a}) : ℤ) = Nat.card F + ε)) := by
  have hC : Subgroup.centralizer (L : Set Q) = ⊥ := hS.almostSimple.centralizer_eq
  have hAel : CFSG.Open.IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hcommA : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc => hAel.comm ha hc
  have hAord : ∀ a ∈ A, a ≠ 1 → orderOf a = 2 :=
    fun a ha ha1 => orderOf_eq_prime (hAel.2 a ha) ha1
  by_cases hstep1 : ∃ a ∈ A, a ∈ L ∧ a ≠ z ∧ orderOf a = 2
  · obtain ⟨a, haA, haL, hane, ha2⟩ := hstep1
    exact ⟨A, hAΩ, hAT, a, haA, ha2, Or.inl ⟨haL, hane⟩⟩
  have hAL : ∀ a ∈ A, a ∈ L → a = 1 ∨ a = z := by
    intro a ha haL
    by_cases h1 : a = 1
    · exact Or.inl h1
    · exact Or.inr (by
        by_contra hne
        exact hstep1 ⟨a, ha, haL, hne, hAord a ha h1⟩)
  have hI : ∀ x ∈ A, x ∈ L → x ≠ 1 → ∀ y ∈ A, y ∈ L → y ≠ 1 → x = y := by
    intro x hx hxL hx1 y hy hyL hy1
    rcases hAL x hx hxL with hx1' | hxz
    · exact absurd hx1' hx1
    · rcases hAL y hy hyL with hy1' | hyz
      · exact absurd hy1' hy1
      · rw [hxz, hyz]
  obtain ⟨v, b, hvA, hvL, hv1, hbA, hbL, hclass⟩ :=
    exists_generators_of_not_two_involutions hS hAel hA4 hI
  have hvz : v = z := by
    rcases hAL v hvA hvL with h1 | hz
    · exact absurd h1 hv1
    · exact hz
  rw [hvz] at hclass
  have hzA : z ∈ A := hvz ▸ hvA
  have hb2 : orderOf b = 2 :=
    orderOf_eq_prime (hAel.2 b hbA) (fun h1 => hbL (h1 ▸ L.one_mem))
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommA z hzA b hbA)
  by_cases hdiag : MulAut.conjNormal b ∈ innDiagSub e
  · refine ⟨A, hAΩ, hAT, b, hbA, hb2, Or.inr ⟨hbL, ?_⟩⟩
    exact card_inf_centralizer_of_conjNormal_mem_innDiagSub hC hF e hε1 hε hb2 hbL hdiag
  · obtain ⟨y, hy, hy2, hyne, hycomm⟩ :=
      exists_involution_commute_of_conjNormal_not_mem_innDiagSub hF e N h9 hb2 hdiag
        ⟨hzL, hzCb⟩ hz2
    have hyb : b * y = y * b :=
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
    have hyA : ∀ a ∈ A, a * y = y * a := by
      intro a ha
      rcases hclass a ha with h1 | hz | hb | hzb
      · rw [h1, one_mul, mul_one]
      · rw [hz]; exact hycomm
      · rw [hb]; exact hyb
      · rw [hzb]
        exact (Commute.mul_left hycomm hyb).eq
    obtain ⟨A', hA'Ω, hA'T, a, haA', ha2, haL, hane⟩ :=
      exists_conj_mem_of_centralizing hS hT hzL hz2 hzT hΩ hAΩ hAel hzA hy.1 hy2 hyne hyA
    exact ⟨A', hA'Ω, hA'T, a, haA', ha2, Or.inl ⟨haL, hane⟩⟩

end CFSG.LocalAnalysis.WeakClosure81
