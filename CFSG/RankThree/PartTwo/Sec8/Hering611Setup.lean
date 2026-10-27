module

public import CFSG.RankThree.PartTwo.Sec8.Hering611A6
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem isElemAbelian_zpowers {X : Type*} [Group X] {p : ℕ} {x : X} (hx : x ^ p = 1) :
    CFSG.Assembly.IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isElemAbelian_two_sup {X : Type*} [Group X] [Finite X] {p q : X} (hp2 : p ^ 2 = 1)
    (hq2 : q ^ 2 = 1) (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q) (hcomm : p * q = q * p) :
    CFSG.Assembly.IsElemAbelian 2 (Subgroup.zpowers p ⊔ Subgroup.zpowers q) ∧
      Nat.card (Subgroup.zpowers p ⊔ Subgroup.zpowers q : Subgroup X) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : CFSG.Assembly.IsElemAbelian 2 (Subgroup.zpowers p) := isElemAbelian_zpowers hp2
  have hqn : q ∉ Subgroup.zpowers p := by
    intro hq
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hp2o : orderOf p = 2 := orderOf_eq_prime hp2 hp1
    have hi' : q = p ^ (i % 2) := by
      rw [← hi, ← zpow_mod_orderOf, hp2o]
      norm_num
    rcases (show i % 2 = 0 ∨ i % 2 = 1 by omega) with h | h
    · rw [h, zpow_zero] at hi'
      exact hq1 hi'
    · rw [h, zpow_one] at hi'
      exact hpq hi'.symm
  have hcomm' : ∀ u ∈ Subgroup.zpowers p, u * q = q * u := by
    intro u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_left (show Commute p q from hcomm) i)).eq
  have := Sec5.isElemAbelian_sup_zpowers hA hqn hq2 hcomm'
  refine ⟨this.1, ?_⟩
  rw [this.2]
  have hc : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hp2 hp1]
  rw [hc]


theorem exists_xV (h : Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (h9 : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9) :
    ∃ (b : G) (hb : b ∈ A) (x : L ⧸ aschbacherSolvableCore 3 L)
      (V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)),
      MulAut.conj x ≠ 1 ∧ x ^ 3 = 1 ∧
      thetaQuotMulAut L (compAction L ⟨b, hAN hb⟩) = MulAut.conj x ∧
      CFSG.Assembly.IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      (∀ v ∈ V, thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) v = v) ∧
      (∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧ ∃ v ∈ V, x * v * x⁻¹ ≠ v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 3 (3 * 2)
  have hAF := h.mem_partTwoF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hF : Nat.card F = 3 ^ (3 * 2) := card_galoisField 3 (3 * 2) (by omega)
  set E : (L ⧸ aschbacherSolvableCore 3 L) ≃* GorensteinWalter.PSL2 F :=
    e₁.trans (projSLEquivPSL F) with hEdef
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd E.symm (GorensteinWalter.psl2_center_eq_bot _)
  have hinj := Item82OneProof.conj_injective_of_center_eq_bot hZ
  have hf := inducesKind_field_of_pow_three L ha3 h.inducesOuterTheta E
  obtain ⟨σ, -, hcard, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_of_field ha3 E hf
  rw [hF] at hcard
  obtain ⟨j, hej, hje⟩ := Item82OneProof.exists_eq_pow_of_pow_three_eq Nat.prime_three hcard
  rw [show j = 2 by omega] at hej
  set C := Sec8.barCentralizer (Subgroup.zpowers a) L with hC
  set Γ := autThetaQuot A L with hΓ
  set τ := thetaQuotMulAut L (compAction L ⟨a, hAN h.a_mem⟩) with hτ
  have hτΓ : τ ∈ Γ := mem_autThetaQuot_iff.mpr ⟨a, hAN h.a_mem, h.a_mem, rfl⟩
  set ιc : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    MulAut.conj with hιc
  set X : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (Γ ⊓ ιc.range).comap ιc with hX
  have hXcard : Nat.card X = Nat.card (Γ ⊓ ιc.range : Subgroup _) := by
    have hmap : X.map ιc = Γ ⊓ ιc.range := Subgroup.map_comap_eq_self inf_le_right
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hX9 : Nat.card X = 9 := by rw [hXcard]; exact h9
  have hXC : X ≤ C := by
    intro x hx
    rw [hC, barCentralizer_zpowers_eq_autFix (hAN h.a_mem)]
    have hcomm := (Item82OneProof.commute_of_mem_autThetaQuot hAe hτΓ
      (Subgroup.mem_comap.mp hx).1).eq
    apply hinj
    change MulAut.conj (τ x) = MulAut.conj x
    rw [← mul_mulAutConj_mul_inv]
    change τ * ιc x * τ⁻¹ = ιc x
    rw [hcomm, mul_inv_cancel_right]
  have hx3 : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact Item82OneProof.pow_three_of_mem_autThetaQuot hAe (Subgroup.mem_comap.mp hx).1
  haveI : Fintype (GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
  have hK9 : Fintype.card (GH74.GLS.IVK.fixedField σ) = 9 := by
    rw [← Nat.card_eq_fintype_card, hej]
    norm_num
  obtain ⟨e6⟩ := ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    (GH74.GLS.IVK.fixedField σ) hK9
  set e6' : C ≃* alternatingGroup (Fin 6) := ι.trans e6 with he6'
  have hXnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : X)
  have hxX : (x : L ⧸ aschbacherSolvableCore 3 L) ∈ X := x.2
  set x' : C := ⟨x, hXC x.2⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (hx3 x x.2)
  have hx'1 : x' ≠ 1 := fun h1 => hx1 (Subtype.ext (by
    simpa [hx'] using congrArg (fun y : C => (y : L ⧸ aschbacherSolvableCore 3 L)) h1))
  obtain ⟨p, hp2, hp1, hcomm, hne, hrel⟩ := exists_involution_of_order_three e6' hx'3 hx'1
  set x0 : L ⧸ aschbacherSolvableCore 3 L := (x : L ⧸ aschbacherSolvableCore 3 L) with hx0
  set p0 : L ⧸ aschbacherSolvableCore 3 L := (p : L ⧸ aschbacherSolvableCore 3 L) with hp0
  set q0 : L ⧸ aschbacherSolvableCore 3 L := x0 * p0 * x0⁻¹ with hq0
  have hp02 : p0 ^ 2 = 1 := congrArg Subtype.val hp2
  have hp01 : p0 ≠ 1 := fun h1 => hp1 (Subtype.ext h1)
  have hq02 : q0 ^ 2 = 1 := by
    have : q0 ^ 2 = x0 * p0 ^ 2 * x0⁻¹ := by simp only [hq0, sq]; group
    rw [this, hp02]; group
  have hq01 : q0 ≠ 1 := by
    intro h1
    apply hp01
    have : p0 = x0⁻¹ * q0 * x0 := by simp only [hq0]; group
    rw [this, h1]; group
  have hpq : p0 ≠ q0 := fun h1 => hne (Subtype.ext h1.symm)
  have hpqc : p0 * q0 = q0 * p0 := congrArg Subtype.val hcomm
  have hrel0 : x0 * q0 * x0⁻¹ = p0 * q0 := congrArg Subtype.val hrel
  obtain ⟨hVe, hV4⟩ := isElemAbelian_two_sup hp02 hq02 hp01 hq01 hpq hpqc
  set V : Subgroup (L ⧸ aschbacherSolvableCore 3 L) :=
    Subgroup.zpowers p0 ⊔ Subgroup.zpowers q0 with hV
  have hq0C : q0 ∈ C := C.mul_mem (C.mul_mem (hXC x.2) p.2) (C.inv_mem (hXC x.2))
  have hVC : V ≤ C := sup_le (Subgroup.zpowers_le.mpr p.2) (Subgroup.zpowers_le.mpr hq0C)
  have hp0V : p0 ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers p0)
  have hq0V : q0 ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers q0)
  have hxV : ∀ v ∈ V, x0 * v * x0⁻¹ ∈ V := by
    have hle : V ≤ V.comap (MulAut.conj x0).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact hq0V
      · rw [Subgroup.mem_comap]
        change x0 * q0 * x0⁻¹ ∈ V
        rw [hrel0]
        exact V.mul_mem hp0V hq0V
    intro v hv
    exact hle hv
  obtain ⟨b, hbN, hbA, hb⟩ := mem_autThetaQuot_iff.mp (Subgroup.mem_comap.mp hxX).1
  refine ⟨b, hbA, x0, V, fun h1 => hx1 (Subtype.ext (hinj (by simpa using h1))),
    hx3 x x.2, hb, hVe, hV4, ?_, hxV, p0, hp0V, ?_⟩
  · intro v hv
    have := hVC hv
    rw [hC, barCentralizer_zpowers_eq_autFix (hAN h.a_mem)] at this
    exact (mem_autFix.mp this)
  · exact fun h1 => hne (Subtype.ext h1)

end CFSG.RankThree.PartTwo.Sec8.Hering611
