module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.LieType.Simplicity.Suzuki
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Mathieu.M23
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.J1
import CFSG.Sporadic.J2
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.HS
import CFSG.Sporadic.He
import CFSG.Sporadic.Ru

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem center_quotient_center_eq_bot {Y : Type*} [Group Y]
    (hP : Group.IsPerfect (Y ⧸ Subgroup.center Y)) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hc : ∀ g : Y, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.center Y := fun g => by
    have h1 := Subgroup.mem_center_iff.mp hq (g : Y ⧸ Subgroup.center Y)
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← h1]
    group
  let χ : Y →* Subgroup.center Y :=
    { toFun := fun g => ⟨x * g * x⁻¹ * g⁻¹, hc g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 := Subgroup.mem_center_iff.mp (hc g') (x * g * x⁻¹)
        have h2 := Subgroup.mem_center_iff.mp (hc g') (x * g * x⁻¹ * g⁻¹)
        calc x * (g * g') * x⁻¹ * (g * g')⁻¹ = (x * g * x⁻¹) * (x * g' * x⁻¹ * g'⁻¹) * g⁻¹ := by
              group
          _ = (x * g' * x⁻¹ * g'⁻¹) * (x * g * x⁻¹) * g⁻¹ := by rw [h1]
          _ = (x * g' * x⁻¹ * g'⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
          _ = x * g * x⁻¹ * g⁻¹ * (x * g' * x⁻¹ * g'⁻¹) := h2.symm }
  have hZ : Subgroup.center Y ≤ χ.ker := fun z hz => by
    apply Subtype.ext
    change x * z * x⁻¹ * z⁻¹ = 1
    rw [Subgroup.mem_center_iff.mp hz x]
    group
  set χ' := QuotientGroup.lift (Subgroup.center Y) χ hZ with hχ'
  have hker : commutator (Y ⧸ Subgroup.center Y) ≤ χ'.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp (χ' v).2 _
  have hx : x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : χ' (g : Y ⧸ Subgroup.center Y) = 1 :=
      hker (hP.commutator_eq_top ▸ Subgroup.mem_top _)
    have hg' : x * g * x⁻¹ * g⁻¹ = 1 := congrArg Subtype.val hg
    calc g * x = (x * g * x⁻¹ * g⁻¹)⁻¹ * (x * g) := by group
      _ = x * g := by rw [hg', inv_one, one_mul]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem center_eq_bot_of_mulEquiv_quotient_center {X Y : Type*} [Group X] [Group Y]
    (hX : IsQuasisimple X) (e : X ≃* Y ⧸ Subgroup.center Y) : Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hX.1
  have hP : Group.IsPerfect (Y ⧸ Subgroup.center Y) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact center_eq_bot_of_mulEquiv e (center_quotient_center_eq_bot hP)

namespace Config426

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem dvd_card (h : Config426 X α P) : 1080 ∣ Nat.card X := by
  have h1 : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six h.tripleCover.isExtOf
  have h2 : 1080 ∣ Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 P), h1]
    exact Dvd.intro _ rfl
  exact h2.trans (Subgroup.card_subgroup_dvd_card P)

theorem false_of_mulEquiv_quotient_center (h : Config426 X α P) {Y : Type*} [Group Y]
    (e : X ≃* Y ⧸ Subgroup.center Y) : False :=
  h.false_of_center_eq_bot (center_eq_bot_of_mulEquiv_quotient_center h.quasisimple e)

theorem false_of_mulEquiv_isSimpleGroup (h : Config426 X α P) {Y : Type*} [Group Y]
    [IsSimpleGroup Y] (e : X ≃* Y) : False :=
  h.false_of_center_eq_bot (center_eq_bot_of_mulEquiv_isSimpleGroup h.quasisimple e)

theorem false_of_projSL (h : Config426 X α P) {n : ℕ} {F : Type} [Field F]
    (e : X ≃* projSL n F) : False :=
  h.false_of_mulEquiv_quotient_center (e.trans (projSLEquivPSLn n F))

theorem false_of_projSU (h : Config426 X α P) {n p f : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    (hf : 1 ≤ f) (e : X ≃* projSU n p f) : False := by
  by_cases hq : (n, p ^ f) = (3, 2)
  · obtain ⟨rfl, hpf⟩ := Prod.mk.inj hq
    have hp2 : p = 2 := by
      have hp := (Fact.out : p.Prime).two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    subst hp2
    have hf1 : f = 1 := by
      have := Nat.pow_right_injective le_rfl (hpf.trans (pow_one 2).symm)
      exact this
    subst hf1
    exact false_of_mulEquiv_projSU_three_two h.quasisimple e
  · have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
      (GaloisField p (2 * f)) p f hK n hn hq
    exact h.false_of_mulEquiv_isSimpleGroup (e.trans (projSUEquivStatedProj n p f))

theorem false_of_projSp (h : Config426 X α P) {n : ℕ} {F : Type} [Field F] (hn : 1 ≤ n)
    (hF : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ n) ∨
      (Nat.card F = 2 ∧ 3 ≤ n)) (e : X ≃* projSp n F) : False := by
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F n hn hF
  exact h.false_of_mulEquiv_isSimpleGroup (e.trans (projSpEquivStatedProj n F))

theorem false_of_projSp_two (h : Config426 X α P) {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSp 2 (GaloisField 2 n)) : False := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    apply absurd h.dvd_card
    rw [Nat.card_congr (e.trans (projSpEquivStatedProj 2 _)).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hF]
    decide
  · refine h.false_of_projSp (by norm_num) (Or.inl (Or.inr ?_)) e
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

theorem false_of_alternating (h : Config426 X α P) {n : ℕ}
    (e : X ≃* alternatingGroup (Fin n)) : False := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · apply absurd h.dvd_card
    rw [Nat.card_congr e.toEquiv]
    intro hd
    have h1 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card (Equiv.Perm (Fin n)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at h1
    have h2 := hd.trans h1
    interval_cases n <;> revert h2 <;> decide
  · exact h.false_of_center_eq_bot (center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simpa using hn)))

theorem false_of_chevalleyExceptional (h : Config426 X α P)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hm : Blueprint.ChevalleyExceptionalModel X t p f) : False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
    exact h.false_of_mulEquiv_quotient_center e
  · obtain ⟨-, K, _, _, -, σ, -, ⟨e⟩⟩ := hm
    exact h.false_of_mulEquiv_quotient_center e

theorem false_of_reeTits (h : Config426 X α P) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (ht : t = .twistedF4 ∨ t = .Tits) (hm : Blueprint.ReeTitsModel X t p f) : False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, a, -, K, _, _, -, ⟨e⟩⟩ := hm
    exact h.false_of_mulEquiv_quotient_center e
  · obtain ⟨-, a, -, K, _, _, -, ⟨e⟩⟩ := hm
    exact h.false_of_mulEquiv_quotient_center e

theorem false_of_suzuki (h : Config426 X α P) {p f : ℕ} (hm : Blueprint.SuzukiModel X p f) :
    False := by
  have := (CFSG.LieType.Simplicity.fam_2b2_simplicity X p f hm).2
  exact h.false_of_mulEquiv_isSimpleGroup (MulEquiv.refl X)

theorem false_of_sporadic46
    (h : Config426 X α P) {s : TauCeti.SporadicName} (hs : s ∈ sporadics46)
    (e : X ≃* Blueprint.NativeSporadic.Carrier s) : False := by
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.M11) e
  · have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.M12) e
  · have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.M22) e
  · have := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.M23) e
  · have := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.M24) e
  · have := CFSG.Sporadic.J1.fam_j1_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.J1) e
  · have := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.J2) e
  · have := CFSG.Sporadic.J3.fam_j3_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.J3) e
  · have := CFSG.Sporadic.J4.fam_j4_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.J4) e
  · have := CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.McL) e
  · have := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.HS) e
  · have := CFSG.Sporadic.He.fam_he_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.He) e
  · have := CFSG.Sporadic.Ru.fam_ru_simplicity.2.2
    exact h.false_of_mulEquiv_isSimpleGroup (Y := Blueprint.NativeSporadic.Ru) e

end Config426

end CFSG.RankThree.PartTwo.Sec4.Item426
