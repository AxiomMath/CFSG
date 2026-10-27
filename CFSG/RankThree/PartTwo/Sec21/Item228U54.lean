module

public import CFSG.RankThree.PartTwo.Sec21.Item229Pre
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec4.Item413Orders
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec21.Item231Of
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem card_le_card_inf_mul_card_inf_centralizer [Finite G] {A X : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A)
    (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center X = ⊥)
    (hX : Sec4.CubeInner X) :
    Nat.card A ≤ Nat.card (A ⊓ X : Subgroup G) *
      Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  have hAe : IsElemAbelian 3 A := hA.prop
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  let ρ : A →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hρ : ∀ (a : A) (y : X), ((ρ a y : X) : G) = (a : G) * y * (a : G)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : x * y * x⁻¹ = y := by
      have := congrArg (fun σ : MulAut X => σ y) (MonoidHom.mem_ker.mp hx)
      simpa [MulAut.conj_apply] using this
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hrange : ρ.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨a, rfl⟩
    apply hX
    rw [← map_pow, hA3 a, map_one]
  set B : Subgroup X := ρ.range.comap (MulAut.conj : X →* MulAut X) with hBdef
  have hB : Nat.card B = Nat.card ρ.range := by
    rw [← Subgroup.map_comap_eq_self hrange, Subgroup.card_map_of_injective hinj]
  have hBA : B.map X.subtype ≤ A ⊓ X := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, x.2⟩
    obtain ⟨a, ha⟩ := hx
    refine Sec4.mem_of_maximal_of_commute hA ?_ ?_
    · have h1 : MulAut.conj (x ^ 3) = MulAut.conj 1 := by
        rw [map_pow, map_one, ← ha, ← map_pow, hA3 a, map_one]
      have h2 := hinj h1
      simpa using congrArg Subtype.val h2
    · intro a' ha'
      have key : MulAut.conj (ρ ⟨a', ha'⟩ x) = MulAut.conj x := by
        have hconj : ρ ⟨a', ha'⟩ * MulAut.conj x * (ρ ⟨a', ha'⟩)⁻¹ =
            MulAut.conj (ρ ⟨a', ha'⟩ x) := by
          ext m
          simp [MulAut.mul_apply, map_mul, map_inv]
        have hcomm : (⟨a', ha'⟩ : A) * a * (⟨a', ha'⟩ : A)⁻¹ = a := by
          rw [hAe.1.is_comm.comm ⟨a', ha'⟩ a, mul_inv_cancel_right]
        rw [← hconj, ← ha, ← map_inv, ← map_mul, ← map_mul, hcomm]
      have h3 : (a' : G) * x * a'⁻¹ = x := by
        have := congrArg Subtype.val (hinj key)
        rwa [hρ] at this
      calc a' * (x : G) = a' * x * a'⁻¹ * a' := by group
        _ = x * a' := by rw [h3]
  have hker : ρ.ker.map A.subtype ≤ A ⊓ Subgroup.centralizer (X : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 : (a : G) * y * (a : G)⁻¹ = y := by
      have := congrArg (fun σ : MulAut X => ((σ ⟨y, hy⟩ : X) : G)) (MonoidHom.mem_ker.mp ha)
      simpa [hρ] using this
    calc y * a = (a : G) * y * (a : G)⁻¹ * a := by rw [h1]
      _ = a * y := by group
  have hcardA : Nat.card A = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h1 : Nat.card ρ.ker ≤ Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective]
    exact Subgroup.card_le_of_le hker
  have h2 : Nat.card ρ.range ≤ Nat.card (A ⊓ X : Subgroup G) := by
    rw [← hB, ← Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_le_of_le hBA
  rw [hcardA, mul_comm]
  exact Nat.mul_le_mul h2 h1

theorem not_three_dvd_card_starOf_of_nine_dvd [Finite G] {A X : Subgroup G}
    (hAc : IsMulCommutative A) (h9 : 9 ∣ Nat.card (A ⊓ X : Subgroup G))
    (h27 : ¬ 27 ∣ Nat.card X) : ¬ 3 ∣ Nat.card (starOf A X) := by
  intro h3
  have hle : A ⊓ X ≤ X ⊓ Subgroup.centralizer (A : Set G) := by
    intro x hx
    refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨x, hx.1⟩)
  have h9' := h9.trans (Subgroup.card_dvd_of_le hle)
  have h27' : 27 ∣ Nat.card (X ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := by
    rw [← card_starOf_mul_card A X, show (27 : ℕ) = 3 * 9 by norm_num]
    exact Nat.mul_dvd_mul h3 h9'
  exact h27 (h27'.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem not_twentySeven_dvd_card_projSU_five_four : ¬ 27 ∣ Nat.card (projSU 5 2 2) := by
  have hU := Sec4.unitaryFieldData_galoisField 2 2 (by norm_num)
  have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four hU
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  intro h
  have h1 := h.trans (Sec4.card_projSU_dvd 5 2 2)
  rw [hSU] at h1
  norm_num at h1

theorem not_three_dvd_card_starOf_of_mulEquiv_projSU_five [Finite G] (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) {A : Subgroup G} (hA : Sec21Std G A) (hA27 : Nat.card A = 3 ^ 3)
    {X : Subgroup G} (hX : X ∈ lStar A) (eX : X ≃* projSU 5 2 2) :
    ¬ 3 ∣ Nat.card (starOf A X) := by
  have hAe : IsElemAbelian 3 A := hA.mem_S.1.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hA.mem_S.1.2.1 B hB hAB).le⟩
  obtain ⟨a, haA, ha1, haX⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hA.standing.toTheoremFourHyp hAe haA ha1 X
      haX
  have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
  have : IsSimpleGroup X := eX.isSimpleGroup
  have hperf : Group.IsPerfect X := isPerfect_of_mem_thetaComponentFamily hX.1
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hab : commutator X = ⊥ := by
        rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
        intro x _ y _
        have hxy : x * y = y * x :=
          (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hxy
      have htop : commutator X = ⊤ := hperf.commutator_eq_top
      rw [hab] at htop
      exact bot_ne_top htop
  have hCI : Sec4.CubeInner X :=
    (Sec4.cubeInner_of_not_three_dvd_card_outer Sec4.outU54_holds).of_mulEquiv eX
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ 3 := by
    have hcyc := h66 G hA.standing A hA.mem_S X hX
    have hle : A ⊓ Subgroup.centralizer (X : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer X := by
      rintro d ⟨hdA, hdC⟩
      refine ⟨hdA, Sec6.mem_thetaQuotCentralizer_iff.mpr
        ⟨Subgroup.centralizer_le_normalizer _ hdC, fun l hl => ?_⟩⟩
      have h1 : l * d = d * l := Subgroup.mem_centralizer_iff.mp hdC l hl
      rw [show l⁻¹ * (d * l * d⁻¹) = 1 by rw [← h1]; group]
      exact Subgroup.one_mem _
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hle3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≤ 3 := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      have : g ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ g.2.1)
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
    exact (Subgroup.card_le_of_le hle).trans hle3
  have hcard := card_le_card_inf_mul_card_inf_centralizer hAmax hAN hZ hCI
  rw [hA27] at hcard
  have h9le : 9 ≤ Nat.card (A ⊓ X : Subgroup G) := by
    have := Nat.mul_le_mul_left (Nat.card (A ⊓ X : Subgroup G)) hC3
    omega
  have hdvd : Nat.card (A ⊓ X : Subgroup G) ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h9 : 9 ∣ Nat.card (A ⊓ X : Subgroup G) := by
    rw [hkeq] at h9le ⊢
    interval_cases k
    · norm_num at h9le
    · norm_num at h9le
    · norm_num
    · norm_num
  have h27 : ¬ 27 ∣ Nat.card X := by
    rw [Nat.card_congr eX.toEquiv]
    exact not_twentySeven_dvd_card_projSU_five_four
  exact not_three_dvd_card_starOf_of_nine_dvd hAe.1 h9 h27

theorem exists_kOf_sup_SL3' [Finite G] (h222 : Item222) (h228 : Item228) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A)
    (hψ : ψ ∈ dStar A) (h3 : orderOf (φ * ψ) = 3) :
    ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* SL3 m) := by
  have hφ2 := mul_self_of_mem_dStar hφ
  have hψ2 := mul_self_of_mem_dStar hψ
  have hnc : ψ * φ ≠ φ * ψ := by
    intro hc
    have h2 : (φ * ψ) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc ψ, hc, mul_assoc, hψ2, mul_one, hφ2]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    norm_num at this
  have hne : ψ ≠ φ := by
    intro h
    apply hnc
    rw [h]
  have h3Y : 3 ∣ Nat.card (starOf A (kOf A φ ⊔ kOf A ψ)) := by
    obtain ⟨h1, h2⟩ := mem_starOf_sup h222 hpair hK hφ hψ
    have := dvd_card_starOf ((starOf A _).mul_mem h1 h2)
    rwa [h3] at this
  obtain ⟨hX1, -, hX3⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX3 hnc with ⟨hYL, hcase, -⟩ | ⟨-, X, hX, hYX, ⟨eX⟩⟩
  · have hYperf : Group.IsPerfect (kOf A φ ⊔ kOf A ψ : Subgroup G) :=
      isPerfect_of_mem_thetaComponentFamily (lStar_subset A hYL)
    rcases hcase with ⟨-, n, hn0, hne', ⟨eL⟩, ⟨eK⟩, -⟩ | ⟨-, -, -, -, -, -, ⟨e8⟩⟩ |
        ⟨-, -, -, -, -, -, ⟨e8⟩⟩ | ⟨-, -, -, ⟨e8⟩⟩ | ⟨h81, -⟩
    · obtain ⟨m', hm'0, hm'e, ⟨eK'⟩, hX'⟩ := hX1 _ hYL le_sup_left
      have hm : m' = n := eq_of_mulEquiv_projSL_two (by omega) (by omega) (eK'.symm.trans eK)
      subst hm
      obtain ⟨eψ⟩ := nonempty_kOf_mulEquiv_of_orderOf_eq_three hK hφ hψ h3
      refine ⟨m', hm'0, hm'e, ⟨eK⟩, ⟨eψ.trans eK⟩, ?_⟩
      have hm2 : 2 ≤ m' := by obtain ⟨k, hk⟩ := hm'e; omega
      rcases hX' with hSL | hS | hS | ⟨hm4, hS⟩ | ⟨-, hS⟩
      · exact hSL
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSp_two hm2
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 4) (n := m') le_rfl (by omega)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 4) (n := m' / 2) le_rfl (by omega)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [hA27] at h81
      norm_num at h81
  · exact (not_three_dvd_card_starOf_of_mulEquiv_projSU_five h45 h66 hpair.toSec21Std hA27 hX eX
      (h3Y.trans (Subgroup.card_dvd_of_le (starOf_mono A hYX)))).elim

end CFSG.RankThree.PartTwo.Sec21
