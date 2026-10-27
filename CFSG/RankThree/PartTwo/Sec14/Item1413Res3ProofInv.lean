module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.J2
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_inv_of_order_four {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (h9 : Nat.card B = 9) {ρ : MulAut ↥B} (h4 : ρ ^ 4 = 1) (h2 : ρ ^ 2 ≠ 1) (x : ↥B) :
    (ρ ^ 2) x = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ u v : ↥B, u * v = v * u := fun u v => hB.1.is_comm.comm u v
  have h3 : ∀ u : ↥B, u ^ 3 = 1 := fun u => Subtype.ext (by simpa using hB.2 u u.2)
  set σ := ρ ^ 2 with hσ
  have hσσ : ∀ u : ↥B, σ (σ u) = u := by
    intro u
    have h1 : σ * σ = 1 := by rw [hσ, ← pow_add]; exact h4
    have h2' := congrArg (fun φ : MulAut ↥B => φ u) h1
    simpa using h2'
  have hρσ : ∀ u : ↥B, σ (ρ u) = ρ (σ u) := by
    intro u
    have h1 : σ * ρ = ρ * σ := by rw [hσ, ← pow_succ, ← pow_succ']
    have h2' := congrArg (fun φ : MulAut ↥B => φ u) h1
    simpa using h2'
  by_contra hx
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥B, σ x₁ ≠ x₁ := by
    by_contra hall
    push Not at hall
    exact h2 (MulEquiv.ext hall)
  set z := x₁ * (σ x₁)⁻¹ with hz
  have hz1 : z ≠ 1 := fun h => hx₁ (by rw [hz, mul_inv_eq_one] at h; exact h.symm)
  have hσz : σ z = z⁻¹ := by
    rw [hz, map_mul, map_inv, hσσ, mul_inv_rev, inv_inv, hcomm]
  have hinv_mul : ∀ u v : ↥B, σ u = u⁻¹ → σ v = v⁻¹ → σ (u * v) = (u * v)⁻¹ := by
    intro u v hu hv
    rw [map_mul, hu, hv, mul_inv_rev, hcomm]
  have hρz : ρ z ∈ Subgroup.zpowers z := by
    by_contra hnot
    apply hx
    have hcl : Subgroup.closure ({z, ρ z} : Set ↥B) = ⊤ := by
      have hlt : Subgroup.zpowers z < Subgroup.closure ({z, ρ z} : Set ↥B) := by
        refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr
          (Subgroup.subset_closure (Set.mem_insert _ _))) fun h => hnot ?_
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hz3 : Nat.card (Subgroup.zpowers z) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (h3 z) hz1]
      have hgt := Subgroup.card_lt_of_lt hlt
      have hdvd : Nat.card (Subgroup.closure ({z, ρ z} : Set ↥B)) ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
        exact Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases k
      · rw [hk', hz3] at hgt; norm_num at hgt
      · rw [hk', hz3] at hgt; norm_num at hgt
      · exact Subgroup.eq_top_of_card_eq _ (by rw [hk', h9]; norm_num)
    have hρz' : σ (ρ z) = (ρ z)⁻¹ := by rw [hρσ, hσz, map_inv]
    have hall : ∀ u ∈ Subgroup.closure ({z, ρ z} : Set ↥B), σ u = u⁻¹ := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        rcases hu with rfl | rfl
        · exact hσz
        · exact hρz'
      | one => simp
      | mul u v _ _ hu hv => exact hinv_mul u v hu hv
      | inv u _ hu => rw [map_inv, hu]
    exact hall x (by rw [hcl]; exact Subgroup.mem_top x)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, z ^ j = ρ z := by
    have h1 : ρ z ∈ (Submonoid.powers z : Set ↥B) := by
      rw [powers_eq_zpowers]
      exact hρz
    exact Submonoid.mem_powers_iff _ _ |>.mp h1
  have hσz' : σ z = z ^ (j * j) := by
    rw [hσ, pow_two, MulAut.mul_apply, ← hj, map_pow, ← hj, ← pow_mul]
  have hzo : orderOf z = 3 := orderOf_eq_prime (h3 z) hz1
  have hj3 : j % 3 ≠ 0 := by
    intro h0
    apply hz1
    have h1 : ρ z = 1 := by
      rw [← hj, ← pow_mod_orderOf, hzo, h0, pow_zero]
    exact (MulEquiv.map_eq_one_iff ρ).mp h1
  have hjj : (j * j) % 3 = 1 := by
    have : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hzz : z = z⁻¹ := by
    rw [← hσz, hσz', ← pow_mod_orderOf, hzo, hjj, pow_one]
  apply hz1
  have h1 : z * z = 1 := by
    calc z * z = z * z⁻¹ := by rw [← hzz]
      _ = 1 := mul_inv_cancel z
  have h2' : z ^ 3 = z * (z * z) := by rw [pow_succ', pow_two]
  rw [h3 z, h1, mul_one] at h2'
  exact h2'.symm

theorem exists_inv_of_order_four_type
    (h131 : Item131)
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G), ∀ x ∈ A ⊓ L, t * x * t⁻¹ = x⁻¹ := by
  have hM12c : Nat.card (alternatingGroup (Fin 7)) ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1, KFacts.KS14.card_nativeM12]
    norm_num
  have hJ2c : Nat.card (alternatingGroup (Fin 7)) ≠
      Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1, KFacts.KS14.card_nativeJ2]
    norm_num
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -, hcase⟩ |
      ⟨-, -, hMJ, -⟩ | ⟨-, hP, -⟩ | ⟨hcL', -⟩
  · have hAa := eq_sup_of_card_nine hD h9 (fun h => hcL h.2)
    obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
    obtain ⟨l, hlN, hlLW, rfl⟩ := Sec4.mem_autIn_iff.mp hρ
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hD.isElemAbelian.2 x hx.1⟩
    refine ⟨l ^ 2, ⟨pow_mem hlLW.1 2, pow_mem hlLW.2 2⟩, fun x hx => ?_⟩
    have h1 := sq_eq_inv_of_order_four hBe h9 hρ4 hρ2 ⟨x, hx⟩
    have h2' := congrArg Subtype.val h1
    rw [normalizerMonoidHom_pow_apply_val] at h2'
    simpa using h2'
  · exfalso
    rcases htype with hA7 | hL3
    · obtain ⟨φ⟩ := hA7
      rcases hMJ with hM | hM
      · obtain ⟨ψ⟩ := hM
        obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
        exact (Proof1413.isEmpty_mulEquiv_of_card_ne hM12c).false (φ.symm.trans χ)
      · obtain ⟨ψ⟩ := hM
        obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
        exact (Proof1413.isEmpty_mulEquiv_of_card_ne hJ2c).false (φ.symm.trans χ)
    · have hnJ2 : ∀ (p e : ℕ) [Fact p.Prime],
          ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 p e :=
        KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_nativeJ2
          (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
          (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2)
      rcases hMJ with hM | hM
      · obtain ⟨ψ⟩ := hM
        obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
        exact not_isLThreePi_of_mulEquiv χ KFacts.KS14.not_isoLThreePi_M12 hL3
      · obtain ⟨ψ⟩ := hM
        obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
        exact not_isLThreePi_of_mulEquiv χ hnJ2 hL3
  · exact absurd hP hPGL
  · exact absurd hcL' hcL

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
