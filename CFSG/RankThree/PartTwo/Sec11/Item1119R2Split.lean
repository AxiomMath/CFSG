module

public import CFSG.RankThree.PartTwo.Sec11.Item1119R2Pgl
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofCentJ
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

section Main


theorem nine_dvd_orderOf_cube {G : Type} [Group G] {x : G} (hx : ∃ k : ℕ, x ^ 3 ^ k = 1)
    (h9 : 9 < orderOf x) : 9 ∣ orderOf (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, hm, hmx⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have h2 : m ≤ 2 := by omega
    have h4 : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have h3 : 3 ∣ orderOf x := by
    rw [hmx]
    exact dvd_pow_self 3 (by omega)
  rw [orderOf_pow_of_dvd (by norm_num) h3, hmx]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have h9' : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9']
  exact pow_dvd_pow 3 (by omega)

theorem sym1119YAlphaSplit_holds (h45 : Sec4.Item4_5) (h119 : Item119) :
    Sym1119YAlphaSplit := by
  intro G _ _ A c L a R Y d x s r g hctx
  have h := hctx.big.toSec11Data
  have hAe := h.mem_partTwoF.1
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hAcard : Nat.card A = 27 := h.card_eq
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a haA u hu).symm
  have hY := h.mem_thetaComponentsAt_Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y hY
  have key : ∀ (X : Type) [Group X], Group.IsPerfect X → Subgroup.center X = ⊥ →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
        Nat.card ↥(A ⊓ (Y ⊔ sym1119Theta a)) = 9 ∧ a ∉ A ⊓ (Y ⊔ sym1119Theta a) := by
    intro X _ hXp hXc e
    exact Item1119R2.split_of_equiv hY hAC hAY hAcomm hA3 hAcard haA ha1 hXc e
      (fun u => by rw [hXp.commutator_eq_top]; exact Subgroup.mem_top _)
  have hbar : ∀ (X : Type) [Group X], (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := fun X _ e =>
    Item1116Proof.nonempty_thetaQuot_equiv_commutator hY hAC hAY hAcomm e
  have hQS := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hsolv : ∀ (X : Type) [Group X], Group.IsSolvable X →
      (sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) → False := by
    intro X _ hXs e
    obtain ⟨φ⟩ := hbar X e
    have : Group.IsSolvable (Y ⧸ aschbacherSolvableCore 3 Y) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (_root_.commutator X).subtype.comp φ.toMonoidHom)
        ((_root_.commutator X).subtype_injective.comp φ.injective)
    exact fieldCent_not_isSolvable hQS inferInstance
  rcases h119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq with
    ⟨hf, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨-, ⟨e⟩, -⟩
  · exact absurd hf hctx.big.not_field
  · rcases h2 with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
        Finite.of_injective (fun x => e.symm (1, x)) fun x y hxy => by
          simpa using congrArg e hxy
      have hperf := SetUp1118Proof.isPerfect_lie_G2 q hq
      exact key _ hperf
        (KS11Lie3Proof.center_eq_bot_g2 _ ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩,
          Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf⟩) e
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
        Finite.of_injective (fun x => e.symm (1, x)) fun x y hxy => by
          simpa using congrArg e hxy
      have hperf := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
      exact key _ hperf
        (KS11Lie3Proof.center_eq_bot_d4 _ ⟨_, inferInstance, ⟨q, hq, ⟨MulEquiv.refl _⟩⟩,
          Item1120V0Bar.nonempty_mulEquiv_commutator_of_isPerfect hperf⟩) e
  · rcases h3 with hL3 | hPGL
    · obtain ⟨p, ee, hp, he1, ⟨hpf, ⟨e'⟩⟩ | ⟨hpf, ⟨e'⟩⟩⟩ := hL3
      · exact key _ (Sec13.isPerfect_center_projSL p ee he1 hpf).1
          (Sec13.isPerfect_center_projSL p ee he1 hpf).2 e'
      · by_cases hq2 : 2 < p ^ ee
        · exact key _ (Sec13.isPerfect_center_projSU p ee he1 hpf hq2).1
            (Sec13.isPerfect_center_projSU p ee he1 hpf hq2).2 e'
        · exfalso
          have h2 : p ^ ee = 2 := by
            have : 2 ≤ p ^ ee := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
            omega
          obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
          exact hsolv _ Sec13.isSolvable_projSU_two e'
    · obtain ⟨π, p, f, F, _, hK, hmod, ⟨e'⟩⟩ := hPGL
      have hq2 : 2 < p ^ f := by
        by_contra hle
        have h2 : p ^ f = 2 := by
          have hf : f ≠ 0 := by have := hK.one_le; omega
          have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
          omega
        cases π
        · exact hsolv _ (Sec13.isSolvable_projImage_glPi_two hK h2) e'
        · change p ^ f % 3 = 1 at hmod
          omega
      have hKmem := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
      have hKH : sec11K L a ≤ Y ⊓ Subgroup.centralizer ({c} : Set G) := by
        obtain ⟨K', -, hKeq⟩ := hKmem
        rw [← hKeq]
        exact Subgroup.map_subtype_le K'
      have hKp : Group.IsPerfect (sec11K L a) := Sec6.isPerfect_inSubgroup_perfectResidual _
      obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
      exact Item1119R2.split_of_equiv hY hAC hAY hAcomm hA3 hAcard haA ha1
        (Item1119R2.center_projImage_glPi_eq_bot hK hmod hq2) e'
        (Item1119R2.hF_of_pgl hY hAC hAY hAcomm hA3 h.closure_eq h.mem_A haA (Item1117Proof.d_mem_A h)
          h.sec11K_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKH hk).2)
          hKp (h.toSec11Std.d_mem_sec11K h.inf_eq) (Item1117Proof.x_cube_mem_sec11K h)
          ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
          (nine_dvd_orderOf_cube ⟨k, hk⟩ hctx.big.orderOf_x_gt) hK hmod hq2 e')
  · exact (Item1117Proof.false_of_card_L32 h hctx.big.orderOf_x_gt e).elim

end Main

end CFSG.RankThree.PartTwo.Sec11
