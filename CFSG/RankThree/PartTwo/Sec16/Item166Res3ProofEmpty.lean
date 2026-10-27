module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res2Proof167
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofComm
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCore
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item169General
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

section Steps

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G)

@[expose] noncomputable def Step167EmptyO2 : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y → scriptY0 A LB = ∅ →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → pPrimeCoreOf 2 Y ≠ ⊥ →
      A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
        pPrimeCoreOf 2 Y ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
          A ⊔ L ⊔ Y ≤ Subgroup.normalizer
            ((pPrimeCoreOf 2 Y ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) →
            ∃ T ∈ invariantPiSubgroups ⊤ (A ⊔ L) (piOf 2), T ≠ ⊥

end Steps

@[expose] noncomputable def Step167EmptyO2R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167EmptyO2 A (lB A) c L

namespace Proof166Res3

theorem isEmpty_l34_of_two_lt {X : Type} [Group X] {n : ℕ} (hiso : Sec4.IsoLThreePi X 2 n)
    (hn : 2 < n) : IsEmpty (X ≃* projSL 3 (GaloisField 2 2)) := by
  refine ⟨fun φ => ?_⟩
  have hX : Nat.card X = 20160 := by rw [Nat.card_congr φ.toEquiv, card_projSL_three_four]
  have h512 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)
  have key : ∀ g : ℕ, g ∣ 3 → ¬ 2 ^ 9 ∣ 20160 * g := by
    intro g hg
    have hg' : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).mp hg
    rcases hg' with rfl | rfl <;> norm_num
  rcases hiso with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega), ← Nat.card_congr ψ.toEquiv, hX] at hc
    exact key _ (Nat.gcd_dvd_left 3 _) (hc ▸ h512.trans (Dvd.intro _ rfl))
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 n (by omega)
    rw [← Nat.card_congr ψ.toEquiv, hX] at hc
    exact key _ (Nat.gcd_dvd_left 3 _) (hc ▸ h512.trans (Dvd.intro _ rfl))

theorem isEmpty_lBarA_l34 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec13Data G A c L)
    (h34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    IsEmpty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) := by
  refine ⟨fun e1 => ?_⟩
  obtain ⟨e2⟩ := hprod
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_lA.1
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hq.1
  have hperf : _root_.commutator (Sec12.lBar c L) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective).commutator_eq_top
  have hfin : Finite (projSL 3 (GaloisField 2 2)) := by
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 2)
    rw [GaloisField.card 2 2 (by norm_num)] at hc
    norm_num at hc
    exact Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨f⟩ := Proof1619.nonempty_mulEquiv_of_prod (e1.symm.trans e2) hperf
  exact h34.false (η.trans f.symm)

theorem commutator_mem_centralizer_L {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h138 : Item138N) (h1612 : Step1612) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hH : Hyp1673 A (lB A) c L Y)
    (h0 : scriptY0 A (lB A) = ∅) (hZA : A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G))
    {x : G} (hx : x ∈ Y ⊓ Subgroup.centralizer (A : Set G)) {z : G}
    (hz : z ∈ pPrimeCoreOf 2 Y) :
    x * z * x⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 Y ⊓ Subgroup.centralizer (L : Set G) := by
  have hctx : Ctx169 G A c L := ⟨h, h0⟩
  obtain ⟨-, -, -, hhyp⟩ := hH
  obtain ⟨n, hn2, hiso, hprod⟩ := hhyp h0
  have hz3 : IsZ3LThreeTwo A c L n := ⟨by omega, hiso, hprod⟩
  have hn3 : ¬ 3 ∣ n := Proof1617.not_three_dvd_of_isZ3 hctx h138 hz3
  have h34 := isEmpty_l34_of_two_lt hiso hn2
  have hLs : IsSimpleGroup ↥L :=
    (Proof1619.simple_of_steps hctx (h1612 G A c L hctx) h34 hprod).1
  have hXL : Sec4.IsoLThreePi ↥L 2 n := Proof1617.isoLThreePi_of_isSimpleGroup hLs hz3.1 hiso
  obtain ⟨-, h9, -⟩ := Proof1617.facts_of_isZ3 hctx hz3
  have hCN := Proof1617.centralizer_le_normalizer_L hctx hz3
  have hcA : c ∈ A := h.mem_A
  obtain ⟨⟨-, -⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  set Z := pPrimeCoreOf 2 Y with hZdef
  have hZY : Z ≤ Y := pPrimeCoreOf_le 2 Y
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_pPrimeCoreOf 2 Y
  set w := x * z * x⁻¹ * z⁻¹ with hw
  have hwZ : w ∈ Z := mul_mem ((Subgroup.mem_normalizer_iff.mp (hYZ hx.1) z).mp hz) (inv_mem hz)
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.2 c hcA).symm
  have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hZA hcA) z hz)
  have hxN := hCN hxc
  have hzN := hCN hzc
  have hwN : w ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (mul_mem (mul_mem hxN hzN) (inv_mem hxN)) (inv_mem hzN)
  set ρ := L.normalizerMonoidHom with hρ
  have hρapp : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : ↥L),
      ((ρ ⟨g, hg⟩ l : ↥L) : G) = g * l * g⁻¹ := fun g hg l => rfl
  set α := ρ ⟨x, hxN⟩ with hα
  set β := ρ ⟨z, hzN⟩ with hβ
  have hγ : α * β * α⁻¹ * β⁻¹ = ρ ⟨w, hwN⟩ := by
    rw [hα, hβ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  set D : Subgroup ↥L := (A ⊓ L).subgroupOf L with hD
  have hDab : CFSG.Assembly.IsElemAbelian 3 D :=
    Proof1617.isElemAbelian_subgroupOf (Proof169.isElemAbelian_of_le h.isElemAbelian inf_le_left) L
  have hD9 : Nat.card D = 9 := by rw [hD, Proof1617.card_subgroupOf_of_le inf_le_right, h9]
  have hαD : ∀ d ∈ D, α d = d := by
    intro d hd
    apply Subtype.ext
    rw [hα, hρapp]
    have hdA : (d : G) ∈ A := (Subgroup.mem_subgroupOf.mp hd).1
    rw [← Subgroup.mem_centralizer_iff.mp hx.2 (d : G) hdA, mul_inv_cancel_right]
  have hβD : ∀ d ∈ D, β d = d := by
    intro d hd
    apply Subtype.ext
    rw [hβ, hρapp]
    have hdA : (d : G) ∈ A := (Subgroup.mem_subgroupOf.mp hd).1
    rw [Subgroup.mem_centralizer_iff.mp (hZA hdA) z hz, mul_inv_cancel_right]
  have hcop : Nat.Coprime 3 (orderOf (α * β * α⁻¹ * β⁻¹)) := by
    rw [hγ]
    have h1 : orderOf (ρ ⟨w, hwN⟩) ∣ orderOf w := by
      have := orderOf_map_dvd ρ (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf w ∣ Nat.card Y := by
      rw [← Subgroup.orderOf_mk (ha := hZY hwZ)]
      exact orderOf_dvd_natCard _
    exact (Nat.Coprime.coprime_dvd_right (h1.trans h2)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3'))
  have h1 := ks167OutComm ↥L n (by omega) hn3 hXL D hDab hD9 α β hαD hβD hcop
  rw [hγ] at h1
  refine ⟨hwZ, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have h2 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h1
  simp only [hρapp, MulAut.one_apply] at h2
  calc l * w = w * l * w⁻¹ * w := by rw [h2]
    _ = w * l := by group

theorem le_normalizer_inf_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A)) (hsol : Group.IsSolvable ↥Y)
    (hF : generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y) :
    A ⊔ L ⊔ Y ≤ Subgroup.normalizer
      ((pPrimeCoreOf 2 Y ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hYAX, -, hZA⟩ := facts1673 h h149 h146 hY hsol hF
  have hA3 : IsPGroup 3 A := h.toSec14Std.isE27.isPGroup
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  set X := deltaZero A (lB A) Y with hXdef
  set Z := pPrimeCoreOf 2 Y with hZdef
  set Z₁ := Z ⊓ Subgroup.centralizer (L : Set G) with hZ₁
  have hXY : X ≤ Y := deltaZero_le Y
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_pPrimeCoreOf 2 Y
  have hXZ : X ≤ Subgroup.centralizer (Z : Set G) := by
    have hAZ : ⁅A, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZA
    have h1 : ⁅⁅A, Z⁆, X⁆ = ⊥ := by rw [hAZ, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅Z, X⁆, A⁆ = ⊥ := by
      have hZXZ : ⁅Z, X⁆ ≤ Z :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp (hXY.trans hYZ)
      have hZA' : ⁅Z, A⁆ = ⊥ := by rw [Subgroup.commutator_comm, hAZ]
      exact le_bot_iff.mp (hZA' ▸ Subgroup.commutator_mono hZXZ le_rfl)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [← deltaZero_eq_commutator Y] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hcen : ∀ K : Subgroup G, (∀ k ∈ K, ∀ t ∈ Z₁, t * k = k * t) →
      K ≤ Subgroup.normalizer (Z₁ : Set G) := by
    intro K hK
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Z₁ : Set G))
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun t ht => hK k hk t ht
  have hAZ₁ : A ≤ Subgroup.normalizer (Z₁ : Set G) :=
    hcen A fun a ha t ht => Subgroup.mem_centralizer_iff.mp (hZA ha) t ht.1
  have hLZ₁ : L ≤ Subgroup.normalizer (Z₁ : Set G) :=
    hcen L fun l hl t ht => (Subgroup.mem_centralizer_iff.mp ht.2 l hl).symm
  have hXZ₁ : X ≤ Subgroup.normalizer (Z₁ : Set G) :=
    hcen X fun x hx t ht => Subgroup.mem_centralizer_iff.mp (hXZ hx) t ht.1
  have hCZ₁ : Y ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Z₁ : Set G) := by
    refine le_normalizer_inf (inf_le_left.trans hYZ) (le_normalizer_centralizer_of_le_normalizer ?_)
    exact inf_le_right.trans ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr h.mem_A)).trans hCN)
  have hYZ₁ : Y ≤ Subgroup.normalizer (Z₁ : Set G) := by
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A Y hA3 hY3' hAY]
    exact sup_le (hYAX.trans hXZ₁) hCZ₁
  exact sup_le (sup_le hAZ₁ hLZ₁) hYZ₁

end Proof166Res3

open Proof166Res3

theorem step167EmptyCent_of_faith {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h138 : Item138N) (h1612 : Step1612)
    (hfaith : Step167EmptyFaith A (lB A) c L) : Step167EmptyCent A (lB A) c L := by
  intro Y hY hH h0 hF hZ1 hZA x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hmem := commutator_mem_centralizer_L h h138 h1612 hY hH h0 hZA hx hz
  rw [hfaith Y hY hH h0 hF hZ1 hZA, Subgroup.mem_bot] at hmem
  calc z * x = (x * z * x⁻¹ * z⁻¹)⁻¹ * (x * z) := by group
    _ = x * z := by rw [hmem, inv_one, one_mul]

theorem step167EmptyFaith_of_o2 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    (h1610 : Step1610) (hY3 : Step1612Y3) (hO2 : Step167EmptyO2 A (lB A) c L) :
    Step167EmptyFaith A (lB A) c L := by
  intro Y hY hH h0 hF hZ1 hZA
  have hctx : Ctx169 G A c L := ⟨h, h0⟩
  by_contra hne
  obtain ⟨-, hsol, -, hhyp⟩ := id hH
  obtain ⟨n, hn2, hiso, hprod⟩ := hhyp h0
  have hz3 : IsZ3LThreeTwo A c L n := ⟨by omega, hiso, hprod⟩
  have hCN := Proof1617.centralizer_le_normalizer_L hctx hz3
  have hN := le_normalizer_inf_centralizer h h149 h146 hCN hY hsol hF
  obtain ⟨T, hT, hT1⟩ := hO2 Y hY hH h0 hF hZ1 hZA hne hN
  have h34 := isEmpty_lBarA_l34 h.toSec13Data (isEmpty_l34_of_two_lt hiso hn2) hprod
  obtain ⟨Y', hY', hY'o⟩ := hY3 G A c L hctx h34 T hT hT1
  rw [h1610 G A c L hctx] at hY'
  exact hY'o hY'.2

theorem step167EmptyCentR_of_faith (h138 : Item138N) (h1612 : Step1612)
    (hfaith : Step167EmptyFaithR) : Step167EmptyCentR := fun G _ _ A c L h =>
  step167EmptyCent_of_faith h h138 h1612 (hfaith G A c L h)

theorem step167EmptyFaithR_of_o2 (h149 : Item149S14) (h146 : Item146S14) (h1610 : Step1610)
    (hY3 : Step1612Y3) (hO2 : Step167EmptyO2R) : Step167EmptyFaithR := fun G _ _ A c L h =>
  step167EmptyFaith_of_o2 h (h149 G A c L h.toSec14Std) (h146 G A c L h.toSec14Std) h1610 hY3
    (hO2 G A c L h)

end CFSG.RankThree.PartTwo.Sec16
