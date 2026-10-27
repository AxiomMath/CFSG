module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
import CFSG.RankThree.PartTwo.Sec18.Item186Act
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.PartTwo.KFacts.L34

namespace Item189O3Proof

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_eq_pCoreOf {L : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) :
    inSubgroup (aschbacherSolvableCore 3) L = CFSG.Open.pCoreOf 2 L := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Sec19.Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  rw [inSubgroup, hθeq]
  rfl

theorem le_thetaQuotCentralizer_of_isPGroup {L B U : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) (hBL : B ≤ L) (hB9 : Nat.card B = 9)
    (hB3 : IsPGroup 3 B) (hUq : IsPGroup q U) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Sec4.thetaQuotCentralizer L := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Sec19.Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  set θ := aschbacherSolvableCore 3 L with hθ
  set NL := Subgroup.normalizer (L : Set G) with hNL
  set D := Sec4.thetaQuotCentralizer L with hD
  let ψ : L ⧸ θ ≃* projectiveSL 3 (GaloisField 2 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hθeq).trans eL).trans
      (projSLEquivProjectiveSL 3 (GaloisField 2 2))
  set β : NL →* MulAut (projectiveSL 3 (GaloisField 2 2)) :=
    (MulAut.congr ψ).toMonoidHom.comp (Sec12.thetaBarAct L) with hβ
  have hβker : ∀ (x : G) (hx : x ∈ NL), β ⟨x, hx⟩ = 1 ↔ x ∈ D := by
    intro x hx
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hx, hβ, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    exact (MulAut.congr ψ).map_eq_one_iff
  have hβinn : ∀ (b : G) (hb : b ∈ L), β ⟨b, Subgroup.le_normalizer hb⟩ =
      MulAut.conj (ψ (QuotientGroup.mk' θ ⟨b, hb⟩)) := by
    intro b hb
    rw [hβ, MonoidHom.comp_apply, Sec12.thetaBarAct_of_mem hb, MulEquiv.coe_toMonoidHom,
      Item186Proof.mulAut_congr_conj]
  set X : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 2))) := (U.subgroupOf NL).map β
    with hXdef
  have hXq : IsPGroup q X := (hUq.comap_subtype (K := NL)).map β
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hXq.exists_card_eq
    rw [hn]
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  set E' : Subgroup L := B.subgroupOf L with hE'
  set Eb : Subgroup (L ⧸ θ) := E'.map (QuotientGroup.mk' θ) with hEb
  set E : Subgroup (projectiveSL 3 (GaloisField 2 2)) := Eb.map ψ.toMonoidHom with hE
  have hE'card : Nat.card E' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB9]
  have hEb9 : Nat.card Eb = 9 := by
    have h1 := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf (QuotientGroup.mk' θ) E'
    have h2 : (QuotientGroup.mk' θ).ker.subgroupOf E' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      obtain ⟨j, hj⟩ := hB3 ⟨((x : L) : G), Subgroup.mem_subgroupOf.mp x.2⟩
      have h3 : (x : L) ^ 3 ^ j = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hj
      exact Subtype.ext (Sec19.Step1914TriProof.eq_one_of_mem_theta' hx h3)
    rw [h2, Subgroup.card_bot, mul_one, hE'card] at h1
    exact h1
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective, hEb9]
  have hconjX : ∀ (b : G) (hb : b ∈ B), ∀ y ∈ X, β ⟨b, Subgroup.le_normalizer (hBL hb)⟩ * y *
      (β ⟨b, Subgroup.le_normalizer (hBL hb)⟩)⁻¹ ∈ X := by
    rintro b hb _ ⟨w, hw, rfl⟩
    have hwU : (w : G) ∈ U := Subgroup.mem_subgroupOf.mp hw
    rw [← map_inv, ← map_mul, ← map_mul]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hBU hb) _).mp hwU
  have hEX : ∀ e ∈ E, MulAut.conj e ∈
      Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 (GaloisField 2 2)))) := by
    rintro _ ⟨_, ⟨b', hb', rfl⟩, rfl⟩
    have hbB : ((b' : L) : G) ∈ B := Subgroup.mem_subgroupOf.mp hb'
    have hbinvB : ((b' : L) : G)⁻¹ ∈ B := B.inv_mem hbB
    have h1 := hβinn _ b'.2
    have h2 := hβinn _ (L.inv_mem b'.2)
    have hb'eq : (⟨((b' : L) : G), b'.2⟩ : L) = b' := rfl
    rw [hb'eq] at h1
    have hinv : (⟨((b' : L) : G)⁻¹, L.inv_mem b'.2⟩ : L) = b'⁻¹ := rfl
    rw [hinv, map_inv, map_inv, map_inv] at h2
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← h1, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconjX _ hbB y
    · intro hy
      have h3 := hconjX _ hbinvB _ hy
      rw [h2, h1] at h3
      simpa [mul_assoc] using h3
  intro u hu
  have huN := hUN hu
  have hmemX : β ⟨u, huN⟩ ∈ X := ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  refine (hβker u huN).mp ?_
  rcases eq_bot_or_eq_zpowers_graphField card_galoisField_two_two hE9 hX3 hEX with hbot |
    ⟨τ, hτ, hτ1, hττ, -⟩
  · rw [hbot, Subgroup.mem_bot] at hmemX
    exact hmemX
  · exfalso
    have hτX : τ ∈ X := by
      rw [hτ]
      exact Subgroup.mem_zpowers τ
    obtain ⟨k, hk⟩ := hXq ⟨τ, hτX⟩
    have hk' : τ ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : τ ^ 2 = 1 := by rw [pow_two]; exact hττ
    have hcop : Nat.Coprime (q ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hq2)
    exact hτ1 ((pow_eq_one_iff_of_coprime hcop).mp ⟨hk', h2⟩)

end Item189O3Proof

end CFSG.RankThree.PartTwo.Sec18
