module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec18.SylowFiveAct
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.PartTwo.KFacts.L34

namespace Item186Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {X : Type*} [Group X] {τ y : X} (hττ : τ * τ = 1)
    (hy : y ∈ Subgroup.zpowers τ) : y = 1 ∨ y = τ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hττ, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hττ, one_zpow, one_mul]

omit [Finite G] in
theorem mulAut_congr_conj {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (y : X) :
    MulAut.congr ψ (MulAut.conj y) = MulAut.conj (ψ y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem inf_thetaQuotCentralizer_le {L : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) :
    L ⊓ Sec4.thetaQuotCentralizer L ≤ CFSG.Open.pCoreOf 2 L := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Sec19.Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  obtain ⟨hZ, -⟩ := SylowFive.center_eq_bot_and_card_mulAut hLp eL
  rintro x ⟨hxL, hxD⟩
  set x' : L := ⟨x, hxL⟩ with hx'
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 L) x' ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) q
    obtain ⟨t, ht, hte⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp hxD).2 l l.2
    have htl : t = l⁻¹ * (x' * l * x'⁻¹) := Subtype.ext hte
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (l⁻¹ * (x' * l * x'⁻¹)) = 1 := by
      rw [← htl, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ht
    simp only [map_mul, map_inv] at h1
    exact eq_mul_inv_iff_mul_eq.mp (inv_mul_eq_one.mp h1)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hθeq] at hcen
  exact ⟨x', hcen, rfl⟩

theorem inv_mul_mem_thetaQuotCentralizer {L B U : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) (hBL : B ≤ L) (hB9 : Nat.card B = 9)
    (hB3 : IsPGroup 3 B) (hU2 : IsPGroup 2 U) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) {u v : G} (hu : u ∈ U) (hv : v ∈ U)
    (huD : u ∉ Sec4.thetaQuotCentralizer L) (hvD : v ∉ Sec4.thetaQuotCentralizer L) :
    u⁻¹ * v ∈ Sec4.thetaQuotCentralizer L := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
      mulAut_congr_conj]
  set X : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 2))) := (U.subgroupOf NL).map β
    with hXdef
  have hX2 : IsPGroup 2 X := (hU2.comap_subtype (K := NL)).map β
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hX2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hmemX : ∀ (x : G) (hx : x ∈ NL), x ∈ U → β ⟨x, hx⟩ ∈ X := fun x hx hxU =>
    ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxU, rfl⟩
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
  have huN := hUN hu
  have hvN := hUN hv
  have hβu : β ⟨u, huN⟩ ≠ 1 := fun h => huD ((hβker u huN).mp h)
  have hβv : β ⟨v, hvN⟩ ≠ 1 := fun h => hvD ((hβker v hvN).mp h)
  rcases eq_bot_or_eq_zpowers_graphField card_galoisField_two_two hE9 hX3 hEX with hbot |
    ⟨τ, hτ, -, hττ, -⟩
  · exfalso
    have h := hmemX u huN hu
    rw [hbot, Subgroup.mem_bot] at h
    exact hβu h
  · have hu' := hmemX u huN hu
    have hv' := hmemX v hvN hv
    rw [hτ] at hu' hv'
    have hu1 := (eq_one_or_eq_of_mem_zpowers hττ hu').resolve_left hβu
    have hv1 := (eq_one_or_eq_of_mem_zpowers hττ hv').resolve_left hβv
    have hmem : u⁻¹ * v ∈ NL := NL.mul_mem (NL.inv_mem huN) hvN
    refine (hβker _ hmem).mp ?_
    have e : (⟨u⁻¹ * v, hmem⟩ : NL) = (⟨u, huN⟩ : NL)⁻¹ * ⟨v, hvN⟩ := rfl
    rw [e, map_mul, map_inv, hu1, hv1, inv_mul_cancel]

end Item186Proof

end CFSG.RankThree.PartTwo.Sec18
