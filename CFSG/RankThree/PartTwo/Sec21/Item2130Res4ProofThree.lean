module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofLift
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofNoField
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofThree
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSU)


@[expose] def KSL3PiCubeField :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G) (c : G) (I : Subgroup G) (m : ℕ),
    1 ≤ m → orderOf c = 3 → c ∈ Subgroup.normalizer (Y : Set G) →
    I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    Sec4.IsSLThreePiAt (lBar Y) (2 ^ (3 * m)) → Sec4.IsSLThreePiAt (lBar I) (2 ^ m) →
      KFacts.InducesStdKind Y c .field

namespace Item2130Res4Proof

variable {G : Type} [Group G] [Finite G]

theorem inf_theta_le_theta {Y I : Subgroup G} (hIY : I ≤ Y) :
    inSubgroup (aschbacherSolvableCore 3) Y ⊓ I ≤ inSubgroup (aschbacherSolvableCore 3) I := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥I) Nat.prime_three
  set θY := inSubgroup (aschbacherSolvableCore 3) Y with hθY
  set T := (θY ⊓ I).subgroupOf I with hT
  have hmemθ : ∀ t : G, t ∈ θY → ∃ ht : t ∈ Y, (⟨t, ht⟩ : Y) ∈ aschbacherSolvableCore 3 Y := by
    rintro _ ⟨t', ht', rfl⟩
    exact ⟨t'.2, ht'⟩
  let ι : T →* aschbacherSolvableCore 3 Y :=
    { toFun := fun t => ⟨⟨((t : I) : G), (hmemθ _ t.2.1).1⟩, (hmemθ _ t.2.1).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun s t hst => by
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : aschbacherSolvableCore 3 Y => ((z : Y) : G)) hst
    exact this
  have hTs : Group.IsSolvable T := by
    have := hθs
    exact Group.isSolvable_of_isSolvable_injective hι
  have hT3 : ¬ 3 ∣ Nat.card T := fun h => hθ3 (h.trans (Subgroup.card_dvd_of_injective ι hι))
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    refine ⟨?_, (I.mul_mem (I.mul_mem g.2 ht.2) (I.inv_mem g.2))⟩
    have hgN := Sec6.le_normalizer_theta Y (hIY g.2)
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp ht.1
  have hle := hmax T hTn hTs hT3
  intro t ht
  have htT : (⟨t, ht.2⟩ : I) ∈ T := Subgroup.mem_subgroupOf.mpr ht
  exact ⟨_, hle htT, rfl⟩

theorem mem_lZeroUnion_of_two_subgroup {A I Y U' : Subgroup G} {b c x : G}
    (hAe : IsElemAbelian 3 A) (hbA : b ∈ A) (hcA : c ∈ A) (hxA : x ∈ A) (hb1 : b ≠ 1)
    (hbI : I ≤ Subgroup.centralizer ({b} : Set G)) (hcI : I ≤ Subgroup.centralizer ({c} : Set G))
    (hxI : x ∈ Subgroup.normalizer (I : Set G))
    (hc : c ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers x)
    (hYb : Y ∈ thetaComponentsAt 3 b) (hIY : I ≤ Y) (hU'I : U' ≤ I) (hU'2 : IsPGroup 2 U')
    (hxU' : x ∈ Subgroup.normalizer (U' : Set G))
    (hU'x : ¬ ⁅U', Subgroup.zpowers x⁆ ≤ inSubgroup (aschbacherSolvableCore 3) I) :
    Y ∈ lZeroUnion A := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hUxI : ⁅U', Subgroup.zpowers x⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro u hu z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzI : x ^ k ∈ Subgroup.normalizer (I : Set G) := Subgroup.zpow_mem _ hxI k
    rw [commutatorElement_def]
    have h1 : x ^ k * u⁻¹ * (x ^ k)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp hzI _).mp (I.inv_mem (hU'I hu))
    have : u * x ^ k * u⁻¹ * (x ^ k)⁻¹ = u * (x ^ k * u⁻¹ * (x ^ k)⁻¹) := by group
    rw [this]
    exact I.mul_mem (hU'I hu) h1
  have hxb : x ∉ Subgroup.zpowers b := by
    intro hxb
    apply hU'x
    have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer (I : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro i hi
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxb
      have h1 : i * b = b * i := Subgroup.mem_centralizer_singleton_iff.mp (hbI hi)
      exact (Commute.zpow_right h1 k).eq
    have hbot : ⁅U', Subgroup.zpowers x⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu z hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hxC hz) u (hU'I hu))
    rw [hbot]
    exact bot_le
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU'x
    rw [hbot, Subgroup.commutator_bot_left]
    exact bot_le
  set E₁ := Subgroup.zpowers b ⊔ Subgroup.zpowers x with hE₁
  set E' := E₁ ⊔ Subgroup.zpowers c with hE'
  have hE₁A : E₁ ≤ A := sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr hxA)
  have hE'A : E' ≤ A := sup_le hE₁A (Subgroup.zpowers_le.mpr hcA)
  have hb3' : Nat.card (Subgroup.zpowers b) = 3 := Sec13.card_zpowers_of_pow_three hb3 hb1
  have hcardE₁ : Nat.card E₁ = 9 := by
    rw [hE₁, PartOne.Planes.card_sup_zpowers Nat.prime_three _ hx3 hxb (fun e he =>
      hcomm e ((Subgroup.zpowers_le.mpr hbA) he) x hxA), hb3']
  have hcardE' : Nat.card E' = 27 := by
    rw [hE', PartOne.Planes.card_sup_zpowers Nat.prime_three _ hc3 hc (fun e he =>
      hcomm e (hE₁A he) c hcA), hcardE₁]
  have hE'N : E' ≤ Subgroup.normalizer (U' : Set G) := by
    have hcen : ∀ g : G, I ≤ Subgroup.centralizer ({g} : Set G) →
        g ∈ Subgroup.normalizer (U' : Set G) := by
      intro g hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mp (hg (hU'I hu))
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (hcen b hbI)
    · exact Subgroup.zpowers_le.mpr hxU'
    · exact Subgroup.zpowers_le.mpr (hcen c hcI)
  have hE'e : IsElemAbelian 3 E' := Sec4.isElemAbelian_of_le hAe hE'A
  have hE'E : E' ∈ partTwoE G := ⟨hE'e, hcardE', U', hU'1, hU'2, hE'N⟩
  have hbE' : b ∈ E' := (le_sup_left.trans le_sup_left : Subgroup.zpowers b ≤ E')
    (Subgroup.mem_zpowers b)
  refine mem_lZeroUnion_iff.mpr ⟨E', hE'E, hE'A, mem_thetaComponentFamily_iff.mpr
    ⟨b, hbE', hb1, hYb⟩, U', (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
    ⟨hU'I.trans hIY, hU'2, hE'N⟩, fun hle => hU'x ?_⟩
  have hxE' : Subgroup.zpowers x ≤ E' := le_sup_right.trans le_sup_left
  exact le_trans (le_inf ((Subgroup.commutator_mono le_rfl hxE').trans hle) hUxI)
    (inf_theta_le_theta hIY)

section Certs


open Item211Res2Proof in
theorem false_of_cube (h45 : Sec4.Item4_5) (h1134 : Item1134Four) (hK : KSL3PiCubeField)
    {A E U L : Subgroup G} {c b : G} {I Y : Subgroup G} (hcfg : Config2130 G A E U c L)
    (h81 : Nat.card A = 3 ^ 4) (hbB : b ∈ A ⊓ L) (hb1 : b ≠ 1)
    (hI : I ∈ thetaComponentsIn
      (Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G)))
    (hBN : A ⊓ L ≤ Subgroup.normalizer (I : Set G))
    (hα : A ⊓ L ⊓ Sec4.thetaQuotCentralizer I ≤ Subgroup.zpowers b)
    (hYb : Y ∈ thetaComponentsAt 3 b) (hY0 : Y ∈ lZeroUnion A) (hIY : I ≤ Y) {m : ℕ}
    (hm : 1 ≤ m) (hYm : Sec4.IsSLThreePiAt (lBar Y) (2 ^ (3 * m)))
    (hIm : Sec4.IsSLThreePiAt (lBar I) (2 ^ m)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfg.pair
  have hG := hpair.standing.toTheoremFourHyp
  obtain ⟨⟨hcE, -⟩, hc1, -, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hbA : b ∈ A := hbB.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcB : c ∉ A ⊓ L := fun h => hcfg.not_mem h.2
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left hcB hcfg.card_eq
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 Y hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have h3n : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer ({b} : Set G) →
      S ≤ Subgroup.normalizer (Y : Set G) := fun S hS hSC =>
    Item211Res3Proof.le_normalizer_of_isPGroup h45 hG hb3 hb1 hS hSC Y hYb
  have hQ : ∀ b' ∈ A ⊓ L, ∃ w, w ∈ Subgroup.normalizer (Y : Set G) ∧
      w ∈ Subgroup.normalizer (A : Set G) ∧ (∀ x ∈ A ⊓ L, w * x * w⁻¹ = x) ∧
        w * c * w⁻¹ = c * b' := by
    intro b' hb'
    have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
    obtain ⟨w, hwW, hwB, hwc⟩ := hcfg.full b' hb'
    obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb' hwB hwc
    have hwkB := pow_conj_eq_of_conj_eq hwB k
    have hle : Subgroup.zpowers (w ^ k) ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h1 := hwkB b hbB
      calc w ^ k * b = w ^ k * b * (w ^ k)⁻¹ * w ^ k := by group
        _ = b * w ^ k := by rw [h1]
    exact ⟨w ^ k, h3n _ hk3 hle (Subgroup.mem_zpowers _), Subgroup.pow_mem _ hwW k, hwkB, hkc⟩
  set D := A ⊓ Sec4.thetaQuotCentralizer Y with hD
  have hbD : b ∈ D := ⟨hbA, Item211Res3Proof.mem_thetaQuotCentralizer_of_le_centralizer hYC⟩
  have hAD : ¬ A ≤ D := fun hle =>
    Item211Res3Proof.not_le_thetaQuotCentralizer hY0 hAY fun x hx => (hle hx).2
  have hDQ : ∀ w, w ∈ Subgroup.normalizer (Y : Set G) → w ∈ Subgroup.normalizer (A : Set G) →
      ∀ x ∈ D, w * x * w⁻¹ ∈ D := fun w hwY hwA x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hwA x).mp hx.1,
      Sec6.conj_mem_thetaQuotCentralizer hx.2 hwY⟩
  have hDB : D ≤ A ⊓ L := by
    intro x hxD
    obtain ⟨i, hi, b₁, hb₁, rfl⟩ := Sec13.exists_pow_mul_of_mem hAe hcA hAB hxD.1
    have hb₁A : b₁ ∈ A := hb₁.1
    interval_cases i
    · rwa [pow_zero, one_mul]
    · exfalso
      have hBD : A ⊓ L ≤ D := by
        intro b'' hb''
        obtain ⟨w, hwY, hwA, hwB, hwc⟩ := hQ b'' hb''
        have h1 := hDQ w hwY hwA _ hxD
        have e : w * (c ^ 1 * b₁) * w⁻¹ * (c ^ 1 * b₁)⁻¹ = b'' := by
          have e1 : w * (c ^ 1 * b₁) * w⁻¹ = (w * c * w⁻¹) * (w * b₁ * w⁻¹) := by group
          rw [e1, hwc, hwB b₁ hb₁, pow_one, mul_inv_rev,
            hcomm c hcA b'' hb''.1]
          group
        rw [← e]
        exact D.mul_mem h1 (D.inv_mem hxD)
      have hcD : c ∈ D := by
        have := D.mul_mem hxD (D.inv_mem (hBD hb₁))
        rwa [pow_one, mul_inv_cancel_right] at this
      exact hAD (hAB ▸ sup_le (Subgroup.zpowers_le.mpr hcD) hBD)
    · exfalso
      have hBD : A ⊓ L ≤ D := by
        intro b'' hb''
        have hb''3 : b'' ^ 3 = 1 := hAe.2 b'' hb''.1
        obtain ⟨w, hwY, hwA, hwB, hwc⟩ := hQ (b'' ^ 2) ((A ⊓ L).pow_mem hb'' 2)
        have h1 := hDQ w hwY hwA _ hxD
        have hcb : c * b'' = b'' * c := hcomm c hcA b'' hb''.1
        have e : w * (c ^ 2 * b₁) * w⁻¹ * (c ^ 2 * b₁)⁻¹ = b'' := by
          have e1 : w * (c ^ 2 * b₁) * w⁻¹ =
              (w * c * w⁻¹) * (w * c * w⁻¹) * (w * b₁ * w⁻¹) := by
            rw [pow_two]
            group
          rw [e1, hwc, hwB b₁ hb₁]
          have hc2 : c * b'' ^ 2 = b'' ^ 2 * c := (Commute.pow_right hcb 2).eq
          have hc4 : c ^ 2 * b'' ^ 4 = b'' ^ 4 * c ^ 2 :=
            ((Commute.pow_right hcb 4).pow_left 2).eq
          have e2 : c * b'' ^ 2 * (c * b'' ^ 2) = c ^ 2 * b'' ^ 4 := by
            calc c * b'' ^ 2 * (c * b'' ^ 2) = c * (b'' ^ 2 * c) * b'' ^ 2 := by
                  simp only [mul_assoc]
              _ = c * (c * b'' ^ 2) * b'' ^ 2 := by rw [hc2]
              _ = (c * c) * (b'' ^ 2 * b'' ^ 2) := by simp only [mul_assoc]
              _ = c ^ 2 * b'' ^ 4 := by rw [← pow_two, ← pow_add]
          have e3 : c ^ 2 * b'' ^ 4 * b₁ * (c ^ 2 * b₁)⁻¹ = b'' ^ 4 := by
            rw [mul_inv_rev, mul_assoc (c ^ 2 * b'' ^ 4) b₁, mul_inv_cancel_left, hc4,
              mul_inv_cancel_right]
          rw [e2, e3, show 4 = 3 + 1 by norm_num, pow_succ, hb''3, one_mul]
        rw [← e]
        exact D.mul_mem h1 (D.inv_mem hxD)
      have hc2D : c ^ 2 ∈ D := by
        have := D.mul_mem hxD (D.inv_mem (hBD hb₁))
        rwa [mul_inv_cancel_right] at this
      have hcD : c ∈ D := by
        have := D.pow_mem hc2D 2
        rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul] at this
      exact hAD (hAB ▸ sup_le (Subgroup.zpowers_le.mpr hcD) hBD)
  have hDb : D ≤ Subgroup.zpowers b := by
    intro d hd
    have hdB := hDB hd
    have hdN := hBN hdB
    refine hα ⟨hdB, Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hdN, fun i hi => ?_⟩⟩
    obtain ⟨-, hdY⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hd.2
    exact inf_theta_le_theta hIY ⟨hdY i (hIY hi),
      I.mul_mem (I.inv_mem hi) ((Subgroup.mem_normalizer_iff.mp hdN i).mp hi)⟩
  have hYs : Y ∈ lStar A := Sec6.mem_lStar_of_inf_le_zpowers hAe hbA hb1 hYb hAY hDb
  have hDeq : D = Subgroup.zpowers b := le_antisymm hDb (Subgroup.zpowers_le.mpr hbD)
  have hsc : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers b : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAY, ← hD, hDeq]
  have hNF := h1134 G A b Y hpair.standing hpair.mem_S.1 h81 hbA hb1 ⟨hYs, hYb⟩ hsc
    (exists_invTwoBarNontrivial hY0) c hcA
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hIYc : I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
    obtain ⟨hICB, hIθ⟩ := mem_thetaComponentsIn_iff.mp hI
    have hcI : I ≤ Subgroup.centralizer ({c} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hICB hy) c
        (Subgroup.subset_closure (by simp))).symm
    have hle1 : I ≤ Y ⊓ Subgroup.centralizer ({c} : Set G) := le_inf hIY hcI
    have hle2 : Y ⊓ Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G) := by
      rintro y ⟨hyY, hyc⟩
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro g hg
      rcases hg with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hYC hyY)).symm
    exact mem_thetaComponentsIn_iff.mpr
      ⟨hle1, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle1 hle2 hIθ⟩
  exact hNF.1 (hK G Y c I m hm hc3' (hAY hcA) hIYc hYm hIm)

end Certs

end Item2130Res4Proof

open Item2130Res4Proof

section Certs


theorem item2130ThreeYU4_of_res4 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h1134 : Item1134Four) (hK : KSL3PiCubeField) :
    Item2130ThreeYU4 := by
  intro G _ _ A E U c L hcfg h27 hL h81 _
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  obtain ⟨b, hbB, hb1, I, hIL, hIth, hIZ, ⟨n, hn, hISL⟩, hBN, hα, x, hxB, U', hU'I, hU'2, hxU',
    hU'x⟩ := item2130ThreeIPlus_holds G A E U c L hcfg h27 hL h81
  obtain ⟨Y, hYb, hIY, hY⟩ := Item2130Res3Proof.exists_mem_of_mem_thetaComponentsIn h48 h426
    hcfg.pair.standing hAe h81 hbB.1 hb1 hcA hpairs.2.1 hIth hIZ (by omega) hISL
  have hbZ : b ∈ I ⊓ Subgroup.centralizer (I : Set G) := by
    have hbO : b ∈ inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) := by
      rw [hIZ]
      exact Subgroup.mem_zpowers b
    exact Subgroup.map_subtype_le _ hbO
  have hbI : I ≤ Subgroup.centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hbZ.2 y hy
  have hcI : I ≤ Subgroup.centralizer ({c} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((mem_thetaComponentsIn_iff.mp hIth).1 hy) c
      (Subgroup.subset_closure (by simp))).symm
  have hc : c ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers x := fun h => hcfg.not_mem
    ((sup_le (Subgroup.zpowers_le.mpr hbB.2) (Subgroup.zpowers_le.mpr hxB.2)) h)
  have hY0 : Y ∈ lZeroUnion A := mem_lZeroUnion_of_two_subgroup hAe hbB.1 hcA hxB.1 hb1 hbI hcI
    (hBN hxB) hc hYb hIY hU'I hU'2 hxU' hU'x
  rcases hY with hY | ⟨m, hm, hYm, hIm⟩
  · exact ⟨b, hbB, hb1, Y, hYb, hY0, I, hIL, hY⟩
  · exact (false_of_cube h45 h1134 hK hcfg h81 hbB hb1 hIth hBN hα hYb hY0 hIY hm hYm
      hIm).elim

theorem item2130LocalThree_of_res4 (h45 : Sec4.Item4_5)
    (h211 : Item211) (h213 : Item213) (h217 : Item217) (h2116 : Item2116) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h1134 : Item1134Four) (hK : KSL3PiCubeField) :
    Item2130LocalThree :=
  item2130LocalThree_of h45 (item2130ThreeY_of h211 h213 h217 h2116
    (item2130ThreeYU4_of_res4 h45 h48 h426 h1134 hK))

end Certs

end CFSG.RankThree.PartTwo.Sec21
