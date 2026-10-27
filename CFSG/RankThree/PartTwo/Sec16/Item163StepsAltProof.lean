module

public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofA7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofSeven
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec4.Steps434
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def Step163A7Hyp162 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
    ∀ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → La ≤ Y →
      Subgroup.zpowers a ≠ Subgroup.zpowers c →
      ∀ w ∈ Subgroup.normalizer (A : Set G),
        Subgroup.zpowers c = (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom →
          QTwoNe A Y (Y.map (MulAut.conj w).toMonoidHom)

@[expose] def Step163A7Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    WStarS4 A → TransOmegaThree A c →
    ∀ Y ∈ scriptY0Star A (lB A), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) →
    ∀ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → La ≤ Y →
      Subgroup.zpowers a ≠ Subgroup.zpowers c →
        ∃ Q ∈ scriptQPi A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))
          (piOf 2), Q ≠ ⊥

namespace Step163Alt

variable {G : Type} [Group G] [Finite G]

theorem sectionCentralizer_eq_zpowers {A Y La : Subgroup G} {a : G} (hLa : La ∈ lA A a)
    (hLaY : La ≤ Y) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤
      Nat.card (↥La ⧸ aschbacherSolvableCore 3 ↥La)) :
    Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers a : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hLaC : La ≤ Subgroup.centralizer {a} := le_centralizer_of_mem_thetaComponentsAt hLa.1
  have hALa : A ≤ Subgroup.normalizer (La : Set G) := hLa.2.1
  have hsc := hLa.2.2.1
  set θ := aschbacherSolvableCore 3 ↥La with hθdef
  have hθ : ∀ l : ↥La, (l : G) ∈ O → l ∈ θ := by
    intro l hl
    have hN : (O.subgroupOf La).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hYO (hLaY g.2)) n).mp hn
    have hP : IsPGroup 2 (O.subgroupOf La) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y).comap_subtype
    exact Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) hN hP hl
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  set ρ : ↥La →* ↥Y ⧸ CFSG.pCore 2 ↥Y := π.comp (Subgroup.inclusion hLaY) with hρ
  have hρker : ρ.ker ≤ θ := by
    intro l hl
    refine hθ l ?_
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pCore_two_iff] at hl
    exact hl
  have hρtop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    have h1 : Nat.card La = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    have h2 : Nat.card La = Nat.card (↥La ⧸ θ) * Nat.card θ :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    have h3 : Nat.card ρ.ker ≤ Nat.card θ := Subgroup.card_le_of_le hρker
    have hpos : 0 < Nat.card θ := Nat.card_pos
    have h4 : Nat.card (↥La ⧸ θ) ≤ Nat.card ρ.range := by
      by_contra hlt
      have := Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) h3 hpos
      omega
    omega
  have hcover : ∀ y : ↥Y, ∃ l : ↥La, (l : G)⁻¹ * y ∈ O := by
    intro y
    obtain ⟨l, hl⟩ : π y ∈ ρ.range := hρtop ▸ Subgroup.mem_top _
    exact ⟨l, (mk_eq_mk_iff (Subgroup.inclusion hLaY l) y).mp hl⟩
  ext t
  constructor
  · rintro ⟨htA, ht⟩
    have hmem : t ∈ Late.sectionCentralizer A La (θ.map La.subtype) := by
      refine ⟨htA, fun l hl => ?_⟩
      have h1 : t * l * t⁻¹ * l⁻¹ ∈ La :=
        La.mul_mem ((Subgroup.mem_normalizer_iff.mp (hALa htA) l).mp hl) (La.inv_mem hl)
      have h2 : t * l * t⁻¹ * l⁻¹ ∈ O := ht l (hLaY hl)
      exact ⟨⟨_, h1⟩, hθ ⟨_, h1⟩ h2, rfl⟩
    rw [hsc] at hmem
    exact hmem
  · intro ht
    have ht' : t ∈ Late.sectionCentralizer A La (θ.map La.subtype) := by
      rw [hsc]
      exact ht
    have htA : t ∈ A := ht'.1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨htA, fun y hy => ?_⟩
    obtain ⟨l, hl⟩ := hcover ⟨y, hy⟩
    set o := (l : G)⁻¹ * y with ho
    have hy' : y = (l : G) * o := by rw [ho, mul_inv_cancel_left]
    have htl : a ^ k * l = l * a ^ k :=
      ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLaC l.2)).symm k)).eq
    have e : a ^ k * y * (a ^ k)⁻¹ * y⁻¹ =
        (l : G) * (a ^ k * o * (a ^ k)⁻¹ * o⁻¹) * (l : G)⁻¹ := by
      calc a ^ k * y * (a ^ k)⁻¹ * y⁻¹
          = (a ^ k * l) * o * (a ^ k)⁻¹ * o⁻¹ * (l : G)⁻¹ := by rw [hy']; group
        _ = (l * a ^ k) * o * (a ^ k)⁻¹ * o⁻¹ * (l : G)⁻¹ := by rw [htl]
        _ = (l : G) * (a ^ k * o * (a ^ k)⁻¹ * o⁻¹) * (l : G)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYO (hLaY l.2)) _).mp
      (O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAO htA) o).mp hl) (O.inv_mem hl))

omit [Finite G] in
theorem sectionCentralizer_map_conj {A Y : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    Late.sectionCentralizer A (Y.map (MulAut.conj w).toMonoidHom)
        (CFSG.Open.pCoreOf 2 (Y.map (MulAut.conj w).toMonoidHom)) =
      (MulAut.conj w) '' Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) := by
  rw [image_sectionCentralizer (MulAut.conj w) A Y (CFSG.Open.pCoreOf 2 Y),
    Sec13.map_conj_eq_of_mem_normalizer hw, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]

omit [Finite G] in
theorem image_conj_eq_of_mem_centralizer {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (A : Set G)) {S : Set G} (hS : S ⊆ A) :
    (MulAut.conj x) '' S = S := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.mp hx t (hS ht), mul_inv_cancel_right]
    exact ht
  · intro hs
    refine ⟨s, hs, ?_⟩
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.mp hx s (hS hs), mul_inv_cancel_right]

theorem nonempty_a7_of_point {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hT : TransOmegaThree A c) {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A)
    (hLa : La ∈ lA A a) :
    Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨v₁, hv₁, hav₁⟩ := hT.2 _ ha
  have ha' : Sec15R G A a La := sec15R_of_point h ha hLa
  exact nonempty_a7_of_map_conj
    (map_conj_eq_of_zpowers ha' h.zpowers_mem_omegaA h.mem_lA hv₁ hav₁) h7

theorem sectionCentralizer_eq_of_config {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hT : TransOmegaThree A c) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) {a : G} {La : Subgroup G}
    (ha : Subgroup.zpowers a ∈ omegaA A) (hLa : La ∈ lA A a) (hLaY : La ≤ Y) :
    Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers a : Set G) := by
  obtain ⟨φa⟩ := nonempty_a7_of_point h h7 hT ha hLa
  refine sectionCentralizer_eq_zpowers hLa hLaY hY.prop.1.1.2 ?_
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr φa.toEquiv]

end Step163Alt

theorem step163A7TwoCycles :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      ∀ Y ∈ scriptY0Star A (lB A),
      ∀ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → La ≤ Y →
        Subgroup.zpowers a ≠ Subgroup.zpowers c →
        ∀ (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) (g : G) (hg : g ∈ Y),
          (∀ y ∈ Y, (g * y * g⁻¹)⁻¹ * (c * y * c⁻¹) ∈ CFSG.Open.pCoreOf 2 Y) →
          ((φ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨g, hg⟩) : alternatingGroup (Fin 7)) :
              Equiv.Perm (Fin 7)).cycleType = {3, 3} →
          generalizedFitting ↥Y = CFSG.pCore 2 ↥Y →
            CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer {c} ≠ ⊥ := by
  intro G _ _ A c L h _ _ _ Y hY _ _ _ _ _ _ φ g hg hcg hσ hF
  have hD := h.toSec13Data
  exact Step163Alt.pCoreOf_inf_centralizer_ne_bot_of_twoCycles (hY.prop.1.1.2 hD.mem_A)
    (hD.isElemAbelian.2 c hD.mem_A) hg φ hcg hσ hF

theorem step163A7Claim_of (h142 : Concl142R) (h153 : Item153MainR) : Step163A7Claim := by
  intro G _ _ A c L h h7 hW hT Y hY hY7 a La ha hLa hLaY hac
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hY7
  have hD := h.toSec13Data
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hcA : c ∈ A := hD.mem_A
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hO
  obtain ⟨-, hZ, hinner, -, -⟩ := KFacts.KS14.a7_facts (↥Y ⧸ N) ⟨φ⟩
  obtain ⟨gb, hgb⟩ := hinner (Step163Alt.conjQuotTwo Y hcN)
    ⟨1, by rw [pow_one]; exact Step163Alt.conjQuotTwo_pow_three Y hcN hc3⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective N gb
  have hact : ∀ y : ↥Y, π ⟨c * y * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y).mp y.2⟩ =
      π g₀ * π y * (π g₀)⁻¹ := by
    intro y
    have h1 := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ (π y)) hgb
    simp only [hπ, QuotientGroup.mk'_apply] at h1
    rw [Step163Alt.conjQuotTwo_mk, MulAut.conj_apply] at h1
    simpa only [hπ, QuotientGroup.mk'_apply] using h1
  have hcg : ∀ y ∈ Y, ((g₀ : G) * y * (g₀ : G)⁻¹)⁻¹ * (c * y * c⁻¹) ∈ O := by
    intro y hy
    have h2 := (Step163Alt.mk_eq_mk_iff (g₀ * ⟨y, hy⟩ * g₀⁻¹)
      ⟨c * y * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y).mp hy⟩).mp
      (by rw [map_mul, map_mul, map_inv]; exact (hact ⟨y, hy⟩).symm)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hsc := Step163Alt.sectionCentralizer_eq_of_config h h7 hT hY φ ha hLa hLaY
  have hgb1 : π g₀ ≠ 1 := by
    intro h1
    have hcsc : c ∈ Late.sectionCentralizer A Y O := by
      refine ⟨hcA, fun y hy => ?_⟩
      have h2 := (Step163Alt.mk_eq_mk_iff ⟨y, hy⟩
        ⟨c * y * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y).mp hy⟩).mp
        (by
          have h3 := hact ⟨y, hy⟩
          rw [h1, one_mul, inv_one, mul_one] at h3
          exact h3.symm)
      have e : c * y * c⁻¹ * y⁻¹ = y * (y⁻¹ * (c * y * c⁻¹)) * y⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hy) _).mp h2
    rw [hsc] at hcsc
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hcsc
    have heq : Subgroup.zpowers c = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [hD.card_zpowers, (zpowers_mem_omegaA_iff.mp ha).2.1])
    exact hac heq.symm
  set σ : Equiv.Perm (Fin 7) := ((φ (π g₀) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
    with hσ
  have hgb3 : π g₀ ^ 3 = 1 := by
    have h1 : MulAut.conj (π g₀ ^ 3) = 1 := by
      rw [map_pow, ← hgb, Step163Alt.conjQuotTwo_pow_three Y hcN hc3]
    have hcen : π g₀ ^ 3 ∈ Subgroup.center (↥Y ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ q) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc q * π g₀ ^ 3 = π g₀ ^ 3 * q * (π g₀ ^ 3)⁻¹ * π g₀ ^ 3 := by rw [this]
        _ = π g₀ ^ 3 * q := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← Subgroup.coe_pow, ← map_pow, hgb3, map_one, Subgroup.coe_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hgb1
    apply φ.injective
    rw [map_one]
    exact Subtype.ext h1
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hR : CFSG.Open.pCoreOf 2 (Y ⊓ Subgroup.centralizer {c}) ≠ ⊥ := by
    rcases KFacts.KP2.cycleType_of_orderOf_eq_three hord with h3 | h33
    · exact Step163Alt.pCoreOf_inf_centralizer_ne_bot hcN hc3 g₀.2 φ hcg h3
    · have hOC :=
        step163A7TwoCycles G A c L h h7 hW hT Y hY a La ha hLa hLaY hac φ g₀ g₀.2 hcg h33
        (h153 G A c L h Y hY).2.2
      intro hbot
      apply hOC
      refine le_bot_iff.mp (le_trans ?_ hbot.le)
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_inf_right _ (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)) ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y).to_le inf_le_left)
      intro z hz
      obtain ⟨hzY, hzc⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hzO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hzY
      constructor
      · rintro ⟨hxO, hxc⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hzO x).mp hxO,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hzc hxc) (Subgroup.inv_mem _ hzc)⟩
      · rintro ⟨hxO, hxc⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hzO x).mpr hxO, ?_⟩
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzc) hxc) hzc
        rwa [show z⁻¹ * (z * x * z⁻¹) * z = x by group] at this
  set R := CFSG.Open.pCoreOf 2 (Y ⊓ Subgroup.centralizer {c}) with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hRK : R ≤ Y ⊓ Subgroup.centralizer {c} := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hAK : A ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) := by
    intro x hx
    have hxY := hAY hx
    have hxc : x ∈ Subgroup.centralizer {c} := hD.A_le_centralizer hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyY, hyc⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxY y).mp hyY,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hxc hyc) (Subgroup.inv_mem _ hxc)⟩
    · rintro ⟨hyY, hyc⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxY y).mpr hyY, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxc) hyc) hxc
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hRK.trans (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers c))
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hRQ : R ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_concl142 (h142 G A c L h) hD.zpowers_mem_omegaA
      ⟨hRH, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hR3, hAR⟩
  exact ⟨R, ⟨⟨hRQ, le_inf (hRK.trans inf_le_left) hRH⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hR2⟩, hR⟩

end CFSG.RankThree.PartTwo.Sec16
