module

public import CFSG.Timmesfeld.Transvection.OddResidueFix
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
import CFSG.Timmesfeld.Transvection.OddTranslationsReg
import CFSG.Timmesfeld.Transvection.OddSU3Borel
import CFSG.Timmesfeld.Transvection.OddTranslations
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.Timmesfeld.Transvection.OddResiduePerp
import CFSG.Timmesfeld.Transvection.LineStabTorus
import CFSG.GroupTheory.FixedPointFreeCommutator
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2Pow
public import CFSG.Timmesfeld.Transvection.PlaneGroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

section CertificateFree

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem conjSub_map_heis_eq (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) {A : Subgroup H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = A) {g : H}
    (hg : conjSub θ.range g = θ.range) (hgA : conjSub A g = A) :
    conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) g =
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
  let B : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ
  have hBA : B ≤ θ.range := Subgroup.map_le_range θ _
  have hcardB : Nat.card ↥B = (2 ^ n) ^ 3 := card_map_heis_of_odd hFn hθk
  have hgAinv : conjSub A g⁻¹ = A := by
    have h := Aux.conjSub_conjSub_inv A g
    rwa [hgA] at h
  have hle : conjSub B g ≤ B := by
    rintro x ⟨b, hb, rfl⟩
    show g * b * g⁻¹ ∈ B
    have hxr : g * b * g⁻¹ ∈ θ.range := hg ▸ conj_mem_conjSub g (hBA hb)
    have hxA : conjSub A (g * b * g⁻¹) = A := by
      rw [conjSub_mul, hgAinv, conjSub_mul,
        conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hb, hgA]
    have hbpow : b ^ 2 ^ (n * 3) = 1 := by
      have h := pow_card_eq_one' (G := ↥B) (x := ⟨b, hb⟩)
      rw [hcardB, ← pow_mul] at h
      simpa using congrArg Subtype.val h
    have hxpow : (g * b * g⁻¹) ^ 2 ^ (n * 3) = 1 := by
      rw [conj_pow, hbpow]
      group
    exact mem_map_heis_of_conjSub_eq hFn hθk hθt hxr hxA hxpow
  have hcard_eq : Nat.card ↥(conjSub B g) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hcardB]; positivity)
  show conjSub B g = B
  exact Subgroup.eq_of_le_of_card_ge hle hcard_eq.ge

theorem IsFrame.map_heis_sup_le_rankTwoResidueGroup (hF : IsFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) {i : Fin r} :
    (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) ≤
      rankTwoResidueGroup Δ P Q k i := by
  refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
  · exact (Subgroup.map_le_range θ _).trans
      (hθr.le.trans (residueGroup_le_rankTwoResidueGroup_left k i))
  · exact fun y hy => hF.lineGroup_le_rankTwoResidueGroup
      (hF.memP_rankTwoResidue_left k i) (hF.memQ_rankTwoResidue_right k i) hy.1.1
  · exact fun y hy => hF.lineGroup_le_rankTwoResidueGroup
      (hF.memP_rankTwoResidue_left k i) (hF.memP_rankTwoResidue_right k i) hy.1.1
  · exact le_rankTwoResidueGroup (hF.memP_rankTwoResidue_left k i)

theorem IsMaxFrame.conjSub_map_heis_sup_eq (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθk : Odd (Nat.card θ.ker)) (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    {i : Fin r} (hik : i ≠ k) {g : H} (hg : g ∈ rankTwoResidueGroup Δ P Q k i)
    (hgP : conjSub (P k) g = P k) (hgQ : conjSub (Q k) g = Q k)
    (hgl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → g ∈ lineStab Δ (P k) C) :
    conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) g =
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) := by
  haveI : Finite H := h.finite
  have hPi : conjSub (P i) g = P i :=
    hF.conjSub_eq_of_mem_frameResidue h.cls h.points hML hik hg hgP hgQ hgl
      (hF.toIsFrame.memP_frameResidue i)
  have hQi : conjSub (Q i) g = Q i :=
    hF.conjSub_eq_of_mem_frameResidue h.cls h.points hML hik hg hgP hgQ hgl
      (hF.toIsFrame.memQ_frameResidue i)
  have hall : ∀ l : Fin r, conjSub (P l) g = P l ∧ conjSub (Q l) g = Q l := by
    intro l
    by_cases hlk : l = k
    · subst hlk
      exact ⟨hgP, hgQ⟩
    · by_cases hli : l = i
      · subst hli
        exact ⟨hPi, hQi⟩
      · have hc := commuting_rankTwoResidueGroup (Δ := Δ) (P := P) (Q := Q) hlk hli
        exact ⟨conjSub_of_forall_commute fun x hx => hc g hg x (Subgroup.mem_sup_left hx),
          conjSub_of_forall_commute fun x hx => hc g hg x (Subgroup.mem_sup_right hx)⟩
  have hrange : conjSub θ.range g = θ.range := by
    rw [hθr]
    have hset : (fun D => conjSub D g) '' frameResidue Δ P Q k = frameResidue Δ P Q k := by
      ext X
      constructor
      · rintro ⟨Y, hY, rfl⟩
        refine ⟨h.cls.root.conjSub_mem hY.1 g, fun l hlk => ?_⟩
        have hc := hY.2 l hlk
        rw [← (hall l).1, ← (hall l).2]
        exact ⟨(Aux.commuting_conjSub_iff g).2 hc.1, (Aux.commuting_conjSub_iff g).2 hc.2⟩
      · intro hX
        have hginv : ∀ l : Fin r, conjSub (P l) g⁻¹ = P l ∧ conjSub (Q l) g⁻¹ = Q l := by
          intro l
          have h1 := congrArg (fun D => conjSub D g⁻¹) (hall l).1
          rw [Aux.conjSub_conjSub_inv] at h1
          have h2 := congrArg (fun D => conjSub D g⁻¹) (hall l).2
          rw [Aux.conjSub_conjSub_inv] at h2
          exact ⟨h1.symm, h2.symm⟩
        have hY : conjSub X g⁻¹ ∈ frameResidue Δ P Q k := by
          refine ⟨h.cls.root.conjSub_mem hX.1 g⁻¹, fun l hlk => ?_⟩
          have hc := hX.2 l hlk
          rw [← (hginv l).1, ← (hginv l).2]
          exact ⟨(Aux.commuting_conjSub_iff g⁻¹).2 hc.1,
            (Aux.commuting_conjSub_iff g⁻¹).2 hc.2⟩
        refine ⟨conjSub X g⁻¹, hY, ?_⟩
        show conjSub (conjSub X g⁻¹) g = X
        rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [residueGroup, conjSub_iSup_mem, hset]
  have hB : conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) g =
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ :=
    conjSub_map_heis_eq hFn hθk hθt hrange hgP
  have hY₁ : conjSub (shortRootGroup Δ (P k) (Q k) (Q i) (P i)) g =
      shortRootGroup Δ (P k) (Q k) (Q i) (P i) := by
    rw [← shortRootGroup_conjSub h.cls.root (P k) (Q k) (Q i) (P i) g, hgP, hgQ, hQi, hPi]
  have hY₂ : conjSub (shortRootGroup Δ (P k) (Q k) (P i) (Q i)) g =
      shortRootGroup Δ (P k) (Q k) (P i) (Q i) := by
    rw [← shortRootGroup_conjSub h.cls.root (P k) (Q k) (P i) (Q i) g, hgP, hgQ, hPi, hQi]
  rw [conjSub_sup_eq_sup, conjSub_sup_eq_sup, conjSub_sup_eq_sup, hB, hY₁, hY₂, hgP]

private theorem eq_one_of_forall_eq_commutatorElement {B : Subgroup H} [Finite B] {t : H}
    (htB : conjSub B t = B) (hK : ∀ x ∈ B, ∃ y ∈ B, x = ⁅y, t⁆) {a : H} (ha : a ∈ B)
    (hta : t * a * t⁻¹ = a) : a = 1 := by
  let φ : ↥B → ↥B := fun y =>
    ⟨⁅(y : H), t⁆, by
      rw [commutatorElement_def]
      have hc : t * (y : H)⁻¹ * t⁻¹ ∈ B := by
        have h := conj_mem_conjSub t (B.inv_mem y.2)
        rwa [htB] at h
      rw [show (y : H) * t * (y : H)⁻¹ * t⁻¹ = (y : H) * (t * (y : H)⁻¹ * t⁻¹) by group]
      exact B.mul_mem y.2 hc⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := hK x hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy.symm⟩
  have hinj : Function.Injective φ := Finite.injective_iff_surjective.2 hsurj
  have hcomm : Commute t a := mul_inv_eq_iff_eq_mul.1 hta
  have h1 : φ ⟨a, ha⟩ = φ 1 := by
    apply Subtype.ext
    show ⁅a, t⁆ = ⁅((1 : ↥B) : H), t⁆
    rw [Subgroup.coe_one, commutatorElement_one_left, commutatorElement_eq_one_iff_commute]
    exact hcomm.symm
  simpa using congrArg Subtype.val (hinj h1)

section Certificates


theorem IsMaxFrame.eq_one_of_mem_map_heis_sup_of_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {u : H}
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k))
    (huQ : conjSub (Q k) u = Q k) : u = 1 := by
  haveI : Finite H := h.finite
  have huG : u ∈ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr hu
  have huP : conjSub (P k) u = P k :=
    hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup h.cls hFn hθt hik hu
  have hul : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → u ∈ lineStab Δ (P k) C :=
    fun C hC hCP hPC =>
      hF.toIsFrame.sup_le_lineStab h hML hq hFn hcard hθt hθb hik hC hCP hPC hu
  have huPi : conjSub (P i) u = P i :=
    hF.conjSub_eq_of_mem_frameResidue h.cls h.points hML hik huG huP huQ hul
      (hF.toIsFrame.memP_frameResidue i)
  have huQi : conjSub (Q i) u = Q i :=
    hF.conjSub_eq_of_mem_frameResidue h.cls h.points hML hik huG huP huQ hul
      (hF.toIsFrame.memQ_frameResidue i)
  obtain ⟨M, hM, hMl⟩ := hF.exists_mem_frameResidue_not_mem_lineOf h hML hq hns hik
  have huM : conjSub M u = M :=
    hF.conjSub_eq_of_mem_frameResidue h.cls h.points hML hik huG huP huQ hul hM
  have hpk : u ∈ P k :=
    hF.mem_of_mem_map_heis_sup_of_conjSub_eq h hML hq hns hFn hcard hθr hθk hθt hθb hmem hik
      hM hMl hu huPi huQi huM
  exact (hF.opposite k).eq_one_of_conjSub_eq hpk huQ

theorem IsMaxFrame.exists_mem_map_heis_sup_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q k i) (hXP : ¬ Commuting X (P k)) :
    ∃ u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k), conjSub (Q k) u = X := by
  haveI : Finite H := h.finite
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  have hUG : U ≤ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr
  have hinj : Set.InjOn (fun u => conjSub (Q k) u) (U : Set H) := by
    intro u hu u' hu' heq
    have hprod : u'⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hu') hu
    have heq' : conjSub (Q k) u = conjSub (Q k) u' := heq
    have hfix : conjSub (Q k) (u'⁻¹ * u) = Q k := by
      rw [conjSub_mul, heq', Aux.conjSub_conjSub_inv]
    have h1 : u'⁻¹ * u = 1 :=
      hF.eq_one_of_mem_map_heis_sup_of_conjSub_eq h hML hq hns hFn hcard hθr hθk hθt hθb hmem
        hik hprod hfix
    exact (inv_mul_eq_one.1 h1).symm
  have himg_sub : (fun u => conjSub (Q k) u) '' (U : Set H) ⊆
      {X | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)} := by
    rintro X ⟨u, hu, rfl⟩
    refine ⟨conjSub_mem_rankTwoResidue h.cls (hF.toIsFrame.memQ_rankTwoResidue_left k i)
      (hUG hu), ?_⟩
    have huP : conjSub (P k) u = P k :=
      hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup h.cls hFn hθt hik hu
    have hiff : Commuting (conjSub (Q k) u) (P k) ↔ Commuting (Q k) (P k) := by
      have h := Aux.commuting_conjSub_iff u (X := Q k) (Y := P k)
      rwa [huP] at h
    exact fun hc => ModelRank.not_commuting_of_opposite (hF.opposite k).symm (hiff.1 hc)
  have himg_card : Nat.card ↥U = (2 ^ n) ^ 7 :=
    hF.card_map_heis_sup_eq h hML hq hns hFn hcard hθr hθk hθt hθb hik
  have hS_card : {X | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)}.ncard =
      (2 ^ n) ^ 7 := by
    rw [hF.ncard_rankTwoResidue_not_commuting_eq h hML hq hns hik, hcard (P k) (hF.memP k)]
  have himg_card' : ((fun u => conjSub (Q k) u) '' (U : Set H)).ncard = (2 ^ n) ^ 7 := by
    rw [hinj.ncard_image, ← Nat.card_coe_set_eq]
    change Nat.card ↥U = (2 ^ n) ^ 7
    exact himg_card
  have hEq : (fun u => conjSub (Q k) u) '' (U : Set H) =
      {X | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)} :=
    Set.eq_of_subset_of_ncard_le himg_sub (by rw [hS_card, himg_card'])
  have hXS : X ∈ (fun u => conjSub (Q k) u) '' (U : Set H) := hEq.symm ▸ ⟨hX, hXP⟩
  obtain ⟨u, hu, hXu⟩ := hXS
  exact ⟨u, hu, hXu⟩

private theorem eq_one_of_mem_map_heis_sup_of_fixed (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {t : H} (htG : t ∈ rankTwoResidueGroup Δ P Q k i)
    (htP : conjSub (P k) t = P k) (htQ : conjSub (Q k) t = Q k)
    (htl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → t ∈ lineStab Δ (P k) C)
    (hfreeP : ∀ a ∈ P k, t * a * t⁻¹ = a → a = 1) :
    ∀ u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k),
      t * u * t⁻¹ = u → u = 1 := by
  intro u hu hfix
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  have huG : u ∈ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr hu
  have huP : conjSub (P k) u = P k :=
    hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup h.cls hFn hθt hik hu
  have hXR : conjSub (Q k) u ∈ rankTwoResidue Δ P Q k i :=
    conjSub_mem_rankTwoResidue h.cls (hF.toIsFrame.memQ_rankTwoResidue_left k i) huG
  have hXP : ¬ Commuting (conjSub (Q k) u) (P k) := by
    have hc := Aux.commuting_conjSub_iff u (X := Q k) (Y := P k)
    rw [huP] at hc
    exact fun hcon => ModelRank.not_commuting_of_opposite (hF.opposite k).symm (hc.1 hcon)
  have hXt : conjSub (conjSub (Q k) u) t = conjSub (Q k) u := by
    rw [← conjSub_mul]
    have htfix : t * u = u * t := mul_inv_eq_iff_eq_mul.1 hfix
    rw [htfix, conjSub_mul, htQ]
  have hXQ : conjSub (Q k) u = Q k :=
    hF.eq_of_not_commuting_of_conjSub_eq h hML hq hns hik htG htP htQ htl hfreeP hXR hXP hXt
  exact hF.eq_one_of_mem_map_heis_sup_of_conjSub_eq h hML hq hns hFn hcard hθr hθk hθt hθb
    hmem hik hu hXQ

theorem IsMaxFrame.exists_mem_sup_forall_eq_commutatorElement (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) :
    ∃ t ∈ P k ⊔ Q k,
      conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
            shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) t =
        (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
            shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) ∧
      ∀ x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
          (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
            shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k),
        ∃ y ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
            (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
              shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k), x = ⁅y, t⁆ := by
  haveI : Finite H := h.finite
  have hn : 2 ≤ n := by
    by_contra hlt
    have h2 : 2 ^ n ≤ 2 := by
      simpa using Nat.pow_le_pow_right (by norm_num) (by omega : n ≤ 1)
    have hq' := hq (P k) (hF.memP k)
    have hcard' := hcard (P k) (hF.memP k)
    omega
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  obtain ⟨s, hs, hsA, hsE, hKs⟩ := exists_torus_map_heis hFn hn hθt hθb
  have htsup : θ s ∈ P k ⊔ Q k := hs
  have hUG : U ≤ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr
  have htG : θ s ∈ rankTwoResidueGroup Δ P Q k i := by
    have hle : P k ⊔ Q k ≤ rankTwoResidueGroup Δ P Q k i :=
      sup_le (le_rankTwoResidueGroup (hF.toIsFrame.memP_rankTwoResidue_left k i))
        (le_rankTwoResidueGroup (hF.toIsFrame.memQ_rankTwoResidue_left k i))
    exact hle hs
  have htl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → θ s ∈ lineStab Δ (P k) C :=
    fun C hC hCP hPC =>
      mem_lineStab_of_mem_sup_of_conjSub_eq h.cls h.points hML (hF.memP k) (hF.memQ k)
        (hF.opposite k).symm hC hCP hPC htsup hsA
  have htB : conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) (θ s) =
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
    refine conjSub_map_heis_eq hFn hθk hθt ?_ hsA
    rw [conjSub_eq_self_iff]
    exact Subgroup.le_normalizer (MonoidHom.mem_range.2 ⟨s, rfl⟩)
  have hPkB : P k ≤ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
    rw [← hθt]
    exact Subgroup.map_mono (su3Top_le_X (unitaryInvolution_involutive hFn))
  have hfreeP : ∀ a ∈ P k, θ s * a * (θ s)⁻¹ = a → a = 1 :=
    fun a ha hfix => eq_one_of_forall_eq_commutatorElement htB hKs (hPkB ha) hfix
  have hfreeU : ∀ u ∈ U, θ s * u * (θ s)⁻¹ = u → u = 1 :=
    eq_one_of_mem_map_heis_sup_of_fixed h hML hq hF hns hFn hcard hθr hθk hθt hθb hmem hik
      htG hsA hsE htl hfreeP
  have htU : conjSub U (θ s) = U :=
    hF.conjSub_map_heis_sup_eq h hML hFn hθr hθk hθt hik htG hsA hsE htl
  refine ⟨θ s, htsup, ?_, ?_⟩
  · exact htU
  · show ∀ x ∈ U, ∃ y ∈ U, x = ⁅y, θ s⁆
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      CFSG.exists_eq_conj_mul_inv_of_fixedPointFree (T := U) (conjSub_eq_self_iff.1 htU)
        hfreeU x⁻¹ (U.inv_mem hx)
    refine ⟨y, hy, ?_⟩
    calc x = (x⁻¹)⁻¹ := by rw [inv_inv]
      _ = (θ s * y * (θ s)⁻¹ * y⁻¹)⁻¹ := by rw [hxy]
      _ = ⁅y, θ s⁆ := by rw [commutatorElement_def]; group

private theorem exists_mem_map_heis_sup_commute (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {w : H}
    (hw : w ∈ rankTwoResidueGroup Δ P Q k i) (hwP : conjSub (P k) w = P k)
    (hwl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → w ∈ lineStab Δ (P k) C)
    (hwN : w ^ (2 ^ n) ^ 7 = 1) :
    ∃ v ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k),
      ∀ x ∈ P k ⊔ Q k, Commute (v⁻¹ * w) x := by
  haveI : Finite H := h.finite
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  have hwQR : conjSub (Q k) w ∈ rankTwoResidue Δ P Q k i :=
    conjSub_mem_rankTwoResidue h.cls (hF.toIsFrame.memQ_rankTwoResidue_left k i) hw
  have hwQP : ¬ Commuting (conjSub (Q k) w) (P k) := by
    have h := Aux.commuting_conjSub_iff w (X := Q k) (Y := P k)
    rw [hwP] at h
    exact fun hc => ModelRank.not_commuting_of_opposite (hF.opposite k).symm (h.1 hc)
  obtain ⟨v, hv, hvQ⟩ :=
    hF.exists_mem_map_heis_sup_conjSub_eq h hML hq hns hFn hcard hθr hθk hθt hθb hmem hik
      hwQR hwQP
  have hUG : U ≤ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr
  set κ : H := v⁻¹ * w with hκ
  have hκG : κ ∈ rankTwoResidueGroup Δ P Q k i :=
    (rankTwoResidueGroup Δ P Q k i).mul_mem
      ((rankTwoResidueGroup Δ P Q k i).inv_mem (hUG hv)) hw
  have hvP : conjSub (P k) v = P k :=
    hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup h.cls hFn hθt hik hv
  have hvPinv : conjSub (P k) v⁻¹ = P k := by
    have h := Aux.conjSub_conjSub_inv (P k) v
    rwa [hvP] at h
  have hκP : conjSub (P k) κ = P k := by
    rw [hκ, conjSub_mul, hwP, hvPinv]
  have hκQ : conjSub (Q k) κ = Q k := by
    rw [hκ, conjSub_mul, show conjSub (Q k) w = conjSub (Q k) v from hvQ.symm,
      Aux.conjSub_conjSub_inv]
  have hvl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → v ∈ lineStab Δ (P k) C :=
    fun C hC hCP hPC =>
      hF.toIsFrame.sup_le_lineStab h hML hq hFn hcard hθt hθb hik hC hCP hPC hv
  have hκl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → κ ∈ lineStab Δ (P k) C := by
    intro C hC hCP hPC
    exact (lineStab Δ (P k) C).mul_mem ((lineStab Δ (P k) C).inv_mem (hvl C hC hCP hPC))
      (hwl C hC hCP hPC)
  have hκU : conjSub U κ = U :=
    hF.conjSub_map_heis_sup_eq h hML hFn hθr hθk hθt hik hκG hκP hκQ hκl
  have hκN : κ ∈ Subgroup.normalizer (U : Set H) := conjSub_eq_self_iff.1 hκU
  have hpow :=
    CFSG.AGLEmbedding.ParabAutIrr.mul_pow_mul_inv_pow_mem (S := U) hκN hv ((2 ^ n) ^ 7)
  have hvκ : v * κ = w := by rw [hκ]; group
  rw [hvκ, hwN, one_mul] at hpow
  have hκpow : κ ^ (2 ^ n) ^ 7 ∈ U := by simpa using U.inv_mem hpow
  have hκQpow : conjSub (Q k) (κ ^ (2 ^ n) ^ 7) = Q k :=
    conjSub_eq_self_iff.2 (Subgroup.pow_mem _ (conjSub_eq_self_iff.1 hκQ) _)
  have hκ1 : κ ^ (2 ^ n) ^ 7 = 1 :=
    hF.eq_one_of_mem_map_heis_sup_of_conjSub_eq h hML hq hns hFn hcard hθr hθk hθt hθb hmem
      hik hκpow hκQpow
  have hκ1' : κ ^ 2 ^ (n * 7) = 1 := by
    rw [← pow_mul] at hκ1
    exact hκ1
  have hκc : ∀ Y ∈ rankTwoResidue Δ P Q k i, ∀ y ∈ Y, Commute κ y :=
    fun Y hY y hy =>
      hF.commute_of_pow_two_pow_eq_one h hML hq hns hik hκG hκP hκQ hκl hκ1' hY hy
  refine ⟨v, hv, ?_⟩
  intro x hx
  exact commute_of_mem_sup_of_commute
    (fun y hy => hκc (P k) (hF.toIsFrame.memP_rankTwoResidue_left k i) y hy)
    (fun y hy => hκc (Q k) (hF.toIsFrame.memQ_rankTwoResidue_left k i) y hy) hx

private theorem conjSub_mem_map_heis_sup_facts (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    {i : Fin r} (hik : i ≠ k) {b u : H} (hb : b ∈ residueGroup Δ P Q i)
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) :
    b * u * b⁻¹ ∈ rankTwoResidueGroup Δ P Q k i ∧
      conjSub (P k) (b * u * b⁻¹) = P k ∧
      (∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → b * u * b⁻¹ ∈ lineStab Δ (P k) C) ∧
      (b * u * b⁻¹) ^ (2 ^ n) ^ 7 = 1 := by
  haveI : Finite H := h.finite
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  set w : H := b * u * b⁻¹ with hwdef
  have hUG : U ≤ rankTwoResidueGroup Δ P Q k i :=
    hF.toIsFrame.map_heis_sup_le_rankTwoResidueGroup hFn hθr
  have hbG : b ∈ rankTwoResidueGroup Δ P Q k i :=
    residueGroup_le_rankTwoResidueGroup_right k i hb
  have hwG : w ∈ rankTwoResidueGroup Δ P Q k i := by
    rw [hwdef]
    exact (rankTwoResidueGroup Δ P Q k i).mul_mem
      ((rankTwoResidueGroup Δ P Q k i).mul_mem hbG (hUG hu))
      ((rankTwoResidueGroup Δ P Q k i).inv_mem hbG)
  have hbP : ∀ y ∈ P k, Commute b y := fun y hy =>
    (commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hik.symm) b hb y
      (Subgroup.mem_sup_left hy)
  have hbP' : conjSub (P k) b = P k := conjSub_of_forall_commute hbP
  have hbPinv : conjSub (P k) b⁻¹ = P k := by
    have h := Aux.conjSub_conjSub_inv (P k) b
    rwa [hbP'] at h
  have hwP : conjSub (P k) w = P k := by
    have huP : conjSub (P k) u = P k :=
      hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup h.cls hFn hθt hik hu
    rw [hwdef, conjSub_mul, hbPinv, conjSub_mul, huP, hbP']
  have hwl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → w ∈ lineStab Δ (P k) C := by
    intro C hC hCP hPC
    have hC' : conjSub C b⁻¹ ∈ Δ := h.cls.root.conjSub_mem hC b⁻¹
    have hCb : conjSub (conjSub C b⁻¹) b = C := by
      simpa using Aux.conjSub_conjSub_inv C b⁻¹
    have hC'P : conjSub C b⁻¹ ≠ P k := by
      intro h
      have h1 : C = P k := by
        rw [← hCb, h, hbP']
      exact hCP h1
    have hPC' : Commuting (P k) (conjSub C b⁻¹) := by
      have h := Aux.commuting_conjSub_iff b⁻¹ (X := P k) (Y := C)
      rw [hbPinv] at h
      exact h.2 hPC
    have hlu : u ∈ lineStab Δ (P k) (conjSub C b⁻¹) :=
      hF.toIsFrame.sup_le_lineStab h hML hq hFn hcard hθt hθb hik hC' hC'P hPC' hu
    have hstab' : lineStab Δ (P k) C =
        conjSub (lineStab Δ (P k) (conjSub C b⁻¹)) b := by
      rw [← lineStab_conjSub h.cls.root (P k) (conjSub C b⁻¹) b, hbP', hCb]
    have hmem : (MulAut.conj b) u ∈ lineStab Δ (P k) C := by
      rw [hstab']
      exact Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hlu
    simpa [hwdef, MulAut.conj_apply] using hmem
  have hwN : w ^ (2 ^ n) ^ 7 = 1 := by
    have huN : u ^ (2 ^ n) ^ 7 = 1 := by
      have hpow := pow_card_eq_one' (G := ↥U) (x := ⟨u, hu⟩)
      rw [hF.card_map_heis_sup_eq h hML hq hns hFn hcard hθr hθk hθt hθb hik] at hpow
      simpa using congrArg Subtype.val hpow
    rw [hwdef, conj_pow, huN]
    group
  exact ⟨hwG, hwP, hwl, hwN⟩

theorem IsMaxFrame.residueGroup_le_normalizer_map_heis_sup (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) :
    residueGroup Δ P Q i ≤ Subgroup.normalizer
      (((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) : Subgroup H) : Set H) := by
  haveI : Finite H := h.finite
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  obtain ⟨t, htsup, htU, hK⟩ :=
    hF.exists_mem_sup_forall_eq_commutatorElement h hML hq hns hFn hcard hθr hθk hθt hθb hmem hik
  intro b hb
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  show b * x * b⁻¹ ∈ U
  obtain ⟨u, hu, rfl⟩ := hK x hx
  obtain ⟨hwG, hwP, hwl, hwN⟩ :=
    conjSub_mem_map_heis_sup_facts h hML hq hF hns hFn hcard hθr hθk hθt hθb hik hb hu
  obtain ⟨v, hv, hvcomm⟩ :=
    exists_mem_map_heis_sup_commute h hML hq hF hns hFn hcard hθr hθk hθt hθb hmem hik
      hwG hwP hwl hwN
  have hbt : Commute b t :=
    (commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hik.symm) b hb t htsup
  have hconj : b * ⁅u, t⁆ * b⁻¹ = ⁅b * u * b⁻¹, t⁆ := by
    have hbt' : b * t * b⁻¹ = t := by rw [hbt.eq]; group
    rw [conjugate_commutatorElement, hbt']
  have hwt : ⁅b * u * b⁻¹, t⁆ = ⁅v, t⁆ := by
    have hκt : Commute (v⁻¹ * (b * u * b⁻¹)) t := hvcomm t htsup
    rw [show b * u * b⁻¹ = v * (v⁻¹ * (b * u * b⁻¹)) by group,
      commutatorElement_def, commutatorElement_def]
    rw [show v * (v⁻¹ * (b * u * b⁻¹)) * t * (v * (v⁻¹ * (b * u * b⁻¹)))⁻¹ * t⁻¹ =
      v * ((v⁻¹ * (b * u * b⁻¹)) * t) * (v⁻¹ * (b * u * b⁻¹))⁻¹ * v⁻¹ * t⁻¹ by group]
    rw [hκt.eq]
    group
  rw [hconj, hwt]
  have htU' : conjSub U t = U := htU
  have htinv : t * v⁻¹ * t⁻¹ ∈ U := htU' ▸ conj_mem_conjSub t (Subgroup.inv_mem U hv)
  rw [commutatorElement_def]
  rw [show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group]
  exact U.mul_mem hv htinv

theorem IsMaxFrame.commutatorElement_mem_map_heis_sup (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {x b : H}
    (hx : x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k))
    (hb : b ∈ residueGroup Δ P Q i) :
    ⁅x, b⁆ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k) := by
  haveI : Finite H := h.finite
  let U : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  have hN : b ∈ Subgroup.normalizer (U : Set H) :=
    hF.residueGroup_le_normalizer_map_heis_sup h hML hq hns hFn hcard hθr hθk hθt hθb hmem hik hb
  have hmem' : b * x⁻¹ * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hN x⁻¹).1 (U.inv_mem hx)
  rw [commutatorElement_def]
  rw [show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group]
  exact U.mul_mem hx hmem'

theorem IsMaxFrame.commutatorElement_mem_map_heis_sup_inf (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k)
    {θ' : SU (unitaryInvolution F 2 n) 3 →* H} (hθr' : θ'.range = residueGroup Δ P Q i)
    (hθk' : Odd (Nat.card θ'.ker)) (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i)
    (hmem' : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q i ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ')
    {b b' : H} (hb : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
    (hb' : b' ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) :
    ⁅b, b'⁆ ∈ ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) ⊓
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' ⊔
        (shortRootGroup Δ (P i) (Q i) (Q k) (P k) ⊔
          shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P i)) := by
  haveI : Finite H := h.finite
  let Uk : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)
  let Ui : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' ⊔
      (shortRootGroup Δ (P i) (Q i) (Q k) (P k) ⊔
        shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P i)
  have hnsi : ¬ IsSmallFrame Δ P Q i := hF.not_isSmallFrame_of_ne h hML hq hik.symm hns
  constructor
  · show ⁅b, b'⁆ ∈ Uk
    have h1 : ⁅b', b⁆ ∈ Uk :=
      hF.commutatorElement_mem_map_heis_sup h hML hq hns hFn hcard hθr hθk hθt hθb hmem hik
        (x := b') (b := b) (Subgroup.mem_sup_left hb')
        (hθr' ▸ Subgroup.map_le_range θ' _ hb)
    rw [show ⁅b, b'⁆ = ⁅b', b⁆⁻¹ by rw [← commutatorElement_inv]]
    exact Uk.inv_mem h1
  · show ⁅b, b'⁆ ∈ Ui
    exact hF.commutatorElement_mem_map_heis_sup (k := i) (i := k) h hML hq hnsi hFn hcard
      hθr' hθk' hθt' hθb' hmem' hik.symm (x := b) (b := b') (Subgroup.mem_sup_left hb)
      (hθr ▸ Subgroup.map_le_range θ _ hb')

end Certificates

end CertificateFree

end CFSG.Timmesfeld.Transvection
