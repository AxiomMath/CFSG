module

public import CFSG.Timmesfeld.Transvection.ShortRoot
import CFSG.Timmesfeld.Transvection.ShortRootReg
import CFSG.Timmesfeld.Transvection.ShortRootPair

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem PairFrame.exists_eq_mul_mul_of_mem_sup [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hq : 4 ≤ Nat.card A) {w : G}
    (hw : w ∈ shortRootGroup Δ E A D E' ⊔ shortRootGroup Δ A E D E' ⊔ D) :
    ∃ x ∈ shortRootGroup Δ E A D E', ∃ u ∈ shortRootGroup Δ A E D E', ∃ d ∈ D,
      w = x * u * d := by
  have hcomm : Commuting (shortRootGroup Δ A E D E') D := fun u hu d hd =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD hu.1.1
      (le_lineGroup (right_mem_lineOf P.memD) hd)
  have hN : shortRootGroup Δ E A D E' ≤
      Subgroup.normalizer ((shortRootGroup Δ A E D E' ⊔ D : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun x hx => ?_
    rw [conjSub_sup_eq_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      have hxu : ⁅x, u⁆ ∈ D := P.commutator_mem_of_mem_shortRootGroup hΔ hpts hq hx hu
      have hcalc : x * u * x⁻¹ = ⁅x, u⁆ * u := by
        rw [commutatorElement_def]
        group
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcalc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxu) (Subgroup.mem_sup_left hu)
    · have hxD : conjSub D x = D :=
        conjSub_eq_of_le_lineGroup hΔ P.memE P.memD P.commuting_ED hx.1.1
          (le_lineGroup (right_mem_lineOf P.memD))
      rw [hxD]
      exact le_sup_right
  rw [sup_assoc, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hw
  obtain ⟨x, hx, v, hv, hvw⟩ := hw
  obtain ⟨u, hu, d, hd, hduv⟩ := mem_sup_of_commuting hcomm hv
  exact ⟨x, hx, u, hu, d, hd, by rw [← hvw, ← hduv, mul_assoc]⟩

theorem PairFrame.mem_of_mem_sup_of_conjSub_eq [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hq : 4 ≤ Nat.card A) {w : G}
    (hw : w ∈ shortRootGroup Δ E A D E' ⊔ shortRootGroup Δ A E D E' ⊔ D)
    (hwA : conjSub A w = A) (hwE : conjSub E w = E) : w ∈ D := by
  obtain ⟨x, hx, u, hu, d, hd, hw'⟩ := P.exists_eq_mul_mul_of_mem_sup hΔ hpts hq hw
  have hqE : 4 ≤ Nat.card E := by rwa [hΔ.root.card_eq P.memE P.memA]
  have huA : conjSub A u = A := conjSub_of_forall_commute fun a ha =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD hu.1.1
      (le_lineGroup (left_mem_lineOf P.memA) ha)
  have hdA : conjSub A d = A := conjSub_of_forall_commute fun a ha =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD
      (le_lineGroup (right_mem_lineOf P.memD) hd) (le_lineGroup (left_mem_lineOf P.memA) ha)
  have hxNA : x ∈ Subgroup.normalizer (A : Set G) := by
    have h1 : x = w * d⁻¹ * u⁻¹ := by rw [hw']; group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (conjSub_eq_self_iff.1 hwA)
        (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 hdA)))
      (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 huA))
  have hxA : conjSub A x = A := conjSub_eq_self_iff.2 hxNA
  have hx1 : x = 1 := P.eq_one_of_conjSub_eq hΔ (P.noIsolated hΔ.root) hpts hq hx hxA
  have hxE : conjSub E x = E := conjSub_of_forall_commute fun e he =>
    commute_of_mem_lineGroup hΔ P.memE P.memD P.commuting_ED hx.1.1
      (le_lineGroup (left_mem_lineOf P.memE) he)
  have hdE : conjSub E d = E := conjSub_of_forall_commute fun e he =>
    (P.commuting_ED e he d hd).symm
  have huNE : u ∈ Subgroup.normalizer (E : Set G) := by
    have h1 : u = x⁻¹ * w * d⁻¹ := by rw [hw']; group
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 hxE))
        (conjSub_eq_self_iff.1 hwE))
      (Subgroup.inv_mem _ (conjSub_eq_self_iff.1 hdE))
  have huE : conjSub E u = E := conjSub_eq_self_iff.2 huNE
  have hu1 : u = 1 := P.flip.eq_one_of_conjSub_eq hΔ (P.noIsolated hΔ.root) hpts hqE hu huE
  rw [hw', hx1, hu1]
  simpa using hd

theorem PairFrame.card_sup_shortRootGroup [Finite G] {A E D E' : Subgroup G}
    (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hq : 4 ≤ Nat.card A) :
    Nat.card ↥(shortRootGroup Δ E A D E' ⊔ shortRootGroup Δ A E D E' ⊔ D) =
      Nat.card ↥(shortRootGroup Δ E A D E') * Nat.card ↥(shortRootGroup Δ A E D E') *
        Nat.card D := by
  let X : Subgroup G := shortRootGroup Δ E A D E'
  let Y : Subgroup G := shortRootGroup Δ A E D E'
  have hcomm : Commuting Y D := fun u hu d hd =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD hu.1.1
      (le_lineGroup (right_mem_lineOf P.memD) hd)
  have hYD : Y ⊓ D = ⊥ :=
    le_antisymm ((inf_le_inf_left Y le_sup_right).trans
      (P.shortRootGroup_inf_sup_eq_bot hΔ).le) bot_le
  have hXinf : X ⊓ (Y ⊔ D) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro w ⟨hwX, hwY⟩
    obtain ⟨u, hu, d, hd, hwd⟩ := mem_sup_of_commuting hcomm hwY
    have hwU : w ∈ lineGroup Δ A D := by
      rw [← hwd]
      exact Subgroup.mul_mem _ hu.1.1 (le_lineGroup (right_mem_lineOf P.memD) hd)
    have hwA : conjSub A w = A := conjSub_of_forall_commute fun a ha =>
      commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD hwU
        (le_lineGroup (left_mem_lineOf P.memA) ha)
    have hw1 : w = 1 := P.eq_one_of_conjSub_eq hΔ (P.noIsolated hΔ.root) hpts hq hwX hwA
    rw [hw1]
    exact Subgroup.one_mem _
  have hupper : Nat.card ↥(X ⊔ Y ⊔ D) ≤ Nat.card ↥X * Nat.card ↥Y * Nat.card D := by
    have hsurj : Function.Surjective (fun p : ↥X × ↥Y × ↥D =>
        (⟨↑p.1 * ↑p.2.1 * ↑p.2.2,
          Subgroup.mul_mem _ (Subgroup.mul_mem _
            (Subgroup.mem_sup_left (Subgroup.mem_sup_left p.1.2))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.1.2)))
          (Subgroup.mem_sup_right p.2.2.2)⟩ : ↥(X ⊔ Y ⊔ D))) := by
      rintro ⟨w, hw⟩
      obtain ⟨x, hx, u, hu, d, hd, hw'⟩ := P.exists_eq_mul_mul_of_mem_sup hΔ hpts hq hw
      refine ⟨(⟨x, hx⟩, ⟨u, hu⟩, ⟨d, hd⟩), ?_⟩
      apply Subtype.ext
      show x * u * d = w
      rw [hw']
    have h := Nat.card_le_card_of_surjective _ hsurj
    simpa [Nat.card_prod, Nat.mul_assoc] using h
  have hlower : Nat.card ↥X * Nat.card ↥Y * Nat.card D ≤ Nat.card ↥(X ⊔ Y ⊔ D) := by
    have h1 : Nat.card ↥Y * Nat.card D ≤ Nat.card ↥(Y ⊔ D) := card_mul_card_le_card_sup hYD
    have h2 : Nat.card ↥X * Nat.card ↥(Y ⊔ D) ≤ Nat.card ↥(X ⊔ (Y ⊔ D)) :=
      card_mul_card_le_card_sup hXinf
    have h3 : Nat.card ↥X * Nat.card ↥Y * Nat.card D ≤ Nat.card ↥(X ⊔ (Y ⊔ D)) := by
      calc Nat.card ↥X * Nat.card ↥Y * Nat.card D
          = Nat.card ↥X * (Nat.card ↥Y * Nat.card D) := Nat.mul_assoc _ _ _
        _ ≤ Nat.card ↥X * Nat.card ↥(Y ⊔ D) := Nat.mul_le_mul_left _ h1
        _ ≤ Nat.card ↥(X ⊔ (Y ⊔ D)) := h2
    simpa [sup_assoc] using h3
  exact le_antisymm hupper hlower

end CFSG.Timmesfeld.Transvection
