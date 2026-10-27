module

public import CFSG.OddTranspositions.PartThree.Twelve.SixPivot
public import CFSG.OddTranspositions.PartThree.CommSetConj
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.OddTranspositions.PartTwoSec6
import CFSG.Goldschmidt75.OddCore
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.Goldschmidt75.Basic

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section TwinFree

variable {X : Type} [Group X] [Finite X] {E : Set X}

theorem oddCore_le_center_of_noOpenTwins (hS : Setup X E)
    (hOT : ∀ a ∈ E, ∀ b ∈ E, commSet E a = commSet E b → a = b) :
    CFSG.oddCore X ≤ Subgroup.center X := by
  obtain ⟨a, ha⟩ := hS.nonempty
  have hodd : Odd (Nat.card (CFSG.oddCore X)) := CFSG.Goldschmidt75.odd_card_oddCore
  refine hS.le_center_of_mem_centralizer ha ?_
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hb : n * a * n⁻¹ ∈ E := hS.conj_mem n ha
  have hn' : n * a * n⁻¹ * a⁻¹ ∈ CFSG.oddCore X := by
    have h1 : a * n⁻¹ * a⁻¹ ∈ CFSG.oddCore X :=
      (inferInstance : (CFSG.oddCore X).Normal).conj_mem _ (inv_mem hn) a
    have h2 : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
    rw [h2]
    exact mul_mem hn h1
  have heq := CFSG.OddTranspositions.commSet_eq_of_mem_mul_normal hS.oddT inferInstance hodd ha hb
    hn' (by group)
  have hab : n * a * n⁻¹ = a := hOT _ hb _ ha heq
  calc n * a = n * a * n⁻¹ * n := by group
    _ = a * n := by rw [hab]

omit [Finite X] in
theorem commute_conj_of_mem_comap_pCore (hE : IsOddTransp E)
    (hOZ : CFSG.oddCore X ≤ Subgroup.center X) {k : X}
    (hk : k ∈ (CFSG.pCore 2 (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X)))
    {a c : X} (ha : a ∈ E) (hc : c ∈ E) (hb : k * a * k⁻¹ ∈ E) (hca : Commute c a) :
    Commute c (k * a * k⁻¹) := by
  set K := (CFSG.pCore 2 (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X))
    with hKdef
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  set b := k * a * k⁻¹ with hbdef
  have ha2 : a * a = 1 := hE.mul_self_eq_one ha
  have hc2 : c * c = 1 := hE.mul_self_eq_one hc
  have hb2 : b * b = 1 := hE.mul_self_eq_one hb
  have hbK : b * c * b * c ∈ K := by
    have hba : QuotientGroup.mk' K b = QuotientGroup.mk' K a := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 : a⁻¹ * k⁻¹ * a ∈ K := by
        have := hKn.conj_mem k⁻¹ (inv_mem hk) a⁻¹
        rwa [inv_inv] at this
      have h2 : b⁻¹ * a = k * (a⁻¹ * k⁻¹ * a) := by
        rw [hbdef]
        group
      rw [h2]
      exact mul_mem hk h1
    have hac : a * c * a * c = 1 := by
      calc a * c * a * c = a * (c * a) * c := by group
        _ = a * (a * c) * c := by rw [hca.eq]
        _ = (a * a) * (c * c) := by group
        _ = 1 := by rw [ha2, hc2, one_mul]
    have h1 : QuotientGroup.mk' K (b * c * b * c) = 1 := by
      rw [map_mul, map_mul, map_mul, hba, ← map_mul, ← map_mul, ← map_mul, hac, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  by_contra hnc
  have hbc : ¬ Commute b c := fun h => hnc h.symm
  have hodd : Odd (orderOf (b * c)) := hE.odd_of_not_commute hb hc hbc
  set w := QuotientGroup.mk' (CFSG.oddCore X) (b * c) with hw
  have hwodd : Odd (orderOf w) := hodd.of_dvd_nat (orderOf_map_dvd _ _)
  have hw2 : w ^ 2 ∈ CFSG.pCore 2 (X ⧸ CFSG.oddCore X) := by
    have h1 : w ^ 2 = QuotientGroup.mk' (CFSG.oddCore X) (b * c * b * c) := by
      rw [hw, ← map_pow, pow_two, ← mul_assoc]
    rw [h1]
    exact hbK
  have hw2odd : Odd (orderOf (w ^ 2)) := hwodd.of_dvd_nat (orderOf_pow_dvd 2)
  have hw21 : w ^ 2 = 1 :=
    CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_isPGroup_of_odd CFSG.pCore_isPGroup hw2 hw2odd
  have hw1 : w = 1 := by
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw21
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hwodd
      exact absurd hwodd (by decide)
  have hcen : b * c ∈ Subgroup.center X := hOZ ((QuotientGroup.eq_one_iff _).mp hw1)
  apply hnc
  have h1 := Subgroup.mem_center_iff.mp hcen b
  show c * b = b * c
  calc c * b = b * b * c * b := by rw [hb2, one_mul]
    _ = b * (b * c) * b := by group
    _ = b * c * b * b := by rw [h1]
    _ = b * c := by rw [mul_assoc, hb2, mul_one]

theorem solvableRadical_le_center_of_noTwins (hS : Setup X E)
    (hOT : ∀ a ∈ E, ∀ b ∈ E, commSet E a = commSet E b → a = b)
    (hCT : ∀ a ∈ E, ∀ b ∈ E, Commute a b → (∀ c ∈ E, Commute c a ↔ Commute c b) → a = b) :
    CFSG.solvableRadical X ≤ Subgroup.center X := by
  have hOZ := oddCore_le_center_of_noOpenTwins hS hOT
  obtain ⟨d, hd⟩ := hS.nonempty
  have hiso : ∀ k ∈ (CFSG.pCore 2 (X ⧸ CFSG.oddCore X)).comap
      (QuotientGroup.mk' (CFSG.oddCore X)), k * d * k⁻¹ = d ∨ ¬ Commute (k * d * k⁻¹) d := by
    intro k hk
    by_contra h
    push Not at h
    obtain ⟨hne, hcomm⟩ := h
    have hb : k * d * k⁻¹ ∈ E := hS.conj_mem k hd
    have hback : k⁻¹ * (k * d * k⁻¹) * k⁻¹⁻¹ = d := by group
    refine hne (hCT _ hd _ hb hcomm.symm fun c hc => ⟨fun h =>
      commute_conj_of_mem_comap_pCore hS.oddT hOZ hk hd hc hb h, fun h => ?_⟩).symm
    have := commute_conj_of_mem_comap_pCore hS.oddT hOZ (inv_mem hk) hb hc
      (by rw [hback]; exact hd) h
    rwa [hback] at this
  have hmap := solvableRadical_map_le_center_of_no_distinct_conj hS hd hiso
  refine hS.le_center_of_mem_centralizer hd ?_
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  set z := r * d * r⁻¹ * d⁻¹ with hz
  have hc : QuotientGroup.mk' (CFSG.oddCore X) r ∈ Subgroup.center (X ⧸ CFSG.oddCore X) :=
    hmap ⟨r, hr, rfl⟩
  have h1 : QuotientGroup.mk' (CFSG.oddCore X) z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv,
      (Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' (CFSG.oddCore X) d)).symm]
    group
  have hzO : z ∈ CFSG.oddCore X := (QuotientGroup.eq_one_iff _).mp h1
  have hzc : z ∈ Subgroup.center X := hOZ hzO
  have hrd : r * d * r⁻¹ = z * d := by rw [hz]; group
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hz2 : z * z = 1 := by
    have h2 : r * d * r⁻¹ * (r * d * r⁻¹) = 1 := hS.oddT.mul_self_eq_one (hS.conj_mem r hd)
    rw [hrd] at h2
    calc z * z = z * z * (d * d) := by rw [hd2, mul_one]
      _ = z * (z * d) * d := by group
      _ = z * (d * z) * d := by rw [Subgroup.mem_center_iff.mp hzc d]
      _ = z * d * (z * d) := by group
      _ = 1 := h2
  have hz1 : z = 1 := by
    have hodd : Odd (orderOf z) :=
      (CFSG.Goldschmidt75.odd_card_oddCore (G := X)).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hzO)
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have h3 : r * d * r⁻¹ = d := by rw [hrd, hz1, one_mul]
  calc r * d = r * d * r⁻¹ * r := by group
    _ = d * r := by rw [h3]

end TwinFree

variable {G : Type} [Group G] [Finite G] {D : Set G}

abbrev gammaAt (D : Set G) (x y v : G) : Set G :=
  commSet D x ∩ commSet D y ∩ commSet D v

@[expose] def compSet (D : Set G) (x y d : G) : Set G :=
  {e | e ∈ commSet D x ∩ commSet D y ∧ Reach (commSet D x ∩ commSet D y) d e}

omit [Finite G] in
theorem compSet_subset (D : Set G) (x y d : G) :
    compSet D x y d ⊆ commSet D x ∩ commSet D y :=
  fun _ he => he.1

omit [Finite G] in
theorem mem_compSet_self {x y d : G} (hd : d ∈ commSet D x ∩ commSet D y) :
    d ∈ compSet D x y d :=
  ⟨hd, reach_refl d⟩

omit [Finite G] in
theorem mem_compSet_of_commute {x y d e e' : G} (he : e ∈ compSet D x y d)
    (he' : e' ∈ commSet D x ∩ commSet D y) (h : Commute e e') : e' ∈ compSet D x y d :=
  ⟨he', reach_trans he.2 (reach_of_commute he.1 he' h)⟩

omit [Finite G] in
theorem gammaAt_subset_compSet {x y d v : G} (hv : v ∈ compSet D x y d) :
    gammaAt D x y v ⊆ compSet D x y d :=
  fun _ hz => mem_compSet_of_commute hv hz.1 hz.2.2.1.symm

omit [Finite G] in
theorem gammaAt_self_subset_compSet {x y d : G} (hd : d ∈ commSet D x ∩ commSet D y) :
    gammaAt D x y d ⊆ compSet D x y d :=
  gammaAt_subset_compSet (mem_compSet_self hd)

omit [Finite G] in
theorem reach_conj_of_mapsTo {E : Set G} (g : G) (hg : ∀ z ∈ E, g * z * g⁻¹ ∈ E) {a b : G}
    (h : Reach E a b) : Reach E (g * a * g⁻¹) (g * b * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.tail ih ⟨hg _ hbc.1, hg _ hbc.2.1, (Commute.conj_iff g).2 hbc.2.2⟩

omit [Finite G] in
theorem conj_mem_compSet (hN : IsNormalSet D) {x y d ω e : G} (hω : ω ∈ compSet D x y d)
    (he : e ∈ compSet D x y d) : ω * e * ω⁻¹ ∈ compSet D x y d := by
  have hmaps : ∀ z ∈ commSet D x ∩ commSet D y, ω * z * ω⁻¹ ∈ commSet D x ∩ commSet D y :=
    fun z hz => ⟨conj_mem_commSet_of_commute hN hω.1.1.2.1 hz.1,
      conj_mem_commSet_of_commute hN hω.1.2.2.1 hz.2⟩
  refine ⟨hmaps e he.1, ?_⟩
  have h1 := reach_conj_of_mapsTo ω hmaps he.2
  have h2 := reach_conj_of_mapsTo ω hmaps hω.2
  rw [mul_inv_cancel_right] at h2
  exact reach_trans (reach_trans hω.2 (reach_symm h2)) h1

omit [Finite G] in
theorem closure_compSet_le_normalizer (hN : IsNormalSet D) (hD : IsOddTransp D) {x y d : G} :
    Subgroup.closure (compSet D x y d) ≤ Subgroup.normalizer (compSet D x y d) := by
  rw [Subgroup.closure_le]
  intro ω hω
  rw [SetLike.mem_coe, Subgroup.mem_set_normalizer_iff]
  intro e
  refine ⟨fun he => conj_mem_compSet hN hω he, fun he => ?_⟩
  have h := conj_mem_compSet hN hω he
  have hω2 : ω * ω = 1 := hD.mul_self_eq_one hω.1.1.1
  have h3 : ω * (ω * e * ω⁻¹) * ω⁻¹ = e := by
    calc ω * (ω * e * ω⁻¹) * ω⁻¹ = (ω * ω) * e * (ω * ω)⁻¹ := by group
      _ = e := by rw [hω2]; group
  rwa [h3] at h

omit [Finite G] in
theorem conj_mem_inClosure_compSet (hN : IsNormalSet D) (hD : IsOddTransp D) {x y d : G}
    (g : Subgroup.closure (compSet D x y d)) {z : Subgroup.closure (compSet D x y d)}
    (hz : z ∈ inClosure (compSet D x y d)) : g * z * g⁻¹ ∈ inClosure (compSet D x y d) :=
  (Subgroup.mem_set_normalizer_iff.mp (closure_compSet_le_normalizer hN hD g.2) z).mp hz

omit [Finite G] in
theorem exists_conj_of_mem_compSet {x y d : G}
    (hT : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v, ∀ b' ∈ gammaAt D x y v,
      ∃ g ∈ Subgroup.closure (gammaAt D x y v), g * b * g⁻¹ = b')
    (hNb : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v,
      ∃ c ∈ gammaAt D x y v, c ≠ b ∧ Commute c b)
    {e : G} (he : e ∈ compSet D x y d) :
    ∃ g ∈ Subgroup.closure (compSet D x y d), g * d * g⁻¹ = e := by
  obtain ⟨heΓ, hreach⟩ := he
  revert heΓ
  induction hreach with
  | refl => exact fun _ => ⟨1, one_mem _, by group⟩
  | @tail b c hdb hbc ih =>
    intro _
    obtain ⟨g, hg, hgb⟩ := ih hbc.1
    have hbΩ : b ∈ compSet D x y d := ⟨hbc.1, hdb⟩
    by_cases hbc' : b = c
    · exact ⟨g, hg, hgb.trans hbc'⟩
    have hcb : c ∈ gammaAt D x y b :=
      ⟨hbc.2.1, hbc.2.1.1.1, hbc.2.2.symm, fun h => hbc' h.symm⟩
    obtain ⟨w, hw, hwc, hwcomm⟩ := hNb b hbΩ c hcb
    have hwΩ : w ∈ compSet D x y d := gammaAt_subset_compSet hbΩ hw
    have hbw : b ∈ gammaAt D x y w := ⟨hbc.1, hbc.1.1.1, hw.2.2.1.symm, fun h => hw.2.2.2 h.symm⟩
    have hcw : c ∈ gammaAt D x y w :=
      ⟨hbc.2.1, hbc.2.1.1.1, hwcomm.symm, fun h => hwc h.symm⟩
    obtain ⟨h, hh, hhb⟩ := hT w hwΩ b hbw c hcw
    have hhΩ : h ∈ Subgroup.closure (compSet D x y d) :=
      Subgroup.closure_mono (gammaAt_subset_compSet hwΩ) hh
    exact ⟨h * g, mul_mem hhΩ hg, by rw [← hhb, ← hgb]; group⟩

omit [Finite G] in
theorem isClass_inClosure_compSet (hN : IsNormalSet D) (hD : IsOddTransp D) {x y d : G}
    (hd : d ∈ commSet D x ∩ commSet D y)
    (hT : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v, ∀ b' ∈ gammaAt D x y v,
      ∃ g ∈ Subgroup.closure (gammaAt D x y v), g * b * g⁻¹ = b')
    (hNb : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v,
      ∃ c ∈ gammaAt D x y v, c ≠ b ∧ Commute c b) :
    ∃ t : Subgroup.closure (compSet D x y d),
      inClosure (compSet D x y d) = {g | IsConj t g} := by
  refine ⟨⟨d, Subgroup.subset_closure (mem_compSet_self hd)⟩, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨g, hg, hgz⟩ := exists_conj_of_mem_compSet hT hNb hz
    exact isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext hgz⟩
  · intro hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hz
    exact conj_mem_inClosure_compSet hN hD c (mem_compSet_self hd)

omit [Finite G] in
theorem reach_compSet {x y d e : G} (he : e ∈ compSet D x y d) :
    Reach (compSet D x y d) d e := by
  obtain ⟨heΓ, hreach⟩ := he
  revert heΓ
  induction hreach with
  | refl => exact fun _ => reach_refl _
  | @tail b c hdb hbc ih =>
    intro _
    exact reach_trans (ih hbc.1) (reach_of_commute ⟨hbc.1, hdb⟩
      ⟨hbc.2.1, reach_trans hdb (reach_of_commute hbc.1 hbc.2.1 hbc.2.2)⟩ hbc.2.2)

omit [Finite G] in
theorem reach_inClosure_of_reach {Ω : Set G} {a b : G} (ha : a ∈ Ω) (h : Reach Ω a b)
    (hb : b ∈ Ω) :
    Reach (inClosure Ω) ⟨a, Subgroup.subset_closure ha⟩ ⟨b, Subgroup.subset_closure hb⟩ := by
  revert hb
  induction h with
  | refl => exact fun _ => reach_refl _
  | @tail c e _ hce ih =>
    intro _
    exact reach_trans (ih hce.1)
      (reach_of_commute (D := inClosure Ω) hce.1 hce.2.1 (Subtype.ext hce.2.2.eq))

omit [Finite G] in
theorem not_disconnected_inClosure_compSet {x y d : G} (hd : d ∈ commSet D x ∩ commSet D y) :
    ¬ Disconnected (inClosure (compSet D x y d)) := by
  rintro ⟨a, ha, b, hb, hab⟩
  apply hab
  have h1 := reach_inClosure_of_reach (mem_compSet_self hd) (reach_compSet ha) ha
  have h2 := reach_inClosure_of_reach (mem_compSet_self hd) (reach_compSet hb) hb
  exact reach_trans (reach_symm h1) h2

omit [Finite G] in
theorem noClosedTwins_inClosure_compSet {x y d : G}
    (hZ : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v, ∃ c ∈ gammaAt D x y v, ¬ Commute b c) :
    ∀ a ∈ inClosure (compSet D x y d), ∀ b ∈ inClosure (compSet D x y d), Commute a b →
      (∀ c ∈ inClosure (compSet D x y d), Commute c a ↔ Commute c b) → a = b := by
  intro a ha b hb hab htwin
  by_contra hne
  have habG : Commute (a : G) (b : G) := congrArg Subtype.val hab.eq
  have hbΓ : (b : G) ∈ gammaAt D x y a :=
    ⟨hb.1, hb.1.1.1, habG.symm, fun h => hne (Subtype.ext h).symm⟩
  obtain ⟨c, hc, hbc⟩ := hZ a ha b hbΓ
  have hcΩ := gammaAt_subset_compSet ha hc
  have hca : Commute (⟨c, Subgroup.subset_closure hcΩ⟩ : Subgroup.closure (compSet D x y d)) a :=
    Subtype.ext hc.2.2.1.eq
  have hcb := (htwin _ hcΩ).mp hca
  exact hbc (congrArg Subtype.val hcb.eq).symm

omit [Finite G] in
theorem noOpenTwins_inClosure_compSet {x y d : G}
    (hne : ∀ v ∈ compSet D x y d, (gammaAt D x y v).Nonempty)
    (hO : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v, ∀ b' ∈ gammaAt D x y v,
      (∀ c ∈ gammaAt D x y v, (c ≠ b ∧ Commute c b) ↔ (c ≠ b' ∧ Commute c b')) → b = b') :
    ∀ a ∈ inClosure (compSet D x y d), ∀ b ∈ inClosure (compSet D x y d),
      commSet (inClosure (compSet D x y d)) a = commSet (inClosure (compSet D x y d)) b →
        a = b := by
  intro a ha b hb hab
  by_cases hc : Commute a b
  · by_contra hne'
    have hmem : b ∈ commSet (inClosure (compSet D x y d)) a := ⟨hb, hc.symm, fun h => hne' h.symm⟩
    rw [hab] at hmem
    exact hmem.2.2 rfl
  obtain ⟨v, hv⟩ := hne a ha
  have hvΩ := gammaAt_subset_compSet ha hv
  set vS : Subgroup.closure (compSet D x y d) := ⟨v, Subgroup.subset_closure hvΩ⟩
  have hva : vS ∈ commSet (inClosure (compSet D x y d)) a :=
    ⟨hvΩ, Subtype.ext hv.2.2.1.eq, fun h => hv.2.2.2 (congrArg Subtype.val h)⟩
  rw [hab] at hva
  have haΓ : (a : G) ∈ gammaAt D x y v :=
    ⟨ha.1, ha.1.1.1, hv.2.2.1.symm, fun h => hv.2.2.2 h.symm⟩
  have hbΓ : (b : G) ∈ gammaAt D x y v :=
    ⟨hb.1, hb.1.1.1, (congrArg Subtype.val hva.2.1.eq).symm,
      fun h => hva.2.2 (Subtype.ext h).symm⟩
  refine Subtype.ext (hO v hvΩ _ haΓ _ hbΓ fun c hcv => ?_)
  have hcΩ := gammaAt_subset_compSet hvΩ hcv
  set cS : Subgroup.closure (compSet D x y d) := ⟨c, Subgroup.subset_closure hcΩ⟩
  have key : ∀ z : Subgroup.closure (compSet D x y d),
      cS ∈ commSet (inClosure (compSet D x y d)) z ↔ (c ≠ z ∧ Commute c z) := fun z =>
    ⟨fun h => ⟨fun h' => h.2.2 (Subtype.ext h'), congrArg Subtype.val h.2.1.eq⟩,
      fun h => ⟨hcΩ, Subtype.ext h.2.eq, fun h' => h.1 (congrArg Subtype.val h')⟩⟩
  rw [← key a, ← key b, hab]

omit [Finite G] in
theorem ne_one_of_isSymplecticTransvection {X : Type} [Group X] {s : X} {m f : ℕ}
    (h : IsSymplecticTransvection X m f s) : s ≠ 1 := by
  obtain ⟨k, hmk, F, hF, hFin, hcard, e, hr⟩ := h
  rintro rfl
  rw [QuotientGroup.mk_one, map_one] at hr
  simp [IsSymplecticTransvectionIn] at hr

theorem commute_iff_commute_mk (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {e c : G} (he : e ∈ commSet D hC.d) (hc : c ∈ commSet D hC.d) :
    Commute e c ↔ Commute
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨e, mem_Halpha_of_mem_commSet hC hα he⟩ : Halpha D hC.alpha))
      (QuotientGroup.mk' _ ⟨c, mem_Halpha_of_mem_commSet hC hα hc⟩) := by
  constructor
  · intro h
    exact (show Commute (⟨e, mem_Halpha_of_mem_commSet hC hα he⟩ : Halpha D hC.alpha)
      ⟨c, mem_Halpha_of_mem_commSet hC hα hc⟩ from Subtype.ext h.eq).map _
  · intro h
    exact congrArg Subtype.val (commute_of_commute_mk_of_le_center hC hMZ
      (mem_DstarH_of_mem_commSet hC hα he) (mem_DstarH_of_mem_commSet hC hα hc) h).eq

theorem exists_localModel (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    ∃ (K : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
      (ι : ∀ b ∈ gammaAt D x y hC.d, K),
      Subgroup.center K = ⊥ ∧
      (∃ d₀ : K, {k : K | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} =
        {g | IsConj d₀ g}) ∧
      (∀ b (hb : b ∈ gammaAt D x y hC.d), IsSymplecticTransvection K (n - 2) f (ι b hb)) ∧
      (∀ b (hb : b ∈ gammaAt D x y hC.d) c (hc : c ∈ gammaAt D x y hC.d),
        ι b hb = ι c hc → b = c) ∧
      (∀ b (hb : b ∈ gammaAt D x y hC.d) c (hc : c ∈ gammaAt D x y hC.d),
        Commute b c ↔ Commute (ι b hb) (ι c hc)) ∧
      Subgroup.closure {k : K | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} = ⊤ ∧
      (gammaAt D x y hC.d).Nonempty := by
  classical
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨t, ht, hts, htu, htw, hSpK, hcl, hcenK⟩ := isSymplecticTransvection_closure_commonCommute
    hZ hn hSp (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have himg := image_commonPerpH hC hMZ hα hs hx hy hxy
  have hne := (subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs
    hSp).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  set Δb := {z | IsConj s z ∧
      Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
      Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} with hΔb
  have hmem : ∀ b (hb : b ∈ gammaAt D x y hC.d),
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨b, mem_Halpha_of_mem_commSet hC hα hb.2⟩ : Halpha D hC.alpha) ∈ Δb := by
    intro b hb
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨b, mem_Halpha_of_mem_commSet hC hα hb.2⟩ : Halpha D hC.alpha) ∈
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
      ⟨_, hb, rfl⟩
    rw [himg] at h1
    exact h1
  let ι : ∀ b ∈ gammaAt D x y hC.d, Subgroup.closure Δb := fun b hb =>
    ⟨_, Subgroup.subset_closure (hmem b hb)⟩
  have hsurj : ∀ k : Subgroup.closure Δb,
      (k : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ∈ Δb →
      ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k := by
    intro k hk
    have hk' : (k : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ∈
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y := by
      rw [himg]
      exact hk
    obtain ⟨w, hw, hwk⟩ := hk'
    exact ⟨(w : G), hw, Subtype.ext hwk⟩
  have hcls : {k : Subgroup.closure Δb | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} =
      {g | IsConj (⟨t, ht⟩ : Subgroup.closure Δb) g} := by
    ext k
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨g, hg, hgk⟩ := (hcl _).mp (hmem b hb)
      exact isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext hgk⟩
    · intro hk
      obtain ⟨g, hgk⟩ := isConj_iff.mp hk
      exact hsurj k ((hcl (k : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))).mpr
        ⟨g, g.2, congrArg Subtype.val hgk⟩)
  have hpre : {k : Subgroup.closure Δb | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} =
      {k : Subgroup.closure Δb |
        (k : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ∈ Δb} := by
    ext k
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hmem b hb
    · exact hsurj k
  refine ⟨Subgroup.closure Δb, ι, hcenK, ⟨⟨t, ht⟩, hcls⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hk : ι b hb ∈ {g | IsConj (⟨t, ht⟩ : Subgroup.closure Δb) g} := by
      rw [← hcls]
      exact ⟨b, hb, rfl⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hk
    have := isSymplecticTransvection_map (MulAut.conj g) hSpK
    rwa [MulAut.conj_apply, hg] at this
  · intro b hb c hc h
    have h1 := hinj (mem_DstarH_of_mem_commSet hC hα hb.2) (mem_DstarH_of_mem_commSet hC hα hc.2)
      (congrArg Subtype.val h)
    exact congrArg Subtype.val h1
  · intro b hb c hc
    rw [commute_iff_commute_mk hC hMZ hα hb.2 hc.2]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · rw [hpre]
    exact Subgroup.closure_preimage_eq_top _
  · obtain ⟨b, hb, -⟩ := hsurj ⟨t, ht⟩ ⟨hts, htu, htw⟩
    exact ⟨b, hb⟩

theorem exists_rootTwin_gammaAt (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {b : G} (hb : b ∈ gammaAt D x y hC.d) :
    ∃ c ∈ gammaAt D x y hC.d, c ≠ b ∧ Commute c b ∧
      ∀ e ∈ gammaAt D x y hC.d, Commute e c ↔ Commute e b := by
  classical
  obtain ⟨K, ι, hZK, ⟨d₀, hcls⟩, hSpK, hinj, hcomm, -, -⟩ :=
    exists_localModel hC hMZ hα hs hn hSp hx hy hxy
  set E := {k : K | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} with hE
  have hbE : ι b hb ∈ E := ⟨b, hb, rfl⟩
  have hcard := ncard_rootBlock_of_isSymplecticTransvection ⟨d₀, hcls⟩ hZK hbE (hSpK b hb)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hnt : (rootBlock E (ι b hb)).Nontrivial := by
    rw [← Set.one_lt_ncard_iff_nontrivial, hcard]
    omega
  obtain ⟨cK, hcK, hcKb⟩ := hnt.exists_ne (ι b hb)
  obtain ⟨c, hc, rfl⟩ := hcK.1
  refine ⟨c, hc, fun h => hcKb (by subst h; rfl), ?_, fun e he => ?_⟩
  · have h1 := (hcK.2 (ι b hb) hbE).mpr (Commute.refl _)
    exact ((hcomm b hb c hc).mpr h1).symm
  · rw [hcomm e he c hc, hcomm e he b hb]
    exact hcK.2 (ι e he) ⟨e, he, rfl⟩

theorem exists_not_commute_gammaAt (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {b : G} (hb : b ∈ gammaAt D x y hC.d) :
    ∃ c ∈ gammaAt D x y hC.d, ¬ Commute b c := by
  classical
  obtain ⟨K, ι, hZK, -, hSpK, -, hcomm, hgen, -⟩ :=
    exists_localModel hC hMZ hα hs hn hSp hx hy hxy
  by_contra h
  push Not at h
  apply ne_one_of_isSymplecticTransvection (hSpK b hb)
  have hcen : ι b hb ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : Subgroup.closure {k : K | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} ≤
        Subgroup.centralizer {ι b hb} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm b hb c hc).mp (h c hc)).eq.symm
    rw [hgen] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [hZK, Subgroup.mem_bot] at hcen
  exact hcen

theorem exists_conj_gammaAt (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {b b' : G} (hb : b ∈ gammaAt D x y hC.d) (hb' : b' ∈ gammaAt D x y hC.d) :
    ∃ g ∈ Subgroup.closure (gammaAt D x y hC.d), g * b * g⁻¹ = b' := by
  obtain ⟨g, -, hg⟩ := exists_conj_deltaIn hC hMZ hα hs hn hSp hx hy hxy
    (Ω := gammaAt D x y hC.d) subset_rfl (δ := ⟨b, Subgroup.subset_closure hb⟩)
    (δ' := ⟨b', Subgroup.subset_closure hb'⟩) hb hb'
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

@[expose] def LocalPivot (D : Set G) (x y v : G) : Prop :=
  (gammaAt D x y v).Nonempty ∧
  (∀ b ∈ gammaAt D x y v, ∀ b' ∈ gammaAt D x y v,
    ∃ g ∈ Subgroup.closure (gammaAt D x y v), g * b * g⁻¹ = b') ∧
  (∀ b ∈ gammaAt D x y v, ∃ c ∈ gammaAt D x y v, c ≠ b ∧ Commute c b) ∧
  (∀ b ∈ gammaAt D x y v, ∃ c ∈ gammaAt D x y v, ¬ Commute b c) ∧
  (∀ b ∈ gammaAt D x y v, ∀ b' ∈ gammaAt D x y v,
    (∀ c ∈ gammaAt D x y v, (c ≠ b ∧ Commute c b) ↔ (c ≠ b' ∧ Commute c b')) → b = b')

theorem localPivot_pivot (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    LocalPivot D x y hC.d := by
  obtain ⟨-, -, -, -, -, -, -, -, hne⟩ := exists_localModel hC hMZ hα hs hn hSp hx hy hxy
  refine ⟨hne, fun b hb b' hb' => exists_conj_gammaAt hC hMZ hα hs hn hSp hx hy hxy hb hb',
    fun b hb => ?_, fun b hb => exists_not_commute_gammaAt hC hMZ hα hs hn hSp hx hy hxy hb, ?_⟩
  · obtain ⟨c, hc, hcb, hcomm, -⟩ := exists_rootTwin_gammaAt hC hMZ hα hs hn hf hSp hx hy hxy hb
    exact ⟨c, hc, hcb, hcomm⟩
  · intro b hb b' hb' htw
    by_contra hne'
    by_cases hc : Commute b' b
    · exact ((htw b' hb').mp ⟨fun h => hne' h.symm, hc⟩).1 rfl
    · obtain ⟨c, hcΔ, hcb, hcomm, hiff⟩ :=
        exists_rootTwin_gammaAt hC hMZ hα hs hn hf hSp hx hy hxy hb
      have h1 : Commute c b' := ((htw c hcΔ).mp ⟨hcb, hcomm⟩).2
      exact hc ((hiff b' hb').mp h1.symm)

omit [Finite G] in
theorem commute_map_iff (φ : G ≃* G) {a b : G} : Commute (φ a) (φ b) ↔ Commute a b :=
  ⟨fun h => by simpa using h.map φ.symm, fun h => h.map φ⟩

omit [Finite G] in
theorem mem_commSet_map_iff (φ : G ≃* G) (hφ : ∀ z, φ z ∈ D ↔ z ∈ D) {a z : G} :
    φ z ∈ commSet D (φ a) ↔ z ∈ commSet D a := by
  simp only [commSet, Set.mem_setOf_eq, hφ, commute_map_iff, φ.injective.ne_iff]

omit [Finite G] in
theorem mem_gammaAt_map_iff (φ : G ≃* G) (hφ : ∀ z, φ z ∈ D ↔ z ∈ D) {x y v z : G} :
    φ z ∈ gammaAt D (φ x) (φ y) (φ v) ↔ z ∈ gammaAt D x y v := by
  simp only [gammaAt, Set.mem_inter_iff, mem_commSet_map_iff φ hφ]

omit [Finite G] in
theorem LocalPivot.map {x y v : G} (h : LocalPivot D x y v) (φ : G ≃* G)
    (hφ : ∀ z, φ z ∈ D ↔ z ∈ D) : LocalPivot D (φ x) (φ y) (φ v) := by
  obtain ⟨⟨b₀, hb₀⟩, hT, hN, hZ, hO⟩ := h
  have hcl : ∀ g ∈ Subgroup.closure (gammaAt D x y v),
      φ g ∈ Subgroup.closure (gammaAt D (φ x) (φ y) (φ v)) := by
    intro g hg
    have h1 : φ.toMonoidHom g ∈ (Subgroup.closure (gammaAt D x y v)).map φ.toMonoidHom :=
      ⟨g, hg, rfl⟩
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_gammaAt_map_iff φ hφ).mpr hz
  refine ⟨⟨φ b₀, (mem_gammaAt_map_iff φ hφ).mpr hb₀⟩, ?_, ?_, ?_, ?_⟩
  · intro w hw w' hw'
    obtain ⟨b, rfl⟩ := φ.surjective w
    obtain ⟨b', rfl⟩ := φ.surjective w'
    obtain ⟨g, hg, hgb⟩ := hT b ((mem_gammaAt_map_iff φ hφ).mp hw) b'
      ((mem_gammaAt_map_iff φ hφ).mp hw')
    exact ⟨φ g, hcl g hg, by rw [← hgb, map_mul, map_mul, map_inv]⟩
  · intro w hw
    obtain ⟨b, rfl⟩ := φ.surjective w
    obtain ⟨c, hc, hcb, hcomm⟩ := hN b ((mem_gammaAt_map_iff φ hφ).mp hw)
    exact ⟨φ c, (mem_gammaAt_map_iff φ hφ).mpr hc, φ.injective.ne hcb,
      (commute_map_iff φ).mpr hcomm⟩
  · intro w hw
    obtain ⟨b, rfl⟩ := φ.surjective w
    obtain ⟨c, hc, hbc⟩ := hZ b ((mem_gammaAt_map_iff φ hφ).mp hw)
    exact ⟨φ c, (mem_gammaAt_map_iff φ hφ).mpr hc, fun h => hbc ((commute_map_iff φ).mp h)⟩
  · intro w hw w' hw' htw
    obtain ⟨b, rfl⟩ := φ.surjective w
    obtain ⟨b', rfl⟩ := φ.surjective w'
    refine congrArg φ (hO b ((mem_gammaAt_map_iff φ hφ).mp hw) b'
      ((mem_gammaAt_map_iff φ hφ).mp hw') fun c hc => ?_)
    have := htw (φ c) ((mem_gammaAt_map_iff φ hφ).mpr hc)
    simpa only [φ.injective.ne_iff, commute_map_iff] using this

theorem localPivot_of_mem (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v x y : G} (hv : v ∈ D) (hx : x ∈ commSet D v) (hy : y ∈ commSet D v)
    (hxy : ¬ Commute x y) : LocalPivot D x y v := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hd : g * hC.d * g⁻¹ = φ hC.d := (MulAut.conj_apply g hC.d).symm
  have hx' : φ.symm x ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hx
  have hy' : φ.symm y ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hy
  have hxy' : ¬ Commute (φ.symm x) (φ.symm y) := fun h =>
    hxy (by simpa using (commute_map_iff φ).mpr h)
  have h := (localPivot_pivot hC hMZ hα hs hn hf hSp hx' hy' hxy').map φ hφD
  rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← hd] at h

theorem twelveSix_sp_component (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    ∃ t, ∃ ht : t ∈ compSet D x y hC.d,
      IsOrthReflection (Subgroup.closure (compSet D x y hC.d)) n f
        ⟨t, Subgroup.subset_closure ht⟩ := by
  have hdΓ := d_mem_commSet_inter hC hx hy
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  have hloc : ∀ v ∈ compSet D x y hC.d, LocalPivot D x y v := fun v hv =>
    localPivot_of_mem hC hMZ hα hs hn hf hSp hv.1.1.1
      ⟨hx.1, hv.1.1.2.1.symm, fun h => hv.1.1.2.2 h.symm⟩
      ⟨hy.1, hv.1.2.2.1.symm, fun h => hv.1.2.2.2 h.symm⟩ hxy
  have hcls := isClass_inClosure_compSet hN hD hdΓ (fun v hv => (hloc v hv).2.1)
    (fun v hv => (hloc v hv).2.2.1)
  have hS := setup_inClosure hD (fun z hz => hz.1.1.1) hcls
  have hcen := solvableRadical_le_center_of_noTwins hS
    (noOpenTwins_inClosure_compSet (fun v hv => (hloc v hv).1) fun v hv => (hloc v hv).2.2.2.2)
    (noClosedTwins_inClosure_compSet fun v hv => (hloc v hv).2.2.2.1)
  exact isOrthReflection_closure_of_pivot hIH hC hMZ hα hs hn hf hSp hx hy hxy
    (compSet_subset D x y hC.d) (mem_compSet_self hdΓ) (gammaAt_self_subset_compSet hdΓ) hcls
    (not_disconnected_inClosure_compSet hdΓ) hcen

omit [Finite G] in
theorem compSet_eq_of_not_disconnected {x y d : G} (hd : d ∈ commSet D x ∩ commSet D y)
    (h : ¬ Disconnected (commSet D x ∩ commSet D y)) :
    compSet D x y d = commSet D x ∩ commSet D y := by
  ext e
  refine ⟨fun he => he.1, fun he => ⟨he, ?_⟩⟩
  by_contra hr
  exact h ⟨d, hd, e, he, hr⟩

end CFSG.OddTranspositions.PartThree

end
