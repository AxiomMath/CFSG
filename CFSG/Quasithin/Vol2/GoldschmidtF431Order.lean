module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G G' : Type*} [Group G] [Group G']

theorem thompsonPairCount_eq_of_hom {u z w : G} {u' z' w' : G'} (hu : orderOf u = 2)
    (hz : orderOf z = 2) (hw : orderOf w = 2) (hu' : orderOf u' = 2) (hz' : orderOf z' = 2)
    (hw' : orderOf w' = 2) (ψ : Subgroup.centralizer ({w} : Set G) →* G')
    (hψ : Function.Injective ψ) (hψr : ψ.range = Subgroup.centralizer ({w'} : Set G'))
    (hψw : ∀ hmem : w ∈ Subgroup.centralizer ({w} : Set G), ψ ⟨w, hmem⟩ = w')
    (hψu : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
      (IsConj u (x : G) ↔ IsConj u' (ψ x)))
    (hψz : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
      (IsConj z (x : G) ↔ IsConj z' (ψ x))) :
    thompsonPairCount u z w = thompsonPairCount u' z' w' := by
  have hG : ∀ p ∈ thompsonPairs u z w,
      p.1 ∈ Subgroup.centralizer ({w} : Set G) ∧ p.2 ∈ Subgroup.centralizer ({w} : Set G) :=
    fun p hp => mem_centralizer_of_mem_thompsonPairs (mul_self_eq_one_of_orderOf_eq_two hu)
      (mul_self_eq_one_of_orderOf_eq_two hz) (mul_self_eq_one_of_orderOf_eq_two hw) hp
  have hG' : ∀ p ∈ thompsonPairs u' z' w',
      p.1 ∈ Subgroup.centralizer ({w'} : Set G') ∧ p.2 ∈ Subgroup.centralizer ({w'} : Set G') :=
    fun p hp => mem_centralizer_of_mem_thompsonPairs (mul_self_eq_one_of_orderOf_eq_two hu')
      (mul_self_eq_one_of_orderOf_eq_two hz') (mul_self_eq_one_of_orderOf_eq_two hw') hp
  have hw0 : w ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hordψ : ∀ x : Subgroup.centralizer ({w} : Set G), orderOf (ψ x) = orderOf (x : G) := by
    intro x
    rw [orderOf_injective ψ hψ x, Subgroup.orderOf_coe]
  let f : thompsonPairs u z w → thompsonPairs u' z' w' := fun p =>
    ⟨(ψ ⟨p.1.1, (hG p.1 p.2).1⟩, ψ ⟨p.1.2, (hG p.1 p.2).2⟩), by
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 p.2
      have o1 : orderOf p.1.1 = 2 := by rw [← orderOf_eq_of_isConj h1]; exact hu
      have o2 : orderOf p.1.2 = 2 := by rw [← orderOf_eq_of_isConj h2]; exact hz
      refine mem_thompsonPairs.2 ⟨(hψu ⟨p.1.1, _⟩ o1).mp h1, (hψz ⟨p.1.2, _⟩ o2).mp h2, ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have hab : (⟨p.1.1, (hG p.1 p.2).1⟩ * ⟨p.1.2, (hG p.1 p.2).2⟩ :
          Subgroup.centralizer ({w} : Set G)) ^ k = ⟨w, hw0⟩ := Subtype.ext hk
      rw [← hψw hw0, ← hab, map_zpow, map_mul]⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · have h := congrArg Subtype.val hpq
      simp only [f, Prod.mk.injEq] at h
      have e1 := hψ h.1
      have e2 := hψ h.2
      exact Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2))
    · obtain ⟨q, hq⟩ := q
      obtain ⟨h1, h2, h3⟩ := mem_thompsonPairs.1 hq
      obtain ⟨hq1, hq2⟩ := hG' q hq
      have hq1' : q.1 ∈ ψ.range := by rw [hψr]; exact hq1
      have hq2' : q.2 ∈ ψ.range := by rw [hψr]; exact hq2
      obtain ⟨a, ha⟩ := hq1'
      obtain ⟨b, hb⟩ := hq2'
      have o1 : orderOf (ψ a) = 2 := by rw [ha, ← orderOf_eq_of_isConj h1]; exact hu'
      have o2 : orderOf (ψ b) = 2 := by rw [hb, ← orderOf_eq_of_isConj h2]; exact hz'
      have oa : orderOf (a : G) = 2 := by rw [← hordψ]; exact o1
      have ob : orderOf (b : G) = 2 := by rw [← hordψ]; exact o2
      have hconj1 : IsConj u (a : G) := (hψu a oa).mpr (by rw [ha]; exact h1)
      have hconj2 : IsConj z (b : G) := (hψz b ob).mpr (by rw [hb]; exact h2)
      have hmem : ((a : G), (b : G)) ∈ thompsonPairs u z w := by
        refine mem_thompsonPairs.2 ⟨hconj1, hconj2, ?_⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have : ψ ((a * b) ^ k) = ψ ⟨w, hw0⟩ := by
          rw [hψw hw0, map_zpow, map_mul, ha, hb]
          exact hk
        exact congrArg Subtype.val (hψ this)
      refine ⟨⟨((a : G), (b : G)), hmem⟩, ?_⟩
      apply Subtype.ext
      simp only [f]
      exact Prod.ext ha hb
  exact Nat.card_congr (Equiv.ofBijective f hf)

variable [Finite G] [Finite G']

theorem card_eq_of_transversal_data {u z : G} {u' z' : G'} (hu : orderOf u = 2)
    (hz : orderOf z = 2) (huz : ¬ IsConj u z) (hu' : orderOf u' = 2) (hz' : orderOf z' = 2)
    (huz' : ¬ IsConj u' z') (T : Finset G) (hT : ∀ w ∈ T, orderOf w = 2)
    (hTrep : ∀ x : G, orderOf x = 2 → ∃! w, w ∈ T ∧ IsConj w x) (T' : Finset G')
    (hT' : ∀ w ∈ T', orderOf w = 2) (hTrep' : ∀ x : G', orderOf x = 2 → ∃! w, w ∈ T' ∧ IsConj w x)
    (e : G → G') (hinj : Set.InjOn e T) (himg : ∀ w' : G', w' ∈ T' ↔ ∃ w ∈ T, e w = w')
    (huT : u ∈ T) (hzT : z ∈ T) (heu : e u = u') (hez : e z = z')
    (hψ : ∀ w ∈ T, ∃ ψ : Subgroup.centralizer ({w} : Set G) →* G', Function.Injective ψ ∧
      ψ.range = Subgroup.centralizer ({e w} : Set G') ∧
      (∀ hmem : w ∈ Subgroup.centralizer ({w} : Set G), ψ ⟨w, hmem⟩ = e w) ∧
      (∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
        (IsConj u (x : G) ↔ IsConj u' (ψ x))) ∧
      (∀ x : Subgroup.centralizer ({w} : Set G), orderOf (x : G) = 2 →
        (IsConj z (x : G) ↔ IsConj z' (ψ x)))) :
    Nat.card G = Nat.card G' := by
  classical
  have h1 := card_eq_sum_transversal hu hz huz T hT hTrep
  have h2 := card_eq_sum_transversal hu' hz' huz' T' hT' hTrep'
  have hT'eq : T' = T.image e := by
    ext w'
    rw [himg, Finset.mem_image]
  have hcent : ∀ w ∈ T, Nat.card (Subgroup.centralizer ({w} : Set G)) =
      Nat.card (Subgroup.centralizer ({e w} : Set G')) := by
    intro w hw
    obtain ⟨ψ, hinjψ, hrange, -⟩ := hψ w hw
    have := Nat.card_congr (MonoidHom.ofInjective hinjψ).toEquiv
    rwa [hrange] at this
  have hterm : ∀ w ∈ T, (thompsonPairCount u z w : ℚ) * Nat.card (Subgroup.centralizer {u}) *
      Nat.card (Subgroup.centralizer {z}) / Nat.card (Subgroup.centralizer {w}) =
      (thompsonPairCount u' z' (e w) : ℚ) * Nat.card (Subgroup.centralizer {u'}) *
        Nat.card (Subgroup.centralizer {z'}) / Nat.card (Subgroup.centralizer {e w}) := by
    intro w hw
    obtain ⟨ψ, hinjψ, hrange, hψw, hcu, hcz⟩ := hψ w hw
    have hew : orderOf (e w) = 2 := hT' _ ((himg _).mpr ⟨w, hw, rfl⟩)
    have ha := thompsonPairCount_eq_of_hom hu hz (hT w hw) hu' hz' hew ψ hinjψ hrange hψw hcu hcz
    have hcu' := hcent u huT
    have hcz' := hcent z hzT
    rw [heu] at hcu'
    rw [hez] at hcz'
    rw [ha, hcu', hcz', hcent w hw]
  rw [hT'eq, Finset.sum_image hinj] at h2
  have : (Nat.card G : ℚ) = Nat.card G' := by
    rw [h1, h2]
    exact Finset.sum_congr rfl hterm
  exact_mod_cast this

end CFSG.Quasithin.H13.F431
