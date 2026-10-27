module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33B0
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs

public section

namespace CFSG.StandardType.RCKU33

open CFSG.Assembly

theorem u33_card_le_of_isCyclic {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} [Finite E] (hc : IsCyclic E) (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p := by
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE.2 g g.2)
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp.pos hexp

theorem u33_inf_inn_eq_bot {R : Type} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    (hpR : ¬ p ∣ Nat.card R) {E : Subgroup (MulAut R)} (hE : CFSG.Open.IsElemAbelian p E) :
    E ⊓ (MulAut.conj : R →* MulAut R).range = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxp : x ^ p = 1 := hE.2 x hx.1
  obtain ⟨r, rfl⟩ := hx.2
  have hdvd : orderOf (MulAut.conj r) ∣ Nat.card R :=
    (orderOf_map_dvd _ r).trans (orderOf_dvd_natCard r)
  have hop : orderOf (MulAut.conj r) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime hp).1 hop with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ hdvd) hpR

theorem u33_card_le_of_outdiagCyclic {R : Type} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    (hpR : ¬ p ∣ Nat.card R) {I : Set (MulAut R)} (hI : GGOutdiagCyclic R I)
    {E : Subgroup (MulAut R)} (hE : CFSG.Open.IsElemAbelian p E) (hEI : ∀ φ ∈ E, φ ∈ I) :
    Nat.card E ≤ p := by
  obtain ⟨φ₀, hφ₀⟩ := hI
  set N := (MulAut.conj : R →* MulAut R).range
  haveI : N.Normal := ⟨fun x hx φ => by
    obtain ⟨r, rfl⟩ := hx
    refine ⟨φ r, ?_⟩
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]⟩
  let f : E →* MulAut R ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN : (x : MulAut R) ∈ N := (QuotientGroup.eq_one_iff _).1 hx
    have h0 : (x : MulAut R) ∈ E ⊓ N := ⟨x.2, hxN⟩
    rw [u33_inf_inn_eq_bot hp hpR hE] at h0
    exact Subtype.ext h0
  have hrange : f.range ≤ Subgroup.zpowers (QuotientGroup.mk' N φ₀) := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : MulAut R) ∈ N ⊔ Subgroup.zpowers φ₀ := hφ₀ (hEI x x.2)
    have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers] at hmap
    exact hmap
  haveI : IsCyclic f.range := Subgroup.isCyclic_of_le hrange
  haveI : IsCyclic E := isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
    (MonoidHom.ofInjective hinj).symm.surjective
  exact u33_card_le_of_isCyclic hp inferInstance hE

theorem u33_card_le_of_comm {R : Type} [Group R] [hs : IsSimpleGroup R] {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a b : R, a * b = b * a) {E : Subgroup (MulAut R)}
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p := by
  haveI : IsMulCommutative R := ⟨⟨hcomm⟩⟩
  have hℓ : (Nat.card R).Prime := Group.is_simple_iff_prime_card.1 hs
  haveI : Fact (Nat.card R).Prime := ⟨hℓ⟩
  haveI : Finite R := Nat.finite_of_card_ne_zero hℓ.ne_zero
  haveI : IsCyclic R := isCyclic_of_prime_card rfl
  haveI : IsCyclic (MulAut R) :=
    isCyclic_of_surjective (IsCyclic.mulAutMulEquiv R).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv R).symm.surjective
  haveI : Finite (MulAut R) :=
    Finite.of_equiv _ (IsCyclic.mulAutMulEquiv R).symm.toEquiv
  exact u33_card_le_of_isCyclic hp inferInstance hE

theorem ggInnCoprimeRankInput :
    GGInnCoprimeRankInput := by
  intro p hp _ lab hlab Q hQ
  refine largeEvenRawDatum_mono ?_ (largeEvenLabelAll_outdiag_simple hlab Q hQ)
  rintro R _ I F ⟨hq, hO⟩
  refine ⟨hq, fun hs hpR E hE hEI => ?_⟩
  by_cases hcomm : ∀ a b : R, a * b = b * a
  · exact u33_card_le_of_comm hp hcomm hE
  · push Not at hcomm
    haveI : Finite R := Nat.finite_of_card_ne_zero fun h => hpR (h ▸ dvd_zero p)
    exact u33_card_le_of_outdiagCyclic hp hpR (hO hs hcomm) hE hEI

end CFSG.StandardType.RCKU33
