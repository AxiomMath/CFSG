module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosurePComp
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeNbr
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section OmegaOneCenter

variable {G : Type} [Group G]

@[expose] def ggOmegaOneCenter (p : ℕ) (J : Subgroup G) :
    Subgroup (↥J ⧸ LargeEvenPPrimeCore p ↥J) where
  carrier := {c | c ∈ Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J) ∧ c ^ p = 1}
  mul_mem' := by
    rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hc : Commute a b := Subgroup.mem_center_iff.mp hb a
    rw [hc.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨ha, hap⟩
    exact ⟨inv_mem ha, by rw [inv_pow, hap, inv_one]⟩

private theorem mem_largeEvenPPrimeCore_of_mem_coreOf {p : ℕ} {J : Subgroup G} {x : ↥J}
    (hx : (x : G) ∈ LargeEvenPPrimeCoreOf p J) : x ∈ LargeEvenPPrimeCore p ↥J := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rwa [show y = x from Subtype.ext hyx] at hy

theorem ggOmegaOneCenter_eq_bot_of_coprime [Finite G] {p : ℕ} [Fact p.Prime] {J : Subgroup G}
    (h : Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J)))) :
    ggOmegaOneCenter p J = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  obtain ⟨hcen, hcp⟩ := hc
  have hdvd1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have hdvd2 : orderOf c ∣ Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J)) :=
    Subgroup.orderOf_dvd_natCard _ hcen
  have hd := Nat.dvd_gcd hdvd1 hdvd2
  rw [h.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem mk_mem_ggOmegaOneCenter {p : ℕ} {J : Subgroup G} {v : G} (hv : v ∈ J) (hvp : v ^ p = 1)
    (hc : ∀ j ∈ J, ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p J) :
    (QuotientGroup.mk (⟨v, hv⟩ : ↥J) : ↥J ⧸ LargeEvenPPrimeCore p ↥J) ∈ ggOmegaOneCenter p J := by
  let N := LargeEvenPPrimeCore p ↥J
  let vJ : ↥J := ⟨v, hv⟩
  have hvJp : vJ ^ p = 1 := by
    apply Subtype.ext
    simpa [vJ] using hvp
  change (QuotientGroup.mk vJ : ↥J ⧸ N) ∈ ggOmegaOneCenter p J
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    refine QuotientGroup.induction_on g ?_
    intro j
    have hmem : ⁅vJ, j⁆ ∈ N := by
      apply mem_largeEvenPPrimeCore_of_mem_coreOf
      simpa [vJ, N, commutatorElement_def] using hc j j.2
    have h1 : (QuotientGroup.mk' N) ⁅vJ, j⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    have hcomm : (QuotientGroup.mk' N) vJ * (QuotientGroup.mk' N) j =
        (QuotientGroup.mk' N) j * (QuotientGroup.mk' N) vJ := by
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, h1]
    exact hcomm.symm
  · change ((QuotientGroup.mk' N) vJ) ^ p = 1
    rw [← map_pow, hvJp, map_one]

theorem card_le_card_ggOmegaOneCenter [Finite G] {p : ℕ} [Fact p.Prime] {J A : Subgroup G}
    (hAJ : A ≤ J) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hc : ∀ v ∈ A, ∀ j ∈ J, ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p J) :
    Nat.card A ≤ Nat.card (ggOmegaOneCenter p J) := by
  let N := LargeEvenPPrimeCore p ↥J
  let φ : ↥A →* ↥J ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hAJ)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haN : Subgroup.inclusion hAJ a ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact ha
    have haCore : (a : G) ∈ LargeEvenPPrimeCoreOf p J :=
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hAJ a, haN, Subgroup.coe_inclusion hAJ a⟩
    have ha1 : (a : G) = 1 := eq_one_of_mem_largeEvenPPrimeCoreOf haCore (hAp a a.2)
    exact Subtype.ext ha1
  have hmem : ∀ a : ↥A, φ a ∈ ggOmegaOneCenter p J := by
    intro a
    have h := mk_mem_ggOmegaOneCenter (p := p) (J := J) (v := (a : G)) (hAJ a.2)
      (by simpa using hAp a a.2) (by intro j hj; simpa using hc a a.2 j hj)
    show (QuotientGroup.mk (Subgroup.inclusion hAJ a) : ↥J ⧸ N) ∈ ggOmegaOneCenter p J
    exact h
  let ψ : ↥A → ↥(ggOmegaOneCenter p J) := fun a => ⟨φ a, hmem a⟩
  have hψinj : Function.Injective ψ := fun a b hab => hφinj (Subtype.ext_iff.mp hab)
  exact Nat.card_le_card_of_injective ψ hψinj

end OmegaOneCenter

section NormalClosure

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_le_of_le_of_commute {E A A' : Subgroup G} (hE : IsMulCommutative E)
    (hA : A ≤ E) (hA' : A' ≤ E) :
    Nat.card A * Nat.card A' ≤ Nat.card E * Nat.card (A ⊓ A' : Subgroup G) := by
  have hc : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    have h := hE.is_comm.comm (⟨x, hA hx⟩ : E) (⟨y, hA' hy⟩ : E)
    simpa using congrArg Subtype.val h
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (H := G) A A' hc
  calc Nat.card A * Nat.card A' = Nat.card (A ⊔ A' : Subgroup G) * Nat.card (A ⊓ A' : Subgroup G) :=
        hcard.symm
    _ ≤ Nat.card E * Nat.card (A ⊓ A' : Subgroup G) :=
        Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (sup_le hA hA'))

theorem commutator_mem_largeEvenPPrimeCoreOf_of_mem_inf {p : ℕ} [Fact p.Prime] {H X X' J : Subgroup G}
    (hX : LargeEvenPComponent p H X) (hX' : LargeEvenPComponent p H X') (hne : X ≠ X')
    (hJX : J ≤ X) {v : G} (hvJ : v ∈ J) (hvX' : v ∈ X') :
    ∀ j ∈ J, ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p J := by
  intro j hj
  have hJH : J ≤ H := hJX.trans hX.1
  have hjX : j ∈ X := hJX hj
  have hcomm : ⁅v, j⁆ ∈ CFSG.Open.lBalancePrimeCore p H :=
    commutator_le_lBalancePrimeCore_of_ne hX' hX hne.symm
      (Subgroup.commutator_mem_commutator hvX' hjX)
  have hmemH : ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p H := by
    rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map p H] at hcomm
    simpa [LargeEvenPPrimeCoreOf, LargeEvenPPrimeCore] using hcomm
  have hmemJ : ⁅v, j⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hvJ hj) (J.inv_mem hvJ)) (J.inv_mem hj)
  exact largeEvenPPrimeCoreOf_inf_le hJH ⟨hmemH, hmemJ⟩

theorem normalizer_inf_le_normalizer_of_pComponent {p : ℕ} [Fact p.Prime] {H X J E : Subgroup G}
    (hX : LargeEvenPComponent p H X) (hJX : J ≤ X) (hE : IsElemAbelian p E)
    (hcard : Nat.card E * Nat.card (ggOmegaOneCenter p J) < Nat.card (E ⊓ J : Subgroup G) ^ 2) :
    Subgroup.normalizer (E : Set G) ⊓ H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  obtain ⟨hgE, hgH⟩ := hg
  by_contra hgX
  let X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  have hX' : LargeEvenPComponent p H X' := by
    have h := largeEvenPComponent_map_conj' hX g
    rwa [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgH)] at h
  have hne : X' ≠ X := fun h => hgX (mem_normalizer_iff_map_conj.mpr h)
  let A : Subgroup G := E ⊓ J
  let A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hAE : A ≤ E := inf_le_left
  have hAJ : A ≤ J := inf_le_right
  have hA'E : A' ≤ E := by
    calc A' = A.map (MulAut.conj g).toMonoidHom := rfl
      _ ≤ E.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hAE
      _ = E := map_conj_eq_of_mem_normalizer hgE
  have hA'X' : A' ≤ X' := by
    calc A' = A.map (MulAut.conj g).toMonoidHom := rfl
      _ ≤ J.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hAJ
      _ ≤ X.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hJX
  have hAJ' : A ⊓ A' ≤ J := inf_le_left.trans hAJ
  have hAp' : ∀ v ∈ A ⊓ A', v ^ p = 1 := fun v hv => hE.2 v (hAE hv.1)
  have hc' : ∀ v ∈ A ⊓ A', ∀ j ∈ J, ⁅v, j⁆ ∈ LargeEvenPPrimeCoreOf p J := by
    intro v hv j hj
    have hvJ : v ∈ J := hAJ hv.1
    have hvX' : v ∈ X' := hA'X' hv.2
    exact commutator_mem_largeEvenPPrimeCoreOf_of_mem_inf hX hX' hne.symm hJX hvJ hvX' j hj
  have hcard_inf : Nat.card (A ⊓ A' : Subgroup G) ≤ Nat.card (ggOmegaOneCenter p J) :=
    card_le_card_ggOmegaOneCenter hAJ' hAp' hc'
  have hmul : Nat.card A * Nat.card A' ≤ Nat.card E * Nat.card (A ⊓ A' : Subgroup G) :=
    card_mul_card_le_of_le_of_commute hE.1 hAE hA'E
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hfinal : Nat.card A ^ 2 ≤ Nat.card E * Nat.card (ggOmegaOneCenter p J) := by
    calc Nat.card A ^ 2 = Nat.card A * Nat.card A' := by rw [hA'card, pow_two]
      _ ≤ Nat.card E * Nat.card (A ⊓ A' : Subgroup G) := hmul
      _ ≤ Nat.card E * Nat.card (ggOmegaOneCenter p J) := Nat.mul_le_mul_left _ hcard_inf
  have hcontra : Nat.card (E ⊓ J : Subgroup G) ^ 2 ≤
      Nat.card E * Nat.card (ggOmegaOneCenter p J) := by
    simpa [A] using hfinal
  exact absurd hcontra (not_le.mpr hcard)

theorem normalizer_inf_le_normalizer_of_pComponent_of_rank {p : ℕ} [Fact p.Prime]
    {H X J E : Subgroup G} (hX : LargeEvenPComponent p H X) (hJX : J ≤ X) (hE : IsElemAbelian p E)
    (hrank : Nat.log p (Nat.card E) + Nat.log p (Nat.card (ggOmegaOneCenter p J)) <
      2 * Nat.log p (Nat.card (E ⊓ J : Subgroup G))) :
    Subgroup.normalizer (E : Set G) ⊓ H ≤ Subgroup.normalizer (X : Set G) := by
  have hPrime : p.Prime := Fact.out
  have hEpg : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hEJpg : IsPGroup p (E ⊓ J : Subgroup G) :=
    fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2.1)⟩
  have hOpg : IsPGroup p (ggOmegaOneCenter p J) :=
    fun g => ⟨1, Subtype.ext (by simpa using g.2.2)⟩
  obtain ⟨a, ha⟩ := hEpg.exists_card_eq
  obtain ⟨m, hm⟩ := hEJpg.exists_card_eq
  obtain ⟨k, hk⟩ := hOpg.exists_card_eq
  have hpa : Nat.log p (Nat.card E) = a := by rw [ha, Nat.log_pow hPrime.one_lt]
  have hpm : Nat.log p (Nat.card (E ⊓ J : Subgroup G)) = m := by
    rw [hm, Nat.log_pow hPrime.one_lt]
  have hpk : Nat.log p (Nat.card (ggOmegaOneCenter p J)) = k := by
    rw [hk, Nat.log_pow hPrime.one_lt]
  have hlt : a + k < 2 * m := by
    rw [hpa, hpm, hpk] at hrank
    exact hrank
  refine normalizer_inf_le_normalizer_of_pComponent hX hJX hE ?_
  rw [ha, hk, hm, ← pow_add, ← pow_mul]
  exact Nat.pow_lt_pow_right hPrime.one_lt (by omega)

theorem normalizer_inf_le_normalizer_of_pComponent_of_coprime_center {p : ℕ} [Fact p.Prime]
    {H X J E : Subgroup G} (hX : LargeEvenPComponent p H X) (hJX : J ≤ X) (hE : IsElemAbelian p E)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J))))
    (hrank : Nat.log p (Nat.card E) < 2 * Nat.log p (Nat.card (E ⊓ J : Subgroup G))) :
    Subgroup.normalizer (E : Set G) ⊓ H ≤ Subgroup.normalizer (X : Set G) := by
  refine normalizer_inf_le_normalizer_of_pComponent_of_rank hX hJX hE ?_
  have hbot : Nat.card (ggOmegaOneCenter p J) = 1 := by
    rw [ggOmegaOneCenter_eq_bot_of_coprime hZ, Subgroup.card_bot]
  have hlog : Nat.log p (Nat.card (ggOmegaOneCenter p J)) = 0 := by
    rw [hbot, Nat.log_one_right]
  rw [hlog, add_zero]
  exact hrank

end NormalClosure

end CFSG.StandardType
