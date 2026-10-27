module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

variable {Q : Type*} [Group Q]

@[expose, reducible] def conjActionOn {E R : Subgroup Q}
    (hER : E ≤ Subgroup.normalizer (R : Set Q)) : MulAction ↥E ↥R where
  smul e r := ⟨(e : Q) * r * (e : Q)⁻¹, (Subgroup.mem_normalizer_iff.1 (hER e.2) r).1 r.2⟩
  one_smul r := Subtype.ext (show (1 : Q) * r * 1⁻¹ = r by simp)
  mul_smul e f r := Subtype.ext (show ((e : Q) * f) * r * ((e : Q) * f)⁻¹ =
    e * (f * r * (f : Q)⁻¹) * (e : Q)⁻¹ by group)

theorem coe_conjActionOn_smul {E R : Subgroup Q} (hER : E ≤ Subgroup.normalizer (R : Set Q))
    (e : ↥E) (r : ↥R) :
    letI := conjActionOn hER
    ((e • r : ↥R) : Q) = (e : Q) * r * (e : Q)⁻¹ :=
  rfl

variable [Finite Q]

theorem card_le_two_of_conj {E R : Subgroup Q} (hE9 : Nat.card E = 9)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hER : E ≤ Subgroup.normalizer (R : Set Q))
    (hR16 : Nat.card R ∣ 16)
    (hC : ∀ e ∈ E, e ≠ 1 → ∀ t ∈ R, ∀ s ∈ R, t ≠ 1 → s ≠ 1 → e * t = t * e →
      e * s = s * e → t = s) :
    Nat.card R ≤ 2 := by
  classical
  let := conjActionOn hER
  have : Fintype E := Fintype.ofFinite _
  have : Fintype R := Fintype.ofFinite _
  have hcomm : ∀ (e : E) (r : R), e • r = r → (e : Q) * r = r * e := by
    intro e r hr
    have h := congrArg Subtype.val hr
    rw [coe_conjActionOn_smul] at h
    calc (e : Q) * r = ((e : Q) * r * (e : Q)⁻¹) * e := by group
      _ = r * e := by rw [h]
  have hfix : ∀ e : E, e ≠ 1 → ∀ r : R, e • r = r → ∀ f : E, f • r = r := by
    intro e he r hr f
    by_contra hf
    have hr1 : (r : Q) ≠ 1 := by
      intro h
      apply hf
      apply Subtype.ext
      rw [coe_conjActionOn_smul, h]
      group
    have hfr1 : ((f • r : R) : Q) ≠ 1 := by
      rw [coe_conjActionOn_smul]
      intro h
      apply hr1
      have hr' : (r : Q) = (f : Q)⁻¹ * ((f : Q) * r * (f : Q)⁻¹) * f := by group
      rw [hr', h]
      group
    have he' : (e : Q) ≠ 1 := fun h => he (Subtype.ext h)
    have hre := hcomm e r hr
    have hef := hEc e e.2 f f.2
    have hef' := hEc e e.2 (f : Q)⁻¹ (E.inv_mem f.2)
    have hfre : (e : Q) * (f • r : R) = (f • r : R) * e := by
      rw [coe_conjActionOn_smul]
      calc (e : Q) * ((f : Q) * r * (f : Q)⁻¹) = ((e : Q) * f) * r * (f : Q)⁻¹ := by group
        _ = ((f : Q) * e) * r * (f : Q)⁻¹ := by rw [hef]
        _ = (f : Q) * (e * r) * (f : Q)⁻¹ := by group
        _ = (f : Q) * (r * e) * (f : Q)⁻¹ := by rw [hre]
        _ = (f : Q) * r * ((e : Q) * (f : Q)⁻¹) := by group
        _ = (f : Q) * r * ((f : Q)⁻¹ * e) := by rw [hef']
        _ = ((f : Q) * r * (f : Q)⁻¹) * e := by group
    exact hf (Subtype.ext (hC e e.2 he' r r.2 _ (f • r).2 hr1 hfr1 hre hfre).symm)
  have hE9' : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card, hE9]
  have hset : ∀ g : E, g ≠ 1 → MulAction.fixedBy R g = MulAction.fixedPoints E R := by
    intro g hg
    ext r
    rw [MulAction.mem_fixedBy, MulAction.mem_fixedPoints]
    exact ⟨fun h f => hfix g hg r h f, fun h => h g⟩
  have hsum : ∑ g : E, Fintype.card (MulAction.fixedBy R g) =
      Fintype.card R + 8 * Fintype.card (MulAction.fixedPoints E R) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : E))]
    have h1 : Fintype.card (MulAction.fixedBy R (1 : E)) = Fintype.card R :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun r => (MulAction.mem_fixedBy).2 (one_smul E r))
    have h2 : ∀ g ∈ Finset.univ.erase (1 : E), Fintype.card (MulAction.fixedBy R g) =
        Fintype.card (MulAction.fixedPoints E R) := fun g hg =>
      Fintype.card_congr (Set.equivOfEq (hset g (Finset.ne_of_mem_erase hg)))
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hE9', smul_eq_mul]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E R
  rw [hsum, hE9'] at hB
  have hF1 : 1 ≤ Fintype.card (MulAction.fixedPoints E R) := by
    refine Fintype.card_pos_iff.2 ⟨⟨1, fun f => Subtype.ext ?_⟩⟩
    rw [coe_conjActionOn_smul]
    simp
  obtain ⟨e, he⟩ : ∃ e : E, e ≠ 1 := by
    have : Nontrivial E := (Fintype.one_lt_card_iff_nontrivial (α := E)).1 (by omega)
    exact exists_ne 1
  have he' : (e : Q) ≠ 1 := fun h => he (Subtype.ext h)
  have hF2 : Fintype.card (MulAction.fixedPoints E R) ≤ 2 := by
    by_contra h
    obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      (Fintype.two_lt_card_iff (α := MulAction.fixedPoints E R)).1 (by omega)
    have hval : ∀ x y : MulAction.fixedPoints E R, ((x : R) : Q) = ((y : R) : Q) → x = y :=
      fun x y h => Subtype.ext (Subtype.ext h)
    have key : ∀ x y : MulAction.fixedPoints E R, ((x : R) : Q) ≠ 1 → ((y : R) : Q) ≠ 1 →
        x = y := fun x y hx hy => hval x y (hC e e.2 he' _ (x : R).2 _ (y : R).2 hx hy
          (hcomm e x (x.2 e)) (hcomm e y (y.2 e)))
    by_cases ha : ((a : R) : Q) = 1
    · exact hbc (key b c (fun hb => hab (hval a b (ha.trans hb.symm)))
        (fun hc => hac (hval a c (ha.trans hc.symm))))
    · by_cases hb : ((b : R) : Q) = 1
      · exact hac (key a c ha (fun hc => hbc (hval b c (hb.trans hc.symm))))
      · exact hab (key a b ha hb)
  obtain ⟨k, hk, hRk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show Nat.card R ∣ 2 ^ 4 by simpa using hR16)
  rw [Nat.card_eq_fintype_card] at hRk ⊢
  rw [hRk] at hB ⊢
  interval_cases k <;> omega

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
