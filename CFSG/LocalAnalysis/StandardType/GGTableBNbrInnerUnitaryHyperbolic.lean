module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Open TableB

@[expose] def GGTableBNbrInnerUnitaryHypLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
    p ≠ 2 ∧ p ∣ 2 ^ lab.n - 1

theorem not_dvd_two_pow_add_one_of_dvd_sub_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) : ¬ p ∣ 2 ^ n + 1 := by
  intro h1
  have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h1 hpq
  have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem four_le_two_pow_of_dvd_sub_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) : 4 ≤ 2 ^ n := by
  have h2n : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hle : p ≤ 2 ^ n - 1 := Nat.le_of_dvd (by omega) hpq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  omega

section Hyp

variable {n p : ℕ} {K : Type} [Field K]

theorem ggSCWeylIrred_hypSU_two (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) : GGSCWeylIrred p 0 (hypSU h 2 0) := by
  intro E hE _ h3 _
  exfalso
  have h2 := card_le_pow_hypSU h hp hp2 hpq E hE
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact absurd (h3.trans h2) (not_le.mpr hlt)

theorem ggSCWeylIrred_hypSU_three (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) : GGSCWeylIrred p 0 (hypSU h 3 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hE _ h3 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := 3) h hp hζ hbar
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζ (by norm_num) E hE h3
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg x hx
    refine ⟨Multiplicative.ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : E.map (MulAut.conj g).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_range_hypTorusHom h hp hζ ι hι]; exact h3)
  have hirr := ggWeylIrred_map (MulAut.conj g⁻¹) (ggWeylIrred_hypTorusRange h hp hp2 hζ hbar ι hι)
  have hback : ι.range.map (MulAut.conj g⁻¹).toMonoidHom = E := by
    rw [← heq, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (hypSU h 3 0) := MonoidHom.ext fun x => by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [hcomp, Subgroup.map_id]
  rwa [hback] at hirr

end Hyp

section Torus

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

theorem ggSCWeylIrred_statedProj_hyp (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) {r : ℕ} (hr : r = 2 ∨ r = 3) :
    GGSCWeylIrred p 0 (StatedProj (StatedSU (2 * r) (2 ^ n) K)) := by
  have hU : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  rcases hr with rfl | rfl
  · exact ggSCWeylIrred_statedProj_of_hypSU hU (by norm_num) hp hpq'
      (ggSCWeylIrred_hypSU_two hU hp hp2 hpq)
  · exact ggSCWeylIrred_statedProj_of_hypSU hU (by norm_num) hp hpq'
      (ggSCWeylIrred_hypSU_three hU hp hp2 hpq)


theorem ggTorusNbrSC_unitaryHyp (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) {d : ℕ} (hd : d = 4 ∨ d = 6) :
    GGTorusNbrSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  have hd4 : 4 ≤ d := by omega
  have hdev : Even d := by rcases hd with rfl | rfl <;> decide
  refine ggTorusNbrSC_of_scWeylIrred hp (center_statedProj_statedSU_eq_bot hK hd4)
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega)
      hp hpq' φ hφ hφp)
    (ggCenterPrime_psu_even hK hdev hd4 hq4 hpq') ?_
  rcases hd with rfl | rfl
  · exact ggSCWeylIrred_statedProj_hyp hK hn hp hp2 hpq (r := 2) (Or.inl rfl)
  · exact ggSCWeylIrred_statedProj_hyp hK hn hp hp2 hpq (r := 3) (Or.inr rfl)

theorem largeEvenLabelAll_torusNbrSC_unitaryHyp {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerUnitaryHypLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hcase, hp2, hpq⟩ := h
  dsimp only at hcase hp2 hpq
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases hcase with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusNbrSC_unitaryHyp (d := l + 1) hK hn hp hp2 hpq (by omega)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show ¬ ((3 : ℕ) = 2) from by norm_num, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusNbrSC_unitaryHyp (d := 4) hK hn hp hp2 hpq (Or.inl rfl)⟩

theorem ggTableBNbrInnerInputOn_unitaryHyp :
    GGTableBNbrInnerInputOn GGTableBNbrInnerUnitaryHypLabel :=
  ggTableBNbrInnerInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbrSC_unitaryHyp hp hlab h

end Torus

end CFSG.StandardType

end
