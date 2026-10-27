module

public import CFSG.GroupTheory.OddInversion
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open Subgroup
open scoped Pointwise
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {G : Type} [Group G]

@[expose] def hypOrbit (N D : Subgroup G) : Set (Subgroup G) :=
  {D' | ∃ n ∈ N, D' = D.map (MulAut.conj n).toMonoidHom}

@[expose] def fixedHyp (p : ℕ) (E : Subgroup G) (t : G) : Set (Subgroup G) :=
  {D | D ∈ hyperplanes p E ∧ D.map (MulAut.conj t).toMonoidHom = D}

private def invertedSub {p : ℕ} (E : Subgroup G) (t : G)
    (hE : CFSG.Open.IsElemAbelian p E) : Subgroup G where
  carrier := CFSG.OddInversion.invertedSet E t
  one_mem' := ⟨E.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxE, hx⟩ ⟨hyE, hy⟩
    have hcomm : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x⁻¹, E.inv_mem hxE⟩
        ⟨y⁻¹, E.inv_mem hyE⟩)
    refine ⟨E.mul_mem hxE hyE, ?_⟩
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hx, hy]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, hcomm]
  inv_mem' := by
    rintro x ⟨hxE, hx⟩
    refine ⟨E.inv_mem hxE, ?_⟩
    calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hx]

private theorem mem_invertedSub {p : ℕ} {E : Subgroup G} {t x : G}
    {hE : CFSG.Open.IsElemAbelian p E} :
    x ∈ invertedSub E t hE ↔ x ∈ E ∧ t * x * t⁻¹ = x⁻¹ :=
  CFSG.OddInversion.mem_invertedSet

private theorem invertedSub_le {p : ℕ} (E : Subgroup G) (t : G)
    (hE : CFSG.Open.IsElemAbelian p E) : invertedSub E t hE ≤ E :=
  fun _ hx => (mem_invertedSub.mp hx).1

private theorem isElemAbelian_mono {p : ℕ} {E H : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hHE : H ≤ E) :
    CFSG.Open.IsElemAbelian p H := by
  refine ⟨⟨⟨fun (x y : ↥H) => ?_⟩⟩, fun x hx => hE.2 x (hHE hx)⟩
  exact Subtype.ext (congrArg (fun z : ↥E => (z : G))
    (hE.1.is_comm.comm ⟨x.1, hHE x.2⟩ ⟨y.1, hHE y.2⟩))

private theorem fixed_inf_inverted_eq_bot {p : ℕ} {E : Subgroup G} {t : G}
    (hE : CFSG.Open.IsElemAbelian p E) (hEodd : Odd (Nat.card E)) :
    E ⊓ Subgroup.centralizer {t} ⊓ invertedSub E t hE = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hxC, hxI⟩
  have hxE : x ∈ E := hxC.1
  have hfix : t * x * t⁻¹ = x := by
    have h : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC.2
    rw [← h]
    group
  have hinv : t * x * t⁻¹ = x⁻¹ := (mem_invertedSub.mp hxI).2
  have hx2 : x ^ 2 = 1 := by
    have h : x = x⁻¹ := hfix.symm.trans hinv
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h
  have hx1 : x = 1 := CFSG.OddInversion.sq_injOn hEodd hxE E.one_mem (by simpa using hx2)
  rw [hx1]
  exact Subgroup.one_mem ⊥

private theorem fixed_sup_inverted_eq {p : ℕ} {E : Subgroup G} {t : G}
    (hE : CFSG.Open.IsElemAbelian p E) (hEodd : Odd (Nat.card E))
    (ht2 : orderOf t = 2) (htE : t ∈ Subgroup.normalizer (E : Set G)) :
    E ⊓ Subgroup.centralizer {t} ⊔ invertedSub E t hE = E := by
  refine le_antisymm (sup_le inf_le_left (invertedSub_le E t hE)) ?_
  intro x hxE
  have hset : (E : Set G) = ((E ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) *
      ((E : Set G) ∩ CFSG.OddInversion.invertedSet E t) :=
    (CFSG.OddInversion.odd_involution_product_decomposition hEodd ht2 htE).2.2 E le_rfl htE |>.2
  have hx' : x ∈ (E : Set G) := hxE
  rw [hset] at hx'
  obtain ⟨c, hc, j, hj, hcj⟩ := Set.mem_mul.mp hx'
  rw [← hcj]
  exact (E ⊓ Subgroup.centralizer {t} ⊔ invertedSub E t hE).mul_mem
    (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hj.2)

private theorem fixed_inverted_facts [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ (2 * f))
    {t : G} (ht2 : orderOf t = 2) (htE : t ∈ Subgroup.normalizer (E : Set G))
    (hCcard : Nat.card ↥(E ⊓ Subgroup.centralizer {t}) = p ^ f) :
    (E ⊓ Subgroup.centralizer {t}) ⊓ invertedSub E t hE = ⊥ ∧
      (E ⊓ Subgroup.centralizer {t}) ⊔ invertedSub E t hE = E ∧
      Nat.card E = Nat.card ↥(E ⊓ Subgroup.centralizer {t}) *
        Nat.card ↥(invertedSub E t hE) ∧
      Nat.card ↥(invertedSub E t hE) = p ^ f := by
  have hEodd : Odd (Nat.card E) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hcomm : ∀ x ∈ E ⊓ Subgroup.centralizer {t}, ∀ y ∈ invertedSub E t hE,
      x * y = y * x := by
    intro x hx y hy
    exact congrArg (fun z : ↥E => (z : G))
      (hE.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, (mem_invertedSub.mp hy).1⟩)
  have hCI := fixed_inf_inverted_eq_bot (t := t) hE hEodd
  have hsup := fixed_sup_inverted_eq hE hEodd ht2 htE
  have hcardE : Nat.card E = Nat.card ↥(E ⊓ Subgroup.centralizer {t}) *
      Nat.card ↥(invertedSub E t hE) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (E ⊓ Subgroup.centralizer {t}) (invertedSub E t hE) hcomm).1
    rw [hsup, hCI, Subgroup.card_bot, mul_one] at h
    exact h
  refine ⟨hCI, hsup, hcardE, ?_⟩
  have h := hcardE
  rw [hcard, hCcard] at h
  have hpow : p ^ (2 * f) = p ^ f * p ^ f := by
    rw [show 2 * f = f + f by ring, pow_add]
  rw [hpow] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos f) h).symm

private theorem fixed_decomposition {p : ℕ} {E D : Subgroup G} {t : G}
    (hE : CFSG.Open.IsElemAbelian p E) (hEodd : Odd (Nat.card E))
    (ht2 : orderOf t = 2) (htE : t ∈ Subgroup.normalizer (E : Set G))
    (hDle : D ≤ E) (hDmap : D.map (MulAut.conj t).toMonoidHom = D) :
    D = (D ⊓ (E ⊓ Subgroup.centralizer {t})) ⊔ (D ⊓ invertedSub E t hE) := by
  have htND : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hDmap
  have hCD : D ⊓ (E ⊓ Subgroup.centralizer {t}) = D ⊓ Subgroup.centralizer {t} := by
    rw [← inf_assoc, inf_eq_left.2 hDle]
  have hset : (D : Set G) = ((D ⊓ (E ⊓ Subgroup.centralizer {t}) : Subgroup G) : Set G) *
      ((D : Set G) ∩ CFSG.OddInversion.invertedSet E t) := by
    rw [hCD]
    exact (CFSG.OddInversion.odd_involution_product_decomposition hEodd ht2 htE).2.2 D hDle htND
      |>.2
  apply le_antisymm
  swap
  · exact sup_le inf_le_left inf_le_left
  intro x hx
  have hx' : x ∈ (D : Set G) := hx
  rw [hset] at hx'
  obtain ⟨c, hc, j, hj, hcj⟩ := Set.mem_mul.mp hx'
  rw [← hcj]
  exact (D ⊓ (E ⊓ Subgroup.centralizer {t}) ⊔ D ⊓ invertedSub E t hE).mul_mem
    (Subgroup.mem_sup_left ⟨hc.1, hc.2⟩)
    (Subgroup.mem_sup_right ⟨hj.1, hj.2⟩)

private theorem relIndex_mul_relIndex_eq_of_decomposition [Finite G] {p : ℕ} (_hp : p.Prime)
    {E C I D : Subgroup G} (hcomm : ∀ x ∈ C, ∀ y ∈ I, x * y = y * x)
    (hCI : C ⊓ I = ⊥) (_hsup : C ⊔ I = E)
    (hcardE : Nat.card E = Nat.card C * Nat.card I)
    (hdecomp : D = (D ⊓ C) ⊔ (D ⊓ I)) (hDle : D ≤ E) (hDrel : D.relIndex E = p) :
    (D ⊓ C).relIndex C * (D ⊓ I).relIndex I = p := by
  have hcomm' : ∀ x ∈ D ⊓ C, ∀ y ∈ D ⊓ I, x * y = y * x :=
    fun x hx y hy => hcomm x hx.2 y hy.2
  have hinf : (D ⊓ C) ⊓ (D ⊓ I) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    exact hCI ▸ ⟨hz.1.2, hz.2.2⟩
  have hDcard : Nat.card D = Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (D ⊓ C) (D ⊓ I)
      hcomm').1
    rw [hinf, Subgroup.card_bot, mul_one] at h
    calc Nat.card D = Nat.card ↥((D ⊓ C) ⊔ (D ⊓ I)) := by
          conv_lhs => rw [hdecomp]
      _ = Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) := h
  have hrelC : Nat.card C = Nat.card ↥(D ⊓ C) * (D ⊓ C).relIndex C := by
    have h := Subgroup.relIndex_mul_card (D ⊓ C) C
    rw [inf_assoc, inf_idem, mul_comm] at h
    exact h.symm
  have hrelI : Nat.card I = Nat.card ↥(D ⊓ I) * (D ⊓ I).relIndex I := by
    have h := Subgroup.relIndex_mul_card (D ⊓ I) I
    rw [inf_assoc, inf_idem, mul_comm] at h
    exact h.symm
  have hrelD : Nat.card E = Nat.card D * p := by
    have h := Subgroup.relIndex_mul_card D E
    rw [inf_eq_left.2 hDle, hDrel, mul_comm] at h
    exact h.symm
  have hkey : Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) *
      ((D ⊓ C).relIndex C * (D ⊓ I).relIndex I) =
      Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) * p := by
    calc Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) *
          ((D ⊓ C).relIndex C * (D ⊓ I).relIndex I)
        = (Nat.card ↥(D ⊓ C) * (D ⊓ C).relIndex C) *
            (Nat.card ↥(D ⊓ I) * (D ⊓ I).relIndex I) := by ring
      _ = Nat.card C * Nat.card I := by rw [← hrelC, ← hrelI]
      _ = Nat.card E := hcardE.symm
      _ = Nat.card D * p := hrelD
      _ = Nat.card ↥(D ⊓ C) * Nat.card ↥(D ⊓ I) * p := by rw [hDcard]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (Nat.card_pos (α := ↥(D ⊓ C))) (Nat.card_pos (α := ↥(D ⊓ I)))) hkey

private theorem fixedHyp_case [Finite G] {p : ℕ} (hp : p.Prime) {E C I D : Subgroup G}
    (hcomm : ∀ x ∈ C, ∀ y ∈ I, x * y = y * x)
    (hCI : C ⊓ I = ⊥) (hsup : C ⊔ I = E)
    (hcardE : Nat.card E = Nat.card C * Nat.card I)
    (hdecomp : D = (D ⊓ C) ⊔ (D ⊓ I)) (hDle : D ≤ E) (hDrel : D.relIndex E = p) :
    ((I ≤ D) ∧ D = (D ⊓ C) ⊔ I ∧ (D ⊓ C) ∈ hyperplanes p C) ∨
      ((¬ I ≤ D) ∧ D = C ⊔ (D ⊓ I) ∧ (D ⊓ I) ∈ hyperplanes p I) := by
  have hprod := relIndex_mul_relIndex_eq_of_decomposition hp hcomm hCI hsup hcardE hdecomp
    hDle hDrel
  rcases (Nat.dvd_prime hp).mp ⟨_, hprod.symm⟩ with hα1 | hαp
  · have hCD : C ≤ D := (Subgroup.relIndex_eq_one.mp hα1).trans inf_le_left
    have hβp : (D ⊓ I).relIndex I = p := by
      rw [hα1, one_mul] at hprod
      exact hprod
    have hIp : ¬ I ≤ D := by
      intro hID
      have hDE : D = E := le_antisymm hDle (hsup ▸ sup_le hCD hID)
      rw [hDE, Subgroup.relIndex_self] at hDrel
      exact hp.ne_one hDrel.symm
    refine Or.inr ⟨hIp, ?_, ⟨inf_le_right, hβp⟩⟩
    calc D = (D ⊓ C) ⊔ (D ⊓ I) := hdecomp
      _ = C ⊔ (D ⊓ I) := by rw [inf_eq_right.2 hCD]
  · have hβ1 : (D ⊓ I).relIndex I = 1 := by
      have h2 : p * (D ⊓ I).relIndex I = p := hαp ▸ hprod
      have h3 : p * (D ⊓ I).relIndex I = p * 1 := by rw [mul_one]; exact h2
      exact Nat.eq_of_mul_eq_mul_left hp.pos h3
    have hID : I ≤ D := (Subgroup.relIndex_eq_one.mp hβ1).trans inf_le_left
    refine Or.inl ⟨hID, ?_, ⟨inf_le_right, hαp⟩⟩
    calc D = (D ⊓ C) ⊔ (D ⊓ I) := hdecomp
      _ = (D ⊓ C) ⊔ I := by rw [inf_eq_right.2 hID]

theorem ncard_fixedHyp_le [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ (2 * f)) {t : G}
    (ht : t ^ 2 = 1) (htE : t ∈ normalizer (E : Set G))
    (hC : Nat.card ↥(E ⊓ centralizer {t}) = p ^ f) :
    (fixedHyp p E t).ncard ≤ 2 * ((p ^ f - 1) / (p - 1)) := by
  classical
  by_cases hf : f = 0
  · subst hf
    have hEbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E (by simpa using hcard)
    have hempty : fixedHyp p E t = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro D hD
      simp only [fixedHyp, Set.mem_setOf_eq] at hD
      obtain ⟨⟨hDle, hDrel⟩, -⟩ := hD
      have hDbot : D = ⊥ := le_antisymm (hEbot ▸ hDle) bot_le
      rw [hDbot, hEbot, Subgroup.relIndex_self] at hDrel
      exact hp.ne_one hDrel.symm
    rw [hempty]
    simp
  have hf0 : 0 < f := Nat.pos_of_ne_zero hf
  have hEodd : Odd (Nat.card E) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  let C : Subgroup G := E ⊓ Subgroup.centralizer {t}
  let I : Subgroup G := invertedSub E t hE
  have htne : t ≠ 1 := by
    intro ht1
    have hCE : C = E := by
      show E ⊓ Subgroup.centralizer {t} = E
      rw [ht1]
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    have hCf : Nat.card C = p ^ f := hC
    rw [hCE] at hCf
    have hpow : p ^ f = p ^ (2 * f) := hCf.symm.trans hcard
    have hfeq : f = 2 * f := Nat.pow_right_injective hp.two_le hpow
    omega
  have ht2 : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) htne
    · exact h2
  obtain ⟨hCI, hsup, hcardE, hcardI⟩ := fixed_inverted_facts hp hp2 hE hcard ht2 htE hC
  have hcomm : ∀ x ∈ C, ∀ y ∈ I, x * y = y * x := by
    intro x hx y hy
    exact congrArg (fun z : ↥E => (z : G))
      (hE.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, (mem_invertedSub.mp hy).1⟩)
  have hkey : ∀ D : Subgroup G, D ∈ fixedHyp p E t →
      ((I ≤ D) ∧ D = (D ⊓ C) ⊔ I ∧ D ⊓ C ∈ hyperplanes p C) ∨
        ((¬ I ≤ D) ∧ D = C ⊔ (D ⊓ I) ∧ D ⊓ I ∈ hyperplanes p I) := by
    intro D hD
    simp only [fixedHyp, Set.mem_setOf_eq] at hD
    obtain ⟨hDhyp, hDmap⟩ := hD
    have hDle : D ≤ E := hDhyp.1
    have hDrel : D.relIndex E = p := hDhyp.2
    have hdec := fixed_decomposition hE hEodd ht2 htE hDle hDmap
    exact fixedHyp_case hp hcomm hCI hsup hcardE hdec hDle hDrel
  let f' : fixedHyp p E t → hyperplanes p C ⊕ hyperplanes p I := fun D =>
    if h : I ≤ D.1 then
      Sum.inl ⟨D.1 ⊓ C, by
        rcases hkey D.1 D.2 with ⟨-, -, hmem⟩ | ⟨hnot, -⟩
        · exact hmem
        · exact absurd h hnot⟩
    else
      Sum.inr ⟨D.1 ⊓ I, by
        rcases hkey D.1 D.2 with ⟨hle, -⟩ | ⟨-, -, hmem⟩
        · exact absurd hle h
        · exact hmem⟩
  have hkey1 : ∀ D : Subgroup G, ∀ hD : D ∈ fixedHyp p E t, I ≤ D →
      D = (D ⊓ C) ⊔ I := by
    intro D hD h
    rcases hkey D hD with ⟨-, hdec, -⟩ | ⟨hnot, -⟩
    · exact hdec
    · exact absurd h hnot
  have hkey2 : ∀ D : Subgroup G, ∀ hD : D ∈ fixedHyp p E t, ¬ I ≤ D →
      D = C ⊔ (D ⊓ I) := by
    intro D hD h
    rcases hkey D hD with ⟨hle, -⟩ | ⟨-, hdec, -⟩
    · exact absurd hle h
    · exact hdec
  have hf_inj : Function.Injective f' := by
    intro D₁ D₂ heq
    by_cases h1 : I ≤ D₁.1
    · by_cases h2 : I ≤ D₂.1
      · simp only [f', dif_pos h1, dif_pos h2, Sum.inl.injEq, Subtype.ext_iff] at heq
        apply Subtype.ext
        rw [hkey1 D₁.1 D₁.2 h1, hkey1 D₂.1 D₂.2 h2, heq]
      · simp only [f', dif_pos h1, dif_neg h2] at heq
        exact (Sum.inl_ne_inr heq).elim
    · by_cases h2 : I ≤ D₂.1
      · simp only [f', dif_neg h1, dif_pos h2] at heq
        exact (Sum.inr_ne_inl heq).elim
      · simp only [f', dif_neg h1, dif_neg h2, Sum.inr.injEq, Subtype.ext_iff] at heq
        apply Subtype.ext
        rw [hkey2 D₁.1 D₁.2 h1, hkey2 D₂.1 D₂.2 h2, heq]
  have hle : Nat.card (fixedHyp p E t) ≤ Nat.card (hyperplanes p C ⊕ hyperplanes p I) :=
    Nat.card_le_card_of_injective f' hf_inj
  rw [Nat.card_sum] at hle
  have : Fact p.Prime := ⟨hp⟩
  have hcardHypC : Nat.card (hyperplanes p C) = ∑ i ∈ Finset.range f, p ^ i :=
    CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.card_hyperplanes
      (isElemAbelian_mono hE inf_le_left) hf0 hC
  have hcardHypI : Nat.card (hyperplanes p I) = ∑ i ∈ Finset.range f, p ^ i :=
    CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.card_hyperplanes
      (isElemAbelian_mono hE (invertedSub_le E t hE)) hf0 hcardI
  rw [hcardHypC, hcardHypI, Nat.geomSum_eq hp.two_le] at hle
  rw [← Nat.card_coe_set_eq]
  calc Nat.card (fixedHyp p E t) ≤ (p ^ f - 1) / (p - 1) + (p ^ f - 1) / (p - 1) := hle
    _ = 2 * ((p ^ f - 1) / (p - 1)) := by ring

theorem exists_fixedHyp_inverted [Finite G] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 0 < f) {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E)
    (hcard : Nat.card E = p ^ (2 * f)) {t : G} (ht : t ^ 2 = 1)
    (htE : t ∈ normalizer (E : Set G)) (hC : Nat.card ↥(E ⊓ centralizer {t}) = p ^ f) :
    ∃ D₀ ∈ fixedHyp p E t, ∃ X : Subgroup G, X ≤ E ∧ Nat.card X = p ∧ X ⊓ D₀ = ⊥ ∧
      ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEodd : Odd (Nat.card E) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  let C : Subgroup G := E ⊓ Subgroup.centralizer {t}
  let I : Subgroup G := invertedSub E t hE
  have htne : t ≠ 1 := by
    intro ht1
    have hCE : C = E := by
      show E ⊓ Subgroup.centralizer {t} = E
      rw [ht1]
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    have hCf : Nat.card C = p ^ f := hC
    rw [hCE] at hCf
    have hpow : p ^ f = p ^ (2 * f) := hCf.symm.trans hcard
    have hfeq : f = 2 * f := Nat.pow_right_injective hp.two_le hpow
    omega
  have ht2 : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) htne
    · exact h2
  obtain ⟨hCI, hsup, hcardE, hcardI⟩ := fixed_inverted_facts hp hp2 hE hcard ht2 htE hC
  have hIle : I ≤ E := invertedSub_le E t hE
  have hIelem : CFSG.Open.IsElemAbelian p I := isElemAbelian_mono hE hIle
  have hIinv : ∀ y ∈ I, t * y * t⁻¹ = y⁻¹ := fun y hy => (mem_invertedSub.mp hy).2
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hIbot : invertedSub E t hE = ⊥ := hbot
    have h1 : p ^ f = 1 := by rw [← hcardI, hIbot, Subgroup.card_bot]
    rcases (Nat.pow_eq_one.mp h1) with hp1 | hf1
    · exact hp.ne_one hp1
    · omega
  obtain ⟨⟨a, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  let X : Subgroup G := Subgroup.zpowers a
  have hXle : X ≤ I := Subgroup.zpowers_le.mpr haI
  have hXleE : X ≤ E := hXle.trans hIle
  have hXcard : Nat.card X = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE.2 a (hIle haI)) ha1'
  have hIE : CFSG.IsElementaryAbelian p ↥I :=
    { toIsMulCommutative := hIelem.1
      exponent_dvd_p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hIelem.2 x x.2) }
  obtain ⟨C', hcompl⟩ := CFSG.IsElementaryAbelian.exists_isCompl p ↥I (X.subgroupOf I)
  let DI : Subgroup G := C'.map I.subtype
  have hDIle : DI ≤ I := Subgroup.map_subtype_le C'
  have hXDI : X ⊓ DI = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxX, hxDI⟩ := hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxDI
    have hxc : c ∈ X.subgroupOf I := by
      rw [Subgroup.mem_subgroupOf]
      have hcx' : (c : G) = x := hcx
      rw [hcx']
      exact hxX
    have hmem : c ∈ X.subgroupOf I ⊓ C' := ⟨hxc, hc⟩
    rw [hcompl.1.eq_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, ← hcx, hmem]
    rfl
  have hXDI_sup : X ⊔ DI = I := by
    have h := hcompl.2.eq_top
    have hmap := congrArg (Subgroup.map I.subtype) h
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXle, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    exact hmap
  have hcommXI : ∀ x ∈ X, ∀ y ∈ DI, x * y = y * x := by
    intro x hx y hy
    exact congrArg (fun z : ↥E => (z : G))
      (hE.1.is_comm.comm ⟨x, hXleE hx⟩ ⟨y, hIle (hDIle hy)⟩)
  have hXIcard : Nat.card I = Nat.card X * Nat.card DI := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X DI hcommXI).1
    rw [hXDI_sup, hXDI, Subgroup.card_bot, mul_one] at h
    exact h
  have hDIcard : Nat.card I = p * Nat.card DI := by
    rw [hXIcard, hXcard]
  have hDIrel : DI.relIndex I = p := by
    have h := Subgroup.relIndex_mul_card DI I
    rw [inf_eq_left.2 hDIle, hDIcard] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥DI)) h
  let D0 : Subgroup G := C ⊔ DI
  have hD0le : D0 ≤ E := sup_le inf_le_left (hDIle.trans hIle)
  have hCcommDI : ∀ x ∈ C, ∀ y ∈ DI, x * y = y * x := by
    intro x hx y hy
    exact congrArg (fun z : ↥E => (z : G))
      (hE.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hIle (hDIle hy)⟩)
  have hCI_DI : C ⊓ DI = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hmem : x ∈ C ⊓ I := ⟨hx.1, hDIle hx.2⟩
    rw [hCI] at hmem
    exact hmem
  have hcardD0 : Nat.card D0 = Nat.card C * Nat.card DI := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C DI hCcommDI).1
    rw [hCI_DI, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardD0E : Nat.card E = p * Nat.card D0 := by
    rw [hcardE, hDIcard, hcardD0]
    ring
  have hD0rel : D0.relIndex E = p := by
    have h := Subgroup.relIndex_mul_card D0 E
    rw [inf_eq_left.2 hD0le, hcardD0E] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥D0)) h
  have hCfix : ∀ x ∈ C, t * x * t⁻¹ = x := by
    intro x hx
    have h : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [← h]
    group
  have hCmap : C.map (MulAut.conj t).toMonoidHom = C := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      show t * x * t⁻¹ ∈ C
      rw [hCfix x hx]
      exact hx
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (K := C)
        (MulAut.conj t).injective]
  have hDImap : DI.map (MulAut.conj t).toMonoidHom = DI := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      show t * y * t⁻¹ ∈ DI
      rw [hIinv y (hDIle hy)]
      exact DI.inv_mem hy
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (K := DI)
        (MulAut.conj t).injective]
  have hD0map : D0.map (MulAut.conj t).toMonoidHom = D0 := by
    show (C ⊔ DI).map (MulAut.conj t).toMonoidHom = C ⊔ DI
    rw [Subgroup.map_sup, hCmap, hDImap]
  have hD0mem : D0 ∈ fixedHyp p E t := ⟨⟨hD0le, hD0rel⟩, hD0map⟩
  have hXD0 : X ⊓ D0 = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxX, hxD0⟩ := hx
    have hsetD0 : ((C ⊔ DI : Subgroup G) : Set G) = (C : Set G) * (DI : Set G) :=
      (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C DI hCcommDI).2
    have hx' : x ∈ (C : Set G) * (DI : Set G) := by
      rw [← hsetD0]
      exact hxD0
    obtain ⟨c, hc, d, hd, hcd⟩ := Set.mem_mul.mp hx'
    have hxI : x ∈ I := hXle hxX
    have hcI : c ∈ I := by
      have hce : c = x * d⁻¹ := by rw [← hcd]; group
      rw [hce]
      exact I.mul_mem hxI (I.inv_mem (hDIle hd))
    have hcbot : c ∈ C ⊓ I := ⟨hc, hcI⟩
    rw [hCI, Subgroup.mem_bot] at hcbot
    have hdX : d ∈ X := by
      have hde : d = c⁻¹ * x := by rw [← hcd]; group
      rw [hde, hcbot, inv_one, one_mul]
      exact hxX
    have hdmem : d ∈ X ⊓ DI := ⟨hdX, hd⟩
    rw [hXDI, Subgroup.mem_bot] at hdmem
    rw [Subgroup.mem_bot, ← hcd, hcbot, hdmem, one_mul]
  refine ⟨D0, hD0mem, X, hXleE, hXcard, hXD0, ?_⟩
  intro x hx
  exact hIinv x (hXle hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
