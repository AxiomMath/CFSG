module

public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Tab
public import CFSG.RankThree.PartOne.F106.NoQD32NAOrb
public import Certificates.Certificate271034

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank

section Abelian

variable {K : Type} [Field K] [CharP K 2] {ω : Cube K} {hK : Nat.card K = (2 ^ 1) ^ 2}
  {c : U6SylowCert} [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))]

open scoped _root_.Classical in
theorem U6Tab.card_trZero_E0 (T : U6Tab ω hK c) (hna : c.NAFacts) :
    Nat.card {g : StatedProj (StatedSU 6 (2 ^ 1) K) //
      g ∈ u6E0 ω hK c ∧ g ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K) g} = 30 := by
  have h := card_set_eq_filter T.S (c.sel ω hK)
    (fun g => g ∈ u6E0 ω hK c ∧ g ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K) g) T.sel_inj T.exists_sel
    T.sel_mem
  have hset : {g : StatedProj (StatedSU 6 (2 ^ 1) K) //
      g ∈ u6E0 ω hK c ∧ g ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K) g} =
      {g : StatedProj (StatedSU 6 (2 ^ 1) K) //
        g ∈ T.S ∧ (g ∈ u6E0 ω hK c ∧ g ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K) g)} := by
    congr 1
    ext g
    constructor
    · intro hg
      exact ⟨T.E0_le hg.1, hg⟩
    · intro hg
      exact hg.2
  rw [hset, h]
  rw [card_filter_range_eq_length 729 _
    (fun i => decide ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) && decide (i ≠ 0) && (c.tab i).trB)]
  · exact hna.a0
  · intro i hi
    rw [T.sel_mem_E0 hi, sel_trZero_iff]
    have h1 : c.sel ω hK i ≠ 1 ↔ i ≠ 0 := by
      constructor
      · rintro h rfl
        exact h T.sel_zero
      · intro hne heq
        exact hne (T.sel_inj i hi 0 (by norm_num) (heq.trans T.sel_zero.symm))
    rw [h1]
    simp only [decide_eq_true_eq, Bool.and_eq_true, and_assoc]

theorem U6Tab.card_trZero_E0' (T : U6Tab ω hK c) (hna : c.NAFacts) :
    Nat.card {y : ↥(u6E0 ω hK c) //
      (y : StatedProj (StatedSU 6 (2 ^ 1) K)) ≠ 1 ∧
        trZeroP (StatedSU 6 (2 ^ 1) K) (y : StatedProj (StatedSU 6 (2 ^ 1) K))} = 30 := by
  rw [← T.card_trZero_E0 hna]
  refine Nat.card_congr ?_
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ u6E0 ω hK c)
    (fun g => g ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K) g))

end Abelian

section Main

open scoped _root_.Classical in
theorem u6_abelian_false
    {T : Type} [Group T] (hmod : StatedClassicalModel T .PSU 6 2 1)
    {E R : Subgroup T} (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) : False := by
  have hord : Nat.card T = CFSG.Open.ordTwistedA (6 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨ω⟩ := exists_cube (K := K) (by rw [hK]; norm_num)
  have hf : u6ThreeCert.Facts :=
    U6SylowCert.facts_of_check _ (Certificates.certificate271061 : U6ThreeRankCheck)
  have hna : u6ThreeCert.NAFacts :=
    U6SylowCert.NAFacts.of_naCheck _ (Certificates.certificate271034 : U6NACheck)
  have hG : Nat.card (StatedProj (StatedSU 6 (2 ^ 1) K)) = 9196830720 := by
    rw [← Nat.card_congr e.toEquiv, hord]
    unfold CFSG.Open.ordTwistedA
    decide +kernel
  have : Finite (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  let T0 : U6Tab ω hK u6ThreeCert := U6Tab.ofFacts hf
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  have h81 : 81 ≤ Nat.card E := by
    have := card_ge_pow_four_of_normalizer_qd32 Nat.prime_three (by norm_num) hE h.normalizes ψ
      hψs hψc
    simpa using this
  have hEcube : ∀ a ∈ E, a ^ 3 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE3 : IsPGroup 3 (E.map e.toMonoidHom) := fun y => by
    obtain ⟨a, ha, hay⟩ := y.2
    have h3 : (y : StatedProj (StatedSU 6 (2 ^ 1) K)) ^ 3 = 1 := by
      rw [← hay, ← map_pow, hEcube a ha, map_one]
    exact ⟨1, Subtype.ext h3⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow (p := 3) (k := 6) T0.S T0.card
    (by rw [hG]; norm_num) _ hE3
  have hEcard : Nat.card ↥((E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective e.injective]
  have hcomm1 := map_comm_of_comm e.toMonoidHom E hEcomm
  have hcube1 := map_pow_of_pow e.toMonoidHom E 3 hEcube
  have hcomm2 := map_comm_of_comm (MulAut.conj g).toMonoidHom _ hcomm1
  have hcube2 := map_pow_of_pow (MulAut.conj g).toMonoidHom _ 3 hcube1
  have hEeq : (E.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = u6E0 ω hK u6ThreeCert :=
    T0.eq_E0_of_elemAbelian hna hg hcomm2 hcube2 (by rw [hEcard]; exact h81)
  have hE81 : Nat.card E = 81 := by
    rw [← hEcard, hEeq]
    exact T0.card_E0 hna
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_conj e g E (u6E0 ω hK u6ThreeCert) hEeq
  let trz : T → Prop := fun x => trZeroP (StatedSU 6 (2 ^ 1) K) (e x)
  have hconj : ∀ n x : T, trz (n * x * n⁻¹) ↔ trz x := by
    intro n x
    simp only [trz, map_mul, map_inv]
    exact trZeroP_conj _ (e n) (e x)
  have : Fintype ↥E := Fintype.ofFinite _
  let A : Finset ↥E := Finset.univ.filter fun x => (x : T) ≠ 1 ∧ trz (x : T)
  have hAcard : A.card = 30 := by
    have h1 : A.card = Nat.card {x : ↥E // (x : T) ≠ 1 ∧ trz (x : T)} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, ← T0.card_trZero_E0' hna]
    refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun x => ?_)
    have hx := hφ x
    change (x : T) ≠ 1 ∧ trz (x : T) ↔ ((φ x : ↥(u6E0 ω hK u6ThreeCert)) :
      StatedProj (StatedSU 6 (2 ^ 1) K)) ≠ 1 ∧ trZeroP (StatedSU 6 (2 ^ 1) K)
        ((φ x : ↥(u6E0 ω hK u6ThreeCert)) : StatedProj (StatedSU 6 (2 ^ 1) K))
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, (trZeroP_conj _ g (e x)).mpr h2⟩
      have : e x = 1 := by simpa using h
      exact e.injective (by rw [this, map_one])
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 ?_, (trZeroP_conj _ g (e x)).mp h2⟩
      rw [h, map_one]
      simp
  obtain ⟨f, hf⟩ := exists_qd32_embedding_normalizerRange h.normalizes ψ hψs hψc
  let f' : GroupTheory.QD32 →* MulAut ↥E := E.normalizerMonoidHom.range.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  have hinv : ∀ q : GroupTheory.QD32, ∀ x ∈ A, f' q x ∈ A := by
    intro q x hx
    obtain ⟨n, hn⟩ := (f q).2
    have hcoe : ((f' q x : ↥E) : T) = (n : T) * (x : T) * (n : T)⁻¹ := by
      have : f' q = E.normalizerMonoidHom n := hn.symm
      rw [this]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe E n x
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcoe]
    refine ⟨fun h1 => hx.1 ?_, (hconj _ _).mpr hx.2⟩
    have : (x : T) = (n : T)⁻¹ * 1 * (n : T) := by
      rw [← h1]
      group
    simpa using this
  have h16 := qd32_dvd_card_of_invariant_nonzero Nat.prime_three (by norm_num)
    (fun x y => Subtype.ext (hEcomm x x.2 y y.2)) (fun x => Subtype.ext (hEcube x x.2)) f' hf'
    (by rw [hE81]; norm_num) A (by simp [A]) hinv
  rw [hAcard] at h16
  omega

end Main

end CFSG.RankThree.PartOne.F106
