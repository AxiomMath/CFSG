module

public import CFSG.LocalAnalysis.WeakClosure81.W172Class2Cl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def W172Lines (d : Γ) (Y : Subgroup Γ) : Set (Subgroup Γ) :=
  {L | ∃ y ∈ W172Inv d Y, y ≠ 1 ∧ L = Subgroup.zpowers y}

private lemma w172_inv_pow {d : Γ} {Y : Subgroup Γ} {y : Γ} (hy : y ∈ W172Inv d Y) (k : ℕ) :
    y ^ k ∈ W172Inv d Y :=
  ⟨Y.pow_mem hy.1 k, by rw [← conj_pow, hy.2, inv_pow]⟩

private lemma w172_inv_inv {d : Γ} {Y : Subgroup Γ} {y : Γ} (hy : y ∈ W172Inv d Y) :
    y⁻¹ ∈ W172Inv d Y :=
  ⟨Y.inv_mem hy.1, by rw [← conj_inv, hy.2]⟩

private lemma w172_inv_zpow {d : Γ} {Y : Subgroup Γ} {y : Γ} (hy : y ∈ W172Inv d Y) (k : ℤ) :
    y ^ k ∈ W172Inv d Y := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa using w172_inv_pow hy n
  · simpa using w172_inv_inv (w172_inv_pow hy n)

private lemma w172_zpowers_subset_inv {d : Γ} {Y : Subgroup Γ} {y : Γ} (hy : y ∈ W172Inv d Y) :
    (Subgroup.zpowers y : Set Γ) ⊆ W172Inv d Y := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact w172_inv_zpow hy k

private noncomputable def w172InvQuotEquiv {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) :
    ↥(W172Inv d Y) ≃ (↥Y ⧸ (⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y) :=
  Equiv.ofBijective (fun z : ↥(W172Inv d Y) => QuotientGroup.mk (⟨z.1, z.2.1⟩ : Y)) (by
    constructor
    · intro z z' hzz'
      have hmem : (⟨z.1, z.2.1⟩ : Y)⁻¹ * (⟨z'.1, z'.2.1⟩ : Y) ∈
          (⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y := QuotientGroup.eq.1 hzz'
      have hmem' : z.1⁻¹ * z'.1 ∈ (⁅Y, Y⁆ : Subgroup Γ) := Subgroup.mem_subgroupOf.1 hmem
      obtain ⟨w, -, huniq⟩ := w172_minInv_transversal h z'.1 z'.2.1
      have hz : z.1 = w := huniq z.1 ⟨z.2, hmem'⟩
      have hz' : z'.1 = w := huniq z'.1 ⟨z'.2, by simp⟩
      exact Subtype.ext (hz.trans hz'.symm)
    · intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨z, hz, -⟩ := w172_minInv_transversal h y.1 y.2
      refine ⟨⟨z, hz.1⟩, ?_⟩
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.2 hz.2)

private lemma w172_inv_natCard {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) {a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup Γ)) :
    Nat.card (W172Inv d Y) = p ^ a := by
  classical
  have hY'le : (⁅Y, Y⁆ : Subgroup Γ) ≤ Y := by
    simpa using Subgroup.commutator_le_sup (H₁ := Y) (H₂ := Y)
  have hcardY' : Nat.card ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y) =
      Nat.card (⁅Y, Y⁆ : Subgroup Γ) := by
    have h := Subgroup.card_subtype Y ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY'le] at h
    exact h.symm
  have hindex : ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y).index = p ^ a := by
    have hmul := Subgroup.card_mul_index ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y)
    rw [hcardY', hcard, mul_comm (p ^ a) (Nat.card (⁅Y, Y⁆ : Subgroup Γ))] at hmul
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(⁅Y, Y⁆ : Subgroup Γ))) hmul
  calc Nat.card (W172Inv d Y)
      = Nat.card (↥Y ⧸ (⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y) :=
        Nat.card_congr (w172InvQuotEquiv h)
    _ = ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y).index :=
        (Subgroup.index_eq_card ((⁅Y, Y⁆ : Subgroup Γ).subgroupOf Y)).symm
    _ = p ^ a := hindex

private lemma w172_zpowers_eq_of_mem {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) {y₀ x : Γ} (hy₀ : y₀ ∈ W172Inv d Y) (hy₀1 : y₀ ≠ 1)
    (hx : x ∈ Subgroup.zpowers y₀) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers y₀ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hy₀p : orderOf y₀ = p := orderOf_eq_prime (w172_minInv_exp h y₀ hy₀.1) hy₀1
  have hxp : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      rw [← hy₀p]
      exact orderOf_dvd_of_mem_zpowers hx
    rcases (Nat.dvd_prime h.prime).1 hdvd with h1 | hp
    · exact absurd (orderOf_eq_one_iff.1 h1) hx1
    · exact hp
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) ?_
  simp [Nat.card_zpowers, hxp, hy₀p]

private lemma w172_mem_of_zpowers_eq {z w : Γ}
    (h : Subgroup.zpowers z = Subgroup.zpowers w) (hz : z ∈ Subgroup.zpowers z) :
    z ∈ Subgroup.zpowers w := by
  rw [← h]
  exact hz

private lemma w172_fiber_natCard {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) {y₀ : Γ} (hy₀ : y₀ ∈ W172Inv d Y) (hy₀1 : y₀ ≠ 1) :
    Nat.card {a : {y : Γ // y ∈ W172Inv d Y ∧ y ≠ 1} //
        Subgroup.zpowers a.1 = Subgroup.zpowers y₀} = p - 1 := by
  classical
  have heq : {a : {y : Γ // y ∈ W172Inv d Y ∧ y ≠ 1} //
        Subgroup.zpowers a.1 = Subgroup.zpowers y₀} ≃
      ↥({x : Γ | x ∈ Subgroup.zpowers y₀ ∧ x ≠ 1} : Set Γ) :=
    { toFun := fun a =>
        ⟨a.1.1, w172_mem_of_zpowers_eq a.2 (Subgroup.mem_zpowers a.1.1), a.1.2.2⟩
      invFun := fun x =>
        ⟨⟨x.1, w172_zpowers_subset_inv hy₀ x.2.1, x.2.2⟩,
          w172_zpowers_eq_of_mem h hy₀ hy₀1 x.2.1 x.2.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  rw [Nat.card_congr heq]
  simp only [Nat.card_coe_set_eq]
  have hset : {x : Γ | x ∈ Subgroup.zpowers y₀ ∧ x ≠ 1} =
      (Subgroup.zpowers y₀ : Set Γ) \ {1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    tauto
  rw [hset, Set.ncard_sdiff' (s := {1}) (t := (Subgroup.zpowers y₀ : Set Γ))
      (Set.singleton_subset_iff.mpr (Subgroup.one_mem _)) (Set.toFinite _),
      Set.ncard_singleton]
  rw [show (Subgroup.zpowers y₀ : Set Γ).ncard = p by
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hzp : (Subgroup.zpowers y₀ : Set Γ).ncard = Nat.card (Subgroup.zpowers y₀) :=
      (Nat.card_coe_set_eq (s := (Subgroup.zpowers y₀ : Set Γ))).symm
    rw [hzp, Nat.card_zpowers]
    exact orderOf_eq_prime (w172_minInv_exp h y₀ hy₀.1) hy₀1]

private lemma w172_inv_ne_one_natCard {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) :
    Nat.card {y : Γ // y ∈ W172Inv d Y ∧ y ≠ 1} =
      (p - 1) * Nat.card (W172Lines d Y) := by
  classical
  let A : Set Γ := {y | y ∈ W172Inv d Y ∧ y ≠ 1}
  let B : Set (Subgroup Γ) := W172Lines d Y
  let f : ↥A → ↥B := fun a => ⟨Subgroup.zpowers a.1, ⟨a.1, a.2.1, a.2.2, rfl⟩⟩
  have hfiber : ∀ b : ↥B, Nat.card {a : ↥A // f a = b} = p - 1 := by
    intro b
    obtain ⟨y₀, hy₀, hy₀1, hb⟩ := b.2
    have hsub : ∀ a : ↥A, f a = b ↔ Subgroup.zpowers a.1 = Subgroup.zpowers y₀ := by
      intro a
      rw [Subtype.ext_iff]
      exact ⟨fun hh => hh.trans hb, fun hh => hh.trans hb.symm⟩
    have hcongr : Nat.card {a : ↥A // f a = b} =
        Nat.card {a : ↥A // Subgroup.zpowers a.1 = Subgroup.zpowers y₀} :=
      Nat.card_congr
        { toFun := fun a => ⟨a.1, (hsub a.1).1 a.2⟩
          invFun := fun a => ⟨a.1, (hsub a.1).2 a.2⟩
          left_inv := fun a => Subtype.ext rfl
          right_inv := fun a => Subtype.ext rfl }
    rw [hcongr]
    exact w172_fiber_natCard h hy₀ hy₀1
  have hsigma : Nat.card ↥A = (p - 1) * Nat.card ↥B := by
    haveI : Fintype ↥B := Fintype.ofFinite _
    calc Nat.card ↥A
        = Nat.card (Σ b : ↥B, {a : ↥A // f a = b}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ b : ↥B, Nat.card {a : ↥A // f a = b} := Nat.card_sigma
      _ = ∑ _b : ↥B, (p - 1) := Finset.sum_congr rfl (fun b _ => hfiber b)
      _ = Nat.card ↥B * (p - 1) := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
      _ = (p - 1) * Nat.card ↥B := mul_comm _ _
  exact hsigma

theorem w172_card_lines {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) {a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup Γ)) :
    Nat.card (W172Lines d Y) = ∑ i ∈ Finset.range a, p ^ i := by
  classical
  have hI : Nat.card (W172Inv d Y) = p ^ a := w172_inv_natCard h hcard
  have hA : Nat.card {y : Γ // y ∈ W172Inv d Y ∧ y ≠ 1} = p ^ a - 1 := by
    change Nat.card ↥({y : Γ | y ∈ W172Inv d Y ∧ y ≠ 1} : Set Γ) = p ^ a - 1
    have hset : {y : Γ | y ∈ W172Inv d Y ∧ y ≠ 1} = W172Inv d Y \ {1} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    rw [hset, Nat.card_coe_set_eq,
      Set.ncard_sdiff' (s := {1}) (t := W172Inv d Y)
        (Set.singleton_subset_iff.mpr (by simp [W172Inv])) (Set.toFinite _),
      Set.ncard_singleton, ← Nat.card_coe_set_eq, hI]
  have hcount : (p - 1) * Nat.card (W172Lines d Y) = p ^ a - 1 := by
    rw [← w172_inv_ne_one_natCard h]
    exact hA
  have hgeom : (p - 1) * (∑ i ∈ Finset.range a, p ^ i) = p ^ a - 1 := by
    rw [mul_comm]
    exact geom_sum_mul_of_one_le h.prime.one_le a
  have hpos : 0 < p - 1 := by
    have := h.prime.two_le
    omega
  exact Nat.mul_left_cancel hpos (hcount.trans hgeom.symm)

@[instance_reducible]
private noncomputable def w172LinesSMul {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : SMul ↥S ↥(W172Lines d Y) where
  smul s L :=
    ⟨(L.1).map (MulAut.conj s.1), by
      obtain ⟨y, hy, hy1, hL⟩ := L.2
      refine ⟨s.1 * y * s.1⁻¹, ⟨h.s_mem s.1 s.2 y hy.1, ?_⟩, ?_, ?_⟩
      · have hcomm : d * s.1 = s.1 * d := (h.s_comm s.1 s.2).symm
        have hinv : s.1⁻¹ * d⁻¹ = d⁻¹ * s.1⁻¹ := by
          rw [← mul_inv_rev, ← h.s_comm s.1 s.2, mul_inv_rev]
        calc d * (s.1 * y * s.1⁻¹) * d⁻¹
            = (d * s.1) * y * (s.1⁻¹ * d⁻¹) := by group
          _ = (s.1 * d) * y * (s.1⁻¹ * d⁻¹) := by rw [hcomm]
          _ = s.1 * (d * y * d⁻¹) * s.1⁻¹ := by rw [hinv]; group
          _ = s.1 * y⁻¹ * s.1⁻¹ := by rw [hy.2]
          _ = (s.1 * y * s.1⁻¹)⁻¹ := by group
      · intro hh
        exact hy1 ((MulAut.conj s.1).injective (by simpa [MulAut.conj_apply] using hh))
      · rw [hL, MonoidHom.map_zpowers]
        change Subgroup.zpowers ((MulAut.conj s.1) y) = Subgroup.zpowers (s.1 * y * s.1⁻¹)
        rw [MulAut.conj_apply]⟩

@[instance_reducible]
private noncomputable def w172LinesMulAction {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : MulAction ↥S ↥(W172Lines d Y) where
  toSMul := w172LinesSMul h
  one_smul L := by
    apply Subtype.ext
    change (L.1).map (MulAut.conj ((1 : ↥S) : Γ)).toMonoidHom = L.1
    have h1 : MulAut.conj ((1 : ↥S) : Γ) = 1 := by simp
    rw [h1]
    exact Subgroup.map_id L.1
  mul_smul s t L := by
    apply Subtype.ext
    change (L.1).map (MulAut.conj (((s * t : ↥S) : Γ))).toMonoidHom =
      ((L.1).map (MulAut.conj (t : Γ)).toMonoidHom).map (MulAut.conj (s : Γ)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    change MulAut.conj ((s : Γ) * (t : Γ)) x =
      MulAut.conj (s : Γ) (MulAut.conj (t : Γ) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group

theorem w172_two_pow_dvd_card_lines {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) (hS : IsPGroup 2 S) {c : ℕ}
    (horb : ∀ y ∈ W172Inv d Y, y ≠ 1 →
      2 ^ c ≤ (Subgroup.normalizer (Subgroup.zpowers y : Set Γ)).relIndex S) :
    2 ^ c ∣ Nat.card (W172Lines d Y) := by
  classical
  letI : MulAction ↥S ↥(W172Lines d Y) := w172LinesMulAction h
  haveI : IsPGroup 2 ↥S := hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horbit : ∀ L : ↥(W172Lines d Y),
      Nat.card (MulAction.orbit ↥S L) =
        (Subgroup.normalizer (L.1 : Set Γ)).relIndex S := by
    intro L
    have hstab : MulAction.stabilizer ↥S L =
        (S ⊓ Subgroup.normalizer (L.1 : Set Γ)).subgroupOf S := by
      ext s
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · intro hs
        refine ⟨s.2, ?_⟩
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change (L.1).map (MulAut.conj (s : Γ)) = L.1
        have hsm := congrArg Subtype.val hs
        change (L.1).map (MulAut.conj (s : Γ)) = L.1 at hsm
        exact hsm
      · rintro ⟨-, hs⟩
        rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hs
        apply Subtype.ext
        change (L.1).map (MulAut.conj (s : Γ)) = L.1
        exact hs
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hstab,
      Subgroup.inf_subgroupOf_left]
    rfl
  refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.dvd_card_of_orbit_dvd
    (K := ↥S) (Ω := ↥(W172Lines d Y)) (2 ^ c) ?_
  intro L
  obtain ⟨y, hy, hy1, hL⟩ := L.2
  have hle : 2 ^ c ≤ Nat.card (MulAction.orbit ↥S L) := by
    rw [horbit L, hL]
    exact horb y hy hy1
  obtain ⟨n, hn⟩ := IsPGroup.card_orbit (p := 2) (G := ↥S) (a := L) hS
  rw [hn]
  exact Nat.pow_dvd_pow 2
    ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by rwa [hn] at hle))

theorem w172_two_pow_dvd_geom_sum {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) (hS : IsPGroup 2 S) {c a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup Γ))
    (horb : ∀ y ∈ W172Inv d Y, y ≠ 1 →
      2 ^ c ≤ (Subgroup.normalizer (Subgroup.zpowers y : Set Γ)).relIndex S) :
    2 ^ c ∣ ∑ i ∈ Finset.range a, p ^ i := by
  rw [← w172_card_lines h hcard]
  exact w172_two_pow_dvd_card_lines h hS horb

end CFSG.LocalAnalysis.WeakClosure81

end
