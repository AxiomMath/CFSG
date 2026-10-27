module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffProof

public section

namespace CFSG.Quasithin.B42U33

open CFSG.Open CFSG.Quasithin H13 H13.Orbit
open scoped Pointwise

theorem sE8_fixQ_le : ∀ e < 8,
    (o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length
      ≤ 8 := by
  decide +kernel

theorem offender_exact_sylow {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 64 ≤ (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2))))) :
    (idx B).card = 8 ∧ Nat.card (fixV (B.map (g2QAct (ZMod 2)))) = 8 := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length := fun i hi => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [Bool.and_eq_true]
    exact ⟨hc.1, hc.2 i hi⟩
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && (fixQB (sM i) c && fixQB (sM j) c)).length :=
    fun i hi j hj => by
      rw [hC]
      refine length_filter_le fun c hc => ?_
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨hc.1, hc.2 i hi, hc.2 j hj⟩
  have hsingle : ∀ i ∈ idx B, i ≠ 0 →
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length ≤ 16 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).2]
    · rw [(sOuter_fix i h).2]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn])) hB1
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2QAct (ZMod 2)))) < 16 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).2
        · have := (hCi j hj).trans_eq (sOuter_fix j h').2
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).2
        omega
    omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
        o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
      refine List.filter_congr fun c _ => ?_
      congr 1
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    have hle := sE8_fixQ_le e he
    rw [← hfilter, ← hC] at hle
    rw [hcard8] at hff ⊢
    exact ⟨rfl, by omega⟩

theorem offender_exact {B : Subgroup (MulAut ModQ)} (hB : B ≤ (g2QAct (ZMod 2)).range)
    (hne : B ≠ ⊥) (hea : IsElemAbelian2 B)
    (hff : Nat.card ModQ ≤ Nat.card B * Nat.card (fixV B)) :
    Nat.card B = 8 ∧ Nat.card (fixV B) = 8 := by
  set ρ := g2QAct (ZMod 2) with hρdef
  have hρ : Function.Injective ρ := g2QAct_injective
  set B₀ := B.comap ρ with hB₀def
  have hB₀ : B₀.map ρ = B := Subgroup.map_comap_eq_self hB
  have hc : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a := fun a ha b hb =>
    hρ (by rw [map_mul, map_mul]; exact hea.1 _ ha _ hb)
  have h2 : ∀ b ∈ B₀, b ^ 2 = 1 := fun b hb => hρ (by rw [map_pow, map_one]; exact hea.2 _ hb)
  have hp : IsPGroup 2 ↥B₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (h2 g.1 g.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set c := (MulAut.conj g).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  set B₁ := B₀.map c with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj g • b ∈ MulAut.conj g • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [← hB₀, (Subgroup.map_eq_bot_iff_of_injective _ hcinj).1 h, Subgroup.map_bot]
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, h2 b hb, map_one]
  have hmap : B₁.map ρ = B.map (MulAut.congr (ρ g)).toMonoidHom := by
    rw [← hB₀, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun b => ?_
    change ρ (g * b * g⁻¹) = MulAut.congr (ρ g) (ρ b)
    rw [congr_eq_conj, map_mul, map_mul, map_inv]
  have hcardB : Nat.card B₁ = Nat.card B := by
    rw [hB₁def, Subgroup.card_map_of_injective hcinj, ← hB₀, Subgroup.card_map_of_injective hρ]
  have hfix : Nat.card (fixV (B₁.map ρ)) = Nat.card (fixV B) := by
    rw [hmap, fixV_map_congr,
      Subgroup.card_map_of_injective (f := (ρ g).toMonoidHom) (ρ g).injective]
  have h := offender_exact_sylow hB₁S hB₁ne hB₁c hB₁2
    (by rw [← card_eq_idx hB₁S, hcardB, hfix, ← card_ModQ]; exact hff)
  rw [← card_eq_idx hB₁S, hcardB, hfix] at h
  exact h

theorem offender_facts_of_equiv {V : Type} [CommGroup V] [Finite V] (e : V ≃* ModQ)
    {X : Subgroup (MulAut V)} (hX : ∀ x ∈ X, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender X B) :
    Nat.card B = 8 ∧ Nat.card (fixV B) = 8 := by
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  obtain ⟨hBX, hB1, hBe, hbest⟩ := hB
  have hle : B.map (MulAut.congr e).toMonoidHom ≤ (g2QAct (ZMod 2)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hX b (hBX hb)
  have hne : B.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hcardB : Nat.card (B.map (MulAut.congr e).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective hφinj
  have hfix : Nat.card (fixV (B.map (MulAut.congr e).toMonoidHom)) = Nat.card (fixV B) := by
    rw [fixV_map_congr, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hff : Nat.card ModQ ≤ Nat.card (B.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixV (B.map (MulAut.congr e).toMonoidHom)) := by
    have h0 := hbest ⊥ bot_le
    rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0
    rw [hcardB, hfix, ← Nat.card_congr e.toEquiv]
    exact h0
  have h := offender_exact hle hne (isElemAbelian2_map_congr e hBe) hff
  rwa [hcardB, hfix] at h

end CFSG.Quasithin.B42U33
