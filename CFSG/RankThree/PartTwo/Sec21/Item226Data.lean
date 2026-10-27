module

public import Certificates.Certificate12950

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix

theorem reflCensus_0 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 0, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.1

theorem reflCensus_1 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.1

theorem reflCensus_2 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.1

theorem reflCensus_3 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.1

theorem reflCensus_4 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.1

theorem reflCensus_5 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.1

theorem reflCensus_6 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.1

theorem reflCensus_7 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.1

theorem reflCensus_8 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.1

theorem reflCensus_9 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_10 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_11 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_12 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_13 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_14 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_15 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_16 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_17 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_18 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_19 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_20 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_21 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_22 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_23 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_24 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_25 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_26 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_27 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_28 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_29 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_30 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_31 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_32 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_33 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_34 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_35 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_36 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_37 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 0] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_38 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 1] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_39 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 2] ![b0, b1, b2, b3]) :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCensus_normVec : ∀ k : Fin 40, ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec (normVec k) ![b0, b1, b2, b3]) := by
  intro k
  fin_cases k
  exacts [reflCensus_0, reflCensus_1, reflCensus_2, reflCensus_3, reflCensus_4, reflCensus_5,
    reflCensus_6, reflCensus_7, reflCensus_8, reflCensus_9, reflCensus_10, reflCensus_11,
    reflCensus_12, reflCensus_13, reflCensus_14, reflCensus_15, reflCensus_16, reflCensus_17,
    reflCensus_18, reflCensus_19, reflCensus_20, reflCensus_21, reflCensus_22, reflCensus_23,
    reflCensus_24, reflCensus_25, reflCensus_26, reflCensus_27, reflCensus_28, reflCensus_29,
    reflCensus_30, reflCensus_31, reflCensus_32, reflCensus_33, reflCensus_34, reflCensus_35,
    reflCensus_36, reflCensus_37, reflCensus_38, reflCensus_39]

private theorem normVec_exists :
    ∀ a0 a1 a2 a3 : ZMod 3, ![a0, a1, a2, a3] ≠ 0 →
    ∃ k : Fin 40, ∃ s : ZMod 3, ![a0, a1, a2, a3] = s • normVec k :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem reflCheck_of_rankOne (a b : Fin 4 → ZMod 3) :
    ReflCheck (1 + vecMulVec a b) := by
  by_cases ha : a = 0
  · intro _ hne
    exact absurd (by rw [ha, zero_vecMulVec, add_zero]) hne
  · have hexists : ∀ a0 a1 a2 a3 : ZMod 3, ![a0, a1, a2, a3] ≠ 0 →
        ∃ k : Fin 40, ∃ s : ZMod 3, ![a0, a1, a2, a3] = s • normVec k :=
      normVec_exists
    have hae : a = ![a 0, a 1, a 2, a 3] := by
      ext i
      fin_cases i <;> rfl
    obtain ⟨k, s, hk⟩ := hexists (a 0) (a 1) (a 2) (a 3) (hae ▸ ha)
    have hsm : vecMulVec (s • normVec k) b = vecMulVec (normVec k) (s • b) := by
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hae, hk, hsm]
    have hbe : s • b = ![(s • b) 0, (s • b) 1, (s • b) 2, (s • b) 3] := by
      ext i
      fin_cases i <;> rfl
    rw [hbe]
    exact reflCensus_normVec k _ _ _ _

theorem checkDeriv_sound (𝒟 : Set Mat4) (hcl : ∀ M ∈ 𝒟, ∀ N ∈ 𝒟, M * N * M ∈ 𝒟) :
    ∀ (cert : List (ℕ × ℕ × ℕ)) (S : List ℕ), (∀ i ∈ S, reflAt i ∈ 𝒟) →
      checkDeriv S cert = true → ∀ i ∈ S ++ cert.map Prod.fst, reflAt i ∈ 𝒟 := by
  intro cert
  induction cert with
  | nil =>
    intro S hS _ i hi
    simp only [List.map_nil, List.append_nil] at hi
    exact hS i hi
  | cons p rest ih =>
    obtain ⟨m, a, b⟩ := p
    intro S hS hc i hi
    simp only [checkDeriv, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨ha, hb⟩, hm⟩, hrest⟩ := hc
    have hmD : reflAt m ∈ 𝒟 := hm ▸ hcl _ (hS a ha) _ (hS b hb)
    have hS' : ∀ j ∈ m :: S, reflAt j ∈ 𝒟 := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hmD
      · exact hS j hj
    have key := ih (m :: S) hS' hrest
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hi
    rcases hi with hi | rfl | hi
    · exact hS i hi
    · exact hmD
    · exact key i (List.mem_append_right _ hi)

theorem refl_types : ∀ c ∈ List.range' 6 39,
    c ∈ tripleTable.map Prod.fst ∨ c ∈ s5aSeeds ∨ c ∈ s5bSeeds ∨ c ∈ g648aSeeds ∨
      c ∈ g648bSeeds :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tripleTable_spec :
    ∀ p ∈ tripleTable, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 < 6 ∧
    p.2.2 < 6 :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_cert :
    ∀ c ∈ s5aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ s5aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_cert :
    ∀ c ∈ s5bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ s5bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_cert :
    ∀ c ∈ g648aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ g648aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_cert :
    ∀ c ∈ g648bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ g648bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem g648a_max_0 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_max_1 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_max_2 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_max_3 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_max_4 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648a_max :
    ∀ i ∈ List.range 45, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  intro i hi
  have hi' : i < 45 := List.mem_range.mp hi
  by_cases h0 : i < 9
  · exact g648a_max_0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h1 : i < 18
  · exact g648a_max_1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 27
  · exact g648a_max_2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h3 : i < 36
  · exact g648a_max_3 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact g648a_max_4 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem g648b_max_0 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_max_1 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_max_2 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_max_3 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_max_4 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_max :
    ∀ i ∈ List.range 45, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  intro i hi
  have hi' : i < 45 := List.mem_range.mp hi
  by_cases h0 : i < 9
  · exact g648b_max_0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h1 : i < 18
  · exact g648b_max_1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 27
  · exact g648b_max_2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h3 : i < 36
  · exact g648b_max_3 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact g648b_max_4 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem g648a_centers :
    ∀ j ∈ g648aL, ∀ k : Fin 4, (reflAt j - 1) 0 k = 0 :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem g648b_fix :
    ∀ j ∈ g648bL, ∀ k : Fin 4, reflAt j k 0 = if k = 0 then 1 else 0 :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5aExt_spec :
    ∀ p ∈ s5aExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5aL ∧ p.2.2 ∈ s5aL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max_0 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max_1 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max_2 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max_3 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max_4 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5a_max : ∀ i ∈ List.range 45, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  intro i hi
  have hi' : i < 45 := List.mem_range.mp hi
  by_cases h0 : i < 9
  · exact s5a_max_0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h1 : i < 18
  · exact s5a_max_1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 27
  · exact s5a_max_2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h3 : i < 36
  · exact s5a_max_3 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact s5a_max_4 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem s5bExt_spec :
    ∀ p ∈ s5bExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5bL ∧ p.2.2 ∈ s5bL :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max_0 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max_1 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max_2 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max_3 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max_4 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5b_max : ∀ i ∈ List.range 45, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  intro i hi
  have hi' : i < 45 := List.mem_range.mp hi
  by_cases h0 : i < 9
  · exact s5b_max_0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h1 : i < 18
  · exact s5b_max_1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 27
  · exact s5b_max_2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h3 : i < 36
  · exact s5b_max_3 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact s5b_max_4 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)


theorem s5aChain_spec :
    reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
    reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
    reflAt 5 * reflAt 43 * reflAt 5 = reflAt 43 * reflAt 5 * reflAt 43 ∧
    CommAt 0 5 ∧ CommAt 0 43 ∧ CommAt 1 43 ∧ reflAt 0 ≠ reflAt 1 :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5aChain_gen : checkDeriv s5aChain s5aChainCert = true ∧
    ∀ i ∈ s5aL, i ∈ s5aChain ++ s5aChainCert.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5bChain_spec :
    reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
    reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
    reflAt 5 * reflAt 38 * reflAt 5 = reflAt 38 * reflAt 5 * reflAt 38 ∧
    CommAt 0 5 ∧ CommAt 0 38 ∧ CommAt 1 38 ∧ reflAt 0 ≠ reflAt 1 :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s5bChain_gen : checkDeriv s5bChain s5bChainCert = true ∧
    ∀ i ∈ s5bL, i ∈ s5bChain ++ s5bChainCert.map Prod.fst :=
  Certificates.certificate12950.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.RankThree.PartTwo.Sec21
