module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51bK
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51bT
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Line.adj_add_two (ℓ : Line Γ) (i : ℤ) : Γ.Adj (ℓ.vert (i + 1)) (ℓ.vert (i + 2)) := by
  have := ℓ.adj (i + 1)
  rwa [show i + 1 + 1 = i + 2 by omega] at this

theorem fan51b (F : FanTree Γ G) (h36 : Fan36 F) : Fan51b F := by
  intro h40 ℓ a n hn hs hexc
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have halt : ∀ i : ℤ, valence Γ (ℓ.vert i) ≠ valence Γ (ℓ.vert (i + 1)) := fun i =>
    F.alternating _ _ (ℓ.adj i)
  have hb : a + ((n - 1 : ℕ) : ℤ) = a + n - 1 := by omega
  rw [hb]
  set L : Subgroup G :=
    Subgroup.closure ((nbrStab Γ G (ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert (a + n))) with hL
  have hKa : ∀ g ∈ nbrStab Γ G (ℓ.vert a), g ∈ L := fun g hg =>
    Subgroup.subset_closure (Or.inl hg)
  have hKn : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + n)), g ∈ L := fun g hg =>
    Subgroup.subset_closure (Or.inr hg)
  have hcs : ∀ i : ℤ, ∀ g ∈ ℓ.edgeCirc (G := G) i, g ∈ ℓ.edgeStab (G := G) i := fun i g hg =>
    ⟨MulAction.mem_stabilizer_iff.2 (ℓ.edgeCirc_fix hg).1,
      MulAction.mem_stabilizer_iff.2 (ℓ.edgeCirc_fix hg).2⟩
  have pack : (∀ g ∈ ℓ.edgeCirc (G := G) a, g ∈ L) →
      (∀ g ∈ ℓ.edgeCirc (G := G) (a + n - 1), g ∈ L) →
      (valence Γ (ℓ.vert a) = 3 → ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
        ∀ g ∈ ℓ.edgeStab (G := G) (a + i), g ∈ L) →
      Subgroup.closure (ℓ.edgeCirc (G := G) a ∪ ℓ.edgeCirc (G := G) (a + n - 1)) ≤ L ∧
        (valence Γ (ℓ.vert a) = 3 →
          Subgroup.closure {g | ∃ i : ℕ, 1 ≤ i ∧ i + 1 ≤ n ∧ g ∈ ℓ.edgeStab (G := G) (a + i)} ≤
            L) := by
    intro h1 h2 h3
    refine ⟨?_, fun h => ?_⟩
    · rw [Subgroup.closure_le]
      rintro g (hg | hg)
      · exact h1 g hg
      · exact h2 g hg
    · rw [Subgroup.closure_le]
      rintro g ⟨i, hi1, hi2, hg⟩
      exact h3 h i hi1 hi2 g hg
  have fromK : (∀ i : ℤ, a ≤ i → i ≤ a + n → ∀ g ∈ nbrStab Γ G (ℓ.vert i), g ∈ L) →
      (∀ g ∈ ℓ.edgeCirc (G := G) a, g ∈ L) ∧ (∀ g ∈ ℓ.edgeCirc (G := G) (a + n - 1), g ∈ L) ∧
      (∀ i : ℕ, 1 ≤ i → i + 1 ≤ n → ∀ g ∈ ℓ.edgeStab (G := G) (a + i), g ∈ L) := by
    intro hloc
    refine ⟨fun g hg => ?_, fun g hg => ?_, fun i hi1 hi2 g hg => ?_⟩
    · exact ℓ.edgeStab_le_of_ker F h40 (hloc a le_rfl (by omega))
        (hloc (a + 1) (by omega) (by omega)) g (hcs a g hg)
    · exact ℓ.edgeStab_le_of_ker F h40 (hloc (a + n - 1) (by omega) (by omega))
        (hloc (a + n - 1 + 1) (by omega) (by omega)) g (hcs _ g hg)
    · exact ℓ.edgeStab_le_of_ker F h40 (hloc (a + i) (by omega) (by omega))
        (hloc (a + i + 1) (by omega) (by omega)) g hg
  have evenA5 : valence Γ (ℓ.vert a) = 5 → valence Γ (ℓ.vert (a + n)) = 5 →
      (∀ g ∈ nbrStab Γ G (ℓ.vert (a + 2)), g ∈ L) →
      (∀ g ∈ nbrStab Γ G (ℓ.vert (a + n - 2)), g ∈ L) →
      (∀ g ∈ ℓ.edgeCirc (G := G) a, g ∈ L) ∧ (∀ g ∈ ℓ.edgeCirc (G := G) (a + n - 1), g ∈ L) := by
    intro hA hB hK2 hK2'
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · obtain ⟨t, htK, hta, hta1, htKa⟩ := ℓ.exists_t_left F h40 a
      rw [ℓ.edgeCirc_of_five hA] at hg
      exact F.gcirc_mem_of_elt (ℓ.adj a) hA hKa (hK2 t htK) hta hta1 htKa hg
    · obtain ⟨t, htK, hta, hta1, htKa⟩ := ℓ.exists_t_right F h40 (a + n)
      have hne : valence Γ (ℓ.vert (a + n - 1)) ≠ 5 := by
        have := halt (a + n - 1)
        rw [show a + n - 1 + 1 = a + n by omega] at this
        omega
      rw [ℓ.edgeCirc_of_ne_five hne, show a + n - 1 + 1 = a + n by omega] at hg
      exact F.gcirc_mem_of_elt (u := ℓ.vert (a + n)) (w := ℓ.vert (a + n - 1))
        (ℓ.adj_pred (a + n)) hB hKn (hK2' t htK) hta1 hta htKa hg
  have mid : valence Γ (ℓ.vert a) = 3 → (∀ g ∈ nbrStab Γ G (ℓ.vert (a + 2)), g ∈ L) →
      ∀ g ∈ nbrStab Γ G (ℓ.vert (a + 1)), g ∈ L := by
    intro hA hK2 k hk
    obtain ⟨g₀, hg₀K, h1, h2, hK⟩ := ℓ.exists_t_mid F h40 a
    have hv2 : valence Γ (ℓ.vert (a + 2)) = 3 := by
      rw [ℓ.valence_add_two F a]
      exact hA
    exact F.ker_mem_of_elt (ℓ.adj_add_two a) hv2 hK2 (hKa g₀ hg₀K) h1 h2 hK hk
  have hnA5 : ¬ valence Γ (ℓ.vert a) = 5 → valence Γ (ℓ.vert a) = 3 := by
    intro h
    have := hval (ℓ.vert a)
    omega
  by_cases hn1 : n = 1
  ·
    have e : a + (n : ℤ) = a + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := fromK (fun i hi1 hi2 => by
      rcases (by omega : i = a ∨ i = a + 1) with rfl | rfl
      · exact hKa
      · intro g hg
        apply hKn g
        rwa [e])
    exact pack h1 h2 fun _ => h3
  by_cases hn2 : n = 2
  ·
    have e : a + (n : ℤ) = a + 2 := by omega
    have hK2 : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + 2)), g ∈ L := by
      intro g hg
      apply hKn g
      rwa [e]
    have hK2' : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + n - 2)), g ∈ L := by
      intro g hg
      rw [show a + (n : ℤ) - 2 = a by omega] at hg
      exact hKa g hg
    have hv2 := ℓ.valence_add_two F a
    by_cases hA : valence Γ (ℓ.vert a) = 5
    · obtain ⟨h1, h2⟩ := evenA5 hA (by rw [e, hv2, hA]) hK2 hK2'
      exact pack h1 h2 fun h => absurd h (by omega)
    · have hA3 := hnA5 hA
      have hK1 := mid hA3 hK2
      obtain ⟨h1, h2, h3⟩ := fromK (fun i hi1 hi2 => by
        rcases (by omega : i = a ∨ i = a + 1 ∨ i = a + 2) with rfl | rfl | rfl
        · exact hKa
        · exact hK1
        · exact hK2)
      exact pack h1 h2 fun _ => h3
  have hn3 : 3 ≤ n := by omega
  have hall := fan51b_loc F h40 h36 ℓ a n hn3 hs hexc
  have hcls : ∀ w : V, (valence Γ w = valence Γ (ℓ.vert a) ∨
      valence Γ w = valence Γ (ℓ.vert (a + n))) → ∀ g ∈ nbrStab Γ G w, g ∈ L := by
    intro w hw g hg
    rcases hw with hw | hw
    · obtain ⟨h, hh, hhw⟩ := F.exists_mem_smul_eq hall hw
      rw [← hhw] at hg
      exact F.kernel_conj_le hKa hh g hg
    · obtain ⟨h, hh, hhw⟩ := F.exists_mem_smul_eq hall hw
      rw [← hhw] at hg
      exact F.kernel_conj_le hKn hh g hg
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  ·
    have hvn : valence Γ (ℓ.vert (a + n)) = valence Γ (ℓ.vert a) := by
      have := ℓ.valence_add_two_nat F a m
      rwa [show a + 2 * (m : ℤ) = a + n by omega] at this
    have hv2 := ℓ.valence_add_two F a
    have hK2 : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + 2)), g ∈ L := hcls _ (Or.inl hv2)
    by_cases hA : valence Γ (ℓ.vert a) = 5
    · have hK2' : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + n - 2)), g ∈ L := by
        refine hcls _ (Or.inl ?_)
        have := ℓ.valence_add_two_nat F a (m - 1)
        rwa [show a + 2 * ((m - 1 : ℕ) : ℤ) = a + n - 2 by omega] at this
      obtain ⟨h1, h2⟩ := evenA5 hA (by rw [hvn, hA]) hK2 hK2'
      exact pack h1 h2 fun h => absurd h (by omega)
    · have hA3 := hnA5 hA
      have hK1 := mid hA3 hK2
      have hv1 : valence Γ (ℓ.vert (a + 1)) = 5 := by
        have := halt a
        have := hval (ℓ.vert (a + 1))
        omega
      have hcls1 : ∀ w : V, valence Γ w = valence Γ (ℓ.vert (a + 1)) →
          ∀ g ∈ nbrStab Γ G w, g ∈ L := by
        intro w hw g hg
        obtain ⟨h, hh, hhw⟩ := F.exists_mem_smul_eq hall hw
        rw [← hhw] at hg
        exact F.kernel_conj_le hK1 hh g hg
      obtain ⟨h1, h2, h3⟩ := fromK (fun i _ _ => by
        have := hval (ℓ.vert i)
        by_cases h5 : valence Γ (ℓ.vert i) = 5
        · exact hcls1 _ (by omega)
        · exact hcls _ (Or.inl (by omega)))
      exact pack h1 h2 fun _ => h3
  ·
    have hvn : valence Γ (ℓ.vert (a + n)) ≠ valence Γ (ℓ.vert a) := by
      have := ℓ.valence_add_two_nat F (a + 1) m
      rw [show a + 1 + 2 * (m : ℤ) = a + n by omega] at this
      have h0 := halt a
      omega
    obtain ⟨h1, h2, h3⟩ := fromK (fun i _ _ => by
      have h5 := hval (ℓ.vert i)
      have h6 := hval (ℓ.vert a)
      have h7 := hval (ℓ.vert (a + n))
      exact hcls _ (by omega))
    exact pack h1 h2 fun _ => h3

end CFSG.Quasithin.Fan86
