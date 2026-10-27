module

public import CFSG.Quasithin.Vol2.Ch11SecAKM4
public import CFSG.Quasithin.Vol2.Ch11SecAKE11
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAKM3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

namespace C10KH

theorem list3_cases {X : Type} [Group X] (h : List11_1_1Three X) :
    IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7)) ∨ List3Other X ∨ A36Case4 X ∨
      (∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
        IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X) ∧
        NaturalSL2Action p X (CFSG.fittingSubgroup X)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem eleven_le_of_mod_five {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 1 ∨ p % 5 = 4) : 11 ≤ p := by
  by_contra h
  interval_cases p <;> simp_all <;> norm_num at hp

theorem list3Other_props (hT3 : FactList3Table) {X : Type} [Group X] [Finite X]
    (h : List3Other X) : CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 := by
  obtain ⟨h1, h2⟩ := hT3
  have of2 : (CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ ∧ 3 ∣ Nat.card X) →
      CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 := fun r =>
    ⟨r.1, by rw [r.2.1, Subgroup.card_bot]; exact one_dvd 3⟩
  rcases h with ⟨p, hp, h5, -, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h
  · exact of2 (h2 X (Or.inl ⟨p, hp, eleven_le_of_mod_five hp h5, h⟩))
  · exact of2 (h2 X (Or.inr (Or.inl h)))
  · cases s
    · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))))))
      exact ⟨r.1, r.2.1⟩
    · exact of2 (h2 X (Or.inr (Or.inr (Or.inl h))))
  · cases s
    · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr h))))))))))
      exact ⟨r.1, r.2.1⟩
    · exact of2 (h2 X (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have r := h1 X (Or.inr (Or.inr (Or.inl h)))
    exact ⟨r.1, r.2.1⟩
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact ⟨r.1, r.2.1⟩
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    exact ⟨r.1, r.2.1⟩
  · exact of2 (h2 X (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    exact ⟨r.1, r.2.1⟩
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    exact ⟨r.1, r.2.1⟩
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    exact ⟨r.1, r.2.1⟩
  · have r := h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
    exact ⟨r.1, r.2.1⟩

theorem center_eq_bot_of_isAlt7 {X : Type} [Group X] [Finite X] (h : IsAlt 7 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := (h : Nonempty (X ≃* alternatingGroup (Fin 7)))
  have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ H13.NotLie.isSimpleGroup_alt7 e
  have hN : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans H13.NotLie.card_alt7
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_of_simple (X := X) (by rw [hN]; norm_num))).2

end C10KH

theorem factModules3n_of (hT2 : FactList2Table) (hT3 : FactList3Table) (hSL3 : FactModulesSL3)
    (hA7 : FactHatA7Module) (h3 : FactModulesList3Order) (h2 : FactModulesList2Bang) :
    FactModules3n := by
  intro K₀ _ _ W _ _ hW ρ n hn hcard hperf hX hρ
  rcases hX with hX2 | ⟨rfl, hX3⟩
  · by_cases hsl : IsSL3 (2 ^ n) (K₀ ⧸ CFSG.pCore 2 K₀) ∨ IsPSL 3 2 n (K₀ ⧸ CFSG.pCore 2 K₀)
    · exact Or.inl (hSL3 K₀ W hW ρ n hn hcard hperf hsl hρ)
    · exfalso
      push Not at hsl
      have hq := (hT2 _ n hn hX2).1
      have hrest : IsPSp4 2 n (K₀ ⧸ CFSG.pCore 2 K₀) ∨ IsG2 2 n (K₀ ⧸ CFSG.pCore 2 K₀) ∨
          Is2F4 n (K₀ ⧸ CFSG.pCore 2 K₀) ∨ Is3D4 2 n (K₀ ⧸ CFSG.pCore 2 K₀) ∨
          (3 ∣ n ∧ Is3D4 2 (n / 3) (K₀ ⧸ CFSG.pCore 2 K₀)) := by
        rcases hX2 with h | h | h
        · exact absurd h hsl.1
        · exact absurd h hsl.2
        · exact h
      exact h2 _ n hn hrest ((C10KH.card_center_dvd_card_mulAut hperf hq ρ hρ).trans
        (C10KH.card_mulAut_dvd hW hcard))
  · rcases C10KH.list3_cases hX3 with h | h | h | h | h
    · refine Or.inr (Or.inl ⟨rfl, Or.inl h, fun y hy hodd => ?_⟩)
      rw [C10KH.center_eq_bot_of_isAlt7 h, Subgroup.mem_bot] at hy
      rw [C10KH.eq_one_of_mk_eq_one hy hodd, map_one]
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h, fun y hy hodd =>
        C10KH.concl_b_hat hA7 hW hcard ρ h y hy hodd⟩)
    · exfalso
      have hq := (C10KH.list3Other_props hT3 h).1
      exact h3 _ h ((C10KH.card_center_dvd_card_mulAut hperf hq ρ hρ).trans
        (C10KH.card_mulAut_dvd hW hcard))
    · obtain ⟨hnq, hF⟩ := C10KH.concl_c hW hcard hperf ρ (Or.inl h)
      exact Or.inr (Or.inr ⟨rfl, hnq, hF⟩)
    · obtain ⟨hnq, hF⟩ := C10KH.concl_c hW hcard hperf ρ (Or.inr h)
      exact Or.inr (Or.inr ⟨rfl, hnq, hF⟩)

end CFSG.Quasithin.Vol2.Ch11.SecA
