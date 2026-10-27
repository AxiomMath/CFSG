module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2aClass
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear
open scoped Matrix

theorem levTwoS2a_comp_swap (n : ℕ) {i j a : Fin (n+1)} (hij : i ≠ j) (hai : a ≠ i)
    (haj : a ≠ j) :
    (Pi.single j 1 - Pi.single a 1 : Fin (n+1) → ℤ) ∘ (Equiv.swap i j) =
      (Pi.single i 1 - Pi.single a 1 : Fin (n+1) → ℤ) := by
  funext k
  simp only [Function.comp_apply, Pi.sub_apply, Pi.single_apply]
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

@[expose] def levTwoS2a_classA (n p : ℕ) (c : Fin n → ZMod p) (B a : Fin (n+1)) (β : Fin n → ℤ) : Prop :=
  (∃ i : Fin (n+1), levTwoS2a_D n p c i = levTwoS2a_D n p c B ∧
    toStd n β = Pi.single i 1 - Pi.single a 1) ∨
  (∃ i : Fin (n+1), levTwoS2a_D n p c i = levTwoS2a_D n p c B ∧
    toStd n β = Pi.single a 1 - Pi.single i 1)

theorem levTwoS2a_Wapply_eps_pos (n : ℕ) (hn : 1 ≤ n) {i j a : Fin (n+1)}
    (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j) {x : Fin n → ℤ}
    (hx : toStd n x = Pi.single j 1 - Pi.single a 1) :
    weylAction (isFiniteType_A n) (rRefl (isFiniteType_A n) (levTwoS2a_eps n i j)) x =
      levTwoS2a_eps n i a := by
  have hαrt : IsRt (isFiniteType_A n) (levTwoS2a_eps n i j) :=
    (levTwoS2a_isRt_iff_coord n hn _).mpr ⟨i, j, hij, levTwoS2a_toStd_eps n i j⟩
  apply toStd_injective n
  rw [levTwoS2a_rRefl_coord n hn hαrt hij (levTwoS2a_toStd_eps n i j), hx,
    levTwoS2a_toStd_eps]
  exact levTwoS2a_comp_swap n hij hai haj


theorem levTwoS2a_Cl_classA (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a B : Fin (n+1)} {x β : Fin n → ℤ}
    (haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B)
    (hxa : levTwoS2a_classA n p c B a x) (hβa : levTwoS2a_classA n p c B a β) :
    Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) β := by
  have ha_of : ∀ {k : Fin (n+1)}, levTwoS2a_D n p c k = levTwoS2a_D n p c B → a ≠ k :=
    fun hk hh => haD (hh.symm ▸ hk)
  have hpos_x : ∃ j : Fin (n+1), levTwoS2a_D n p c j = levTwoS2a_D n p c B ∧
      Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) (levTwoS2a_eps n j a) := by
    rcases hxa with ⟨j, hjB, hxj⟩ | ⟨j, hjB, hxj⟩
    · refine ⟨j, hjB, ?_⟩
      have hxeq : x = levTwoS2a_eps n j a :=
        toStd_injective n (by rw [hxj, levTwoS2a_toStd_eps])
      rw [← hxeq]
      exact Cl.base (Or.inr (Set.mem_singleton x))
    · refine ⟨j, hjB, ?_⟩
      have hxrt : IsRt (isFiniteType_A n) x :=
        (levTwoS2a_isRt_iff_coord n hn x).mpr ⟨a, j, ha_of hjB, hxj⟩
      have hxcl : Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) x :=
        Cl.base (Or.inr (Set.mem_singleton x))
      have hstep := Cl.refl hxcl hxcl
      rw [levTwoS2a_weylAction_rRefl_self n hn hxrt] at hstep
      have hxeq : -x = levTwoS2a_eps n j a := by
        apply toStd_injective
        rw [toStd_neg, hxj, levTwoS2a_toStd_eps]
        simp
      rwa [← hxeq]
  obtain ⟨j, hjB, hpcl⟩ := hpos_x
  have hqcl_of : ∀ (i : Fin (n+1)), levTwoS2a_D n p c i = levTwoS2a_D n p c B →
      Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) (levTwoS2a_eps n i a) := by
    intro i hiB
    by_cases hij : i = j
    · subst hij; simpa using hpcl
    · have hai : a ≠ i := ha_of hiB
      have haj : a ≠ j := ha_of hjB
      have hαcl : Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) (levTwoS2a_eps n i j) :=
        Cl.base (Or.inl (by
          rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h]
          exact ⟨i, j, hij, levTwoS2a_toStd_eps n i j, hiB.trans hjB.symm⟩))
      have hstep := Cl.refl hαcl hpcl
      rwa [levTwoS2a_Wapply_eps_pos n hn hij hai haj (levTwoS2a_toStd_eps n j a)] at hstep
  rcases hβa with ⟨i, hiB, hβi⟩ | ⟨i, hiB, hβi⟩
  · have hβeq : β = levTwoS2a_eps n i a :=
      toStd_injective n (by rw [hβi, levTwoS2a_toStd_eps])
    rw [hβeq]
    exact hqcl_of i hiB
  · have hqcl := hqcl_of i hiB
    have hirt : IsRt (isFiniteType_A n) (levTwoS2a_eps n i a) :=
      (levTwoS2a_isRt_iff_coord n hn _).mpr ⟨i, a, (ha_of hiB).symm, levTwoS2a_toStd_eps n i a⟩
    have hflip := Cl.refl hqcl hqcl
    rw [levTwoS2a_weylAction_rRefl_self n hn hirt] at hflip
    have hβeq : β = -levTwoS2a_eps n i a := by
      apply toStd_injective
      rw [toStd_neg, hβi, levTwoS2a_toStd_eps]
      simp
    rw [hβeq]
    exact hflip

end CFSG.StandardType.LevTwo
