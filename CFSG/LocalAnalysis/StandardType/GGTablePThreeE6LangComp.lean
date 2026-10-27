module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobData
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableT
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatQS
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatDistinct
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatTransfer
import CFSG.Quasithin.H13.NQTermLinearThreeTools
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTStatic
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem exists_componentRoots_eq_of_kernelRoots_eq {τ : Tag} {M M' : Type*}
    [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') (i' : KernelComponent χ') :
    ∃ i : KernelComponent χ, componentRoots χ i = componentRoots χ' i' := by
  induction i' using Quotient.inductionOn with
  | h a =>
    obtain ⟨α, hα'⟩ := a
    exact ⟨⟦⟨α, h.ge hα'⟩⟧,
      CFSG.LieType.Chevalley.OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq h (h.ge hα') hα'⟩

section Certificates

theorem e6_lang_rationalComponents
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup Tag.E6 L 3)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧ E6CompLabel S.D.q lab := by
  classical
  have h3ne : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [hcast, h2, zero_add]
    rw [h3]; exact one_ne_zero
  obtain ⟨ω, hω⟩ :=
    CFSG.Quasithin.H13.NQTerm.exists_isPrimitiveRoot_of_isAlgClosed (n := 3) (by norm_num) h3ne
  have ha3 : ∀ j, ((a j : L)) ^ 3 = 1 := fun j => by
    rw [← Units.val_pow_eq_pow_val, hap j, Units.val_one]
  choose k hklt hk using fun j => hω.eq_pow_of_pow_eq_one (ha3 j)
  let v : Fin Tag.E6.rank → ZMod 3 := fun j => (k j : ZMod 3)
  have hv : ∀ j, ((a j : Lˣ) : L) = ω ^ (v j).val := by
    intro j
    rw [ZMod.val_natCast_of_lt (hklt j)]
    exact (hk j).symm
  have hvne : v ≠ 0 := by
    intro hv0
    apply h1
    have ha1 : a = 1 := by
      funext j
      apply Units.ext
      have h : ((a j : Lˣ) : L) = 1 := by
        have hj := hv j
        rw [hv0] at hj
        simpa using hj
      simpa using h
    rw [ha1, rootDiagUnit_one]
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    rw [show a ^ 3 = 1 from funext fun j => hap j, rootDiagUnit_one]
  have hQSi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    e6_rationalComponent_quasisimple S hT hap h1 i
  have horbit : ∀ i' : KernelComponent (rootCharHom a),
      ∃ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i' := by
    intro i'
    by_contra hno
    have hno' : ∀ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i' := by
      intro kk hk
      exact hno ⟨kk, hk⟩
    exact (rationalComponent_ne_of_not_orbit S hT i i' hno' hQSi)
      ((huniq i' (e6_rationalComponent_quasisimple S hT hap h1 i')).symm)
  have hker' : kernelRoots (e6Chi v) =
      {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
    ext γ
    have hchi : (e6Chi v) (Multiplicative.ofAdd γ) =
        Multiplicative.ofAdd (∑ k, ((γ k : ℤ) : ZMod 3) * v k) := rfl
    simp only [kernelRoots, Set.mem_setOf_eq, hchi, ofAdd_eq_one]
  have hker : kernelRoots (rootCharHom a) = kernelRoots (e6Chi v) := by
    rw [(frobRootMap_e6_admissible S hT ω hω v hv).2, ← hker']
  have horbitE : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
      ∃ kk : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[kk] ''
        componentRoots (rootCharHom a) i = Ψ' := by
    intro Ψ' hΨ'
    obtain ⟨i', rfl⟩ := hΨ'
    obtain ⟨i'', hi''⟩ := exists_componentRoots_eq_of_kernelRoots_eq hker i'
    obtain ⟨kk, hkk⟩ := horbit i''
    exact ⟨kk, hkk.trans hi''⟩
  have hTres := e6TableT_sound S.ρ v ((S.D.q : ℕ) : ZMod 3)
    (frobRootMap_map_add S.D S.frob) (fun γ hγ => (S.frob.isRoot_iff γ).2 hγ)
    (frobRootMap_e6_admissible S hT ω hω v hv).1 hvne
    (componentRoots (rootCharHom a) i) (e6_kerComponent_of_component hω v hv i) horbitE
  rcases hTres with hD5 | hA5 | hD4 | hA2
  ·
    obtain ⟨hr5, hn40, horb1⟩ := hD5
    have hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
      rw [hr5, hn40]; norm_num
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
        rationalLabel_innerD_E6 S Nat.prime_three h3ne hT hTp i hshape hinner hQSi
      refine ⟨lab, hRL, ?_⟩
      refine e6CompLabel_of_innerD (q := S.D.q) (m := 1)
        (r := compRank (componentRoots (rootCharHom a) i)) ?_ rfl ?_ htag hrank
      · right; exact hr5
      · rw [hdeg, horb1]
    · obtain ⟨lab, hdeg, hc1, hc2, hc3, hRL⟩ :=
        rationalLabel_outerD S Nat.prime_three hT hap h1 i hshape hinner hQSi
      refine ⟨lab, hRL, ?_⟩
      have hk := twistKind_outerD S.ρ (rootCharHom a) i hshape hinner
      refine e6CompLabel_of_outerD (q := S.D.q) (m := 1)
        (r := compRank (componentRoots (rootCharHom a) i))
        (twistKind S.ρ (rootCharHom a) i) ?_ ?_ rfl ?_ ?_ ?_ ?_
      · exact hk
      · right; exact hr5
      · rw [hdeg, horb1]
      · exact hc1
      · exact hc2
      · exact hc3
  ·
    obtain ⟨hr5, hn30, horb1⟩ := hA5
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr5, hn30]; norm_num
    obtain ⟨lab, hdeg, hrank, hinn, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQSi
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner ∨
        twistKind S.ρ (rootCharHom a) i = .suN := by
      by_cases htw : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · left; unfold twistKind; rw [if_pos htw]
      · right
        unfold twistKind
        rw [if_neg htw]
        have hexc : ¬ ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
            (componentRoots (rootCharHom a) i).ncard = 72) ∨
            (compRank (componentRoots (rootCharHom a) i) = 4 ∧
              (componentRoots (rootCharHom a) i).ncard = 24 ∧
              ¬ twistInner (componentRoots (rootCharHom a) i)
                ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
                  (componentRoots (rootCharHom a) i)]))) := by
          rintro (⟨h6, h72⟩ | ⟨h4, h24, -⟩) <;> omega
        have htwoD : ¬ (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
            (componentRoots (rootCharHom a) i).ncard =
              2 * compRank (componentRoots (rootCharHom a) i) *
                (compRank (componentRoots (rootCharHom a) i) - 1)) := by
          rintro ⟨h4, htwo⟩
          rw [hr5] at htwo
          omega
        rw [if_neg hexc, if_neg htwoD,
          if_pos (show 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
              (componentRoots (rootCharHom a) i).ncard =
                compRank (componentRoots (rootCharHom a) i) *
                  (compRank (componentRoots (rootCharHom a) i) + 1) from
            ⟨by omega, by omega⟩)]
    refine ⟨lab, hRL, ?_⟩
    refine e6CompLabel_of_A5 (q := S.D.q) (m := 1) ?_ ?_ ?_ ?_
    · rfl
    · rw [hdeg, horb1]
    · rw [hrank, hr5]
    · rcases hkind with hkind | hkind
      · exact Or.inl (hinn hkind)
      · exact Or.inr (hsu hkind)
  ·
    obtain ⟨hr4, hn24, horb1⟩ := hD4
    have hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) := by
      rw [hr4, hn24]; norm_num
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨lab, hdeg, htag, hrank, hRL⟩ :=
        rationalLabel_innerD_E6 S Nat.prime_three h3ne hT hTp i hshape hinner hQSi
      refine ⟨lab, hRL, ?_⟩
      refine e6CompLabel_of_innerD (q := S.D.q) (m := 1)
        (r := compRank (componentRoots (rootCharHom a) i)) ?_ rfl ?_ htag hrank
      · left; exact hr4
      · rw [hdeg, horb1]
    · obtain ⟨lab, hdeg, hc1, hc2, hc3, hRL⟩ :=
        rationalLabel_outerD S Nat.prime_three hT hap h1 i hshape hinner hQSi
      refine ⟨lab, hRL, ?_⟩
      have hk := twistKind_outerD S.ρ (rootCharHom a) i hshape hinner
      refine e6CompLabel_of_outerD (q := S.D.q) (m := 1)
        (r := compRank (componentRoots (rootCharHom a) i))
        (twistKind S.ρ (rootCharHom a) i) ?_ ?_ rfl ?_ ?_ ?_ ?_
      · exact hk
      · left; exact hr4
      · rw [hdeg, horb1]
      · exact hc1
      · exact hc2
      · exact hc3
  ·
    obtain ⟨hr2, hn6, horb3, htw1, htw2⟩ := hA2
    have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard =
          compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1) := by
      rw [hr2, hn6]; norm_num
    obtain ⟨lab, hdeg, hrank, hinn, hsu, hRL⟩ :=
      rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hQSi
    refine ⟨lab, hRL, ?_⟩
    refine e6CompLabel_of_A2 (q := S.D.q) (m := 3)
      (k := twistKind S.ρ (rootCharHom a) i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rfl
    · rw [hdeg, horb3]
    · rw [hrank, hr2]
    · exact hinn
    · exact hsu
    · intro hq1
      have htw : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) := by
        have h := htw1 hq1
        rw [horb3]
        exact h
      unfold twistKind
      rw [if_pos htw]
    · intro hq2
      have hnot : ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) := by
        have h := htw2 hq2
        rw [horb3]
        exact h
      exact twistKind_A2_of_not_inner S.ρ (rootCharHom a) i hr2 hn6 hnot
    · have hq : ((S.D.q : ℕ) : ZMod 3) = 1 ∨ ((S.D.q : ℕ) : ZMod 3) = 2 := by
        by_contra hcon
        have hcon1 : ((S.D.q : ℕ) : ZMod 3) ≠ 1 := fun h => hcon (Or.inl h)
        have hcon2 : ((S.D.q : ℕ) : ZMod 3) ≠ 2 := fun h => hcon (Or.inr h)
        have h0 : ((S.D.q : ℕ) : ZMod 3) = 0 :=
          (by decide : ∀ x : ZMod 3, x ≠ 1 → x ≠ 2 → x = 0) _ hcon1 hcon2
        exact S.hpq ((ZMod.natCast_eq_zero_iff S.D.q 3).1 h0)
      exact hq

end Certificates

end CFSG.StandardType.TablePThreeKG

end
