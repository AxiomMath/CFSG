module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitWeyl
import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeylSplit
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormFrame
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitOccursDict
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
import CFSG.LocalAnalysis.StandardType.GGLinImageSubspace
import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.QTwoCav
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.LangRat CFSG.StandardType.TableCRes CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

noncomputable section

section Helpers

variable {L : Type} [Field L]

private theorem frameRoots_subset_of_add_neg {ν : ℕ} {ψ : SL(ν, L) →* ModGL .E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hadd : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot .E6 (α + β) → α + β ∈ Ψ)
    (hneg : ∀ α ∈ Ψ, -α ∈ Ψ)
    (hsucc : ∀ (c : Fin ν) (h : (c : ℕ) + 1 < ν), σ c ⟨c + 1, h⟩ ∈ Ψ) :
    frameRoots σ ⊆ Ψ := by
  have key : ∀ i j : Fin ν, i < j → σ i j ∈ Ψ := by
    intro i j hij
    have hkey : ∀ n : ℕ, ∀ i j : Fin ν, (j : ℕ) = (i : ℕ) + n + 1 → σ i j ∈ Ψ := by
      intro n
      induction n with
      | zero =>
        intro i j h
        have hj : j = ⟨(i : ℕ) + 1, by omega⟩ := Fin.ext (by simpa using h)
        rw [hj]
        exact hsucc i (by omega)
      | succ n ih =>
        intro i j h
        have hi1 : (i : ℕ) + 1 < ν := by omega
        set m : Fin ν := ⟨(i : ℕ) + 1, hi1⟩ with hm
        have hmj : (j : ℕ) = (m : ℕ) + n + 1 := by
          have hmv : (m : ℕ) = (i : ℕ) + 1 := rfl
          omega
        have h2 : σ i m ∈ Ψ := by
          rw [hm]
          exact hsucc i hi1
        have h1 : σ m j ∈ Ψ := ih m j hmj
        have hroot : IsRoot .E6 (σ i m + σ m j) := by
          rw [hψ.add i m j]
          exact hψ.isRoot i j (by omega)
        rw [← hψ.add i m j]
        exact hadd (σ i m) h2 (σ m j) h1 hroot
    exact hkey ((j : ℕ) - (i : ℕ) - 1) i j (by omega)
  rintro r ⟨i, j, hij, rfl⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt
  · rw [hψ.neg j i]
    exact hneg _ (key j i hgt)

private theorem e6Split_iform_perm_short_long :
    ∀ (i j : ExcRaw.Root 1), ExcRaw.tabFix1.getD i.val false = true →
      ExcRaw.tabFix1.getD j.val false = false →
      iform (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot j)) (e6SplitRoot i) =
        iform (e6SplitRoot j) (e6SplitRoot i) := by
  decide +kernel

end Helpers


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

theorem E6SplitDatum.add_mem_e6SplitCodeRoots (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀)
    {c : Finset (ExcRaw.Root 1)} (hc : ∃ U, ExcRaw.occurs 1 U c)
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6SplitCodeRoots c) (hδ : δ ∈ e6SplitCodeRoots c)
    (hγδ : IsRoot .E6 (γ + δ)) : γ + δ ∈ e6SplitCodeRoots c := by
  classical
  obtain ⟨U, hU⟩ := hc
  obtain ⟨A, hA, hAU⟩ :=
    exists_le_ggLinImage_eq_of_addEquiv (p := 3) d.coord U
  obtain ⟨a, ha, hT, -⟩ := exists_family_of_le_fullThreeTorus (S := S) (A := A)
    (hA.trans d.le_fullThreeTorus)
  have hU' : ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c := by
    rwa [hAU]
  obtain ⟨j, hj⟩ := E6SplitDatum.exists_kernelComponent_of_occurs hS d hA ha hU'
  rw [← hj] at hγ hδ ⊢
  have hker : ∀ x ∈ kernelRoots (famCharHom a), S.ρ x ∈ kernelRoots (famCharHom a) :=
    fun x hx => CFSG.StandardType.TableCRes.rho_mem_kernelRoots_famChar S a hT hx
  have hΨ : TableCRes.rationalRootsM S.ρ (famCharHom a) j ⊆
      kernelRoots (famCharHom a) :=
    CFSG.StandardType.TableCRes.famComp_rationalRootsM_subset_kernelRoots hker j
  have hγK : γ ∈ kernelRoots (famCharHom a) := hΨ hγ
  have hδK : δ ∈ kernelRoots (famCharHom a) := hΨ hδ
  have hsum : γ + δ ∈ kernelRoots (famCharHom a) := by
    refine ⟨hγδ, ?_⟩
    rw [ofAdd_add, map_mul, hγK.2, hδK.2, mul_one]
  have hτ : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
    Or.inr (Or.inl rfl)
  have hγγ : iform γ γ = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγK.1
  have hδδ : iform δ δ = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hδK.1
  have hγδδ : iform (γ + δ) (γ + δ) = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγδ
  have hprod : iform γ δ = -1 := by
    rw [iform_add_left, iform_add_right, iform_add_right, hγγ, hδδ,
      iform_comm δ γ] at hγδδ
    linarith
  have hclass : (⟦⟨γ + δ, hsum⟩⟧ : KernelComponent (famCharHom a)) =
      ⟦⟨γ, hγK⟩⟧ := by
    apply CFSG.LieType.Chevalley.mk_eq_of_iform_ne_zero
    rw [iform_add_left, hγγ, iform_comm δ γ, hprod]
    norm_num
  refine CFSG.StandardType.TableCRes.famLabelIndex_rationalRootsM_closed hker
    S.frob.iform_eq j hγ hsum ?_
  simpa using hclass

theorem e6SplitWeyl_long_mem_e6SplitComponent (hS : E6SplitLangTwo S)
    {c : Finset (ExcRaw.Root 1)}
    (hadd : ∀ γ ∈ e6SplitCodeRoots c, ∀ δ ∈ e6SplitCodeRoots c, IsRoot .E6 (γ + δ) →
      γ + δ ∈ e6SplitCodeRoots c)
    {i j : ExcRaw.Root 1} (hi : i ∈ c) (hj : j ∈ c)
    (hlong : ExcRaw.tabFix1.getD i.val false = true)
    (hshort : ExcRaw.tabFix1.getD j.val false = false)
    (hij : iform (e6SplitRoot j) (e6SplitRoot i) ≠ 0) :
    e6SplitWeyl L i ∈ e6SplitComponent S c := by
  classical
  have : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1)
    (by rw [hS.1, pow_one])
  let γ : Fin Tag.E6.rank → ℤ := e6SplitRoot i
  let β : Fin Tag.E6.rank → ℤ := e6SplitRoot j
  let σβ : Fin Tag.E6.rank → ℤ := permLattice (τ := .E6) e6SplitPerm β
  have hγroot : IsRoot .E6 γ := isRoot_e6SplitRoot i
  have hβroot : IsRoot .E6 β := isRoot_e6SplitRoot j
  have hσβroot : IsRoot .E6 σβ := isRoot_permLattice_e6SplitRoot j
  have hγfix : permLattice (τ := .E6) e6SplitPerm γ = γ :=
    (e6SplitRoot_fixed_iff i).2 hlong
  have hσσ : permLattice (τ := .E6) e6SplitPerm σβ = β :=
    permLattice_permLattice_e6SplitRoot j
  have hne : β ≠ γ := by
    intro h
    have hfixβ : permLattice (τ := .E6) e6SplitPerm β = β := by
      rw [h, hγfix]
    have htrue := (e6SplitRoot_fixed_iff j).1 hfixβ
    have hfalse := hshort
    rw [htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  have hne' : β ≠ -γ := by
    intro h
    have hfixβ : permLattice (τ := .E6) e6SplitPerm β = β := by
      rw [h, permLattice_neg, hγfix]
    have htrue := (e6SplitRoot_fixed_iff j).1 hfixβ
    have hfalse := hshort
    rw [htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  have hsq : iform β γ ^ 2 < iform β β * iform γ γ :=
    CFSG.LieType.Steinberg.Adjoint.iform_sq_lt hβroot hγroot hne hne'
  have hββ : iform β β = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hβroot
  have hγγ : iform γ γ = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hγroot
  have ht : iform β γ = 1 ∨ iform β γ = -1 := by
    have h2 : iform β γ ^ 2 < 4 := by rw [hββ, hγγ] at hsq; exact hsq
    have hlo : -2 < iform β γ := by nlinarith [sq_nonneg (iform β γ + 2)]
    have hhi : iform β γ < 2 := by nlinarith [sq_nonneg (iform β γ - 2)]
    have h0 : iform β γ ≠ 0 := by simpa [β, γ] using hij
    omega
  let s : ℤ := -iform β γ
  have hs : s = 1 ∨ s = -1 := by
    rcases ht with h | h
    · right; simp [s, h]
    · left; simp [s, h]
  have hst : s * iform β γ = -1 := by
    rcases ht with h | h <;> simp [s, h]
  have hsβγ : iform (s • β) γ = -1 := by
    rw [iform_smul_left, hst]
  have hσβγ : iform σβ γ = iform β γ := by
    simpa [β, γ, σβ] using e6Split_iform_perm_short_long i j hlong hshort
  have hγsσβ : iform γ (s • σβ) = -1 := by
    rw [iform_smul_right, iform_comm γ σβ, hσβγ, hst]
  have hpair : iform (s • β) (s • σβ) = 0 := by
    rw [iform_smul_left, iform_smul_right, (e6SplitShortFacts j hshort).1, mul_zero,
      mul_zero]
  have hsβroot : IsRoot .E6 (s • β) := by
    rcases hs with h | h
    · simpa [h] using hβroot
    · simpa [h] using IsRoot.neg hβroot
  have hsσβroot : IsRoot .E6 (s • σβ) := by
    rcases hs with h | h
    · simpa [h] using hσβroot
    · simpa [h] using IsRoot.neg hσβroot
  let β' : Fin 3 → Fin Tag.E6.rank → ℤ := ![s • β, γ, s • σβ]
  have hβ'root : ∀ k : Fin 3, IsRoot .E6 (β' k) := by
    intro k
    fin_cases k
    · simpa [β'] using hsβroot
    · simpa [β'] using hγroot
    · simpa [β'] using hsσβroot
  have h00 : iform (β' 0) (β' 0) = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl))
      (hβ'root 0)
  have h11 : iform (β' 1) (β' 1) = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl))
      (hβ'root 1)
  have h22 : iform (β' 2) (β' 2) = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl))
      (hβ'root 2)
  have h01 : iform (β' 0) (β' 1) = -1 := by simpa [β'] using hsβγ
  have h10 : iform (β' 1) (β' 0) = -1 := by rw [iform_comm]; exact h01
  have h12 : iform (β' 1) (β' 2) = -1 := by simpa [β'] using hγsσβ
  have h21 : iform (β' 2) (β' 1) = -1 := by rw [iform_comm]; exact h12
  have h02 : iform (β' 0) (β' 2) = 0 := by simpa [β'] using hpair
  have h20 : iform (β' 2) (β' 0) = 0 := by rw [iform_comm]; exact h02
  have hG : ∀ a b : Fin 3, iform (β' a) (β' b) = chainGram a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [chainGram, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  have hθ : ∀ (k : Fin 3) (h : (k : ℕ) + 1 < 3),
      ∃ θ : SL(3, L) →* ModGL .E6 L,
        θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 .E6 L (β' k) ∧
          θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 .E6 L (β' ⟨k + 1, h⟩) := by
    intro k h
    fin_cases k
    · refine exists_a2Hom_of_iform_eq_neg_one (Or.inl rfl) (hβ'root 0) (hβ'root 1) ?_
      simpa [β'] using h01
    · refine exists_a2Hom_of_iform_eq_neg_one (Or.inl rfl) (hβ'root 1) (hβ'root 2) ?_
      simpa [β'] using h12
    · simp at h
  obtain ⟨ψ, hψ⟩ := exists_chainHom (m := 3) (Or.inr (Or.inl rfl)) β' hβ'root hG hθ
  have hframe : IsSLFrame ψ (chainσ β') :=
    isSLFrame_chainHom (Or.inr (Or.inl rfl)) hβ'root hG hψ
  have hneg : ∀ α ∈ e6SplitCodeRoots c, -α ∈ e6SplitCodeRoots c := by
    rintro α ⟨k, hk, h⟩
    refine ⟨k, hk, ?_⟩
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (neg_neg _)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (neg_neg _)))
  have hsmul_mem : ∀ (δ : Fin Tag.E6.rank → ℤ), δ ∈ e6SplitCodeRoots c →
      s • δ ∈ e6SplitCodeRoots c := by
    intro δ hδ
    rcases hs with h | h
    · simpa [h] using hδ
    · simpa [h] using hneg δ hδ
  have hβmem : β ∈ e6SplitCodeRoots c := ⟨j, hj, Or.inl rfl⟩
  have hσβmem : σβ ∈ e6SplitCodeRoots c := ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩
  have hthree : ∀ k : Fin 3, β' k ∈ e6SplitCodeRoots c := by
    intro k
    fin_cases k
    · simpa [β'] using hsmul_mem β hβmem
    · simpa [β'] using (show γ ∈ e6SplitCodeRoots c from ⟨i, hi, Or.inl rfl⟩)
    · simpa [β'] using hsmul_mem σβ hσβmem
  have hsucc : ∀ (k : Fin 4) (h : (k : ℕ) + 1 < 4),
      chainσ β' k ⟨k + 1, h⟩ ∈ e6SplitCodeRoots c := by
    intro k h
    rw [chainσ_of_val_eq β' (a := k) (b := ⟨k + 1, h⟩) rfl]
    exact hthree ⟨k, by omega⟩
  have hsub : frameRoots (chainσ β') ⊆ e6SplitCodeRoots c :=
    frameRoots_subset_of_add_neg hframe hadd hneg hsucc
  have hσ0 : permLattice (τ := .E6) e6SplitPerm (β' 0) = β' 2 := by
    change permLattice (τ := .E6) e6SplitPerm (s • β) = s • σβ
    rw [permLattice_zsmul]
  have hσ1 : permLattice (τ := .E6) e6SplitPerm (β' 1) = β' 1 := by
    simpa [β'] using hγfix
  have hσ2 : permLattice (τ := .E6) e6SplitPerm (β' 2) = β' 0 := by
    change permLattice (τ := .E6) e6SplitPerm (s • σβ) = s • β
    rw [permLattice_zsmul, hσσ]
  have hT : permLattice (τ := .E6) e6SplitPerm (β' 0 + β' 1 + β' 2) =
      β' 0 + β' 1 + β' 2 := by
    rw [permLattice_add, permLattice_add, hσ0, hσ1, hσ2]
    abel
  have hω1 : chainω β' 1 = β' 0 := by simp [chainω]
  have hω2 : chainω β' 2 = β' 0 + β' 1 := by simp [chainω, Fin.sum_univ_three]
  have hω3 : chainω β' 3 = β' 0 + β' 1 + β' 2 := by
    simp [chainω, Fin.sum_univ_three]
  have hω : ∀ k : ℕ, k ≤ 3 →
      chainω β' (3 - k) = β' 0 + β' 1 + β' 2 -
        permLattice (τ := .E6) e6SplitPerm (chainω β' k) := by
    intro k hk
    interval_cases k
    · rw [show 3 - 0 = 3 by norm_num, hω3, chainω_zero,
        show permLattice (τ := .E6) e6SplitPerm (0 : Fin Tag.E6.rank → ℤ) = 0 from rfl,
        sub_zero]
    · rw [show 3 - 1 = 2 by norm_num, hω2, hω1, hσ0]
      abel
    · rw [show 3 - 2 = 1 by norm_num, hω1, hω2, permLattice_add, hσ0, hσ1]
      abel
    · rw [show 3 - 3 = 0 by norm_num, chainω_zero, hω3, hT, sub_self]
  have hrev : ∀ a : Fin 4, ((Fin.revPerm a : Fin 4) : ℕ) = 3 - (a : ℕ) := by
    intro a
    simp [Fin.revPerm, Fin.rev]
  have hπ : ∀ a b : Fin 4, a ≠ b →
      S.ρ (chainσ β' a b) = chainσ β' (Fin.revPerm a) (Fin.revPerm b) := by
    intro a b hab
    rw [e6SplitRho_eq hS (hframe.isRoot a b hab)]
    have hchain : chainσ β' (Fin.revPerm a) (Fin.revPerm b) =
        -permLattice (τ := .E6) e6SplitPerm (chainσ β' a b) := by
      calc chainσ β' (Fin.revPerm a) (Fin.revPerm b)
          = chainω β' (3 - (b : ℕ)) - chainω β' (3 - (a : ℕ)) := by
              simp only [chainσ, hrev]
        _ = (β' 0 + β' 1 + β' 2 -
              permLattice (τ := .E6) e6SplitPerm (chainω β' b)) -
              (β' 0 + β' 1 + β' 2 -
                permLattice (τ := .E6) e6SplitPerm (chainω β' a)) := by
              rw [hω b (by omega), hω a (by omega)]
        _ = permLattice (τ := .E6) e6SplitPerm (chainω β' a) -
              permLattice (τ := .E6) e6SplitPerm (chainω β' b) := by abel
        _ = permLattice (τ := .E6) e6SplitPerm (chainω β' a - chainω β' b) := by
              rw [permLattice_sub]
        _ = -permLattice (τ := .E6) e6SplitPerm (chainω β' b - chainω β' a) := by
              rw [show chainω β' a - chainω β' b = -(chainω β' b - chainω β' a) by
                abel, permLattice_neg]
        _ = -permLattice (τ := .E6) e6SplitPerm (chainσ β' a b) := by
              rw [chainσ]
    exact hchain.symm
  obtain ⟨K, hKfield, hKfin, hKalg, -⟩ := S.exists_fixedField
  let : Field K := hKfield
  let : Finite K := hKfin
  let : Algebra K L := hKalg
  have hAlg : S.IsAlgebraic := hS.2.1
  have hKclos : IsAlgClosure K L := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hnpos, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hnpos.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  let : IsAlgClosure K L := hKclos
  obtain ⟨F', hcomm, hperf⟩ :=
    exists_split_source_perfect_of_frame_of_rho S (ν := 4) (ψ := ψ) (σ := chainσ β')
      (by norm_num) hframe Fin.revPerm hπ (k' := K) (r := 2) (e := 1) Nat.prime_two
      (by norm_num) (by rw [hS.1]; norm_num)
  have hker : ψ.ker ≠ ⊤ := frame_ker_ne_top_of_isSLFrame (by norm_num) hframe
  have hkercenter : ψ.ker ≤ Subgroup.center SL(4, L) := by
    intro X hX
    refine mem_center_SL_of_commute (by norm_num) ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_of_frame_of_isSLFrame (by norm_num) hker
  have hγframe : γ ∈ frameRoots (chainσ β') := by
    refine ⟨1, 2, by decide, ?_⟩
    rw [chainσ_of_val_eq β' (a := (1 : Fin 4)) (b := (2 : Fin 4)) rfl]
    simp [β']
  have hnegγframe : -γ ∈ frameRoots (chainσ β') := by
    refine ⟨2, 1, by decide, ?_⟩
    rw [chainσ_neg, chainσ_of_val_eq β' (a := (1 : Fin 4)) (b := (2 : Fin 4)) rfl]
    simp [β']
  have hgpair : rootSL2 .E6 L γ WSL ∈ rootSpan .E6 L {γ, -γ} :=
    rootSL2_mem_rootSpan_pair hγroot WSL
  have hg : rootSL2 .E6 L γ WSL ∈ rootSpan .E6 L (frameRoots (chainσ β')) := by
    refine rootSpan_mono ?_ hgpair
    intro x hx
    rcases hx with rfl | rfl
    · exact hγframe
    · exact hnegγframe
  have hmodel : rootSL2 .E6 L γ WSL ∈ S.D.model :=
    S.Γ_le_model (by
      rw [show rootSL2 .E6 L γ WSL = e6SplitWeyl L i by
        rw [e6SplitWeyl, if_pos hlong]]
      exact e6SplitWeyl_mem_Γ hS i)
  have hgfix : S.D.step (rootSL2 .E6 L γ WSL) = rootSL2 .E6 L γ WSL :=
    (S.D.mem_model.1 hmodel).2
  have hg2 : rootSL2 .E6 L γ WSL ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self γ
  rw [e6SplitWeyl, if_pos hlong]
  exact map_eqLocus_le_commutator_of_frame S hframe hsub hkercenter hodd F' hcomm hperf
    hg hgfix hg2

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
