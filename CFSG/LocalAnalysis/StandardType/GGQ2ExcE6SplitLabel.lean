module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitCensus
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
import CFSG.LocalAnalysis.StandardType.GGFamLabelKind
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes CFSG.LieType.Steinberg.Adjoint


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}

theorem compRank_eq_four_of_ncard_eq_24 {R : Set (Fin Tag.E6.rank → ℤ)}
    (hR : IsRootComponent R) (hne : R.Nonempty) (h24 : R.ncard = 24) : compRank R = 4 := by
  have hle : compRank R ≤ 6 := by
    have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) R
    simpa [Tag.rank] using h
  rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
    (τ := .E6) (Or.inr (Or.inl rfl)) hR hne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
    ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
  · have h2 : R.ncard = 2 :=
      CFSG.StandardType.LangRat.j4d_rank_one_ncard (τ := .E6)
        (Or.inr (Or.inl rfl)) hR h1
    omega
  · rw [h24] at h3
    set r := compRank R with hr
    rw [← hr] at *
    interval_cases r <;> omega
  · rw [h24] at h3
    set r := compRank R with hr
    rw [← hr] at *
    interval_cases r <;> omega
  · omega
  · omega
  · omega

theorem componentRoots_eq_e6SplitCodeRoots_of_longCount_ne_zero (hS : E6SplitLangTwo S)
    {ι : Type} {a : ι → Fin Tag.E6.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus) (i : KernelComponent (famCharHom a))
    {c : Finset (ExcRaw.Root 1)}
    (hR : rationalRootsM S.ρ (famCharHom a) i = e6SplitCodeRoots c)
    (hlong : ExcRaw.longCount 1 c ≠ 0) :
    componentRoots (famCharHom a) i = e6SplitCodeRoots c := by
  classical
  let χ := famCharHom a
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := componentRoots χ i
  let R : Set (Fin Tag.E6.rank → ℤ) := e6SplitCodeRoots c
  let e : ℕ := componentOrbitLength S.ρ Ψ
  have hrho : ∀ γ, IsRoot .E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ := hS.2.2
  have hR' : rationalRootsM S.ρ χ i = R := hR
  have hRroot : ∀ γ ∈ R, IsRoot .E6 γ := fun γ hγ => isRoot_of_mem_e6SplitCodeRoots hγ
  have hΨcomp : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hΨfin : Ψ.Finite := (finite_setOf_isRoot .E6).subset fun α hα => hα.1.1
  have hσ2 : ∀ γ : Fin Tag.E6.rank → ℤ,
      permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm γ) = γ := by
    intro γ
    funext j
    fin_cases j <;> rfl
  have hρ2 : ∀ γ, IsRoot .E6 γ → S.ρ (S.ρ γ) = γ := by
    intro γ hγ
    have hγ' : IsRoot .E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
    have hσγ : S.ρ γ = -permLattice TwistTag.E6.perm γ := hrho γ hγ
    have hγ'' : IsRoot .E6 (-permLattice TwistTag.E6.perm γ) := hσγ ▸ hγ'
    have h1 : S.ρ (S.ρ γ) = S.ρ (-permLattice TwistTag.E6.perm γ) := by rw [hσγ]
    have h2 : S.ρ (-permLattice TwistTag.E6.perm γ) =
        -permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) :=
      hrho (-permLattice TwistTag.E6.perm γ) hγ''
    have h3 : -permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) = γ := by
      rw [show permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) =
        -permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm γ) from rfl, hσ2]
      exact neg_neg γ
    rw [h1, h2, h3]
  have hρ2Ψ : ∀ γ ∈ Ψ, S.ρ (S.ρ γ) = γ := fun γ hγ => hρ2 γ hγ.1.1
  have hρ2image : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] '' Ψ = Ψ := by
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      show S.ρ (S.ρ δ) ∈ Ψ
      rw [hρ2Ψ δ hδ]
      exact hδ
    · intro hγ
      exact ⟨γ, hγ, hρ2Ψ γ hγ⟩
  have hS_mem : 2 ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' Ψ = Ψ} :=
    ⟨by norm_num, hρ2image⟩
  have he_le : e ≤ 2 := Nat.sInf_le hS_mem
  have he_pos : 0 < e := (Nat.sInf_mem ⟨2, hS_mem⟩).1
  obtain ⟨jimg, hjimg⟩ :=
    exists_image_component_of_stable (χ := χ) (ρ := S.ρ)
      (fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ) S.frob.iform_eq i
  have hlongpos : 0 < ExcRaw.longCount 1 c := Nat.pos_of_ne_zero hlong
  have hlongpos' : 0 < (c.filter fun j => ExcRaw.tabFix1.getD j.val false = true).card :=
    hlongpos
  obtain ⟨j, hjmem⟩ := Finset.card_pos.1 hlongpos'
  have hjc : j ∈ c := (Finset.mem_filter.1 hjmem).1
  have hjfix : ExcRaw.tabFix1.getD j.val false = true := (Finset.mem_filter.1 hjmem).2
  have hσγ : permLattice TwistTag.E6.perm (e6SplitRoot j) = e6SplitRoot j :=
    (permLattice_e6SplitRoot_eq_iff j).2 hjfix
  have hγroot : IsRoot .E6 (e6SplitRoot j) := isRoot_e6SplitRoot j
  have hργ : S.ρ (e6SplitRoot j) = -e6SplitRoot j := by
    rw [hrho _ hγroot, hσγ]
    rfl
  have hγR : e6SplitRoot j ∈ R := ⟨j, hjc, Or.inl rfl⟩
  have he_ne_two : e ≠ 2 := by
    intro he2
    have hRunion : R = Ψ ∪ (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ := by
      rw [← hR']
      ext γ
      constructor
      · rintro ⟨m, ε, hε, rfl⟩
        induction m with
        | zero => exact Or.inl (by simpa using hε)
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with h | ⟨η, hη, hηeq⟩
          · exact Or.inr ⟨(S.ρ : _ → _)^[m] ε, h, rfl⟩
          · refine Or.inl ?_
            rw [← hηeq, hρ2Ψ η hη]
            exact hη
      · rintro (hγ | ⟨ε, hε, rfl⟩)
        · exact ⟨0, γ, hγ, rfl⟩
        · exact ⟨1, ε, hε, rfl⟩
    have hdisj : Disjoint Ψ ((S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ) := by
      rw [Set.disjoint_left]
      intro x hxΨ hximg
      have hij : i = jimg := eq_of_mem_componentRoots hxΨ (hjimg ▸ hximg)
      have himg : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ = Ψ := by
        rw [hjimg, ← hij]
      exact image_ne_of_two_le_componentOrbitLength (ρ := S.ρ) (Ψ := Ψ) (by omega) himg
    have hnegmem : ∀ γ ∈ Ψ, -γ ∈ Ψ := fun γ hγ => hΨcomp.neg_mem γ hγ
    have hγunion : e6SplitRoot j ∈ Ψ ∪ (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ := by
      rw [← hRunion]
      exact hγR
    rcases hγunion with hγΨ | hγimg
    · have hnegΨ : -e6SplitRoot j ∈ Ψ := hnegmem _ hγΨ
      have hnegimg : -e6SplitRoot j ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ :=
        ⟨e6SplitRoot j, hγΨ, hργ⟩
      exact Set.disjoint_left.1 hdisj hnegΨ hnegimg
    · obtain ⟨η, hηΨ, hηeq⟩ := hγimg
      have hnegΨ : -e6SplitRoot j ∈ Ψ := by
        rw [← hργ, ← hηeq, hρ2Ψ η hηΨ]
        exact hηΨ
      have hnegimg : -e6SplitRoot j ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ :=
        ⟨-η, hnegmem η hηΨ, by rw [S.frob.neg_eq, hηeq]⟩
      exact Set.disjoint_left.1 hdisj hnegΨ hnegimg
  have he1 : e = 1 := by omega
  have hρΨ : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ = Ψ := by
    have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' Ψ = Ψ} := by
      rw [← he1]
      exact Nat.sInf_mem ⟨2, hS_mem⟩
    simpa using hmem.2
  have hρmem : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hρΨ]
    exact ⟨γ, hγ, rfl⟩
  have hΨR : Ψ = R := by
    rw [← hR']
    ext γ
    constructor
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
    · rintro ⟨m, ε, hε, rfl⟩
      induction m with
      | zero => simpa using hε
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hρmem _ ih
  simpa [Ψ, R] using hΨR

theorem componentLabel_e6Split_eq_label (hS : E6SplitLangTwo S) {ι : Type}
    {a : ι → Fin Tag.E6.rank → Lˣ} (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a)) {U : Submodule (ZMod 3) (ExcRaw.V 1)}
    {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.occurs 1 U c)
    (hR : rationalRootsM S.ρ (famCharHom a) i = e6SplitCodeRoots c) {n : ℕ}
    (hn : 2 ^ n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) :
    componentLabel (compRank (componentRoots (famCharHom a) i))
        (componentRoots (famCharHom a) i).ncard
        (twistKindOf S.ρ (componentRoots (famCharHom a) i)) n = ExcRaw.label 1 c := by
  classical
  let χ := famCharHom a
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := componentRoots χ i
  let R : Set (Fin Tag.E6.rank → ℤ) := e6SplitCodeRoots c
  let long : ℕ := ExcRaw.longCount 1 c
  let e : ℕ := componentOrbitLength S.ρ Ψ
  change componentLabel (compRank Ψ) Ψ.ncard (twistKindOf S.ρ Ψ) n = ExcRaw.label 1 c
  have hq : S.D.q = 2 := hS.1
  have hrho : ∀ γ, IsRoot .E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ := hS.2.2
  have hR' : rationalRootsM S.ρ χ i = R := hR
  have hRroot : ∀ γ ∈ R, IsRoot .E6 γ := fun γ hγ => isRoot_of_mem_e6SplitCodeRoots hγ
  have hΨcomp : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hΨfin : Ψ.Finite := (finite_setOf_isRoot .E6).subset fun α hα => hα.1.1
  have hππ : ∀ j : Fin 6, TwistTag.E6.perm (TwistTag.E6.perm j) = j := by
    intro j
    fin_cases j <;> rfl
  have hπsymm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by
    ext j
    fin_cases j <;> rfl
  have hσ2 : ∀ γ : Fin Tag.E6.rank → ℤ,
      permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm γ) = γ := by
    intro γ
    funext j
    fin_cases j <;> rfl
  have hρ2 : ∀ γ, IsRoot .E6 γ → S.ρ (S.ρ γ) = γ := by
    intro γ hγ
    have hγ' : IsRoot .E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
    have hσγ : S.ρ γ = -permLattice TwistTag.E6.perm γ := hrho γ hγ
    have hγ'' : IsRoot .E6 (-permLattice TwistTag.E6.perm γ) := hσγ ▸ hγ'
    have h1 : S.ρ (S.ρ γ) = S.ρ (-permLattice TwistTag.E6.perm γ) := by rw [hσγ]
    have h2 : S.ρ (-permLattice TwistTag.E6.perm γ) =
        -permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) :=
      hrho (-permLattice TwistTag.E6.perm γ) hγ''
    have h3 : -permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) = γ := by
      rw [show permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm γ) =
        -permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm γ) from rfl, hσ2]
      exact neg_neg γ
    rw [h1, h2, h3]
  have hρ2Ψ : ∀ γ ∈ Ψ, S.ρ (S.ρ γ) = γ := fun γ hγ => hρ2 γ hγ.1.1
  have hρ2image : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] '' Ψ = Ψ := by
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      show S.ρ (S.ρ δ) ∈ Ψ
      rw [hρ2Ψ δ hδ]
      exact hδ
    · intro hγ
      exact ⟨γ, hγ, hρ2Ψ γ hγ⟩
  have hS_mem : 2 ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' Ψ = Ψ} :=
    ⟨by norm_num, hρ2image⟩
  have he_le : e ≤ 2 := Nat.sInf_le hS_mem
  have he_pos : 0 < e := (Nat.sInf_mem ⟨2, hS_mem⟩).1
  have hn_eq : n = e := by
    have h : 2 ^ n = 2 ^ e := by
      rw [hn, hq]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
  have hcne : c.Nonempty := hc.1
  have hRne : R.Nonempty := by
    obtain ⟨j, hj⟩ := hcne
    exact ⟨e6SplitRoot j, j, hj, Or.inl rfl⟩
  obtain ⟨jimg, hjimg⟩ :=
    exists_image_component_of_stable (χ := χ) (ρ := S.ρ)
      (fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ) S.frob.iform_eq i
  by_cases hlong0 : long = 0
  ·
    have hΨne : Ψ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hRempty : R = ∅ := by
        rw [← hR']
        simp [rationalRootsM, show componentRoots χ i = Ψ from rfl, h]
      exact hRne.ne_empty hRempty
    have he_ne_one : e ≠ 1 := by
      intro he1
      have hρΨ : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ = Ψ := by
        have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' Ψ = Ψ} := by
          rw [← he1]
          exact Nat.sInf_mem ⟨2, hS_mem⟩
        simpa using hmem.2
      have hρmem : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
        rw [← hρΨ]
        exact ⟨γ, hγ, rfl⟩
      have hΨR : Ψ = R := by
        rw [← hR']
        ext γ
        constructor
        · intro hγ
          exact ⟨0, γ, hγ, rfl⟩
        · rintro ⟨m, ε, hε, rfl⟩
          induction m with
          | zero => simpa using hε
          | succ m ih =>
            rw [Function.iterate_succ_apply']
            exact hρmem _ ih
      obtain ⟨Y, hYR, hYne, hYcomp, horth⟩ := e6Split_split_of_occurs hc hlong0
      have hYsub : Y ⊆ Ψ := by rwa [hΨR]
      have horth' : ∀ α ∈ Y, ∀ β ∈ Ψ, β ∉ Y → iform α β = 0 := by
        intro α hα β hβ hβY
        have hβR : β ∈ R := by rwa [hΨR] at hβ
        exact horth α hα β ⟨hβR, hβY⟩
      rcases hΨcomp.irreducible Y hYsub horth' with hYempty | hYfull
      · exact hYne.ne_empty hYempty
      · have hRdiff : R \ Y = ∅ := by
          rw [hYfull, ← hΨR]
          exact Set.diff_self
        exact hYcomp.ne_empty hRdiff
    have he2 : e = 2 := by omega
    have hn2 : n = 2 := by omega
    have hRunion : R = Ψ ∪ (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ := by
      rw [← hR']
      ext γ
      constructor
      · rintro ⟨m, ε, hε, rfl⟩
        induction m with
        | zero => exact Or.inl (by simpa using hε)
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with h | ⟨η, hη, hηeq⟩
          · exact Or.inr ⟨(S.ρ : _ → _)^[m] ε, h, rfl⟩
          · refine Or.inl ?_
            rw [← hηeq, hρ2Ψ η hη]
            exact hη
      · rintro (hγ | ⟨ε, hε, rfl⟩)
        · exact ⟨0, γ, hγ, rfl⟩
        · exact ⟨1, ε, hε, rfl⟩
    have hdisj : Disjoint Ψ ((S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ) := by
      rw [Set.disjoint_left]
      intro x hxΨ hximg
      have hij : i = jimg := eq_of_mem_componentRoots hxΨ (hjimg ▸ hximg)
      have himg : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Ψ = Ψ := by
        rw [hjimg, ← hij]
      exact image_ne_of_two_le_componentOrbitLength (ρ := S.ρ) (Ψ := Ψ) (by omega) himg
    have hRcard : R.ncard = 2 * Ψ.ncard := by
      rw [hRunion, Set.ncard_union_eq hdisj hΨfin (hΨfin.image _)]
      rw [Set.ncard_image_of_injective _ S.ρ.injective]
      ring
    have hRcard' : R.ncard = 4 * c.card := by
      have h := ncard_e6SplitCodeRoots c
      rw [h, show ExcRaw.longCount 1 c = 0 from hlong0]
      simp
    have hN : Ψ.ncard = 2 * c.card := by omega
    have htwist : twistInner Ψ
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) := by
      rw [show componentOrbitLength S.ρ Ψ = e from rfl, he2]
      refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
      show (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] γ = 1 • γ
      rw [one_smul]
      exact hρ2Ψ γ hγ
    have hkind : twistKindOf S.ρ Ψ = .inner :=
      twistKindOf_eq_inner_of_twistInner S.ρ Ψ htwist
    have htype := e6Split_type_mem_of_occurs hc
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at htype
    rcases htype with ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ |
      ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩
    ·
      have hN2 : Ψ.ncard = 2 := by
        have h2 : Ψ.ncard = 2 * 1 := by rw [hN, hcard]
        norm_num at h2
        exact h2
      have hrank : compRank Ψ = 1 := by
        have hle : compRank Ψ ≤ 6 := by
          have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) Ψ
          simpa [Tag.rank] using h
        rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
          (τ := .E6) (Or.inr (Or.inl rfl)) hΨcomp hΨne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
          ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
        · exact h1
        · rw [hN2] at h3
          have : 2 * 3 ≤ compRank Ψ * (compRank Ψ + 1) := Nat.mul_le_mul h2 (by omega)
          omega
        · rw [hN2] at h3
          have h3' : 3 ≤ compRank Ψ - 1 := by omega
          have : 2 * 4 * 3 ≤ 2 * compRank Ψ * (compRank Ψ - 1) := by
            calc 2 * 4 * 3 = 2 * 4 * 3 := rfl
              _ ≤ 2 * compRank Ψ * (compRank Ψ - 1) := by
                exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h4) h3'
          omega
        · omega
        · omega
        · omega
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.A, 1, 2⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 0 from hlong, ExcRaw.labelE6Rel]
      rw [hkind, hrank, hN2, hn2, hraw]
      exact componentLabel_inner_A (n := 2) (by norm_num)
    ·
      have hN2 : Ψ.ncard = 6 := by
        have h2 : Ψ.ncard = 2 * 3 := by rw [hN, hcard]
        norm_num at h2
        exact h2
      have hrank : compRank Ψ = 2 :=
        CFSG.StandardType.LangRat.compRank_eq_two_of_ncard_eq_six hΨcomp hN2
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.A, 2, 2⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 0 from hlong, ExcRaw.labelE6Rel]
      rw [hkind, hrank, hN2, hn2, hraw]
      exact componentLabel_inner_A (n := 2) (by norm_num)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

  ·
    have hΨR : Ψ = R :=
      componentRoots_eq_e6SplitCodeRoots_of_longCount_ne_zero hS hT i hR
        (by simpa [long] using hlong0)
    have hstab : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := by
      intro γ hγ
      have hmem : S.ρ γ ∈ rationalRootsM S.ρ χ i := by
        refine ⟨1, γ, hγ, ?_⟩
        rw [Function.iterate_one]
      rwa [hR', ← hΨR] at hmem
    have hmem1 : 1 ∈ {s : ℕ | 0 < s ∧
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' Ψ = Ψ} := by
      refine ⟨Nat.one_pos, ?_⟩
      rw [Function.iterate_one]
      exact ((hΨfin.injOn_iff_bijOn_of_mapsTo hstab).1 S.ρ.injective.injOn).image_eq
    have he1 : e = 1 := by
      refine le_antisymm (Nat.sInf_le hmem1) ?_
      exact Nat.succ_le_of_lt (Nat.sInf_mem ⟨1, hmem1⟩).1
    have he1R : componentOrbitLength S.ρ R = 1 := by
      rw [← hΨR]
      exact he1
    have hn1 : n = 1 := by omega
    let f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) :=
      fun γ => -permLattice TwistTag.E6.perm γ
    have hfg : ∀ γ ∈ R, S.ρ γ = f γ := fun γ hγ => hrho γ (hRroot γ hγ)
    have htwist_iff : twistInner R S.ρ ↔ twistInner R f := by
      constructor
      · rintro ⟨w, hw, h⟩
        exact ⟨w, hw, fun γ hγ => by rw [← hfg γ hγ, h γ hγ]⟩
      · rintro ⟨w, hw, h⟩
        exact ⟨w, hw, fun γ hγ => by rw [hfg γ hγ, h γ hγ]⟩
    have htype : (c.card, long) ∈
        ({(1, 0), (3, 0), (1, 1), (3, 3), (4, 2), (9, 3), (9, 6), (24, 12)} : Finset (ℕ × ℕ)) := by
      have := e6Split_type_mem_of_occurs hc
      simpa [long] using this
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at htype
    rcases htype with ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ |
      ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩ | ⟨hcard, hlong⟩
    · omega
    · omega
    ·
      have hNR : R.ncard = 2 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 1 + 4 * (1 - 1) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 1 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 1 := by
        have hcomp : IsRootComponent R := by rwa [← hΨR]
        have hle : compRank R ≤ 6 := by
          have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) R
          simpa [Tag.rank] using h
        rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
          (τ := .E6) (Or.inr (Or.inl rfl)) hcomp hRne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
          ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
        · exact h1
        · rw [hNR] at h3
          have : 2 * 3 ≤ compRank R * (compRank R + 1) := Nat.mul_le_mul h2 (by omega)
          omega
        · rw [hNR] at h3
          have h3' : 3 ≤ compRank R - 1 := by omega
          have : 2 * 4 * 3 ≤ 2 * compRank R * (compRank R - 1) := by
            calc 2 * 4 * 3 = 2 * 4 * 3 := rfl
              _ ≤ 2 * compRank R * (compRank R - 1) := by
                exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h4) h3'
          omega
        · omega
        · omega
        · omega
      have hkindR : twistKindOf S.ρ R = .inner :=
        twistKindOf_eq_inner_of_compRank_eq_one S.ρ R hrankR
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.A, 1, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 1 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_inner_A (n := 1) (by norm_num)
    ·
      have hNR : R.ncard = 6 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 3 + 4 * (3 - 3) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 3 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 2 :=
        CFSG.StandardType.LangRat.compRank_eq_two_of_ncard_eq_six
          (by rwa [← hΨR]) hNR
      have hnot : ¬ twistInner R (fun γ => -permLattice TwistTag.E6.perm γ) :=
        e6Split_not_twistInner_of_occurs hc
          (Or.inl (by rw [hcard, show ExcRaw.longCount 1 c = 3 from hlong]))
      have hni : ¬ twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ R]) := by
        rw [he1R, Function.iterate_one]
        exact fun h => hnot (htwist_iff.1 h)
      have hkindR : twistKindOf S.ρ R = .suN :=
        twistKindOf_eq_suN S.ρ R hni (by omega) (by rw [hrankR, hNR])
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.twA, 2, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 3 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_suN 2 6 1
    ·
      have hNR : R.ncard = 12 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 2 + 4 * (4 - 2) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 2 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 3 := by
        have hcomp : IsRootComponent R := by rwa [← hΨR]
        have hle : compRank R ≤ 6 := by
          have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) R
          simpa [Tag.rank] using h
        rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
          (τ := .E6) (Or.inr (Or.inl rfl)) hcomp hRne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
          ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
        · have h2 : R.ncard = 2 :=
            CFSG.StandardType.LangRat.j4d_rank_one_ncard (τ := .E6)
              (Or.inr (Or.inl rfl)) hcomp h1
          omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · omega
        · omega
        · omega
      have hinnerR : twistInner R (fun γ => -permLattice TwistTag.E6.perm γ) :=
        e6Split_twistInner_of_occurs hc
          (Or.inl (by rw [hcard, show ExcRaw.longCount 1 c = 2 from hlong]))
      have hin : twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ R]) := by
        rw [he1R, Function.iterate_one]
        exact htwist_iff.2 hinnerR
      have hkindR : twistKindOf S.ρ R = .inner :=
        twistKindOf_eq_inner_of_twistInner S.ρ R hin
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.A, 3, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 2 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_inner_A (n := 1) (by norm_num)
    ·
      have hNR : R.ncard = 30 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 3 + 4 * (9 - 3) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 3 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 5 := by
        have hcomp : IsRootComponent R := by rwa [← hΨR]
        have hle : compRank R ≤ 6 := by
          have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) R
          simpa [Tag.rank] using h
        rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
          (τ := .E6) (Or.inr (Or.inl rfl)) hcomp hRne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
          ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
        · have h2 : R.ncard = 2 :=
            CFSG.StandardType.LangRat.j4d_rank_one_ncard (τ := .E6)
              (Or.inr (Or.inl rfl)) hcomp h1
          omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · omega
        · omega
        · omega
      have hinnerR : twistInner R (fun γ => -permLattice TwistTag.E6.perm γ) :=
        e6Split_twistInner_of_occurs hc
          (Or.inr (Or.inl (by rw [hcard, show ExcRaw.longCount 1 c = 3 from hlong])))
      have hin : twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ R]) := by
        rw [he1R, Function.iterate_one]
        exact htwist_iff.2 hinnerR
      have hkindR : twistKindOf S.ρ R = .inner :=
        twistKindOf_eq_inner_of_twistInner S.ρ R hin
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.A, 5, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 3 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_inner_A (n := 1) (by norm_num)
    ·
      have hNR : R.ncard = 24 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 6 + 4 * (9 - 6) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 6 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 4 :=
        compRank_eq_four_of_ncard_eq_24 (by rwa [← hΨR]) hRne hNR
      have hnot : ¬ twistInner R (fun γ => -permLattice TwistTag.E6.perm γ) :=
        e6Split_not_twistInner_of_occurs hc
          (Or.inr (by rw [hcard, show ExcRaw.longCount 1 c = 6 from hlong]))
      have hni : ¬ twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ R]) := by
        rw [he1R, Function.iterate_one]
        exact fun h => hnot (htwist_iff.1 h)
      have hin2 : twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ R]) := by
        rw [he1R, mul_one]
        refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
        show (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] γ = 1 • γ
        rw [one_smul]
        exact hρ2 γ (hRroot γ hγ)
      have hkindR : twistKindOf S.ρ R = .twoD :=
        twistKindOf_eq_twoD_of_D4 S.ρ R hni hrankR hNR hin2
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.twD, 4, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 6 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_twoD 4 24 1
    ·
      have hNR : R.ncard = 72 := by
        have h := ncard_e6SplitCodeRoots c
        have h2 : R.ncard = 2 * 12 + 4 * (24 - 12) := by
          rw [show R = e6SplitCodeRoots c from rfl, h, hcard,
            show ExcRaw.longCount 1 c = 12 from hlong]
        norm_num at h2
        exact h2
      have hrankR : compRank R = 6 := by
        have hcomp : IsRootComponent R := by rwa [← hΨR]
        have hle : compRank R ≤ 6 := by
          have h := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := .E6) R
          simpa [Tag.rank] using h
        rcases CFSG.StandardType.LieKnownR2.ExcPos.compRank_ncard_ade
          (τ := .E6) (Or.inr (Or.inl rfl)) hcomp hRne with h1 | ⟨h2, h3⟩ | ⟨h4, h3⟩ |
          ⟨h6, h3⟩ | ⟨h7, h3⟩ | ⟨h8, h3⟩
        · have h2 : R.ncard = 2 :=
            CFSG.StandardType.LangRat.j4d_rank_one_ncard (τ := .E6)
              (Or.inr (Or.inl rfl)) hcomp h1
          omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · rw [hNR] at h3
          set r := compRank R with hr
          rw [← hr] at *
          interval_cases r <;> omega
        · omega
        · omega
        · omega
      have hinnerR : twistInner R (fun γ => -permLattice TwistTag.E6.perm γ) :=
        e6Split_twistInner_of_occurs hc
          (Or.inr (Or.inr (by rw [hcard, show ExcRaw.longCount 1 c = 12 from hlong])))
      have hin : twistInner R
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ R]) := by
        rw [he1R, Function.iterate_one]
        exact htwist_iff.2 hinnerR
      have hkindR : twistKindOf S.ρ R = .inner :=
        twistKindOf_eq_inner_of_twistInner S.ρ R hin
      have hraw : ExcRaw.label 1 c = ⟨LargeEvenLieTag.E6, 0, 1⟩ := by
        have h : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) := rfl
        simp [h, hcard, show ExcRaw.longCount 1 c = 12 from hlong, ExcRaw.labelE6Rel]
      rw [hΨR, hkindR, hrankR, hNR, hn1, hraw]
      exact componentLabel_inner_E6 (N := 72) 1 rfl


end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
