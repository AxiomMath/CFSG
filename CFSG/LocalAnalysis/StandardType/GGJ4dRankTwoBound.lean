module

public import CFSG.LocalAnalysis.StandardType.GGJ4dComponents
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankOne
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankTwo
public import CFSG.LocalAnalysis.StandardType.GGJ4dOrthogonalRank

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {τ : Tag}

private theorem one_le_compRank_of_nonempty
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hroot : ∀ x ∈ Ψ, IsRoot τ x) (hne : Ψ.Nonempty) :
    1 ≤ compRank Ψ := by
  classical
  obtain ⟨α, hαΨ⟩ := hne
  have hαroot : IsRoot τ α := hroot α hαΨ
  have hα0 : α ≠ 0 := hαroot.ne_zero
  let f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun γ i => (γ i : ℚ)
  have hαne : f α ≠ 0 := by
    intro h
    apply hα0
    funext i
    have hi := congrFun h i
    simpa [f] using hi
  have hspan : Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ)) ≤
      Submodule.span ℚ (f '' Ψ) := by
    rw [Submodule.span_le]
    rintro x rfl
    exact Submodule.subset_span ⟨α, hαΨ, rfl⟩
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_singleton hαne] at hle
  simpa [compRank, f] using hle

private def RConn (F : Set (Fin τ.rank → ℤ)) (x y : Fin τ.rank → ℤ) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ iform a b ≠ 0) x y

private def RComp (F : Set (Fin τ.rank → ℤ)) (α : Fin τ.rank → ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {β | β ∈ F ∧ RConn F α β}

private theorem mem_RComp {F : Set (Fin τ.rank → ℤ)} {α x : Fin τ.rank → ℤ} :
    x ∈ RComp F α ↔ x ∈ F ∧ RConn F α x :=
  Iff.rfl

private theorem RConn_symm
    {F : Set (Fin τ.rank → ℤ)} {x y : Fin τ.rank → ℤ} (h : RConn F x y) :
    RConn F y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, by
        rw [iform_comm]
        exact hstep.2.2⟩ ih

private theorem mem_of_RConn_of_horth
    {F S : Set (Fin τ.rank → ℤ)}
    (horth : ∀ x ∈ S, ∀ y ∈ F, y ∉ S → iform x y = 0)
    {x y : Fin τ.rank → ℤ} (h : RConn F x y) (hx : x ∈ S) :
    y ∈ S := by
  induction h with
  | refl => exact hx
  | @tail b c _ hstep ih =>
      have hbS : b ∈ S := ih
      by_contra hcS
      exact hstep.2.2 (horth b hbS c hstep.2.1 hcS)

private theorem isRootComponent_of_RComp_eq
    {F : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (hFroot : ∀ x ∈ F, IsRoot τ x) (hFneg : ∀ x ∈ F, -x ∈ F)
    (hFadd : ∀ x ∈ F, ∀ y ∈ F, IsRoot τ (x + y) → x + y ∈ F)
    (hFrefl : ∀ x ∈ F, ∀ y ∈ F, rootReflection y • x ∈ F)
    (hCF : RComp F α = F) :
    IsRootComponent F := by
  refine ⟨hFroot, hFneg, hFadd, hFrefl, ?_⟩
  intro S hSsub horth
  by_cases hS : S = ∅
  · exact Or.inl hS
  · right
    obtain ⟨x, hxS⟩ := Set.nonempty_iff_ne_empty.2 hS
    by_cases hαS : α ∈ S
    · apply Set.Subset.antisymm hSsub
      intro y hyF
      have hyC : y ∈ RComp F α := by
        rw [hCF]
        exact hyF
      exact mem_of_RConn_of_horth horth (mem_RComp.mp hyC).2 hαS
    · exfalso
      have hxC : x ∈ RComp F α := by
        rw [hCF]
        exact hSsub hxS
      have hconn : RConn F x α := RConn_symm (mem_RComp.mp hxC).2
      exact hαS (mem_of_RConn_of_horth horth hconn hxS)

theorem ncard_eq_two_of_closed_rank_one
    (hτ : SimplyLacedTag τ) {D : Set (Fin τ.rank → ℤ)}
    (hDroot : ∀ x ∈ D, IsRoot τ x)
    (hDneg : ∀ x ∈ D, -x ∈ D)
    (hDne : D.Nonempty) (hrank : compRank D = 1) :
    D.ncard = 2 := by
  classical
  obtain ⟨α, hαD⟩ := hDne
  have hαroot : IsRoot τ α := hDroot α hαD
  have hαα : iform α α = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hαroot
  have hα0 : α ≠ 0 := hαroot.ne_zero
  have hαne : α ≠ -α := by
    intro h
    apply hα0
    funext i
    have hi := congrFun h i
    simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
    omega
  let f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun γ i => (γ i : ℚ)
  have hfinj : Function.Injective f := by
    intro x y h
    funext i
    exact Int.cast_injective (congrFun h i)
  let S : Submodule ℚ (Fin τ.rank → ℚ) := Submodule.span ℚ (f '' D)
  have hS : Module.finrank ℚ S = 1 := by
    simpa [compRank, S, f] using hrank
  have hαS : f α ∈ S := Submodule.subset_span ⟨α, hαD, rfl⟩
  have hαne' : f α ≠ 0 := by
    intro h
    apply hα0
    funext i
    simpa [f] using congrFun h i
  let T : Submodule ℚ (Fin τ.rank → ℚ) := Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ))
  have hTle : T ≤ S := by
    change Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ)) ≤ S
    rw [Submodule.span_le]
    rintro x rfl
    exact hαS
  have hTfin : Module.finrank ℚ T = 1 := by
    change Module.finrank ℚ (Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ))) = 1
    exact finrank_span_singleton hαne'
  have hT_eq : T = S := Submodule.eq_of_le_of_finrank_eq hTle (by rw [hTfin, hS])
  have hmem : ∀ β ∈ D, β = α ∨ β = -α := by
    intro β hβD
    have hβroot : IsRoot τ β := hDroot β hβD
    have hββ : iform β β = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hβroot
    have hβS : f β ∈ S := Submodule.subset_span ⟨β, hβD, rfl⟩
    have hβT : f β ∈ T := by
      rw [hT_eq]
      exact hβS
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hβT
    let p : ℤ := c.num
    let q : ℤ := c.den
    have hq0 : (q : ℚ) ≠ 0 := by
      dsimp [q]
      exact_mod_cast c.den_ne_zero
    have hcq : c = (p : ℚ) / (q : ℚ) := by
      dsimp [p, q]
      push_cast
      exact (Rat.num_div_den c).symm
    have hcq' : ((p : ℚ) / (q : ℚ)) • f α = f β := by
      rw [← hcq]
      exact hc
    have hmul : (p : ℚ) • f α = (q : ℚ) • f β := by
      have h := congrArg (fun v => (q : ℚ) • v) hcq'
      rw [smul_smul, mul_div_cancel₀ (p : ℚ) hq0] at h
      exact h
    have hEqf : f (p • α) = f (q • β) := by
      funext i
      have hi := congrFun hmul i
      simp only [f, Pi.smul_apply, smul_eq_mul] at hi ⊢
      push_cast at hi ⊢
      exact hi
    have hZ : p • α = q • β := by
      funext i
      have hi := congrFun hEqf i
      simp only [f, Pi.smul_apply, smul_eq_mul] at hi ⊢
      exact_mod_cast hi
    have hnorm : q ^ 2 = p ^ 2 := by
      have h1 : iform (q • β) (q • β) = iform (p • α) (p • α) := by rw [hZ]
      rw [iform_smul_left, iform_smul_right, iform_smul_left, iform_smul_right,
        hββ, hαα] at h1
      nlinarith
    have hpq : p = q ∨ p = -q :=
      eq_or_eq_neg_of_sq_eq_sq p q (by rw [hnorm])
    have hc1 : c = 1 ∨ c = -1 := by
      rcases hpq with h | h
      · left
        rw [hcq, h]
        exact div_self hq0
      · right
        rw [hcq, h]
        push_cast
        exact neg_div_self hq0
    have hfβ : f β = c • f α := hc.symm
    rcases hc1 with rfl | rfl
    · left
      exact hfinj (by simpa using hfβ)
    · right
      exact hfinj (by
        rw [hfβ]
        funext i
        simp [f])
  have hset : D = ({α, -α} : Set (Fin τ.rank → ℤ)) := by
    apply Set.Subset.antisymm
    · intro β hβ
      rcases hmem β hβ with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · intro β hβ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
      rcases hβ with rfl | rfl
      · exact hαD
      · exact hDneg α hαD
  rw [hset, Set.ncard_pair hαne]

theorem j4d_closed_ncard_le_six_of_compRank_le_two
    {τ : Tag} {F : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (hτ : SimplyLacedTag τ)
    (hFroot : ∀ x ∈ F, IsRoot τ x) (hFneg : ∀ x ∈ F, -x ∈ F)
    (hFadd : ∀ x ∈ F, ∀ y ∈ F, IsRoot τ (x + y) → x + y ∈ F)
    (hFrefl : ∀ x ∈ F, ∀ y ∈ F, rootReflection y • x ∈ F)
    (hFfin : F.Finite) (hα : α ∈ F) (hr : compRank F ≤ 2) :
    F.ncard ≤ 6 := by
  classical
  by_cases hFcomp : IsRootComponent F
  ·
    have hpos : 0 < compRank F :=
      lt_of_lt_of_le Nat.zero_lt_one (one_le_compRank_of_nonempty hFroot ⟨α, hα⟩)
    have hcases : compRank F = 1 ∨ compRank F = 2 := by omega
    rcases hcases with h1 | h2
    · have hcount : F.ncard = 2 := j4d_rank_one_ncard hτ hFcomp h1
      omega
    · have hcount : F.ncard = 6 := j4d_rank_two_ncard hτ hFcomp h2
      omega
  ·
    let C : Set (Fin τ.rank → ℤ) := RComp F α
    let D : Set (Fin τ.rank → ℤ) := F \ C
    have hCsub : C ⊆ F := by
      intro x hx
      exact (mem_RComp.mp hx).1
    have hCα : α ∈ C := by
      change α ∈ RComp F α
      exact mem_RComp.mpr ⟨hα, Relation.ReflTransGen.refl⟩
    have hCne : C ≠ F := by
      intro hCF
      apply hFcomp
      exact isRootComponent_of_RComp_eq hFroot hFneg hFadd hFrefl hCF
    have hCroot : ∀ x ∈ C, IsRoot τ x := fun x hx => hFroot x (hCsub hx)
    have hCneg : ∀ x ∈ C, -x ∈ C := by
      intro x hx
      have hxF : x ∈ F := hCsub hx
      have hxroot : IsRoot τ x := hFroot x hxF
      have hxx : iform x x ≠ 0 := (iform_self_pos_of_isRoot hxroot).ne'
      have hform : iform x (-x) ≠ 0 := by
        intro h
        have h' : iform x (-x) = -iform x x := by
          rw [← neg_one_smul ℤ x, iform_smul_right]
          ring
        rw [h'] at h
        exact hxx (neg_eq_zero.mp h)
      exact mem_RComp.mpr
        ⟨hFneg x hxF, (mem_RComp.mp hx).2.tail ⟨hxF, hFneg x hxF, hform⟩⟩
    have hDsub : D ⊆ F := by
      intro x hx
      exact Set.mem_of_mem_sdiff hx
    have hDroot : ∀ x ∈ D, IsRoot τ x := fun x hx => hFroot x (hDsub hx)
    have hDneg : ∀ x ∈ D, -x ∈ D := by
      intro x hx
      have hxF : x ∈ F := hDsub hx
      have hxC : x ∉ C := Set.notMem_of_mem_sdiff hx
      change -x ∈ F \ C
      refine ⟨hFneg x hxF, ?_⟩
      intro hnegC
      exact hxC (by simpa using hCneg (-x) hnegC)
    have hDne : D.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hDempty
      apply hCne
      have hsub : F ⊆ C := by
        have hDempty' : F \ C = ∅ := by simpa [D] using hDempty
        exact Set.sdiff_eq_empty.mp hDempty'
      exact Set.Subset.antisymm hCsub hsub
    have horthCD : ∀ x ∈ C, ∀ y ∈ D, iform x y = 0 := by
      intro x hx y hy
      have hxF : x ∈ F := hCsub hx
      have hyF : y ∈ F := hDsub hy
      have hyC : y ∉ C := Set.notMem_of_mem_sdiff hy
      by_contra hne
      have hxconn : RConn F α x := (mem_RComp.mp hx).2
      exact hyC (mem_RComp.mpr ⟨hyF, hxconn.tail ⟨hxF, hyF, hne⟩⟩)
    let Ψ : Fin 2 → Set (Fin τ.rank → ℤ) := fun i => if i = 0 then C else D
    have horth : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        ∀ j ∈ (Finset.univ : Finset (Fin 2)), i ≠ j →
          ∀ x ∈ Ψ i, ∀ y ∈ Ψ j, iform x y = 0 := by
      intro i _ j _ hij x hx y hy
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa [Ψ] using horthCD x hx y hy
      · simpa [Ψ, iform_comm] using horthCD y hy x hx
      · exact absurd rfl hij
    have hUnion : (⋃ i ∈ (Finset.univ : Finset (Fin 2)), Ψ i) = C ∪ D := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl (by simpa [Ψ] using hi)
        · exact Or.inr (by simpa [Ψ] using hi)
      · rintro (hx | hx)
        · exact ⟨0, by simpa [Ψ] using hx⟩
        · exact ⟨1, by simpa [Ψ] using hx⟩
    have hCunionD : C ∪ D = F := by
      refine Set.Subset.antisymm (Set.union_subset hCsub hDsub) ?_
      intro x hx
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr ⟨hx, hxC⟩
    have hadd := compRank_iUnion_finset_eq_sum
      (s := (Finset.univ : Finset (Fin 2))) Ψ horth
    rw [hUnion, hCunionD] at hadd
    have hsum : compRank F = compRank C + compRank D := by
      simpa [Ψ, Fin.sum_univ_two] using hadd
    have hCpos : 1 ≤ compRank C := one_le_compRank_of_nonempty hCroot ⟨α, hCα⟩
    have hDpos : 1 ≤ compRank D := one_le_compRank_of_nonempty hDroot hDne
    have hle : compRank C + compRank D ≤ 2 := by
      rw [← hsum]
      exact hr
    have hCrank : compRank C = 1 := by omega
    have hDrank : compRank D = 1 := by omega
    have hCcount : C.ncard = 2 :=
      ncard_eq_two_of_closed_rank_one hτ hCroot hCneg ⟨α, hCα⟩ hCrank
    have hDcount : D.ncard = 2 :=
      ncard_eq_two_of_closed_rank_one hτ hDroot hDneg hDne hDrank
    have hdisj : Disjoint C D := by
      rw [Set.disjoint_left]
      intro x hxC hxD
      exact (Set.notMem_of_mem_sdiff hxD) hxC
    have hCfin : C.Finite := hFfin.subset hCsub
    have hDfin : D.Finite := hFfin.subset hDsub
    rw [← hCunionD, Set.ncard_union_eq hdisj hCfin hDfin, hCcount, hDcount]
    norm_num

end CFSG.StandardType.LangRat

end
