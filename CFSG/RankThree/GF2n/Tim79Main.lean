module

public import CFSG.RankThree.GF2n.Tim79Hyper

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

theorem Hyp79.isCentralProductOfL3_classGroup (H : Hyp79 M V Q) {U : Subgroup G}
    (hUg : ∃ g : G, U = conjSubgroup g V) (hUQ : U ≤ Q) (hUV : U ≠ V) {n : ℕ}
    (hVn : Nat.card V = 2 ^ n) (D : MulData V U Q (GaloisField 2 n)) :
    ∃ k : ℕ, IsCentralProductOfL3 (classGroup V Q D.γ) V n k := by
  obtain ⟨g, rfl⟩ := hUg
  obtain ⟨n', hVn', D', M₀, S₁, S₂, hcompl, hS₁, hS₂⟩ := H.exists_hyperbolic_quadModel hUV hUQ
  have hnn : n' = n := Nat.pow_right_injective (le_refl 2) (hVn'.symm.trans hVn)
  subst hnn
  have hcl : classOf V Q D'.γ = classOf V Q D.γ :=
    classOf_eq_of_mem D (mem_classOf_self D ⟨g, rfl⟩ hUQ hUV) D'
  have hQF : classGroup V Q D'.γ = classGroup V Q D.γ := by
    unfold classGroup
    rw [hcl]
  obtain ⟨k, hk⟩ := isCentralProductOfL3_of_quadModel (QF := classGroup V Q D'.γ) (V := V)
    (γ := D'.γ) V_le_classGroup
    (fun v hv y hy => H.V_central hv (classGroup_le H.V_le_Q hy)) D'.γ_add D'.γ_inj D'.γ_surj M₀
    ⟨S₁, S₂, hcompl, hS₁, hS₂⟩ (classGroup_ne_of_mem (mem_classOf_self D' ⟨g, rfl⟩ hUQ hUV))
  refine ⟨k, ?_⟩
  rw [← hQF]
  exact hk

theorem commute_of_closure {S T : Set G} (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure T ≤ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.closure_le _).mpr fun t ht =>
        Subgroup.mem_centralizer_iff.mpr fun z hz => by
          rw [Set.mem_singleton_iff.mp hz]
          exact h x hx t ht
    have := Subgroup.mem_centralizer_iff.mp (hle hy) x rfl
    exact this
  intro x hx y hy
  have hle : Subgroup.closure S ≤
      Subgroup.centralizer ((Subgroup.closure T : Subgroup G) : Set G) :=
    (Subgroup.closure_le _).mpr fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => (h1 s hs z hz).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem isCentralProductOf_of_fintype {P : Subgroup G → Prop} {Q Z : Subgroup G} {ι : Type}
    [Fintype ι] [Nonempty ι] (D : ι → Subgroup G) (hle : ∀ i, D i ≤ Q) (hP : ∀ i, P (D i))
    (hZ : ∀ i, (Subgroup.center ↥(D i)).map (D i).subtype = Z)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ D i, ∀ y ∈ D j, x * y = y * x) (hgen : ⨆ i, D i = Q) :
    IsCentralProductOf P Q Z (Fintype.card ι) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card_pos, fun i => D (e.symm i), fun i => hle _, fun i => hP _,
    fun i => hZ _, fun i j hij => hc _ _ (fun h => hij (e.symm.injective h)), ?_⟩
  rw [e.symm.iSup_comp (g := D)]
  exact hgen

private def Opp (V Q : Subgroup G) : Set (Subgroup G) :=
  {U | (∃ g : G, U = conjSubgroup g V) ∧ U ≤ Q ∧ U ≠ V}

private theorem exists_datum (H : Hyp79 M V Q) {n : ℕ} (hVn : Nat.card V = 2 ^ n)
    {U : Subgroup G} (hUg : ∃ g : G, U = conjSubgroup g V) (hUQ : U ≤ Q) (hUV : U ≠ V) :
    Nonempty (MulData V U Q (GaloisField 2 n)) := by
  obtain ⟨g, rfl⟩ := hUg
  obtain ⟨n', hVn', ⟨D⟩⟩ := H.exists_mulData hUV hUQ
  have hnn : n' = n := Nat.pow_right_injective (le_refl 2) (hVn'.symm.trans hVn)
  subst hnn
  exact ⟨D⟩

theorem Hyp79.exists_isCentralProductOfL3 (H : Hyp79 M V Q) :
    ∃ n k : ℕ, Nat.card V = 2 ^ n ∧ IsCentralProductOfL3 Q V n k := by
  classical
  obtain ⟨g₀, hg₀V, hg₀Q⟩ := H.exists_opposite
  obtain ⟨n, hVn, -⟩ := H.exists_mulData hg₀V hg₀Q
  obtain ⟨Dm⟩ : Nonempty (∀ U : ↥(Opp V Q), MulData V U.1 Q (GaloisField 2 n)) :=
    ⟨fun U => Classical.choice (exists_datum H hVn U.2.1 U.2.2.1 U.2.2.2)⟩
  obtain ⟨f, hf⟩ : ∃ f : ↥(Opp V Q) → Set (Subgroup G),
      ∀ U, f U = classOf V Q (Dm U).γ := ⟨fun U => classOf V Q (Dm U).γ, fun _ => rfl⟩
  have hfself : ∀ U : ↥(Opp V Q), U.1 ∈ f U := fun U => by
    rw [hf]
    exact mem_classOf_self (Dm U) U.2.1 U.2.2.1 U.2.2.2
  have hfeq : ∀ U U' : ↥(Opp V Q), U'.1 ∈ f U → f U' = f U := fun U U' h => by
    rw [hf, hf]
    rw [hf] at h
    exact classOf_eq_of_mem (Dm U) h (Dm U')
  let ι : Type := ↥(Set.range f)
  haveI : Finite ι := (Set.finite_range f).to_subtype
  haveI : Fintype ι := Fintype.ofFinite ι
  let U₀ : ↥(Opp V Q) := ⟨conjSubgroup g₀ V, ⟨g₀, rfl⟩, hg₀Q, hg₀V⟩
  haveI : Nonempty ι := ⟨⟨f U₀, U₀, rfl⟩⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : ι → ↥(Opp V Q), ∀ c, f (rep c) = c.1 :=
    ⟨fun c => Classical.choose c.2, fun c => Classical.choose_spec c.2⟩
  have hcp : ∀ c : ι, ∃ k : ℕ,
      IsCentralProductOfL3 (classGroup V Q (Dm (rep c)).γ) V n k := fun c =>
    H.isCentralProductOfL3_classGroup (rep c).2.1 (rep c).2.2.1 (rep c).2.2.2 hVn (Dm (rep c))
  choose k hk using hcp
  choose Df hDf using fun c => (hk c).2
  have hFQ : ∀ c : ι, classGroup V Q (Dm (rep c)).γ ≤ Q := fun c => classGroup_le H.V_le_Q
  have hFcomm : ∀ c c' : ι, c ≠ c' → ∀ x ∈ classGroup V Q (Dm (rep c)).γ,
      ∀ y ∈ classGroup V Q (Dm (rep c')).γ, x * y = y * x := by
    intro c c' hcc' x hx y hy
    refine commute_of_closure ?_ x hx y hy
    rintro x (hx | hx) y (hy | hy)
    · exact H.V_central hx (H.V_le_Q hy)
    · obtain ⟨U', hU', hyU'⟩ := Set.mem_iUnion₂.mp hy
      exact H.V_central hx (hU'.2.1 hyU')
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
      exact (H.V_central hy (hU.2.1 hxU)).symm
    · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨U', hU', hyU'⟩ := Set.mem_iUnion₂.mp hy
      refine H.commute_of_not_class (Dm (rep c)) hU hU'.1 hU'.2.1 hU'.2.2.1 ?_ x hxU y hyU'
      intro hmem
      apply hcc'
      have h1 : f (rep c) = f (rep c') := by
        rw [hf, hf]
        exact classOf_eq_of_mem_of_mem hmem hU'
      exact Subtype.ext ((hrep c).symm.trans (h1.trans (hrep c')))
  let J : Type := Σ c : ι, Fin (k c)
  haveI : Nonempty J := ⟨⟨Classical.arbitrary ι, ⟨0, (hk _).1⟩⟩⟩
  haveI : Fintype J := inferInstance
  refine ⟨n, Fintype.card J, hVn, isCentralProductOf_of_fintype (fun j : J => Df j.1 j.2)
    ?_ ?_ ?_ ?_ ?_⟩
  · intro j
    exact ((hDf j.1).1 j.2).trans (hFQ j.1)
  · intro j
    exact (hDf j.1).2.1 j.2
  · intro j
    exact (hDf j.1).2.2.1 j.2
  · rintro ⟨c, i⟩ ⟨c', i'⟩ hne x hx y hy
    by_cases hcc : c = c'
    · subst hcc
      have hii : i ≠ i' := fun h => hne (by subst h; rfl)
      exact (hDf c).2.2.2.1 i i' hii x hx y hy
    · exact hFcomm c c' hcc x ((hDf c).1 i hx) y ((hDf c').1 i' hy)
  ·
    apply le_antisymm
    · exact iSup_le fun j => ((hDf j.1).1 j.2).trans (hFQ j.1)
    · refine H.gen.le.trans (iSup₂_le fun g hg => ?_)
      have hup : ∀ c : ι, classGroup V Q (Dm (rep c)).γ ≤ ⨆ j : J, Df j.1 j.2 := fun c => by
        rw [← (hDf c).2.2.2.2]
        exact iSup_le fun i => le_iSup (fun j : J => Df j.1 j.2) ⟨c, i⟩
      by_cases hgV : conjSubgroup g V = V
      · obtain ⟨c₀⟩ : Nonempty ι := inferInstance
        exact hgV.le.trans (V_le_classGroup.trans (hup c₀))
      · let U : ↥(Opp V Q) := ⟨conjSubgroup g V, ⟨g, rfl⟩, hg, hgV⟩
        let c : ι := ⟨f U, U, rfl⟩
        have hUc : conjSubgroup g V ∈ classOf V Q (Dm (rep c)).γ := by
          rw [← hf, hrep c]
          exact hfself U
        exact (le_classGroup_of_mem hUc).trans (hup c)

end CFSG.RankThree.GF2n.Tim79

namespace CFSG.RankThree.GF2n

theorem tim79 : Tim79Statement :=
  fun _ _ _ _ _ _ H => H.exists_isCentralProductOfL3

end CFSG.RankThree.GF2n
