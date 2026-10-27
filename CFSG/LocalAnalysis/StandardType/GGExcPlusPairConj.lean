module

public import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcConj
import CFSG.LocalAnalysis.StandardType.GGA2Conj
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthE
import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggExcPlusModel_isWeylMatrixE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    GGIsWeylMatrixE (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) := by
  rcases hτ with rfl | rfl | rfl
  · have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
    exact Or.inl ⟨Equiv.refl _, (coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6) (M := CoxeterMatrix.E₆)
      (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)).trans
      (ggCoxeterMatrix_reindex_refl _).symm⟩
  · exact Or.inr (Or.inl ⟨Equiv.refl _,
      CFSG.StandardType.FrameRoute.coxeterE7_eq.symm.trans (ggCoxeterMatrix_reindex_refl _).symm⟩)
  · exact Or.inr (Or.inr ⟨Equiv.refl _,
      CFSG.StandardType.FrameRoute.coxeterE8_eq.symm.trans (ggCoxeterMatrix_reindex_refl _).symm⟩)

private theorem ggExcPlusModel_exists_labels {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∃ i j : Fin τ.rank,
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j = 2) ∧
    ∃ i j : Fin τ.rank,
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j = 3 := by
  rcases ggExcPlusModel_isWeylMatrixE hτ with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ <;> rw [he] <;>
    refine ⟨⟨e 0, e 1, ?_⟩, ⟨e 0, e 2, ?_⟩⟩ <;>
    rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> decide

private theorem ggExcPlusModel_refl_order3 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {t t' : WeylGroup τ}
    (ht : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t = w * simple τ i * w⁻¹)
    (ht' : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t' = w * simple τ i * w⁻¹)
    (hncomm : ¬ Commute t t') :
    (t * t') ^ 3 = 1 := by
  have hconn : GGSimplyLacedConnected
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)) :=
    ggSimplyLacedConnected_of_weyl (ggExcPlusModel_isWeylMatrixE hτ).isWeylMatrix
      (ggExcPlusModel_isWeylMatrixE hτ).le_three
  obtain ⟨w, i, ht_eq⟩ := ht
  obtain ⟨w', i', ht'_eq⟩ := ht'
  have h1 : w * (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i *
      w⁻¹ = t := ht_eq.symm
  have h2 : w' * (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).simple i' *
      w'⁻¹ = t' := ht'_eq.symm
  have hord := ggWeyl_refl_order3 (A := Tag.cartan τ) (isFiniteType_cartan τ) hconn
    w w' i i' (by
      intro hc
      exact hncomm ((commute_iff_eq t t').mpr (by
        rw [← h1, ← h2]
        exact Commute.eq hc)))
  rwa [h1, h2] at hord

private theorem ggExcPlusModel_orth_conj {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {t t' : WeylGroup τ}
    (ht : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t = w * simple τ i * w⁻¹)
    (ht' : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t' = w * simple τ i * w⁻¹)
    (hne : t ≠ t') (hcomm : Commute t t') {i j : Fin τ.rank}
    (h2 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j = 2) :
    ∃ w : WeylGroup τ, w * simple τ i * w⁻¹ = t ∧ w * simple τ j * w⁻¹ = t' := by
  rcases ggExcPlusModel_isWeylMatrixE hτ with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact ggOrth_conj_E6 he ht ht' hne hcomm h2
  · exact ggOrth_conj_E7 he ht ht' hne hcomm h2
  · exact ggOrth_conj_E8 he ht ht' hne hcomm h2

private theorem ggExcPlusModel_a2_conj {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {t t' : WeylGroup τ}
    (ht : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t = w * simple τ i * w⁻¹)
    (ht' : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t' = w * simple τ i * w⁻¹)
    (hne : t ≠ t') (hncomm : ¬ Commute t t') {i j : Fin τ.rank}
    (h3 : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j = 3) :
    ∃ w : WeylGroup τ, w * simple τ i * w⁻¹ = t ∧ w * simple τ j * w⁻¹ = t' := by
  obtain ⟨w, hw1, hw2⟩ :=
    ggA2_conj (ggExcPlusModel_isWeylMatrixE hτ).isWeylMatrix
      (ggExcPlusModel_isWeylMatrixE hτ).le_three ht ht' hne
      (ggExcPlusModel_refl_order3 hτ ht ht' hncomm) h3
  exact ⟨w, hw1, hw2⟩

private theorem ggExcPlusModel_conj_of_base
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {τ : Tag}
    {ψ : WeylGroup τ →* MulAut ↥A}
    {s w w' t u : WeylGroup τ} {a b : MulAut ↥A}
    (hat : a = ψ t) (hbu : b = ψ u)
    (hws : w * s * w⁻¹ = t) (hw's : w' * s * w'⁻¹ = u) :
    b = ψ (w' * w⁻¹) * a * (ψ (w' * w⁻¹))⁻¹ := by
  rw [hbu, hat, ← hws, ← hw's, ← map_inv]
  simp only [← map_mul]
  congr 1
  group

theorem ggExcPlusModel_exists_weylHom
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hM : GGExcPlusWeylModel τ p A) :
    ∃ ψ : WeylGroup τ →* MulAut ↥A,
      (∀ u, ψ u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∧
      ∀ a ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p a →
        ∃ (w : WeylGroup τ) (i : Fin τ.rank), a = ψ (w * simple τ i * w⁻¹) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, w, hw, hact, hnorm⟩ := hM
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (b : A), Multiplicative.toAdd (Φ (ρ i b)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ b)) :=
    fun i b => hact i b (ρ i b) (ggConjAut_apply A (hN i) b)
  have hreal : ∀ u : WeylGroup τ, ∃ φ ∈ Subgroup.closure (Set.range ρ),
      ∀ b : A, Multiplicative.toAdd (Φ (φ b)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ b)) := by
    intro u
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil =>
      refine ⟨1, Subgroup.one_mem _, fun b => ?_⟩
      rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
      rfl
    | cons i ω ih =>
      obtain ⟨φ, hφ, hφact⟩ := ih
      refine ⟨ρ i * φ, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hφ, fun b => ?_⟩
      rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, MulAut.mul_apply, hρ, hφact]
  have hAL : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range ρ) := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro φ ⟨g, hgH, hgN, hφ⟩
      obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hgH
      obtain ⟨u, hu⟩ := hnorm m hgN
      obtain ⟨φu, hφu, hact'⟩ := hreal u
      have hφeq : φ = φu := by
        refine MulEquiv.ext fun b => ?_
        apply Φ.injective
        apply Multiplicative.toAdd.injective
        rw [hact' b]
        exact hu b (φ b) (hφ b)
      rw [hφeq]
      exact hφu
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨w i, rfl⟩) (hN i)
  let V := Fin τ.rank → ZMod p
  let ι : Additive A ≃+ V := Φ.toAdditive
  let h : Fin τ.rank → V := fun i => Pi.single i 1
  let α : Fin τ.rank → Module.Dual (ZMod p) V := fun i =>
    ∑ j : Fin τ.rank, ((τ.cartan i j : ℤ) : ZMod p) • (LinearMap.proj j : V →ₗ[ZMod p] ZMod p)
  have hα_apply : ∀ (i : Fin τ.rank) (v : V),
      α i v = ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * v j := by
    intro i v
    simp [α, smul_eq_mul, LinearMap.proj]
  have hpair : ∀ i j, α i (h j) = ((τ.cartan i j : ℤ) : ZMod p) := by
    intro i j
    rw [hα_apply]
    rw [Finset.sum_eq_single j]
    · dsimp [h]
      rw [Pi.single_eq_same, mul_one]
    · intro b _ hbj
      dsimp [h]
      rw [Pi.single_eq_of_ne hbj, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hind : LinearIndependent (ZMod p) h := by
    have hb : (⇑(Pi.basisFun (ZMod p) (Fin τ.rank)) : Fin τ.rank → V) = h := by
      funext i
      simp [h]
    exact hb ▸ (Pi.basisFun (ZMod p) (Fin τ.rank)).linearIndependent
  have hs : ∀ i (v : V), ggLin (p := p) ι (ρ i) v = v - α i v • h i := by
    intro i v
    let b : A := Additive.toMul (ι.symm v)
    have hv : ι (Additive.ofMul b) = v := by
      dsimp [b]
      exact AddEquiv.apply_symm_apply ι v
    calc ggLin (p := p) ι (ρ i) v
        = ggLin (p := p) ι (ρ i) (ι (Additive.ofMul b)) :=
          congrArg (fun x => ggLin (p := p) ι (ρ i) x) hv.symm
      _ = ι (Additive.ofMul (ρ i b)) := ggLin_apply_ofMul ι (ρ i) b
      _ = Multiplicative.toAdd (Φ (ρ i b)) := rfl
      _ = TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ b)) := hρ i b
      _ = Multiplicative.toAdd (Φ b) -
            (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * (Multiplicative.toAdd (Φ b)) j) •
              Pi.single i 1 := ggExcPlus_torusAct_simple_eq τ i _
      _ = v - α i v • h i := by
          have hb : Multiplicative.toAdd (Φ b) = v := hv
          rw [hb, ← hα_apply]
  have hRC : GGReflClosed (fun i : Fin τ.rank => ggLin (p := p) ι (ρ i)) :=
    ggReflClosed_of_indep (p := p) hp2 (isFiniteType_cartan τ) (SpJoinRefl.ggIntCartan_tag_E hτ)
      h α hpair hind (fun i => ggLin (p := p) ι (ρ i)) hs
  have hconj : GGReflConjSimple p
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ρ :=
    ggReflConjSimple_of_reflClosed (G := MulAut L') (Bs := A)
      (L := (MulAut.conj : L' →* MulAut L').range) ι ρ hAL hRC
  have hact_mul : ∀ (u v : WeylGroup τ) (φ ψ : MulAut A),
      (∀ b : A, Multiplicative.toAdd (Φ (φ b)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ b))) →
      (∀ b : A, Multiplicative.toAdd (Φ (ψ b)) =
        TableBExc.torusAct τ p v (Multiplicative.toAdd (Φ b))) →
      ∀ b : A, Multiplicative.toAdd (Φ ((φ * ψ) b)) =
        TableBExc.torusAct τ p (u * v) (Multiplicative.toAdd (Φ b)) := by
    intro u v φ ψ hφ hψ b
    rw [MulAut.mul_apply, hφ, hψ, ← TableBExc.torusAct_mul]
  have hact_pow : ∀ (u : WeylGroup τ) (φ : MulAut A) (n : ℕ),
      (∀ b : A, Multiplicative.toAdd (Φ (φ b)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ b))) →
      ∀ b : A, Multiplicative.toAdd (Φ ((φ ^ n) b)) =
        TableBExc.torusAct τ p (u ^ n) (Multiplicative.toAdd (Φ b)) := by
    intro u φ n
    induction n with
    | zero =>
      intro hφ b
      rw [pow_zero, pow_zero, MulAut.one_apply, TableBExc.torusAct_one]
    | succ n ih =>
      intro hφ b
      rw [pow_succ, pow_succ, MulAut.mul_apply, ih hφ, hφ, ← TableBExc.torusAct_mul]
  have hlift : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).IsLiftable ρ := by
    intro i j
    have hm : (simple τ i * simple τ j) ^
        (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j = 1 :=
      (coxeterSystem τ).simple_mul_simple_pow i j
    have hact_ij : ∀ b : A, Multiplicative.toAdd
        (Φ (((ρ i * ρ j) ^
          (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ)).M i j) b)) =
        Multiplicative.toAdd (Φ b) := by
      intro b
      rw [hact_pow (simple τ i * simple τ j) (ρ i * ρ j) _
        (hact_mul (simple τ i) (simple τ j) (ρ i) (ρ j) (hρ i) (hρ j)) b, hm,
        TableBExc.torusAct_one]
    refine MulEquiv.ext fun b => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [hact_ij b, MulAut.one_apply]
  let ψ : WeylGroup τ →* MulAut A := (coxeterSystem τ).lift ⟨ρ, hlift⟩
  have hψ_simple : ∀ i, ψ (simple τ i) = ρ i := fun i =>
    (coxeterSystem τ).lift_apply_simple hlift i
  refine ⟨ψ, ?_, ?_⟩
  · intro u
    have hψ_mem : ψ u ∈ Subgroup.closure (Set.range ρ) := by
      obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
      have hmap : ψ ((coxeterSystem τ).wordProd ω) = (ω.map ρ).prod := by
        rw [CoxeterSystem.wordProd, map_list_prod, List.map_map]
        exact congrArg List.prod (List.map_congr_left fun i _ => hψ_simple i)
      rw [hmap]
      exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact Subgroup.subset_closure ⟨i, rfl⟩
    rwa [hAL]
  · intro a ha haR
    obtain ⟨w₁, hw₁, i, hai⟩ := hconj a ha haR
    have hw₁' : w₁ ∈ Subgroup.closure (Set.range ρ) := by rwa [← hAL]
    have hρ_mem : Set.range ρ ⊆ ψ.range := by
      rintro _ ⟨i, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨simple τ i, hψ_simple i⟩
    have hclosure_le : Subgroup.closure (Set.range ρ) ≤ ψ.range :=
      (Subgroup.closure_le ψ.range).mpr hρ_mem
    obtain ⟨u₁, hu₁⟩ := hclosure_le hw₁'
    refine ⟨u₁, i, ?_⟩
    rw [hai, ← hu₁, ← hψ_simple i, ← map_inv]
    simp only [← map_mul]

theorem ggExcPlusModel_exists_conj_pair
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L']
    [Finite L'] {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hM : GGExcPlusWeylModel τ p A) {a a' b b' : MulAut ↥A}
    (ha : a ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (haR : GGIsReflection p a)
    (ha' : a' ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (haR' : GGIsReflection p a')
    (hb : b ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (hbR : GGIsReflection p b)
    (hb' : b' ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (hbR' : GGIsReflection p b')
    (hne : a ≠ a') (hne' : b ≠ b') (hcomm : a * a' = a' * a ↔ b * b' = b' * b) :
    ∃ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      b = v * a * v⁻¹ ∧ b' = v * a' * v⁻¹ := by
  classical
  obtain ⟨ψ, hψA, hψrefl⟩ :=
    ggExcPlusModel_exists_weylHom hτ hp hp2 hsc hM
  obtain ⟨w, i, hat⟩ := hψrefl a ha haR
  obtain ⟨w', i', hat'⟩ := hψrefl a' ha' haR'
  obtain ⟨vb, jb, hbu⟩ := hψrefl b hb hbR
  obtain ⟨vb', jb', hb'u'⟩ := hψrefl b' hb' hbR'
  set t : WeylGroup τ := w * simple τ i * w⁻¹ with ht_def
  set t' : WeylGroup τ := w' * simple τ i' * w'⁻¹ with ht'_def
  set u : WeylGroup τ := vb * simple τ jb * vb⁻¹ with hu_def
  set u' : WeylGroup τ := vb' * simple τ jb' * vb'⁻¹ with hu'_def
  have ht : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t = w * simple τ i * w⁻¹ :=
    ⟨w, i, ht_def⟩
  have ht' : ∃ (w : WeylGroup τ) (i : Fin τ.rank), t' = w * simple τ i * w⁻¹ :=
    ⟨w', i', ht'_def⟩
  have hu : ∃ (w : WeylGroup τ) (i : Fin τ.rank), u = w * simple τ i * w⁻¹ :=
    ⟨vb, jb, hu_def⟩
  have hu' : ∃ (w : WeylGroup τ) (i : Fin τ.rank), u' = w * simple τ i * w⁻¹ :=
    ⟨vb', jb', hu'_def⟩
  have ht_ne : t ≠ t' := fun h => hne (by rw [hat, hat', h])
  have hu_ne : u ≠ u' := fun h => hne' (by rw [hbu, hb'u', h])
  have hcomm_t : Commute t t' ↔ a * a' = a' * a := by
    constructor
    · intro hc
      rw [hat, hat']
      simp only [← map_mul]
      rw [Commute.eq hc]
    · intro hc
      by_contra hn
      have hord : (t * t') ^ 3 = 1 := ggExcPlusModel_refl_order3 hτ ht ht' hn
      have ha2 : a ^ 2 = 1 := haR.1
      have ha'2 : a' ^ 2 = 1 := haR'.1
      have h3a : (a * a') ^ 3 = 1 := by
        rw [hat, hat']
        simp only [← map_mul, ← map_pow]
        rw [hord, map_one]
      have hcaa' : Commute a a' := (commute_iff_eq a a').mpr hc
      have h2a : (a * a') ^ 2 = 1 := by
        rw [hcaa'.mul_pow 2, ha2, ha'2, one_mul]
      have hone : a * a' = 1 := by
        have h := h3a
        rw [pow_succ] at h
        rw [h2a, one_mul] at h
        exact h
      have hEq : a' = a := by
        have haa : a * a = 1 := by rwa [pow_two] at ha2
        exact mul_left_cancel (by rw [hone, haa])
      exact hne hEq.symm
  have hcomm_u : Commute u u' ↔ b * b' = b' * b := by
    constructor
    · intro hc
      rw [hbu, hb'u']
      simp only [← map_mul]
      rw [Commute.eq hc]
    · intro hc
      by_contra hn
      have hord : (u * u') ^ 3 = 1 := ggExcPlusModel_refl_order3 hτ hu hu' hn
      have hb2 : b ^ 2 = 1 := hbR.1
      have hb'2 : b' ^ 2 = 1 := hbR'.1
      have h3b : (b * b') ^ 3 = 1 := by
        rw [hbu, hb'u']
        simp only [← map_mul, ← map_pow]
        rw [hord, map_one]
      have hcbb' : Commute b b' := (commute_iff_eq b b').mpr hc
      have h2b : (b * b') ^ 2 = 1 := by
        rw [hcbb'.mul_pow 2, hb2, hb'2, one_mul]
      have hone : b * b' = 1 := by
        have h := h3b
        rw [pow_succ] at h
        rw [h2b, one_mul] at h
        exact h
      have hEq : b' = b := by
        have hbb : b * b = 1 := by rwa [pow_two] at hb2
        exact mul_left_cancel (by rw [hone, hbb])
      exact hne' hEq.symm
  have hiff : Commute t t' ↔ Commute u u' :=
    hcomm_t.trans (hcomm.trans hcomm_u.symm)
  by_cases hct : Commute t t'
  · have hcu : Commute u u' := hiff.mp hct
    obtain ⟨⟨i₂, j₂, h2⟩, -⟩ := ggExcPlusModel_exists_labels hτ
    obtain ⟨w, hwt, hwt'⟩ := ggExcPlusModel_orth_conj hτ ht ht' ht_ne hct h2
    obtain ⟨w', hwu, hwu'⟩ := ggExcPlusModel_orth_conj hτ hu hu' hu_ne hcu h2
    exact ⟨ψ (w' * w⁻¹), hψA _, ggExcPlusModel_conj_of_base hat hbu hwt hwu,
      ggExcPlusModel_conj_of_base hat' hb'u' hwt' hwu'⟩
  · have hcu : ¬ Commute u u' := fun h => hct (hiff.mpr h)
    obtain ⟨-, ⟨i₃, j₃, h3⟩⟩ := ggExcPlusModel_exists_labels hτ
    obtain ⟨w, hwt, hwt'⟩ := ggExcPlusModel_a2_conj hτ ht ht' ht_ne hct h3
    obtain ⟨w', hwu, hwu'⟩ := ggExcPlusModel_a2_conj hτ hu hu' hu_ne hcu h3
    exact ⟨ψ (w' * w⁻¹), hψA _, ggExcPlusModel_conj_of_base hat hbu hwt hwu,
      ggExcPlusModel_conj_of_base hat' hb'u' hwt' hwu'⟩

end CFSG.StandardType

end
