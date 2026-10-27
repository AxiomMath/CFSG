module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormLe
import CFSG.LieType.Chevalley.RootComponentType
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

theorem reflection_braid {m : Fin 6} {i j : Root m}
    (h : ((pairing m i j * pairing m j i : ℤ) : ZMod 3) = 1) :
    reflection m i * reflection m j * reflection m i =
      reflection m j * reflection m i * reflection m j := by
  have hab : (pairing m i j : ZMod 3) * (pairing m j i : ZMod 3) = 1 := by
    rw [← Int.cast_mul]
    exact h
  have hcases : ∀ a b : ZMod 3, a * b = 1 → a = 1 ∧ b = 1 ∨ a = 2 ∧ b = 2 := by
    decide
  rcases hcases _ _ hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · ext v
    simp only [LinearEquiv.mul_apply, reflection_apply, map_sub, map_smul, smul_eq_mul,
      pairing_eq, pairing_self, ha, hb, Pi.sub_apply, Pi.smul_apply]
    ring
  · have ha' : (pairing m i j : ZMod 3) = -1 := by rw [ha]; decide
    have hb' : (pairing m j i : ZMod 3) = -1 := by rw [hb]; decide
    ext v
    simp only [LinearEquiv.mul_apply, reflection_apply, map_sub, map_smul, smul_eq_mul,
      pairing_eq, pairing_self, ha', hb', Pi.sub_apply, Pi.smul_apply]
    ring

theorem six_le_card_of_admissible {m : Fin 6} (hm : 2 ≤ m.val) {c : Finset (Root m)}
    (hc : admissible m c) : 6 ≤ c.card := by
  by_contra h
  have hlab := hc.2
  unfold label at hlab
  split at hlab
  · omega
  · omega
  · have hcard : c.card ≤ 5 := by omega
    interval_cases c.card <;>
      (simp only [labelSL] at hlab; simp [CFSG.Assembly.LargeEvenInLambda2] at hlab)

end CFSG.StandardType.GGQ2Frame.ExcRaw

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes
open scoped commutatorElement


namespace ExcCoordDatum

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} (d : ExcCoordDatum S T₀ m)
include d

theorem pairing_mul_pairing_eq_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : ExcRaw.Root m}
    (hij : i ≠ j) (hadj : ExcRaw.Adj m i j) :
    ExcRaw.pairing m i j * ExcRaw.pairing m j i = 1 := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hsymm : ∀ k, τ.symmetrizer k k = 1 := by
    rcases hτ with rfl | rfl | rfl <;> intro k <;> simp [Tag.symmetrizer]
  have hne : d.γ i ≠ d.γ j := fun h => hij (d.eq_of_eq i j (Or.inl h))
  have hne' : d.γ i ≠ -d.γ j := fun h => hij (d.eq_of_eq i j (Or.inr h))
  have hx := (adj_iff_iform_ne_zero d i j).1 hadj
  rw [d.pairing_eq i j, d.pairing_eq j i,
    corootPair_eq_iform_of_simplyLaced hτ' (d.isRoot j) (d.γ i),
    corootPair_eq_iform_of_simplyLaced hτ' (d.isRoot i) (d.γ j),
    CFSG.LieType.Steinberg.Adjoint.iform_comm (d.γ j) (d.γ i)]
  rcases CFSG.LieType.Chevalley.SimplyLacedCover.iform_mem hsymm (d.isRoot i) (d.isRoot j)
    hne hne' with h | h | h
  · rw [h]; norm_num
  · exact absurd h hx
  · rw [h]; norm_num

theorem ncard_codeRoots (c : Finset (ExcRaw.Root m)) :
    (codeRoots d.γ c).ncard = 2 * c.card := by
  classical
  have hset : codeRoots d.γ c =
      d.γ '' (c : Set (ExcRaw.Root m)) ∪
        (fun i => -d.γ i) '' (c : Set (ExcRaw.Root m)) := by
    ext δ
    simp only [codeRoots, Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨i, hi, h | h⟩
      · exact Or.inl ⟨i, hi, h.symm⟩
      · exact Or.inr ⟨i, hi, h.symm⟩
    · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
      · exact ⟨i, hi, Or.inl h.symm⟩
      · exact ⟨i, hi, Or.inr h.symm⟩
  have hinj : Set.InjOn d.γ (c : Set (ExcRaw.Root m)) :=
    fun i _ j _ h => d.eq_of_eq i j (Or.inl h)
  have hinj' : Set.InjOn (fun i => -d.γ i) (c : Set (ExcRaw.Root m)) :=
    fun i _ j _ h => d.eq_of_eq i j (Or.inl (by simpa using h))
  have hdisj : Disjoint (d.γ '' (c : Set (ExcRaw.Root m)))
      ((fun i => -d.γ i) '' (c : Set (ExcRaw.Root m))) := by
    rw [Set.disjoint_left]
    rintro δ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
    have hji' : -d.γ j = d.γ i := by simpa using hji
    have hEq : i = j := d.eq_of_eq i j (Or.inr hji'.symm)
    have h0 : d.γ j = 0 := by
      rw [← hEq] at hji' ⊢
      funext k
      simp only [Pi.zero_apply]
      have hk : d.γ i k = -d.γ i k := by simpa using congrFun hji'.symm k
      omega
    exact (d.isRoot j).ne_zero h0
  rw [hset, Set.ncard_union_eq hdisj (c.finite_toSet.image _) (c.finite_toSet.image _),
    Set.InjOn.ncard_image hinj, Set.InjOn.ncard_image hinj', Set.ncard_coe_finset]
  ring

theorem isRootComponent_codeRoots {c : Finset (ExcRaw.Root m)}
    (hc : ∃ U, ExcRaw.occurs m U c) : IsRootComponent (codeRoots d.γ c) := by
  obtain ⟨A, a, j, hj⟩ := d.exists_famCharHom_componentRoots_eq hc
  rw [← hj]
  exact isRootComponent_componentRoots j

theorem three_le_compRank_codeRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hm : 2 ≤ m.val)
    {c : Finset (ExcRaw.Root m)} (hc : ExcRaw.admissible m c) :
    3 ≤ compRank (codeRoots d.γ c) := by
  have hcomp : IsRootComponent (codeRoots d.γ c) := d.isRootComponent_codeRoots hc.1
  have hne : (codeRoots d.γ c).Nonempty := by
    obtain ⟨U, hU⟩ := hc.1
    obtain ⟨i, hi⟩ := hU.1
    exact ⟨d.γ i, i, hi, Or.inl rfl⟩
  have hcard6 : 6 ≤ c.card := ExcRaw.six_le_card_of_admissible hm hc
  have hncard : 12 ≤ (codeRoots d.γ c).ncard := by
    rw [d.ncard_codeRoots c]
    omega
  obtain ⟨t, e, ht, hsl, hiform, hcard, hN⟩ :=
    exists_dynkinType (Or.inr hτ) hcomp hne
  have hrank : compRank (codeRoots d.γ c) = t.rank := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hcomp, hcard]
  rw [hrank]
  rw [hN] at hncard
  cases t with
  | A n =>
      rw [TauCeti.DynkinType.rank_A]
      rw [TauCeti.DynkinType.numRoots_A] at hncard
      have hn : 1 ≤ n := TauCeti.DynkinType.valid_A.1 ht
      by_contra h3
      have h3' : n < 3 := by omega
      interval_cases n <;> norm_num at hncard
  | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
      rw [TauCeti.DynkinType.rank_D]
      have hn : 4 ≤ n := TauCeti.DynkinType.valid_D.1 ht
      omega
  | E6 =>
      rw [TauCeti.DynkinType.rank_E6]
      norm_num
  | E7 =>
      rw [TauCeti.DynkinType.rank_E7]
      norm_num
  | E8 =>
      rw [TauCeti.DynkinType.rank_E8]
      norm_num
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

theorem weyl_le_map_of_propagate {c : Finset (ExcRaw.Root m)} (hc : ∃ U, ExcRaw.occurs m U c)
    {i₀ : ExcRaw.Root m} (hi₀ : i₀ ∈ c)
    (h₀ : ExcRaw.reflection m i₀ ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord))
    (hstep : ∀ i ∈ c, ∀ j ∈ c, ExcRaw.Adj m i j →
      ExcRaw.reflection m i ∈
        (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) →
      ExcRaw.reflection m j ∈
        (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord)) :
    ExcRaw.weyl m c ≤ (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
  classical
  obtain ⟨U, hU⟩ := hc
  have hT := hU.2.2.2 (c.filter fun i => ExcRaw.reflection m i ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord))
    (Finset.filter_subset _ _) ⟨i₀, Finset.mem_filter.2 ⟨hi₀, h₀⟩⟩
    (fun i hi j hj hadj => Finset.mem_filter.2
      ⟨hj, hstep i (Finset.mem_filter.1 hi).1 j hj hadj (Finset.mem_filter.1 hi).2⟩)
  rw [ExcRaw.weyl, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i ∈ c.filter fun i => ExcRaw.reflection m i ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
    rw [hT]
    exact hi
  exact (Finset.mem_filter.1 hi').2

section Rational


theorem exists_rootSL2_mem_codeComponent (hS : NegLangTwo S)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hm : 2 ≤ m.val) {c : Finset (ExcRaw.Root m)}
    (hc : ExcRaw.admissible m c) :
    ∃ i ∈ c, rootSL2 τ L (d.γ i) WSL ∈ codeComponent S d.γ c := by
  have hΨ := d.isRootComponent_codeRoots hc.1
  obtain ⟨U, hU⟩ := hc.1
  obtain ⟨i₀, hi₀⟩ := hU.1
  obtain ⟨ν, ψ, σ, hν, hψ, hsub⟩ := exists_slFrame_of_three_le_compRank (L := L) hτ hΨ
    ⟨d.γ i₀, i₀, hi₀, Or.inl rfl⟩ (d.three_le_compRank_codeRoots hτ hm hc)
  have hab : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨i, hi, hσ⟩ := hsub ⟨_, _, hab, rfl⟩
  refine ⟨i, hi, rootSL2_WSL_mem_commutator_of_frame hS hν hψ hsub ?_⟩
  rcases hσ with h | h
  · exact ⟨_, _, hab, h.symm⟩
  · exact ⟨_, _, hab.symm, by rw [hψ.neg, h, neg_neg]⟩

theorem reflection_mem_of_pairing_mul_eq_one (hS : NegLangTwo S)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : Finset (ExcRaw.Root m)}
    {i j : ExcRaw.Root m} (hj : j ∈ c)
    (hij : ExcRaw.pairing m i j * ExcRaw.pairing m j i = 1)
    (hi : ExcRaw.reflection m i ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord)) :
    ExcRaw.reflection m j ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
  obtain ⟨φ, hφ, hφr⟩ := Subgroup.mem_map.1 hi
  obtain ⟨g, hgR, hgN, hgφ⟩ := mem_ggAutomizer_iff.1 hφ
  have hnN := d.rootSL2_mem_normalizer hS j
  have hnX : rootSL2 τ L (d.γ j) WSL ∈ rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ := by
    refine ⟨rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) (d.isRoot j) WSL),
      rootWeylSL2_mem_Γ_of_rho_neg S hτ (by rw [hS.1, pow_one]) hS.2.1 (d.isRoot j)
        (hS.2.2 _ (d.isRoot j))⟩
    rintro δ (rfl | rfl)
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j, hj, Or.inr rfl⟩
  have hxR : ⁅rootSL2 τ L (d.γ j) WSL, g⁆ ∈ codeComponent S d.γ c :=
    Subgroup.commutator_mem_commutator hnX (Subgroup.commutator_le_self _ hgR)
  have hxN : ⁅rootSL2 τ L (d.γ j) WSL, g⁆ ∈ Subgroup.normalizer (T₀ : Set (ModGL τ L)) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hnN hgN) (inv_mem hnN)) (inv_mem hgN)
  have hcn : ∀ b : ↥T₀, ((ggConjAut T₀ hnN b : ↥T₀) : ModGL τ L) =
      rootSL2 τ L (d.γ j) WSL * b * (rootSL2 τ L (d.γ j) WSL)⁻¹ := fun b => rfl
  have hconj : ggConjAut T₀ hxN = ggConjAut T₀ hnN * φ * (ggConjAut T₀ hnN)⁻¹ * φ⁻¹ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have h1 : ((ggConjAut T₀ hxN b : ↥T₀) : ModGL τ L) =
        ⁅rootSL2 τ L (d.γ j) WSL, g⁆ * b * ⁅rootSL2 τ L (d.γ j) WSL, g⁆⁻¹ := rfl
    rw [h1, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hcn, hgφ,
      inv_apply_of_forall hcn, inv_apply_of_forall hgφ, commutatorElement_def]
    group
  have hbraid := ExcRaw.reflection_braid (m := m) (i := i) (j := j) (by
    rw [hij, Int.cast_one])
  have hcomm : ExcRaw.reflection m j * ExcRaw.reflection m i * (ExcRaw.reflection m j)⁻¹ *
      (ExcRaw.reflection m i)⁻¹ = ExcRaw.reflection m i * ExcRaw.reflection m j := by
    have hi2 : ExcRaw.reflection m i * ExcRaw.reflection m i = 1 :=
      mul_inv_cancel (ExcRaw.reflection m i)
    rw [show (ExcRaw.reflection m j)⁻¹ = ExcRaw.reflection m j from rfl,
      show (ExcRaw.reflection m i)⁻¹ = ExcRaw.reflection m i from rfl, ← hbraid]
    rw [mul_assoc (ExcRaw.reflection m i * ExcRaw.reflection m j), hi2, mul_one]
  have hprod : ExcRaw.reflection m i * ExcRaw.reflection m j ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
    refine Subgroup.mem_map.2 ⟨_, ggConjAut_mem_ggAutomizer hxR hxN, ?_⟩
    rw [hconj, map_mul, map_mul, map_mul, map_inv, map_inv, d.ggLin_ggConjAut_rootSL2 hS j, hφr,
      hcomm]
  have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hi) hprod
  rwa [inv_mul_cancel_left] at h

theorem reflection_mem_of_adj (hS : NegLangTwo S) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : Finset (ExcRaw.Root m)} {i j : ExcRaw.Root m} (hj : j ∈ c) (hadj : ExcRaw.Adj m i j)
    (hi : ExcRaw.reflection m i ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord)) :
    ExcRaw.reflection m j ∈
      (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
  by_cases hij : i = j
  · exact hij ▸ hi
  exact d.reflection_mem_of_pairing_mul_eq_one hS (Or.inr hτ) hj
    (d.pairing_mul_pairing_eq_one hτ hij hadj) hi

theorem weyl_le_map_ggAutomizer_codeComponent (hS : NegLangTwo S)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hm : 2 ≤ m.val) {c : Finset (ExcRaw.Root m)}
    (hc : ExcRaw.admissible m c) :
    ExcRaw.weyl m c ≤ (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) := by
  obtain ⟨i₀, hi₀, hw₀⟩ := d.exists_rootSL2_mem_codeComponent hS hτ hm hc
  exact d.weyl_le_map_of_propagate hc.1 hi₀ (d.reflection_mem_map_ggAutomizer_of_mem hS i₀ hw₀)
    fun _ _ _ hj hadj hri => d.reflection_mem_of_adj hS hτ hj hadj hri

end Rational

end ExcCoordDatum

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
