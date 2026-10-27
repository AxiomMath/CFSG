module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.Sporadic.Recognition.CoverCubeTransfer
public import CFSG.Sporadic.Recognition.CoverRecipeCube

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.AGLEmbedding Subgroup

theorem kernelTrivialAt_three_of_local_card {X : Type} [Group X] [Finite X] {m : ℕ}
    (g : Fin m → X) {R : List (List (Fin m × Bool))} {ord : Fin m → ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) (hpow : ∀ i, g i ^ ord i = 1)
    (hord : ∀ i, ord i ≠ 0 ∧ (ord i).Coprime 3) {n : ℕ}
    (hPG : Finite (PG m (cover₃Words R (fun i => [(i, true)]) ord)) ∧
      Nat.card (PG m (cover₃Words R (fun i => [(i, true)]) ord)) ≤ n)
    (hcard : n ≤ Nat.card (Subgroup.closure (Set.range g)))
    (hsyl : (Nat.card X).factorization 3 ≤ n.factorization 3) : KernelTrivialAt X 3 := by
  intro E _ _ _ π hπ hC hp
  set N : Subgroup X := Subgroup.closure (Set.range g) with hN
  let gX : Fin m → N := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have coe_gX : ∀ i, (gX i : X) = g i := fun i => rfl
  have closure_gX : Subgroup.closure (Set.range gX) = ⊤ := by
    have e : Set.range gX = Subtype.val ⁻¹' Set.range g := by
      ext ⟨x, hx⟩
      simp only [Set.mem_range, Set.mem_preimage]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← coe_gX, hy]⟩,
        fun ⟨y, hy⟩ => ⟨y, Subtype.ext (by rw [coe_gX]; exact hy)⟩⟩
    rw [e]
    exact closure_closure_coe_preimage
  have coe_lift : ∀ w : FreeGroup (Fin m),
      ((FreeGroup.lift gX w : N) : X) = FreeGroup.lift g w := by
    intro w
    have : N.subtype.comp (FreeGroup.lift gX) = FreeGroup.lift g :=
      FreeGroup.ext_hom _ _ fun i => by simp [coe_gX]
    exact congrArg (fun φ : FreeGroup (Fin m) →* X => φ w) this
  have hR' : ∀ r ∈ R, FreeGroup.lift gX (FreeGroup.mk r) = 1 := fun r hr =>
    Subtype.ext (by rw [coe_lift, hR r hr, Subgroup.coe_one])
  have hw : ∀ i, FreeGroup.lift gX (FreeGroup.mk [(i, true)]) = gX i := fun i => by
    rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
  have hpow' : ∀ i, ord i ≠ 0 → gX i ^ ord i = 1 := fun i _ =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, coe_gX]; exact hpow i)
  obtain ⟨hfin, hle⟩ := hPG
  have hge : Nat.card N ≤ Nat.card (PG m (cover₃Words R (fun i => [(i, true)]) ord)) :=
    card_le_card_cover₃ closure_gX hR' hw hpow'
  have hcardN : Nat.card N = n := le_antisymm (hge.trans hle) hcard
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hπ
  have hsylN : (Nat.card π.range).factorization 3 ≤ (Nat.card N).factorization 3 := by
    rw [hrange, Subgroup.card_top, hcardN]
    exact hsyl
  refine ker_eq_bot_of_sylow_subgroup π hC hp N (hrange ▸ le_top) hsylN ?_
  intro M _ _ φ hφ hc hpg hd
  refine ker_eq_bot_of_cover₃ (g := gX) (R := R) (cw := fun i => [(i, true)]) (ord := ord)
    closure_gX hR' (fun i h0 => absurd h0 (hord i).1) (fun i hi => ⟨rfl, hpow' i hi, (hord i).2⟩)
    hfin (hle.trans hcardN.ge) φ hφ hc hpg hd

theorem kernelTrivialAt_three_of_local {X : Type} [Group X] [Finite X] {m : ℕ} (g : Fin m → X)
    {R : List (List (Fin m × Bool))} {ord : Fin m → ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) (hpow : ∀ i, g i ^ ord i = 1)
    (hord : ∀ i, ord i ≠ 0 ∧ (ord i).Coprime 3) {k cap n : ℕ}
    (henum : subsetCheckShortCC (cover₃Words R (fun i => [(i, true)]) ord) [] k cap n = true)
    (hcard : n ≤ Nat.card (Subgroup.closure (Set.range g)))
    (hsyl : (Nat.card X).factorization 3 ≤ n.factorization 3) : KernelTrivialAt X 3 :=
  kernelTrivialAt_three_of_local_card g hR hpow hord
    (card_PG_le_of_subsetCheckShortCC_nil _ henum) hcard hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
