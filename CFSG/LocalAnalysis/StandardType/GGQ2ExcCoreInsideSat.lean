module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideTorus
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Idx
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)

noncomputable section

private def corootTupleHom {τ : Tag} {K : Type} [Field K] (β : Fin τ.rank → ℤ) :
    Kˣ →* (Fin τ.rank → Kˣ) where
  toFun u := fun j => u ^ corootPair β (Pi.single j 1)
  map_one' := by funext j; simp
  map_mul' u v := by funext j; simp only [Pi.mul_apply, mul_zpow]

private theorem corootTupleHom_apply {τ : Tag} {K : Type} [Field K]
    (β : Fin τ.rank → ℤ) (u : Kˣ) :
    corootTupleHom β u = fun j => u ^ corootPair β (Pi.single j 1) := rfl

private theorem rootChar_corootProd
    {τ : Tag} {K : Type} [Field K] {ι : Type*}
    (s : Finset ι) (δ : ι → Fin τ.rank → ℤ) (u : ι → Kˣ)
    (hδ : ∀ x ∈ s, IsRoot τ (δ x)) (γ : Fin τ.rank → ℤ) :
    rootChar (∏ x ∈ s, corootTupleHom (δ x) (u x)) γ
      = ∏ x ∈ s, u x ^ corootPair (δ x) γ := by
  classical
  revert hδ
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [rootChar]
  · intro x s hx ih hδ
    rw [Finset.prod_insert hx, Finset.prod_insert hx,
      CFSG.LieType.Chevalley.rootChar_mul_tuple,
      ih (fun y hy => hδ y (Finset.mem_insert_of_mem hy))]
    congr 1
    rw [corootTupleHom_apply]
    exact CFSG.StandardType.LangRat.j4e_rootChar_corootTuple
      (hδ x (Finset.mem_insert_self x s)) (u x) γ

private theorem pow_three_zpow {G : Type*} [CommGroup G] {c : G} (hc : c ^ 3 = 1) (m : ℤ) :
    (c ^ m) ^ 3 = 1 := by
  have h3 : c ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hc
  have h : (c ^ m) ^ ((3 : ℕ) : ℤ) = 1 := by
    rw [← zpow_mul, mul_comm, zpow_mul, h3, one_zpow]
  rwa [zpow_natCast] at h

private theorem corootPair_neg_right_of_isRoot
    {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    corootPair β (-v) = -corootPair β v := by
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum hβ (-v),
    CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum hβ v,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply]; ring

private theorem satWitness_corootPair_mul_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) {i : ExcRaw.Root m} (hi : i ∈ c)
    (v : Fin τ.rank → ℤ) :
    w.e * corootPair (d.γ i) v = ∑ a, w.n i a * corootPair (d.γ (w.b a)) v := by
  have hroot : ∀ j : ExcRaw.Root m, w.e * corootPair (d.γ i) (d.γ j)
      = ∑ a, w.n i a * corootPair (d.γ (w.b a)) (d.γ j) := by
    intro j
    calc w.e * corootPair (d.γ i) (d.γ j)
        = w.e * ExcRaw.pairing m j i := by rw [d.pairing_eq j i]
      _ = ∑ a, w.n i a * ExcRaw.pairing m j (w.b a) := w.pairing_eq i hi j
      _ = ∑ a, w.n i a * corootPair (d.γ (w.b a)) (d.γ j) := by
            refine Finset.sum_congr rfl fun a _ => by rw [d.pairing_eq j (w.b a)]
  have hsingle : ∀ j : Fin τ.rank, w.e * corootPair (d.γ i) (Pi.single j 1)
      = ∑ a, w.n i a * corootPair (d.γ (w.b a)) (Pi.single j 1) := by
    intro j
    obtain ⟨l, hl | hl⟩ := d.exists_eq (Pi.single j 1) (IsRoot.basis j)
    · rw [hl]; exact hroot l
    · rw [hl, corootPair_neg_right_of_isRoot (d.isRoot i)]
      have hterm : ∀ a, w.n i a * corootPair (d.γ (w.b a)) (-(d.γ l))
          = -(w.n i a * corootPair (d.γ (w.b a)) (d.γ l)) := by
        intro a; rw [corootPair_neg_right_of_isRoot (d.isRoot (w.b a))]; ring
      rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_neg_distrib, ← hroot l]
      ring
  calc w.e * corootPair (d.γ i) v
      = w.e * ∑ j, v j * corootPair (d.γ i) (Pi.single j 1) := by
          rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum (d.isRoot i) v]
    _ = ∑ j, v j * (w.e * corootPair (d.γ i) (Pi.single j 1)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, v j * ∑ a, w.n i a * corootPair (d.γ (w.b a)) (Pi.single j 1) := by
          exact Finset.sum_congr rfl fun j _ => by rw [hsingle j]
    _ = ∑ a, w.n i a * ∑ j, v j * corootPair (d.γ (w.b a)) (Pi.single j 1) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a, w.n i a * corootPair (d.γ (w.b a)) v := by
          exact Finset.sum_congr rfl fun a _ => by
            rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum
              (d.isRoot (w.b a)) v]

private theorem corootTupleHom_pow_eq_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) {i : ExcRaw.Root m} (hi : i ∈ c)
    (u : Lˣ) :
    (corootTupleHom (d.γ i) u) ^ w.e
      = ∏ a, corootTupleHom (d.γ (w.b a)) (u ^ w.n i a) := by
  rw [← map_zpow, corootTupleHom_apply]
  funext j
  rw [Finset.prod_apply]
  simp only [corootTupleHom_apply]
  rw [← zpow_mul]
  have hR : ∏ a, (u ^ w.n i a) ^ corootPair (d.γ (w.b a)) (Pi.single j 1)
      = u ^ (w.e * corootPair (d.γ i) (Pi.single j 1)) := by
    simp only [← zpow_mul]
    rw [Finset.prod_zpow_eq_zpow_sum,
      satWitness_corootPair_mul_eq d w hi (Pi.single j 1)]
  rw [hR]

private theorem corootTupleHom_neg_pow_eq_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) {i : ExcRaw.Root m} (hi : i ∈ c)
    (u : Lˣ) :
    (corootTupleHom (-(d.γ i)) u) ^ w.e
      = ∏ a, corootTupleHom (d.γ (w.b a)) (u ^ (-(w.n i a))) := by
  rw [← map_zpow, corootTupleHom_apply]
  funext j
  rw [Finset.prod_apply]
  simp only [corootTupleHom_apply]
  rw [CFSG.StandardType.LayerCycCoroot.corootPair_neg_root (d.isRoot i), ← zpow_mul]
  have hR : ∏ a, (u ^ (-(w.n i a))) ^ corootPair (d.γ (w.b a)) (Pi.single j 1)
      = u ^ (-(w.e * corootPair (d.γ i) (Pi.single j 1))) := by
    simp only [← zpow_mul]
    rw [Finset.prod_zpow_eq_zpow_sum]
    have hsum : ∑ a, -w.n i a * corootPair (d.γ (w.b a)) (Pi.single j 1)
        = -(w.e * corootPair (d.γ i) (Pi.single j 1)) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
      rw [← satWitness_corootPair_mul_eq d w hi (Pi.single j 1)]
    rw [hsum]
  rw [hR,
    show w.e * -(corootPair (d.γ i) (Pi.single j 1))
      = -(w.e * corootPair (d.γ i) (Pi.single j 1)) by ring]

private theorem exists_corootTuple_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c)
    {Δ : Finset (Fin τ.rank → ℤ)} (hΔ : ∀ β ∈ Δ, β ∈ codeRoots d.γ c)
    (x : (Fin τ.rank → ℤ) → Lˣ) :
    ∃ y : Fin w.r → Lˣ, (coordTuple Δ x) ^ w.e
      = ∏ a, corootTupleHom (d.γ (w.b a)) (y a) := by
  classical
  suffices H : ∀ (Δ : Finset (Fin τ.rank → ℤ)), (∀ β ∈ Δ, β ∈ codeRoots d.γ c) →
      ∀ x : (Fin τ.rank → ℤ) → Lˣ, ∃ y : Fin w.r → Lˣ,
        (coordTuple Δ x) ^ w.e = ∏ a, corootTupleHom (d.γ (w.b a)) (y a) from H Δ hΔ x
  intro Δ
  induction Δ using Finset.induction_on with
  | empty =>
      intro _ x
      refine ⟨fun _ => 1, ?_⟩
      have hone : coordTuple (∅ : Finset (Fin τ.rank → ℤ)) x = 1 := by
        funext i
        simp [coordTuple]
      rw [hone, one_zpow]
      simp
  | insert β Δ hβΔ ih =>
      intro hΔ x
      obtain ⟨i, hi, hβi⟩ := hΔ β (Finset.mem_insert_self β Δ)
      obtain ⟨y₀, hy₀⟩ := ih (fun b hb => hΔ b (Finset.mem_insert_of_mem hb)) x
      have hcoord : coordTuple (insert β Δ) x
          = (fun j => x β ^ corootPair β (Pi.single j 1)) * coordTuple Δ x := by
        funext j
        simp only [coordTuple, Pi.mul_apply, Finset.prod_insert hβΔ]
      have hsplit : (coordTuple (insert β Δ) x) ^ w.e
          = (corootTupleHom β (x β)) ^ w.e * (coordTuple Δ x) ^ w.e := by
        rw [hcoord, corootTupleHom_apply, mul_zpow]
      rcases hβi with hβi | hβi
      · subst hβi
        refine ⟨fun a => (x (d.γ i)) ^ w.n i a * y₀ a, ?_⟩
        rw [hsplit, corootTupleHom_pow_eq_prod d w hi, hy₀, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun a _ => (map_mul (corootTupleHom (d.γ (w.b a))) _ _).symm
      · subst hβi
        refine ⟨fun a => (x (-(d.γ i))) ^ (-(w.n i a)) * y₀ a, ?_⟩
        rw [hsplit, corootTupleHom_neg_pow_eq_prod d w hi, hy₀, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun a _ => (map_mul (corootTupleHom (d.γ (w.b a))) _ _).symm

private theorem mem_rootDiag_single
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) (n : Fin w.r → ℕ)
    (x : Fin w.r) :
    rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x)) ∈ T₀ := by
  rw [map_pow, ← rootDiagUnit_pow, show rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) d.ζ)
      = rootDiagUnit τ (fun j => d.ζ ^ corootPair (d.γ (w.b x)) (Pi.single j 1)) by
    rw [corootTupleHom_apply]]
  exact T₀.pow_mem (d.coroot_mem (w.b x)) (n x)

private theorem mem_rootDiag_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) (n : Fin w.r → ℕ)
    (s : Finset (Fin w.r)) :
    rootDiagUnit τ (∏ a ∈ s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)) ∈ T₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [show (∏ a ∈ (∅ : Finset (Fin w.r)),
        corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)) = 1 by simp, rootDiagUnit_one]
      exact T₀.one_mem
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, rootDiagUnit_mul]
      exact T₀.mul_mem (mem_rootDiag_single d w n x) ih

private theorem coord_rootDiag_single
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) (n : Fin w.r → ℕ)
    (x : Fin w.r) :
    d.coord (Additive.ofMul (⟨rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x)),
      mem_rootDiag_single d w n x⟩ : ↥T₀)) = n x • ExcRaw.coroot m (w.b x) := by
  have hH : rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) d.ζ)
      = rootDiagUnit τ (fun j => d.ζ ^ corootPair (d.γ (w.b x)) (Pi.single j 1)) := by
    rw [corootTupleHom_apply]
  have h1 : (⟨rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x)),
      mem_rootDiag_single d w n x⟩ : ↥T₀)
      = (⟨rootDiagUnit τ (fun j => d.ζ ^ corootPair (d.γ (w.b x)) (Pi.single j 1)),
          d.coroot_mem (w.b x)⟩ : ↥T₀) ^ n x := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x))
      = (rootDiagUnit τ
        (fun j => d.ζ ^ corootPair (d.γ (w.b x)) (Pi.single j 1))) ^ n x
    rw [map_pow, ← rootDiagUnit_pow, hH]
  rw [h1, ofMul_pow, map_nsmul, d.coord_coroot (w.b x)]

private theorem coord_rootDiag_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
    {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {c : Finset (ExcRaw.Root m)}
    (d : ExcCoordDatum S T₀ m) (w : ExcRaw.SatWitness m c) (n : Fin w.r → ℕ)
    (s : Finset (Fin w.r)) :
    d.coord (Additive.ofMul (⟨rootDiagUnit τ
        (∏ a ∈ s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)),
      mem_rootDiag_prod d w n s⟩ : ↥T₀))
      = ∑ a ∈ s, n a • ExcRaw.coroot m (w.b a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (⟨rootDiagUnit τ (∏ a ∈ (∅ : Finset (Fin w.r)),
            corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)),
          mem_rootDiag_prod d w n ∅⟩ : ↥T₀) = 1 := by
        apply Subtype.ext
        show rootDiagUnit τ (∏ a ∈ (∅ : Finset (Fin w.r)),
          corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)) = (1 : ModGL τ L)
        rw [show (∏ a ∈ (∅ : Finset (Fin w.r)),
          corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)) = 1 by simp, rootDiagUnit_one]
      rw [hone, Finset.sum_empty]
      simp
  | insert x s hx ih =>
      have hprod : (∏ a ∈ insert x s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a))
          = corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x)
            * ∏ a ∈ s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a) :=
        Finset.prod_insert hx
      have helem : (⟨rootDiagUnit τ (∏ a ∈ insert x s,
            corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)),
          mem_rootDiag_prod d w n (insert x s)⟩ : ↥T₀)
          = (⟨rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x)),
              mem_rootDiag_single d w n x⟩ : ↥T₀)
            * ⟨rootDiagUnit τ (∏ a ∈ s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)),
              mem_rootDiag_prod d w n s⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        show rootDiagUnit τ (∏ a ∈ insert x s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a))
          = rootDiagUnit τ (corootTupleHom (d.γ (w.b x)) (d.ζ ^ n x))
            * rootDiagUnit τ (∏ a ∈ s, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a))
        rw [hprod, rootDiagUnit_mul]
      rw [helem, Finset.sum_insert hx, ofMul_mul, map_add,
        coord_rootDiag_single d w n x, ih]

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

theorem coord_mem_inside_of_coordTuple (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)}
    (w : ExcRaw.SatWitness m c) {Δ : Finset (Fin τ.rank → ℤ)} (hΔ : ∀ β ∈ Δ, β ∈ codeRoots d.γ c)
    (x : (Fin τ.rank → ℤ) → Lˣ) {t : ↥T₀}
    (ht : (t : ModGL τ L) = rootDiagUnit τ (coordTuple Δ x)) :
    d.coord (Additive.ofMul t) ∈ ExcRaw.inside m c := by
  classical
  obtain ⟨y, hy⟩ := exists_corootTuple_prod d w hΔ x
  have hBT : (((t ^ w.e : ↥T₀) : ModGL τ L))
      = rootDiagUnit τ (∏ a, corootTupleHom (d.γ (w.b a)) (y a)) := by
    rw [Subgroup.coe_zpow, ht,
      show rootDiagUnit τ (coordTuple Δ x) ^ w.e = rootDiagUnit τ ((coordTuple Δ x) ^ w.e)
        from (map_zpow (rootDiagUnitHom τ L) _ _).symm, hy]
  have hrow : ∀ a'' : ExcRaw.Root m, ∃ n : ℕ,
      ∏ a, (y a) ^ ExcRaw.pairing m a'' (w.b a) = d.ζ ^ n := by
    intro a''
    refine ⟨(ExcRaw.root m a'' (d.coord (Additive.ofMul (t ^ w.e)))).val, ?_⟩
    have h1 := d.rootChar_eq (t ^ w.e) _ hBT a''
    have h2 : rootChar (∏ a, corootTupleHom (d.γ (w.b a)) (y a)) (d.γ a'')
        = ∏ a, (y a) ^ ExcRaw.pairing m a'' (w.b a) := by
      rw [rootChar_corootProd Finset.univ (fun a => d.γ (w.b a)) y
        (fun a _ => d.isRoot (w.b a)) (d.γ a'')]
      exact Finset.prod_congr rfl fun a _ => by rw [d.pairing_eq a'' (w.b a)]
    exact h2.symm.trans h1
  have hP3 : ∀ a'' : ExcRaw.Root m,
      (∏ a, (y a) ^ ExcRaw.pairing m a'' (w.b a)) ^ 3 = 1 := by
    intro a''
    obtain ⟨n, hn⟩ := hrow a''
    rw [hn, ← pow_mul, mul_comm n 3, pow_mul, d.ζ_pow_three, one_pow]
  have hmul : ∀ a, ∏ a'', (∏ a', (y a') ^ ExcRaw.pairing m (w.k a'') (w.b a')) ^ w.A a a''
      = y a ^ w.D := by
    intro a
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow_eq_zpow_sum]
    have hexp : ∀ a', ∑ a'', ExcRaw.pairing m (w.k a'') (w.b a') * w.A a a''
        = if a = a' then w.D else 0 := by
      intro a'
      rw [← w.mul_eq a a']
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    simp only [hexp]
    rw [Finset.prod_eq_single a
      (fun b _ hb => by rw [if_neg (fun h => hb h.symm), zpow_zero])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [if_pos rfl]
  have hcube : ∀ a, (y a ^ w.D) ^ 3 = 1 := by
    intro a
    have h : (∏ a'', (∏ a', (y a') ^ ExcRaw.pairing m (w.k a'') (w.b a')) ^ w.A a a'')
        ^ 3 = 1 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun a'' _ => pow_three_zpow (hP3 (w.k a'')) (w.A a a'')
    rw [hmul a] at h
    exact h
  have heval : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  have he0 : ((w.e : ℤ) : ZMod 3) ≠ 0 := fun h =>
    w.not_three_dvd_e ((ZMod.intCast_zmod_eq_zero_iff_dvd w.e 3).mp h)
  have hD0 : ((w.D : ℤ) : ZMod 3) ≠ 0 := fun h =>
    w.not_three_dvd_D ((ZMod.intCast_zmod_eq_zero_iff_dvd w.D 3).mp h)
  obtain ⟨s, hs⟩ : ∃ s : ℤ, w.e * w.D * s ≡ 1 [ZMOD 3] := by
    rcases heval _ he0 with he1 | he1 <;> rcases heval _ hD0 with hD1 | hD1
    · exact ⟨1, (ZMod.intCast_eq_intCast_iff (w.e * w.D * 1) 1 3).mp
        (by push_cast [he1, hD1]; decide)⟩
    · exact ⟨2, (ZMod.intCast_eq_intCast_iff (w.e * w.D * 2) 1 3).mp
        (by push_cast [he1, hD1]; decide)⟩
    · exact ⟨2, (ZMod.intCast_eq_intCast_iff (w.e * w.D * 2) 1 3).mp
        (by push_cast [he1, hD1]; decide)⟩
    · exact ⟨1, (ZMod.intCast_eq_intCast_iff (w.e * w.D * 1) 1 3).mp
        (by push_cast [he1, hD1]; decide)⟩
  have ht_pow : (t : ModGL τ L) ^ (w.e * w.D * s) = (t : ModGL τ L) := by
    have ht3 : (t : ModGL τ L) ^ 3 = 1 := (d.le_fullThreeTorus t.2).2
    have h' : (t : ModGL τ L) ^ (w.e * w.D * s) = (t : ModGL τ L) ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq]
      have hd : ((orderOf (t : ModGL τ L) : ℕ) : ℤ) ∣ ((3 : ℕ) : ℤ) := by
        exact_mod_cast orderOf_dvd_of_pow_eq_one ht3
      exact hs.of_dvd hd
    rwa [zpow_one] at h'
  have hz3 : ∀ a, (y a ^ (w.D * s)) ^ 3 = 1 := by
    intro a
    rw [zpow_mul]
    exact pow_three_zpow (hcube a) s
  have hdecomp : (t : ModGL τ L)
      = rootDiagUnit τ (∏ a, corootTupleHom (d.γ (w.b a)) (y a ^ (w.D * s))) := by
    calc (t : ModGL τ L)
        = (t : ModGL τ L) ^ (w.e * w.D * s) := ht_pow.symm
      _ = ((t : ModGL τ L) ^ w.e) ^ (w.D * s) := by
            rw [show w.e * w.D * s = w.e * (w.D * s) by ring, zpow_mul]
      _ = (rootDiagUnit τ (∏ a, corootTupleHom (d.γ (w.b a)) (y a))) ^ (w.D * s) := by
            rw [← Subgroup.coe_zpow, hBT]
      _ = rootDiagUnit τ ((∏ a, corootTupleHom (d.γ (w.b a)) (y a)) ^ (w.D * s)) :=
            (map_zpow (rootDiagUnitHom τ L) _ _).symm
      _ = rootDiagUnit τ (∏ a, corootTupleHom (d.γ (w.b a)) (y a ^ (w.D * s))) := by
            congr 1
            rw [← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).symm
  have hζo : orderOf d.ζ = 3 := orderOf_eq_prime d.ζ_pow_three d.ζ_ne_one
  have hprim : IsPrimitiveRoot d.ζ 3 := hζo ▸ IsPrimitiveRoot.orderOf d.ζ
  choose n hn using fun a =>
    hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 _).2 (hz3 a))
  have ht_eq : t = ⟨rootDiagUnit τ (∏ a, corootTupleHom (d.γ (w.b a)) (d.ζ ^ n a)),
      mem_rootDiag_prod d w n Finset.univ⟩ := by
    apply Subtype.ext
    rw [hdecomp]
    congr 1
    exact Finset.prod_congr rfl fun a _ => by rw [(hn a).2]
  rw [ht_eq, coord_rootDiag_prod d w n Finset.univ]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hx : ExcRaw.coroot m (w.b a) ∈ ExcRaw.inside m c :=
    Submodule.subset_span ⟨w.b a, by simpa using w.b_mem a, rfl⟩
  have hy : ((n a : ℕ) : ZMod 3) • ExcRaw.coroot m (w.b a) ∈ ExcRaw.inside m c :=
    Submodule.smul_mem _ _ hx
  simpa only [Nat.cast_smul_eq_nsmul] using hy


theorem ggLinImage_codeComponent_le_inside (d : ExcCoordDatum S T₀ m)
    {c : Finset (ExcRaw.Root m)} (w : ExcRaw.SatWitness m c) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (hJ : unionRoots χ J = codeRoots d.γ c) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ c) ≤ ExcRaw.inside m c := by
  intro v hv
  have ht : ((Additive.toMul (d.coord.symm v) : ↥T₀) : ModGL τ L)
      ∈ codeComponent S d.γ c :=
    (mem_ggLinImage d.coord (codeComponent S d.γ c) v).mp hv
  obtain ⟨Δ, x, hΔ, htup⟩ :=
    exists_coordTuple_of_mem_codeComponent d hJ (Additive.toMul (d.coord.symm v)).2 ht
  have hmem := coord_mem_inside_of_coordTuple d w hΔ x htup
  simpa using hmem

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
