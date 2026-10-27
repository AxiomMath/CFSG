module

public import Certificates.Data.CFSGNative.YGroups.DCE.Omega
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 Pointwise

@[expose] def rowFinset (n : ℕ) (D : XData) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∃ k < D.m, D.XT[D.m * i + k]! = (x : ℕ)

@[expose] def listFinset (n : ℕ) (X0 : Array ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∃ k < X0.size, X0[k]! = (x : ℕ)

theorem mem_rowFinset {n : ℕ} {D : XData} {i : ℕ} {x : Fin n} :
    x ∈ rowFinset n D i ↔ ∃ k < D.m, D.XT[D.m * i + k]! = (x : ℕ) := by
  simp [rowFinset]

theorem mem_listFinset {n : ℕ} {X0 : Array ℕ} {x : Fin n} :
    x ∈ listFinset n X0 ↔ ∃ k < X0.size, X0[k]! = (x : ℕ) := by
  simp [listFinset]

theorem sumMod_eq_sum_range (m : ℕ) (f : ℕ → ℕ) : sumMod m f = ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp [sumMod]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [sumMod, Nat.fold_succ]

theorem sum_range_eq_sum_finset {m n : ℕ} (f W : ℕ → ℕ) (hlt : ∀ k < m, f k < n)
    (hinj : ∀ k₁ < m, ∀ k₂ < m, f k₁ = f k₂ → k₁ = k₂) :
    ∑ k ∈ Finset.range m, W (f k) =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n => ∃ k < m, f k = (x : ℕ)), W (x : ℕ) := by
  refine Finset.sum_bij (fun k hk => (⟨f k, hlt k (Finset.mem_range.1 hk)⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, k, Finset.mem_range.1 hk, rfl⟩
  · intro a ha b hb hab
    exact hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) (congrArg Fin.val hab)
  · intro x hx
    obtain ⟨-, k, hk, hkx⟩ := Finset.mem_filter.1 hx
    exact ⟨k, Finset.mem_range.2 hk, Fin.ext hkx⟩
  · intro k hk
    rfl

structure XtFacts (D : XData) (gens : Array (Array ℕ)) (X0 : Array ℕ) (fix : List ℕ) : Prop where
  m_eq : D.m = X0.size
  X0_lt : ∀ a < X0.size, X0[a]! < D.n
  X0_inj : ∀ a < X0.size, ∀ b < X0.size, X0[a]! = X0[b]! → a = b
  row0 : ∀ k < D.m, D.XT[k]! = X0[k]!
  fix_lt : ∀ l ∈ fix, l < gens.size
  fix_maps : ∀ l ∈ fix, ∀ a < X0.size, X0.contains ((gens[l]!)[X0[a]!]!) = true
  tree : ∀ i < D.N, i ≠ 0 → D.par[i]! < D.N ∧ D.lab[i]! < gens.size ∧
    D.dist[D.par[i]!]! < D.dist[i]! ∧
    ∀ k < D.m, D.XT[D.m * i + k]! = (gens[D.lab[i]!]!)[D.XT[D.m * D.par[i]! + k]!]!
  find_spec : ∀ i < D.N, D.find.get? (rowHash D i) = some i

theorem xtFacts {D : XData} {gens : Array (Array ℕ)} {X0 : Array ℕ} {fix : List ℕ}
    (h : xtOK D gens X0 fix = true) : XtFacts D gens X0 fix := by
  simp only [xtOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq, List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have := allLt_spec h9 ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro a ha b hb hab
    have := allLt_spec h9 ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h2' := allLt_spec this.2 hb
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2'
    rcases h2' with h2' | h2'
    · exact h2'
    · exact absurd hab h2'
  · intro k hk
    have := allLt_spec h10 hk
    simpa using this
  · intro l hl
    exact (h11 l hl).1
  · intro l hl a ha
    exact allLt_spec (h11 l hl).2 ha
  · intro i hi hi0
    have := allLt_spec h12 hi
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h0 | ⟨⟨⟨hp, hl⟩, hd⟩, hk⟩
    · exact absurd h0 hi0
    · refine ⟨hp, hl, hd, fun k hk' => ?_⟩
      have := allLt_spec hk hk'
      simpa using this
  · intro i hi
    have := allLt_spec h13 hi
    simpa using this

theorem rowHash_eq_sum {n : ℕ} {D : XData} {i : ℕ} (hlt : ∀ k < D.m, D.XT[D.m * i + k]! < n)
    (hinj : ∀ k₁ < D.m, ∀ k₂ < D.m, D.XT[D.m * i + k₁]! = D.XT[D.m * i + k₂]! → k₁ = k₂) :
    rowHash D i = ∑ x ∈ rowFinset n D i, D.R[(x : ℕ)]! := by
  rw [rowHash, sumMod_eq_sum_range]
  exact sum_range_eq_sum_finset (fun k => D.XT[D.m * i + k]!) (fun y => D.R[y]!) hlt hinj

theorem imgHash_eq_sum {n : ℕ} {D : XData} {σ : Array ℕ} {i : ℕ}
    (hlt : ∀ k < D.m, σ[D.XT[D.m * i + k]!]! < n)
    (hinj : ∀ k₁ < D.m, ∀ k₂ < D.m,
      σ[D.XT[D.m * i + k₁]!]! = σ[D.XT[D.m * i + k₂]!]! → k₁ = k₂) :
    imgHash D σ i = ∑ x ∈ Finset.univ.filter
      (fun x : Fin n => ∃ k < D.m, σ[D.XT[D.m * i + k]!]! = (x : ℕ)), D.R[(x : ℕ)]! := by
  rw [imgHash, sumMod_eq_sum_range]
  exact sum_range_eq_sum_finset (fun k => σ[D.XT[D.m * i + k]!]!) (fun y => D.R[y]!) hlt hinj

theorem imgFinset_eq_smul {n : ℕ} {D : XData} {Γ : Subgroup (Equiv.Perm (Fin n))} {σ : Array ℕ}
    {e : Γ} (hσ : Rep n σ (e : Equiv.Perm (Fin n))) {i : ℕ}
    (hlt : ∀ k < D.m, D.XT[D.m * i + k]! < n) :
    Finset.univ.filter (fun x : Fin n => ∃ k < D.m, σ[D.XT[D.m * i + k]!]! = (x : ℕ)) =
      e • rowFinset n D i := by
  ext x
  rw [Finset.mem_filter, Finset.mem_smul_finset]
  constructor
  · rintro ⟨-, k, hk, hkx⟩
    refine ⟨⟨D.XT[D.m * i + k]!, hlt k hk⟩, mem_rowFinset.2 ⟨k, hk, rfl⟩, ?_⟩
    apply Fin.ext
    exact ((hσ ⟨D.XT[D.m * i + k]!, hlt k hk⟩).symm).trans hkx
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨k, hk, hkc⟩ := mem_rowFinset.1 hc
    refine ⟨Finset.mem_univ _, k, hk, ?_⟩
    rw [hkc, hσ c]
    exact congrArg Fin.val hcx


theorem fix_lt_of_xtOK {D : XData} {gens : Array (Array ℕ)} {X0 : Array ℕ} {fix : List ℕ}
    (h : xtOK D gens X0 fix = true) {l : ℕ} (hl : l ∈ fix) : l < gens.size :=
  (xtFacts h).fix_lt l hl

theorem exists_index_of_contains {X0 : Array ℕ} {v : ℕ} (hv : X0.contains v = true) :
    ∃ k < X0.size, X0[k]! = v := by
  obtain ⟨i, hi, hiv⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hv)
  exact ⟨i, hi, by rw [getElem!_pos X0 i hi]; exact hiv⟩

section Rows

variable {n : ℕ} {D : XData} {gens : Array (Array ℕ)} {X0 : Array ℕ} {fix : List ℕ}
  (Γ : Subgroup (Equiv.Perm (Fin n))) (g : ℕ → Equiv.Perm (Fin n))
  (hg : ∀ l < gens.size, g l ∈ Γ ∧ Rep n gens[l]! (g l))
  (h : xtOK D gens X0 fix = true) (hn : D.n = n)

include hg h hn

theorem row_good : ∀ i < D.N, (∀ k < D.m, D.XT[D.m * i + k]! < n) ∧
    (∀ k₁ < D.m, ∀ k₂ < D.m, D.XT[D.m * i + k₁]! = D.XT[D.m * i + k₂]! → k₁ = k₂) ∧
    rowFinset n D i ∈ MulAction.orbit Γ (listFinset n X0) := by
  have F := xtFacts h
  have key : ∀ d, ∀ i < D.N, D.dist[i]! = d →
      (∀ k < D.m, D.XT[D.m * i + k]! < n) ∧
      (∀ k₁ < D.m, ∀ k₂ < D.m, D.XT[D.m * i + k₁]! = D.XT[D.m * i + k₂]! → k₁ = k₂) ∧
      rowFinset n D i ∈ MulAction.orbit Γ (listFinset n X0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hdi
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          rw [Nat.mul_zero, Nat.zero_add, F.row0 k hk]
          have := F.X0_lt k (F.m_eq ▸ hk)
          omega
        · intro k₁ hk₁ k₂ hk₂ he
          rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, F.row0 k₁ hk₁, F.row0 k₂ hk₂] at he
          exact F.X0_inj k₁ (F.m_eq ▸ hk₁) k₂ (F.m_eq ▸ hk₂) he
        · have : rowFinset n D 0 = listFinset n X0 := by
            ext x
            rw [mem_rowFinset, mem_listFinset]
            simp only [Nat.mul_zero, Nat.zero_add]
            constructor
            · rintro ⟨k, hk, hkx⟩
              exact ⟨k, F.m_eq ▸ hk, by rw [← F.row0 k hk]; exact hkx⟩
            · rintro ⟨k, hk, hkx⟩
              exact ⟨k, F.m_eq ▸ hk, by rw [F.row0 k (F.m_eq ▸ hk)]; exact hkx⟩
          rw [this]
          exact MulAction.mem_orbit_self _
      · obtain ⟨hpar, hlab, hdist, hrow⟩ := F.tree i hi hi0
        obtain ⟨hp_lt, hp_inj, hp_orb⟩ :=
          ih (D.dist[D.par[i]!]!) (hdi ▸ hdist) D.par[i]! hpar rfl
        obtain ⟨hgl, hrep⟩ := hg D.lab[i]! hlab
        have hent : ∀ (k : ℕ) (hk : k < D.m), D.XT[D.m * i + k]! =
            (((g D.lab[i]!) ⟨D.XT[D.m * D.par[i]! + k]!, hp_lt k hk⟩ : Fin n) : ℕ) := by
          intro k hk
          rw [hrow k hk]
          exact hrep ⟨D.XT[D.m * D.par[i]! + k]!, hp_lt k hk⟩
        have hsm : ∀ c : Fin n, ((⟨g D.lab[i]!, hgl⟩ : Γ) • c) = (g D.lab[i]!) c := fun c => rfl
        have hrowEq : rowFinset n D i = (⟨g D.lab[i]!, hgl⟩ : Γ) • rowFinset n D D.par[i]! := by
          ext x
          rw [Finset.mem_smul_finset, mem_rowFinset]
          constructor
          · rintro ⟨k, hk, hkx⟩
            refine ⟨⟨D.XT[D.m * D.par[i]! + k]!, hp_lt k hk⟩, mem_rowFinset.2 ⟨k, hk, rfl⟩, ?_⟩
            apply Fin.ext
            rw [hsm]
            exact (hent k hk).symm.trans hkx
          · rintro ⟨c, hc, hcx⟩
            obtain ⟨k, hk, hkc⟩ := mem_rowFinset.1 hc
            refine ⟨k, hk, ?_⟩
            rw [hent k hk]
            have hc' : (⟨D.XT[D.m * D.par[i]! + k]!, hp_lt k hk⟩ : Fin n) = c := Fin.ext hkc
            rw [hc', ← hsm c, hcx]
        refine ⟨fun k hk => ?_, fun k₁ hk₁ k₂ hk₂ he => ?_, ?_⟩
        · rw [hent k hk]
          exact Fin.is_lt _
        · rw [hent k₁ hk₁, hent k₂ hk₂] at he
          have h1 := (g D.lab[i]!).injective (Fin.ext he)
          exact hp_inj k₁ hk₁ k₂ hk₂ (congrArg Fin.val h1)
        · obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hp_orb
          refine ⟨⟨g D.lab[i]!, hgl⟩ * a, ?_⟩
          show ((⟨g D.lab[i]!, hgl⟩ * a : Γ)) • listFinset n X0 = rowFinset n D i
          rw [mul_smul, ha, hrowEq]
  exact fun i hi => key _ i hi rfl

theorem rowFinset_mem_orbit :
    ∀ i < D.N, rowFinset n D i ∈ MulAction.orbit Γ (listFinset n X0) :=
  fun i hi => (row_good Γ g hg h hn i hi).2.2

theorem rowFinset_injOn :
    ∀ i < D.N, ∀ j < D.N, rowFinset n D i = rowFinset n D j → i = j := by
  intro i hi j hj hij
  have F := xtFacts h
  obtain ⟨hi1, hi2, -⟩ := row_good Γ g hg h hn i hi
  obtain ⟨hj1, hj2, -⟩ := row_good Γ g hg h hn j hj
  have e1 : rowHash D i = rowHash D j := by
    rw [rowHash_eq_sum hi1 hi2, rowHash_eq_sum hj1 hj2, hij]
  have h1 := F.find_spec i hi
  rw [e1, F.find_spec j hj] at h1
  exact (Option.some.inj h1).symm

theorem rows_card : ((Finset.range D.N).image (rowFinset n D)).card = D.N := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact rowFinset_injOn Γ g hg h hn a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) hab

theorem rows_subset_orbit :
    (↑((Finset.range D.N).image (rowFinset n D)) : Set (Finset (Fin n))) ⊆
      MulAction.orbit Γ (listFinset n X0) := by
  intro s hs
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
  exact rowFinset_mem_orbit Γ g hg h hn j (Finset.mem_range.1 hj)

theorem card_orbit_ge : D.N ≤ (MulAction.orbit Γ (listFinset n X0)).ncard := by
  have h1 := Set.ncard_le_ncard (rows_subset_orbit Γ g hg h hn) (Set.toFinite _)
  rwa [Set.ncard_coe_finset, rows_card Γ g hg h hn] at h1

omit hn in
theorem fix_smul_listFinset :
    ∀ (l : ℕ) (hl : l ∈ fix), (⟨g l, (hg l (fix_lt_of_xtOK h hl)).1⟩ : Γ) • listFinset n X0 =
      listFinset n X0 := by
  intro l hl
  have F := xtFacts h
  have hgl := hg l (F.fix_lt l hl)
  have hsub : (⟨g l, hgl.1⟩ : Γ) • listFinset n X0 ⊆ listFinset n X0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_smul_finset.1 hy
    obtain ⟨k, hk, hkc⟩ := mem_listFinset.1 hc
    have hcont := F.fix_maps l hl k hk
    have h1 : (gens[l]!)[X0[k]!]! = (((g l) c : Fin n) : ℕ) := by
      rw [hkc]
      exact hgl.2 c
    rw [h1] at hcont
    obtain ⟨k', hk', hk'eq⟩ := exists_index_of_contains hcont
    exact mem_listFinset.2 ⟨k', hk', hk'eq⟩
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

theorem act_spec (hcard : (MulAction.orbit Γ (listFinset n X0)).ncard ≤ D.N)
    {σ : Array ℕ} {e : Γ} (hσ : Rep n σ (e : Equiv.Perm (Fin n))) {i : ℕ} (hi : i < D.N) :
    act D σ i < D.N ∧ rowFinset n D (act D σ i) = e • rowFinset n D i := by
  have F := xtFacts h
  have hT : (↑((Finset.range D.N).image (rowFinset n D)) : Set (Finset (Fin n))) =
      MulAction.orbit Γ (listFinset n X0) :=
    Set.eq_of_subset_of_ncard_le (rows_subset_orbit Γ g hg h hn)
      (by rw [Set.ncard_coe_finset, rows_card Γ g hg h hn]; exact hcard) (Set.toFinite _)
  obtain ⟨hi1, hi2, hiorb⟩ := row_good Γ g hg h hn i hi
  have hmem : e • rowFinset n D i ∈ MulAction.orbit Γ (listFinset n X0) := by
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hiorb
    exact MulAction.mem_orbit_iff.2 ⟨e * a, by rw [mul_smul, ha]⟩
  rw [← hT] at hmem
  obtain ⟨j, hj, hjrow⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hmem)
  have hjN : j < D.N := Finset.mem_range.1 hj
  obtain ⟨hj1, hj2, -⟩ := row_good Γ g hg h hn j hjN
  have hσk : ∀ (k : ℕ) (hk : k < D.m), σ[D.XT[D.m * i + k]!]! =
      ((((e : Equiv.Perm (Fin n)) ⟨D.XT[D.m * i + k]!, hi1 k hk⟩ : Fin n)) : ℕ) :=
    fun k hk => hσ ⟨D.XT[D.m * i + k]!, hi1 k hk⟩
  have hlt : ∀ k < D.m, σ[D.XT[D.m * i + k]!]! < n := fun k hk => by
    rw [hσk k hk]
    exact Fin.is_lt _
  have hinj : ∀ k₁ < D.m, ∀ k₂ < D.m,
      σ[D.XT[D.m * i + k₁]!]! = σ[D.XT[D.m * i + k₂]!]! → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ he
    rw [hσk k₁ hk₁, hσk k₂ hk₂] at he
    exact hi2 k₁ hk₁ k₂ hk₂ (congrArg Fin.val ((e : Equiv.Perm (Fin n)).injective (Fin.ext he)))
  have himg : imgHash D σ i = rowHash D j := by
    rw [imgHash_eq_sum hlt hinj, imgFinset_eq_smul hσ hi1, ← hjrow, rowHash_eq_sum hj1 hj2]
  have hf : D.find[rowHash D j]? = some j := F.find_spec j hjN
  have hact : act D σ i = j := by
    unfold act
    rw [himg, Std.HashMap.getD_eq_getD_getElem?, hf]
    rfl
  exact ⟨by rw [hact]; exact hjN, by rw [hact, hjrow]⟩

end Rows

end CFSG.YGroups.DCE
