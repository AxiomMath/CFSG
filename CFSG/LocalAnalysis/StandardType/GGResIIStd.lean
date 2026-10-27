module

public import CFSG.LocalAnalysis.StandardType.GGResIISym
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggStdEntry {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (u v : R) (k : Fin (n + 1)) (l : Fin (n + 2)) : R :=
  if hk : k.val < n then
    if hl : l.val < n then ι (C ⟨k.val, hk⟩ ⟨l.val, hl⟩)
    else if l.val = n then (if k.val = ic.val then ι (-1) else if k.val = ib.val then v else ι 0)
    else ι 0
  else
    if l.val < n then (if l.val = ic.val then ι (-1) else if l.val = ib.val then u else ι 0)
    else if l.val = n then ι 2
    else ι 1

@[expose] def ggStdTable {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (u v : R) : Fin (n + 1) → Vector R (n + 2) :=
  fun k => Vector.ofFn (ggStdEntry ι C ib ic u v k)

@[expose] def ggStdTableSym {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) :
    Fin (n + 1) → Vector GGPoly (n + 2) :=
  ggStdTable GGPoly.const C ib ic GGPoly.U GGPoly.V

theorem ggStdTable_eval {S : Type} [CommRing S] (u v : S) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) :
    GGPoly.evalT u v (ggStdTableSym C ib ic) = ggStdTable (Int.cast) C ib ic u v := by
  funext k
  ext l hl
  change (GGPoly.evalV u v (ggStdTableSym C ib ic k)).get ⟨l, hl⟩ =
    (ggStdTable (Int.cast) C ib ic u v k).get ⟨l, hl⟩
  rw [GGPoly.get_evalV, ggStdTableSym, ggStdTable, ggStdTable, Vector.get_ofFn, Vector.get_ofFn]
  unfold ggStdEntry
  split_ifs <;> simp [GGPoly.eval_const]

section Concl

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def GGResIIConcl {n : ℕ} (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (h : Fin (n + 1) → V)
    (α : Fin (n + 1) → Module.Dual (ZMod p) V) (ib : Fin n) : Prop :=
  (∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
    (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Fin n, j ≠ ib ∧ j' ≠ ib ∧
      α j'.castSucc (ψ (h j.castSucc)) * α j.castSucc (ψ⁻¹ (h j'.castSucc)) ∉
        ({0, 1, 2, 3, 4} : Set (ZMod p))) ∨
    ZS.LinWeyl p (Subgroup.closure (Set.range g))

theorem ggResII_five_le_of_not_mem {z : ZMod p} (hz : z ∉ ({0, 1, 2, 3, 4} : Set (ZMod p))) :
    5 ≤ p := by
  by_contra hp
  push Not at hp
  apply hz
  have hlt : z.val < 5 := lt_trans (ZMod.val_lt z) hp
  have hz' : z = ((z.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val z).symm
  rw [hz']
  interval_cases hv : z.val <;> simp

theorem ggResII_sum_two {R : Type} [CommRing R] {n : ℕ} {b c : Fin n} (hbc : b ≠ c) (u : R)
    (f : Fin n → R) :
    ∑ i, (if i.val = c.val then (-1 : R) else if i.val = b.val then u else 0) * f i =
      -f c + u * f b := by
  have hsplit : ∀ i : Fin n, (if i.val = c.val then (-1 : R) else if i.val = b.val then u else 0) *
      f i = (if i = c then -f c else 0) + (if i = b then u * f b else 0) := by
    intro i
    by_cases hic : i = c
    · subst hic
      have : i ≠ b := fun h => hbc h.symm
      simp [this]
    · by_cases hib : i = b
      · subst hib
        have : i.val ≠ c.val := fun h => hic (Fin.ext h)
        simp [this, hic]
      · have h1 : i.val ≠ c.val := fun h => hic (Fin.ext h)
        have h2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
        simp [h1, h2, hic, hib]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp

section Entries

variable {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (u v : R)

theorem ggStdEntry_LL (j i : Fin n) :
    ggStdEntry ι C ib ic u v j.castSucc i.castSucc.castSucc = ι (C j i) := by
  unfold ggStdEntry
  simp

theorem ggStdEntry_La (j : Fin n) :
    ggStdEntry ι C ib ic u v j.castSucc (Fin.last n).castSucc =
      if j.val = ic.val then ι (-1) else if j.val = ib.val then v else ι 0 := by
  unfold ggStdEntry
  simp

theorem ggStdEntry_aL (i : Fin n) :
    ggStdEntry ι C ib ic u v (Fin.last n) i.castSucc.castSucc =
      if i.val = ic.val then ι (-1) else if i.val = ib.val then u else ι 0 := by
  unfold ggStdEntry
  simp

theorem ggStdEntry_aa : ggStdEntry ι C ib ic u v (Fin.last n) (Fin.last n).castSucc = ι 2 := by
  unfold ggStdEntry
  simp

theorem ggStdEntry_Lx (j : Fin n) :
    ggStdEntry ι C ib ic u v j.castSucc (Fin.last (n + 1)) = ι 0 := by
  unfold ggStdEntry
  simp

theorem ggStdEntry_ax : ggStdEntry ι C ib ic u v (Fin.last n) (Fin.last (n + 1)) = ι 1 := by
  unfold ggStdEntry
  simp

end Entries

theorem ggResII_conic {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} (hbc : ib ≠ ic)
    {u v : ZMod p} {h : Fin (n + 1) → V} {x : V} {α : Fin (n + 1) → Module.Dual (ZMod p) V}
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc))
    (adj : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (hadj : adj * C = d • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    (adj ic ic : ZMod p) - u * adj ib ic - v * adj ic ib + u * v * adj ib ib = 2 * d := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hdep
  have hpair : ∀ k l : Fin (n + 1), α k (h l) =
      ggStdEntry (Int.cast) C ib ic u v k l.castSucc := by
    intro k l
    rw [hT.1 k l]
    simp [ggStdTable, Vector.get_ofFn]
  set col : Fin n → ZMod p := fun j =>
    if j.val = ic.val then (-1 : ZMod p) else if j.val = ib.val then v else 0 with hcoldef
  set row : Fin n → ZMod p := fun i =>
    if i.val = ic.val then (-1 : ZMod p) else if i.val = ib.val then u else 0 with hrowdef
  have hcol : ∀ j : Fin n, col j = ∑ i, c i * (C j i : ZMod p) := by
    intro j
    have h1 := congrArg (α j.castSucc) hc
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul, hpair, ggStdEntry_LL, ggStdEntry_La] at h1
    rw [hcoldef]
    simp only
    rw [h1]
    split_ifs <;> simp
  have hrow : (2 : ZMod p) = ∑ i, row i * c i := by
    have h1 := congrArg (α (Fin.last n)) hc
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul, hpair, ggStdEntry_aL, ggStdEntry_aa] at h1
    rw [show ((2 : ℤ) : ZMod p) = 2 by norm_num] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrowdef, mul_comm]
    simp only
    split_ifs <;> simp
  have hadj' : ∀ i : Fin n, ∑ j, (adj i j : ZMod p) * col j = d * c i := by
    intro i
    simp only [hcol, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ j, (adj i j : ZMod p) * (c m * (C j m : ZMod p)) =
        c m * (((adj * C) i m : ℤ) : ZMod p) := by
      intro m
      rw [Matrix.mul_apply, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    simp only [hm, hadj, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun m _ hm => by simp [Ne.symm hm])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp only [if_true, mul_one]
    ring
  have key : ∑ i, row i * ∑ j, (adj i j : ZMod p) * col j = 2 * d := by
    simp only [hadj']
    rw [hrow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hrowsum : ∑ i, row i * ∑ j, (adj i j : ZMod p) * col j =
      -(∑ j, (adj ic j : ZMod p) * col j) + u * ∑ j, (adj ib j : ZMod p) * col j :=
    ggResII_sum_two hbc u (fun i => ∑ j, (adj i j : ZMod p) * col j)
  have hcolsum : ∀ i : Fin n,
      ∑ j, (adj i j : ZMod p) * col j = -(adj i ic : ZMod p) + v * adj i ib := by
    intro i
    rw [← ggResII_sum_two hbc v (fun j => (adj i j : ZMod p))]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrowsum, hcolsum, hcolsum] at key
  linear_combination key

end Concl

end CFSG.StandardType
