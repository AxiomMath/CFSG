module

public import CFSG.LieType.Chevalley.StandardParabolicCells

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

abbrev ga : Fin Tag.G2.rank := ⟨0, by decide⟩

abbrev gb : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem g2_cases (i : Fin Tag.G2.rank) : i = ga ∨ i = gb := by
  rcases i with ⟨i, hi⟩
  have hi2 : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sum_g2 (f : Fin Tag.G2.rank → ℤ) : ∑ x, f x = f ga + f gb :=
  Fin.sum_univ_two (f := f)

theorem sab_smul (v : Fin Tag.G2.rank → ℤ) :
    (simple Tag.G2 ga * simple Tag.G2 gb) • v = fun i =>
      if i = ga then 2 * v ga - v gb else 3 * v ga - v gb := by
  have c1 : Tag.G2.cartan ga ga = 2 := rfl
  have c2 : Tag.G2.cartan ga gb = -1 := rfl
  have c3 : Tag.G2.cartan gb ga = -3 := rfl
  have c4 : Tag.G2.cartan gb gb = 2 := rfl
  rw [mul_smul, simple_smul, simple_smul]
  funext i
  rcases g2_cases i with rfl | rfl <;>
    simp [reflect, sum_g2, c1, c2, c3, c4, Pi.single_apply] <;> ring

theorem sab3_not_mem (j : Fin Tag.G2.rank) :
    (simple Tag.G2 ga * simple Tag.G2 gb) ^ 3 ∉ parabolicWeylGroup Tag.G2 {j} := by
  intro h
  have key : ∀ v : Fin Tag.G2.rank → ℤ, (simple Tag.G2 ga * simple Tag.G2 gb) ^ 3 • v =
      (simple Tag.G2 ga * simple Tag.G2 gb) • (simple Tag.G2 ga * simple Tag.G2 gb) •
        (simple Tag.G2 ga * simple Tag.G2 gb) • v := fun v => by
    rw [pow_succ, pow_two, mul_smul, mul_smul]
  have hab : gb ≠ ga := by decide
  rcases g2_cases j with rfl | rfl
  · have h1 := smul_apply_of_mem_parabolicWeylGroup h (Pi.single gb 1) (i := gb)
      (by simp [hab])
    rw [key, sab_smul, sab_smul, sab_smul] at h1
    simp [hab] at h1
  · have h1 := smul_apply_of_mem_parabolicWeylGroup h (Pi.single ga 1) (i := ga)
      (by simp [hab.symm])
    rw [key, sab_smul, sab_smul, sab_smul] at h1
    simp [hab] at h1

section Bruhat

variable {τ : Tag} {K : Type} [Field K]

theorem mem_parabolicWeylGroup_of_canonicalRep_mem
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (h : canonicalRep (coxeterSystem τ) K w ∈ parabolicSubgroup τ K J) :
    w ∈ parabolicWeylGroup τ J := by
  have h' : canonicalRep (coxeterSystem τ) K w ∈ parabolicCells τ K J := by
    rw [← parabolicSubgroup_eq_parabolicCells]
    exact h
  obtain ⟨w', hw', hx⟩ := mem_parabolicCells.1 h'
  by_cases hww : w' = w
  · rwa [hww] at hw'
  · exact absurd (canonicalRep_mem_bruhatCell (K := K) w)
      (Set.disjoint_left.1 (disjoint_bruhatCell hww) hx)

@[expose] def InCoset
    (x : ModGL τ K) (w : WeylGroup τ) : Prop :=
  ∃ k ∈ torusGroup τ K, x = k * canonicalRep (coxeterSystem τ) K w

theorem inCoset_simple
    (i : Fin τ.rank) : InCoset (weylElt τ K i 1) (simple τ i) :=
  ⟨1, one_mem _, by rw [canonicalRep_simple, one_mul]⟩

theorem inCoset_mul
    {x y : ModGL τ K} {w w' : WeylGroup τ} (hx : InCoset x w)
    (hy : InCoset y w') : InCoset (x * y) (w * w') := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨k', hk', rfl⟩ := hy
  obtain ⟨k'', hk'', h⟩ := canonicalRep_mul_mem (R := K) w w'
  have hn := canonicalRep_mem_normalizer (R := K) w
  refine ⟨k * (canonicalRep (coxeterSystem τ) K w * k' * (canonicalRep (coxeterSystem τ) K w)⁻¹) *
    k'', mul_mem (mul_mem hk ((Subgroup.mem_normalizer_iff.mp hn k').mp hk')) hk'', ?_⟩
  calc k * canonicalRep (coxeterSystem τ) K w * (k' * canonicalRep (coxeterSystem τ) K w')
      = k * (canonicalRep (coxeterSystem τ) K w * k' * (canonicalRep (coxeterSystem τ) K w)⁻¹) *
          (canonicalRep (coxeterSystem τ) K w * canonicalRep (coxeterSystem τ) K w') := by group
    _ = _ := by rw [h]; group

end Bruhat

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def g2D (a b : Kˣ) : ModGL Tag.G2 K :=
  torusElt Tag.G2 K ga a * torusElt Tag.G2 K gb b

@[expose] noncomputable def g2N : ModGL Tag.G2 K := weylElt Tag.G2 K ga 1 * weylElt Tag.G2 K gb 1

theorem conj_a_g2D {a b : Kˣ} (hb : b ^ 3 = 1) :
    weylElt Tag.G2 K ga 1 * g2D a b * (weylElt Tag.G2 K ga 1)⁻¹ = g2D a⁻¹ b := by
  have h1 := weylElt_one_mul_torusElt_mul_inv Tag.G2 K ga ga a
  have h2 := weylElt_one_mul_torusElt_mul_inv Tag.G2 K ga gb b
  have c1 : Tag.G2.cartan ga ga = 2 := rfl
  have c3 : Tag.G2.cartan gb ga = -3 := rfl
  rw [c1] at h1
  rw [c3, neg_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hb, torusElt_one,
    mul_one] at h2
  have ha : torusElt Tag.G2 K ga a * torusElt Tag.G2 K ga (a ^ (-2 : ℤ)) =
      torusElt Tag.G2 K ga a⁻¹ := by
    rw [← torusElt_mul]
    congr 1
    group
  unfold g2D
  calc weylElt Tag.G2 K ga 1 * (torusElt Tag.G2 K ga a * torusElt Tag.G2 K gb b) *
        (weylElt Tag.G2 K ga 1)⁻¹
      = (weylElt Tag.G2 K ga 1 * torusElt Tag.G2 K ga a * (weylElt Tag.G2 K ga 1)⁻¹) *
          (weylElt Tag.G2 K ga 1 * torusElt Tag.G2 K gb b * (weylElt Tag.G2 K ga 1)⁻¹) := by
        group
    _ = _ := by rw [h1, h2, ha]

theorem conj_b_g2D (a b : Kˣ) :
    weylElt Tag.G2 K gb 1 * g2D a b * (weylElt Tag.G2 K gb 1)⁻¹ = g2D a (a * b⁻¹) := by
  have h1 := weylElt_one_mul_torusElt_mul_inv Tag.G2 K gb ga a
  have h2 := weylElt_one_mul_torusElt_mul_inv Tag.G2 K gb gb b
  have c2 : Tag.G2.cartan ga gb = -1 := rfl
  have c4 : Tag.G2.cartan gb gb = 2 := rfl
  rw [c2, neg_neg, zpow_one] at h1
  rw [c4] at h2
  unfold g2D
  calc weylElt Tag.G2 K gb 1 * (torusElt Tag.G2 K ga a * torusElt Tag.G2 K gb b) *
        (weylElt Tag.G2 K gb 1)⁻¹
      = (weylElt Tag.G2 K gb 1 * torusElt Tag.G2 K ga a * (weylElt Tag.G2 K gb 1)⁻¹) *
          (weylElt Tag.G2 K gb 1 * torusElt Tag.G2 K gb b * (weylElt Tag.G2 K gb 1)⁻¹) := by
        group
    _ = torusElt Tag.G2 K ga a * (torusElt Tag.G2 K gb a * (torusElt Tag.G2 K gb b *
          torusElt Tag.G2 K gb (b ^ (-2 : ℤ)))) := by rw [h1, h2]; group
    _ = _ := by
        rw [← torusElt_mul, ← torusElt_mul]
        congr 2
        group

theorem g2N_cube_conj (hcube : ∀ t : Kˣ, t ^ 3 = 1) (a b : Kˣ) :
    g2N ^ 3 * g2D a b * (g2N ^ 3)⁻¹ = g2D (K := K) a⁻¹ b⁻¹ := by
  have hc : ∀ a b : Kˣ, g2N * g2D a b * g2N⁻¹ = g2D (K := K) a⁻¹ (a * b⁻¹) := by
    intro a b
    have e : g2N * g2D a b * g2N⁻¹ = weylElt Tag.G2 K ga 1 * (weylElt Tag.G2 K gb 1 * g2D a b *
        (weylElt Tag.G2 K gb 1)⁻¹) * (weylElt Tag.G2 K ga 1)⁻¹ := by
      unfold g2N
      group
    rw [e, conj_b_g2D, conj_a_g2D (hcube _)]
  have e : g2N ^ 3 * g2D a b * (g2N ^ 3)⁻¹ =
      g2N * (g2N * (g2N * g2D a b * g2N⁻¹) * g2N⁻¹) * g2N⁻¹ := by
    rw [pow_three]
    group
  have h2 : a⁻¹⁻¹ * (a⁻¹ * (a * b⁻¹)⁻¹)⁻¹ = b⁻¹ := by
    simp only [inv_inv, mul_inv_rev]
    rw [mul_assoc a b⁻¹ a, mul_comm b⁻¹ a]
    calc a * (a * (a * b⁻¹)) = a ^ 3 * b⁻¹ := by rw [pow_three]; group
      _ = b⁻¹ := by rw [hcube a, one_mul]
  rw [e, hc, hc, hc, h2, inv_inv a⁻¹]

theorem torusElt_inv' (i : Fin Tag.G2.rank) (t : Kˣ) :
    torusElt Tag.G2 K i t⁻¹ = (torusElt Tag.G2 K i t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← torusElt_mul, inv_mul_cancel, torusElt_one])

theorem g2N_cube_conj_torus (hcube : ∀ t : Kˣ, t ^ 3 = 1) {x : ModGL Tag.G2 K}
    (hx : x ∈ torusGroup Tag.G2 K) : g2N ^ 3 * x * (g2N ^ 3)⁻¹ = x⁻¹ := by
  have hx' : x ∈ Subgroup.closure
      (Set.range fun p : Fin Tag.G2.rank × Kˣ => torusElt Tag.G2 K p.1 p.2) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hy
    rcases g2_cases i with h | h
    · have e := g2N_cube_conj (K := K) hcube t 1
      rw [g2D, g2D, torusElt_one, mul_one, inv_one, torusElt_one, mul_one] at e
      rw [h, e, torusElt_inv']
    · have e := g2N_cube_conj (K := K) hcube 1 t
      rw [g2D, g2D, torusElt_one, one_mul, inv_one, torusElt_one, one_mul] at e
      rw [h, e, torusElt_inv']
  | one => rw [mul_one, mul_inv_cancel, inv_one]
  | mul y z hy hz ihy ihz =>
    have hc := mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (R := K) hy)
      (torusGroup_le_diagonalGroup (R := K) hz)
    calc g2N ^ 3 * (y * z) * (g2N ^ 3)⁻¹ =
        (g2N ^ 3 * y * (g2N ^ 3)⁻¹) * (g2N ^ 3 * z * (g2N ^ 3)⁻¹) := by group
      _ = (y * z)⁻¹ := by rw [ihy, ihz, hc, mul_inv_rev]
  | inv y hy ih =>
    calc g2N ^ 3 * y⁻¹ * (g2N ^ 3)⁻¹ = (g2N ^ 3 * y * (g2N ^ 3)⁻¹)⁻¹ := by group
      _ = y⁻¹⁻¹ := by rw [ih]

end Torus

theorem g2N_cube_not_mem_parabolic
    {K : Type} [Field K] (j : Fin Tag.G2.rank) :
    (g2N : ModGL Tag.G2 K) ^ 3 ∉ parabolicSubgroup Tag.G2 K {j} := by
  intro h
  have hN : InCoset (g2N : ModGL Tag.G2 K) (simple Tag.G2 ga * simple Tag.G2 gb) :=
    inCoset_mul (inCoset_simple ga) (inCoset_simple gb)
  obtain ⟨k, hk, he⟩ : InCoset ((g2N : ModGL Tag.G2 K) ^ 3)
      ((simple Tag.G2 ga * simple Tag.G2 gb) ^ 3) := by
    rw [pow_three, pow_three]
    exact inCoset_mul hN (inCoset_mul hN hN)
  have hc : canonicalRep (coxeterSystem Tag.G2) K ((simple Tag.G2 ga * simple Tag.G2 gb) ^ 3) ∈
      parabolicSubgroup Tag.G2 K {j} := by
    have e : canonicalRep (coxeterSystem Tag.G2) K ((simple Tag.G2 ga * simple Tag.G2 gb) ^ 3) =
        k⁻¹ * (g2N : ModGL Tag.G2 K) ^ 3 := by rw [he, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem (torusGroup_le_parabolicSubgroup _ hk)) h
  exact sab3_not_mem j (mem_parabolicWeylGroup_of_canonicalRep_mem hc)

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
