module

public import CFSG.Sporadic.Co2Smith.RigidModule

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

namespace LocalConfig

variable (c : LocalConfig.{u})

@[expose] noncomputable def yb
    (k : ℕ) (e : Bool) (m : c.M) : c.M :=
  if e then c.mA (frS k) m else m

theorem yb_false
    (k : ℕ) (m : c.M) : c.yb k false m = m := rfl

theorem yb_true
    (k : ℕ) (m : c.M) : c.yb k true m = c.mA (frS k) m := rfl

theorem yb_mul
    (k : ℕ) (e : Bool) (m n : c.M) : c.yb k e (m * n) = c.yb k e m * c.yb k e n := by
  cases e
  · rfl
  · exact map_mul _ m n

theorem yb_one
    (k : ℕ) (e : Bool) : c.yb k e 1 = 1 := by
  cases e
  · rfl
  · exact map_one _

@[expose] noncomputable def vv
    (e0 e1 e2 : Bool) : c.M := c.yb 0 e0 (c.yb 2 e1 (c.yb 4 e2 c.w))

@[expose] noncomputable def v
    (a : Fin 8) : c.M :=
  c.vv (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2)

@[expose] noncomputable def β
    (u : Fin 8 → ZMod 2) : c.M := ∏ a, c.v a ^ (u a).val

theorem β_add
    (u u' : Fin 8 → ZMod 2) : c.β (u + u') = c.β u * c.β u' := by
  rw [β, β, β, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Pi.add_apply, pow_val_add (c.sq_M _)]

theorem β_zero :
    c.β 0 = 1 := by
  rw [β]
  exact Finset.prod_eq_one fun a _ => by rw [Pi.zero_apply, ZMod.val_zero, pow_zero]

theorem β_single
    (a : Fin 8) : c.β (Pi.single a 1) = c.v a := by
  rw [β, Finset.prod_eq_single a]
  · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZMod.val_zero, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem pow_val_sum
    (x : c.M) (hx : x * x = 1) {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    x ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, x ^ (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, pow_val_add hx, ih]

theorem pow_val_mul
    (x : c.M) (a b : ZMod 2) : x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rcases zmod_two_cases b with rfl | rfl
  · simp
  · rw [mul_one, val_one_two, pow_one]

@[expose] def Rep
    (T : c.M → c.M) (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Prop :=
  ∀ u, T (c.β u) = c.β (A.mulVec u)

theorem rep_of_cols
    (T : c.M →* c.M) (A : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (h : ∀ a, T (c.v a) = c.β fun b => A b a) : c.Rep T A := by
  intro u
  rw [β, map_prod]
  simp only [map_pow, h]
  rw [β]
  simp only [Matrix.mulVec, dotProduct]
  calc ∏ a, (∏ b, c.v b ^ (A b a).val) ^ (u a).val
      = ∏ a, ∏ b, c.v b ^ (A b a * u a).val := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [pow_val_mul]
    _ = ∏ b, ∏ a, c.v b ^ (A b a * u a).val := Finset.prod_comm
    _ = ∏ b, c.v b ^ (∑ a, A b a * u a).val := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [c.pow_val_sum _ (c.sq_M _)]

theorem Rep.comp
    {T T' : c.M → c.M} {A A' : Matrix (Fin 8) (Fin 8) (ZMod 2)} (h : c.Rep T A)
    (h' : c.Rep T' A') : c.Rep (T ∘ T') (A * A') := by
  intro u
  rw [Function.comp_apply, h', h, Matrix.mulVec_mulVec]

theorem rep_id :
    c.Rep id 1 := fun u => by rw [Matrix.one_mulVec]; rfl

theorem rep_congr
    {T T' : c.M → c.M} {A : Matrix (Fin 8) (Fin 8) (ZMod 2)} (h : c.Rep T A)
    (hT : ∀ m, T' m = T m) : c.Rep T' A := fun u => by rw [hT, h]

theorem range_mul
    {x y : c.M} (hx : x ∈ Set.range c.β) (hy : y ∈ Set.range c.β) :
    x * y ∈ Set.range c.β := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨u', rfl⟩ := hy
  exact ⟨u + u', c.β_add u u'⟩

theorem one_mem_range :
    (1 : c.M) ∈ Set.range c.β := ⟨0, c.β_zero⟩

theorem v_mem_range
    (a : Fin 8) : c.v a ∈ Set.range c.β := ⟨_, c.β_single a⟩

theorem vv_mem_range
    (e0 e1 e2 : Bool) : c.vv e0 e1 e2 ∈ Set.range c.β := by
  have h := c.v_mem_range ⟨(if e0 then 1 else 0) + 2 * (if e1 then 1 else 0) +
    4 * (if e2 then 1 else 0), by split_ifs <;> omega⟩
  cases e0 <;> cases e1 <;> cases e2 <;> exact h

theorem mem_range_of_C123
    {s : c.M} (hs : s ∈ c.C123) (e0 e1 e2 : Bool) :
    c.yb 0 e0 (c.yb 2 e1 (c.yb 4 e2 s)) ∈ Set.range c.β := by
  rcases c.eq_w_of_mem hs with rfl | rfl
  · rw [yb_one, yb_one, yb_one]
    exact c.one_mem_range
  · exact c.vv_mem_range e0 e1 e2

theorem yb_comm
    (k l : ℕ) (hk : k < 6) (hl : l < 6) (hkl : k / 2 ≠ l / 2) (e e' : Bool)
    (m : c.M) : c.yb k e (c.yb l e' m) = c.yb l e' (c.yb k e m) := by
  cases e <;> cases e'
  · rfl
  · rfl
  · rfl
  · exact c.mA_comm' hk hl hkl m

theorem β_surjective :
    Function.Surjective c.β := by
  intro m
  obtain ⟨x, hx, x', hx', rfl⟩ := c.decomp1.2 m
  obtain ⟨t1, ht1, t1', ht1', rfl⟩ := c.decomp2.2 x hx
  obtain ⟨t2, ht2, t2', ht2', rfl⟩ := c.decomp2.2 x' hx'
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := c.decomp3.2 t1 ht1
  obtain ⟨s3, hs3, s4, hs4, rfl⟩ := c.decomp3.2 t1' ht1'
  obtain ⟨s5, hs5, s6, hs6, rfl⟩ := c.decomp3.2 t2 ht2
  obtain ⟨s7, hs7, s8, hs8, rfl⟩ := c.decomp3.2 t2' ht2'
  simp only [map_mul]
  refine c.range_mul (c.range_mul (c.range_mul ?_ ?_) (c.range_mul ?_ ?_))
    (c.range_mul (c.range_mul ?_ ?_) (c.range_mul ?_ ?_))
  · exact c.mem_range_of_C123 hs1 false false false
  · exact c.mem_range_of_C123 hs2 false false true
  · exact c.mem_range_of_C123 hs3 false true false
  · exact c.mem_range_of_C123 hs4 false true true
  · exact c.mem_range_of_C123 hs5 true false false
  · exact c.mem_range_of_C123 hs6 true false true
  · exact c.mem_range_of_C123 hs7 true true false
  · exact c.mem_range_of_C123 hs8 true true true

theorem β_bijective :
    Function.Bijective c.β := by
  refine ⟨?_, c.β_surjective⟩
  have hcard : Nat.card (Fin 8 → ZMod 2) ≤ Nat.card c.M := by
    rw [c.card_M, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  exact (Function.Surjective.bijective_of_nat_card_le c.β_surjective hcard).1

theorem β_injective :
    Function.Injective c.β := c.β_bijective.1

theorem Rep.eq_one
    {T : c.M → c.M} {A : Matrix (Fin 8) (Fin 8) (ZMod 2)} (h : c.Rep T A)
    (hT : ∀ m, T m = m) : A = 1 := by
  have hv : ∀ u, A.mulVec u = u := fun u => c.β_injective (by rw [← h, hT])
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  rw [show A i j = (A.col j) i from rfl, this]
  by_cases hij : i = j
  · rw [hij, Pi.single_eq_same, Matrix.one_apply_eq]
  · rw [Pi.single_eq_of_ne hij, Matrix.one_apply_ne hij]

end LocalConfig

end CFSG.Sporadic.Co2Smith
