module

public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork
public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep

public section

namespace CFSG.StandardType


open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Lattice

@[expose] def ggSRefl {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (m : N → ℤ) : N → ℤ :=
  m - (∑ i, X j i * m i) • Pi.single j 1

@[expose] def ggSReflR {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (c : N → ℤ) : N → ℤ :=
  c - (∑ i, c i * X i j) • Pi.single j 1

@[expose] def ggSWord {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) :
    List N → (N → ℤ) → (N → ℤ)
  | [], m => m
  | j :: ψ, m => ggSRefl X j (ggSWord X ψ m)

@[expose] def ggSWordR {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) :
    List N → (N → ℤ) → (N → ℤ)
  | [], c => c
  | j :: ψ, c => ggSReflR X j (ggSWordR X ψ c)

end Lattice

section Datum

structure GGExtDatum {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {N : Type} (ι : Additive ↥Bs ≃+ V) (X : Matrix N N ℤ)
    (φ' : N → MulAut ↥Bs) (h' : N → V) (α' : N → Module.Dual (ZMod p) V) : Prop where
  mem : ∀ o, φ' o ∈ ggInduced ⊤ Bs
  lin : ∀ o w, ggLin (p := p) ι (φ' o) w = w - α' o w • h' o
  pair : ∀ i j, α' i (h' j) = (X i j : ZMod p)
  indep : LinearIndependent (ZMod p) h'
  diag : ∀ j, X j j = 2

private theorem latw_single_cast {p : ℕ} {N : Type} [DecidableEq N] (k i : N) :
    (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
      (Pi.single k (1 : ZMod p) : N → ZMod p) i := by
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h]; exact Int.cast_one
  · rw [if_neg h, if_neg h]; exact Int.cast_zero

private theorem latw_single_smul_sum {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {N : Type} [Fintype N] [DecidableEq N] (k : N) (v : N → V) :
    ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) • v i = v k := by
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro i hi
    rw [Pi.single_apply, if_neg hi, zero_smul]
  · rw [Pi.single_apply, if_pos rfl, one_smul]

private theorem latw_single_mul_sum {p : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (k : N) (f : N → ZMod p) :
    ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) * f i = f k := by
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro i hi
    rw [Pi.single_apply, if_neg hi, zero_mul]
  · rw [Pi.single_apply, if_pos rfl, one_mul]

private theorem latw_reflect_involutive {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (o : N) (w : V) :
    ggLin (p := p) ι (φ' o) (ggLin (p := p) ι (φ' o) w) = w := by
  rw [hD.lin o, hD.lin o]
  have hα : α' o (w - α' o w • h' o) = -(α' o w) := by
    rw [map_sub, map_smul, smul_eq_mul, hD.pair o o, hD.diag o]
    ring
  rw [hα, neg_smul]
  abel

private theorem latw_inv_reflection {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (o : N) :
    (ggLin (p := p) ι (φ' o))⁻¹ = ggLin (p := p) ι (φ' o) := by
  have hmul : ggLin (p := p) ι (φ' o) * ggLin (p := p) ι (φ' o) = 1 := by
    refine LinearEquiv.ext (fun w => ?_)
    rw [LinearEquiv.mul_apply, latw_reflect_involutive hD o w]
    rfl
  exact inv_eq_of_mul_eq_one_right hmul

private theorem latw_lin_comb {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (j : N) (m : N → ℤ) :
    ggLin (p := p) ι (φ' j) (∑ i, ((m i : ℤ) : ZMod p) • h' i)
      = ∑ i, ((ggSRefl X j m i : ℤ) : ZMod p) • h' i := by
  set C : ZMod p := ∑ i, ((X j i : ℤ) : ZMod p) * ((m i : ℤ) : ZMod p) with hC
  have hα : α' j (∑ i, ((m i : ℤ) : ZMod p) • h' i) = C := by
    rw [hC, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, hD.pair j i]
    exact mul_comm _ _
  have hstep : (∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) •
      h' i) = (∑ i, ((m i : ℤ) : ZMod p) • h' i) - C • h' j := by
    have h1 : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i
        = ((m i : ℤ) : ZMod p) • h' i - (C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i :=
      fun i => sub_smul _ _ _
    simp only [h1]
    rw [Finset.sum_sub_distrib]
    congr 1
    calc ∑ i, (C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i
        = ∑ i, C • (((Pi.single j (1 : ZMod p) : N → ZMod p) i) • h' i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_smul]
      _ = C • ∑ i, ((Pi.single j (1 : ZMod p) : N → ZMod p) i) • h' i := (Finset.smul_sum).symm
      _ = C • h' j := by rw [latw_single_smul_sum]
  have hcoef : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i))
      = ((ggSRefl X j m i : ℤ) : ZMod p) := by
    intro i
    have hgg : ggSRefl X j m i = m i - (∑ k, X j k * m k) * ((Pi.single j (1 : ℤ) : N → ℤ) i) := by
      simp [ggSRefl]
    have hsingle : (((Pi.single j (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
        (Pi.single j (1 : ZMod p) : N → ZMod p) i :=
      latw_single_cast j i
    have hsum : ((∑ k, X j k * m k : ℤ) : ZMod p) = C := by
      rw [hC, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Int.cast_mul (X j k) (m k))
    rw [hgg, Int.cast_sub, Int.cast_mul, hsingle, hsum]
  calc ggLin (p := p) ι (φ' j) (∑ i, ((m i : ℤ) : ZMod p) • h' i)
      = (∑ i, ((m i : ℤ) : ZMod p) • h' i) - C • h' j := by rw [hD.lin j, hα]
    _ = ∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) •
          h' i := hstep.symm
    _ = ∑ i, ((ggSRefl X j m i : ℤ) : ZMod p) • h' i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hcoef i]

private theorem latw_word_coroot {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ggLin (p := p) ι ((ψ.map φ').prod) (h' k)
      = ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  induction ψ with
  | nil =>
      show ggLin (p := p) ι (1 : MulAut ↥Bs) (h' k)
        = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) • h' i
      rw [map_one]
      rw [show (1 : V ≃ₗ[ZMod p] V) (h' k) = h' k from rfl]
      calc h' k = ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) • h' i :=
            (latw_single_smul_sum k h').symm
        _ = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) • h' i := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [latw_single_cast]
  | cons j ψ ih =>
      rw [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]
      rw [ih]
      rw [latw_lin_comb hD j]
      rfl

private theorem latw_root_reflect {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (i j : N) (v : V) :
    α' i (ggLin (p := p) ι (φ' j) v) = α' i v - ((X i j : ℤ) : ZMod p) * α' j v := by
  rw [hD.lin j, map_sub, map_smul, smul_eq_mul, hD.pair i j]
  ring

private theorem latw_root_split {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {N : Type} [Fintype N] [DecidableEq N]
    {X : Matrix N N ℤ} {α' : N → Module.Dual (ZMod p) V} (j : N) (c : N → ℤ) (v : V) :
    ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v
      = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
        - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
  set S : ZMod p := ∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p) with hS
  have hgg : ∀ i, ggSReflR X j c i =
      c i - (∑ k, c k * X k j) * ((Pi.single j (1 : ℤ) : N → ℤ) i) := by
    intro i
    simp [ggSReflR]
  have hSc : ∀ i, ((ggSReflR X j c i : ℤ) : ZMod p)
      = ((c i : ℤ) : ZMod p) - S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i) := by
    intro i
    have hsum : ((∑ k, c k * X k j : ℤ) : ZMod p) = S := by
      rw [hS, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Int.cast_mul (c k) (X k j))
    rw [hgg i, Int.cast_sub, Int.cast_mul, latw_single_cast j i, hsum]
  calc ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v
      = ∑ i, (((c i : ℤ) : ZMod p) - S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hSc i]
    _ = ∑ i, (((c i : ℤ) : ZMod p) * α' i v
          - (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - ∑ i, (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v :=
          Finset.sum_sub_distrib _ _
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v - S * α' j v := by
          congr 1
          calc ∑ i, (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v
              = S * ∑ i, ((Pi.single j (1 : ZMod p) : N → ZMod p) i) * α' i v := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  ring
            _ = S * α' j v := by rw [latw_single_mul_sum]
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
          rw [hS]

private theorem latw_root_apply_sum {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (j : N) (c : N → ℤ) (v : V) :
    ∑ i, ((c i : ℤ) : ZMod p) * α' i (ggLin (p := p) ι (φ' j) v)
      = ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v := by
  calc ∑ i, ((c i : ℤ) : ZMod p) * α' i (ggLin (p := p) ι (φ' j) v)
      = ∑ i, ((c i : ℤ) : ZMod p)
          * (α' i v - ((X i j : ℤ) : ZMod p) * α' j v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [latw_root_reflect hD i j v]
    _ = ∑ i, (((c i : ℤ) : ZMod p) * α' i v
          - (((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - ∑ i, (((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v :=
          Finset.sum_sub_distrib _ _
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
          rw [Finset.sum_mul]
    _ = ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v :=
          (latw_root_split j c v).symm

private theorem latw_word_root {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ∀ v, α' k ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ v)
      = ∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i v := by
  induction ψ with
  | nil =>
      intro v
      show α' k ((ggLin (p := p) ι (1 : MulAut ↥Bs))⁻¹ v)
        = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) * α' i v
      rw [map_one, inv_one]
      rw [show (1 : V ≃ₗ[ZMod p] V) v = v from rfl]
      calc α' k v = ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) * α' i v :=
            (latw_single_mul_sum k (fun i => α' i v)).symm
        _ = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) * α' i v := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [latw_single_cast]
  | cons j ψ ih =>
      intro v
      have hP : (List.map φ' (j :: ψ)).prod = φ' j * (List.map φ' ψ).prod := by
        rw [List.map_cons, List.prod_cons]
      rw [hP, map_mul, mul_inv_rev, latw_inv_reflection hD j, LinearEquiv.mul_apply]
      rw [ih (ggLin (p := p) ι (φ' j) v)]
      rw [latw_root_apply_sum hD j]
      rfl

private theorem latw_conj_word {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N)
    (w : V) :
    ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) w
      = w - (∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i w) •
          ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  have hmap : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
      = ggLin (p := p) ι ((ψ.map φ').prod) * ggLin (p := p) ι (φ' k)
        * (ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hD.lin k, map_sub, map_smul]
  rw [show ggLin (p := p) ι ((ψ.map φ').prod)
        ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ w) = w from by
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]]
  rw [latw_word_coroot hD ψ k, latw_word_root hD ψ k w]

theorem ggExtDatum_word {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type} [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ggLin (p := p) ι ((ψ.map φ').prod) (h' k) =
        ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i ∧
      (∀ v, α' k ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ v) =
        ∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i v) ∧
      ∀ w, ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) w =
        w - (∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i w) •
          ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  exact ⟨latw_word_coroot hD ψ k, fun v => latw_word_root hD ψ k v,
    fun w => latw_conj_word hD ψ k w⟩

@[expose] def ggLCoroots {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (X : Matrix (Option Λ) (Option Λ) ℤ) : Set (Option Λ → ℤ) :=
  {v | ∃ (ψ : List Λ) (i : Λ), v = ggSWord X (ψ.map some) (Pi.single (some i) 1)}

private theorem latc_prod_inv_eq_reverse_prod {M : Type} [Group M] (l : List M)
    (h : ∀ x ∈ l, x⁻¹ = x) : l.prod⁻¹ = l.reverse.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, mul_inv_rev, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem latc_gen_refl {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    {X : Matrix (Option Λ) (Option Λ) ℤ} {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} {ι : Additive ↥Bs ≃+ V}
    (hD : GGExtDatum ι X φ' h' α') (hp2 : p ≠ 2) (o : Option Λ) :
    GGIsReflection p (φ' o) := by
  have hfx : α' o (h' o) = 2 := by
    rw [hD.pair o o, hD.diag o]
    norm_num
  exact ggIsReflection_of_eq_reflection hp2 ι hfx
    (ggLin_eq_reflection ι hfx (hD.lin o))

private theorem latc_exists_word {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ} {Λ : Type}
    {φ' : Option Λ → MulAut ↥Bs} (hgen : ∀ i : Λ, GGIsReflection p (φ' (some i)))
    {w : MulAut ↥Bs} (hw : w ∈ Subgroup.closure (Set.range fun i : Λ => φ' (some i))) :
    ∃ ψ : List Λ, w = (ψ.map fun i => φ' (some i)).prod := by
  let K : Subgroup (MulAut ↥Bs) :=
    { carrier := {w | ∃ ψ : List Λ, w = (ψ.map fun i => φ' (some i)).prod}
      one_mem' := ⟨[], by simp⟩
      mul_mem' := by
        rintro x y ⟨ψ₁, rfl⟩ ⟨ψ₂, rfl⟩
        exact ⟨ψ₁ ++ ψ₂, by rw [List.map_append, List.prod_append]⟩
      inv_mem' := by
        rintro x ⟨ψ, rfl⟩
        have hself : ∀ z ∈ ψ.map (fun i => φ' (some i)), z⁻¹ = z := by
          intro z hz
          rw [List.mem_map] at hz
          obtain ⟨i, -, rfl⟩ := hz
          exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using (hgen i).1)
        refine ⟨ψ.reverse, ?_⟩
        rw [List.map_reverse, ← latc_prod_inv_eq_reverse_prod (ψ.map fun i => φ' (some i)) hself] }
  have hle : Subgroup.closure (Set.range fun i : Λ => φ' (some i)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨[i], by simp⟩
  exact hle hw

private theorem latc_linearIndependent_coeff {V : Type} [AddCommGroup V] {p : ℕ}
    [Module (ZMod p) V] {Λ : Type} [Fintype Λ] {h' : Option Λ → V}
    (hind : LinearIndependent (ZMod p) h') {a b : Option Λ → ZMod p}
    (h : ∑ j, a j • h' j = ∑ j, b j • h' j) : a = b := by
  funext j
  have h0 : ∑ i, (a - b) i • h' i = 0 := by
    simp only [Pi.sub_apply, sub_smul]
    rw [Finset.sum_sub_distrib, h, sub_self]
  have h1 := (Fintype.linearIndependent_iff.mp hind (a - b)) h0 j
  have h2 : a j - b j = 0 := by simpa [Pi.sub_apply] using h1
  exact sub_eq_zero.mp h2

private theorem latc_mem_ggFixG {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {x : G} (hxBs : x ∈ Bs)
    (hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0)
    (ψ : List (Option Λ)) (k : Option Λ)
    (ha : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) = 0) :
    x ∈ ggFixG Bs ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) := by
  set xv : V := ι (Additive.ofMul ⟨x, hxBs⟩) with hxv
  have hsum : (∑ o, ((ggSWordR X ψ (Pi.single k 1) o : ℤ) : ZMod p) * α' o xv) = 0 := by
    rw [Fintype.sum_option]
    have h1 : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) * α' none xv = 0 := by
      rw [ha, zero_mul]
    have h2 : ∀ i : Λ,
        ((ggSWordR X ψ (Pi.single k 1) (some i) : ℤ) : ZMod p) * α' (some i) xv = 0 := by
      intro i
      rw [hx i, mul_zero]
    rw [h1, Finset.sum_eq_zero (fun i _ => h2 i), add_zero]
  have hfix : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) xv = xv := by
    have h3 := (ggExtDatum_word hD ψ k).2.2 xv
    rw [h3, hsum, zero_smul, sub_zero]
  refine ⟨⟨x, hxBs⟩, ?_, rfl⟩
  change (⟨x, hxBs⟩ : ↥Bs) ∈ ggFix ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
  rw [mem_ggFix, ggLin_fix_iff (p := p) ι]
  simpa [hxv] using hfix

private theorem latc_reflConjSimple {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α')
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M fun i j => X (some i) (some j)) (hp2 : p ≠ 2) {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i))) :
    GGReflConjSimple p (ggAutomizer L Bs) (fun i : Λ => φ' (some i)) := by
  classical
  unfold GGReflConjSimple
  rw [hAL]
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  have hFT : TauCeti.IsFiniteType (fun i j => X (some i) (some j)) :=
    isFiniteType_of_ggIsWeylMatrixFixed hM hC
  have hind : LinearIndependent (ZMod p) (fun i : Λ => h' (some i)) :=
    hD.indep.comp some (Option.some_injective _)
  have hRC := ggReflClosed_of_indep (p := p) hp2 hFT hC
    (fun i : Λ => h' (some i)) (fun i : Λ => α' (some i))
    (fun i j => hD.pair (some i) (some j)) hind
    (fun i => ggLin (p := p) ι (φ' (some i))) (fun i v => hD.lin (some i) v)
  have hmap : (Subgroup.closure (Set.range fun i : Λ => φ' (some i))).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]; rfl
  intro t ht hrefl
  have hr := (ggIsReflection_iff (p := p) ι t).mp hrefl
  have ht1 : ggLin (p := p) ι t ≠ 1 := by
    intro h1
    have hc := hr.2
    rw [h1] at hc
    have he : Nat.card {v : V // (1 : V ≃ₗ[ZMod p] V) v = v} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun v => rfl)
    rw [he] at hc
    have hpos : 0 < Nat.card V := Nat.card_pos
    have : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hc)
    exact (Fact.out : p.Prime).one_lt.ne' this
  have htW : ggLin (p := p) ι t ∈
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ ht
  obtain ⟨xv, fv, hfv, hlinv⟩ := exists_of_ggIsReflection ι hrefl
  obtain ⟨u, hu, i, hui⟩ := hRC _ htW hr.1 ht1 ⟨xv, fv, hlinv⟩
  rw [← hmap] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨w, hw, i, ggLin_injective (p := p) ι ?_⟩
  rw [hui, map_mul, map_mul, map_inv]

private theorem latc_not_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (hp2 : p ≠ 2)
    {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    {ψ : List (Option Λ)} {k : Option Λ}
    (hnp : ∀ v ∈ ggLCoroots X, ∀ r : (ZMod p)ˣ,
      (fun i => ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p)) ≠
        fun i => (r : ZMod p) * (v i : ZMod p)) :
    ∀ w ∈ ggAutomizer L Bs, ∀ i : Λ,
      (ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹ ≠
        w * φ' (some i) * w⁻¹ := by
  classical
  intro w hw i heq
  have hgen : ∀ j : Λ, GGIsReflection p (φ' (some j)) :=
    fun j => latc_gen_refl hD hp2 (some j)
  have hw' : w ∈ Subgroup.closure (Set.range fun j : Λ => φ' (some j)) := hAL ▸ hw
  obtain ⟨ψw, hψw⟩ := latc_exists_word hgen hw'
  set ψhat : MulAut ↥Bs := (ψ.map φ').prod with hψhat
  set W : V ≃ₗ[ZMod p] V := ggLin (p := p) ι ψhat with hW
  set W' : V ≃ₗ[ZMod p] V := ggLin (p := p) ι w with hW'
  set d : V := ∑ o, ((ggSWord X ψ (Pi.single k 1) o : ℤ) : ZMod p) • h' o with hd
  set v : V := W' (h' (some i)) with hv
  set β : V → ZMod p := fun u => ∑ o,
    ((ggSWordR X ψ (Pi.single k 1) o : ℤ) : ZMod p) * α' o u with hβ
  set g : V → ZMod p := fun u => α' (some i) (W'⁻¹ u) with hg
  have hword1 : W (h' k) = d := by
    rw [hW, hψhat, hd]
    exact (ggExtDatum_word hD ψ k).1
  have hword2 : ∀ u, β u = α' k (W⁻¹ u) := by
    intro u
    rw [hβ, hW, hψhat]
    exact ((ggExtDatum_word hD ψ k).2.1 u).symm
  have hword3 : ∀ u, ggLin (p := p) ι (ψhat * φ' k * ψhat⁻¹) u = u - β u • d := by
    intro u
    rw [hψhat, hβ, hd]
    exact (ggExtDatum_word hD ψ k).2.2 u
  have hRHS : ∀ u, ggLin (p := p) ι (w * φ' (some i) * w⁻¹) u = u - g u • v := by
    intro u
    rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [hD.lin (some i), map_sub, map_smul,
      show (ggLin ι w)⁻¹ = (ggLin ι w).symm from rfl, LinearEquiv.apply_symm_apply]
    rw [hg, hv, hW']
    rfl
  have hpoint : ∀ u, β u • d = g u • v := by
    intro u
    have h3 : ggLin (p := p) ι (ψhat * φ' k * ψhat⁻¹) u =
        ggLin (p := p) ι (w * φ' (some i) * w⁻¹) u := by rw [heq]
    rw [hword3 u, hRHS u] at h3
    exact sub_right_inj.mp h3
  have hβd : β d = 2 := by
    rw [hword2 d, ← hword1, show W⁻¹ = W.symm from rfl, LinearEquiv.symm_apply_apply,
      hD.pair k k, hD.diag k]
    norm_num
  have hd0 : d ≠ 0 := by
    intro h0
    have hWk : W (h' k) = W 0 := by rw [hword1, h0, map_zero]
    exact hD.indep.ne_zero k (W.injective hWk)
  have hgd0 : g d ≠ 0 := by
    intro hgd
    have h2d : (2 : ZMod p) • d = 0 := by
      have h := hpoint d
      rw [hβd, hgd, zero_smul] at h
      exact h
    exact hd0 ((smul_eq_zero.mp h2d).resolve_left (zmod_two_ne_zero (p := p) hp2))
  let r0 : ZMod p := (2 : ZMod p)⁻¹ * g d
  have hr0 : r0 ≠ 0 :=
    mul_ne_zero (inv_ne_zero (zmod_two_ne_zero (p := p) hp2)) hgd0
  have hdv : d = r0 • v := by
    have h := hpoint d
    rw [hβd] at h
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hp2
    calc d = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • d) := by
            rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : ZMod p)⁻¹ • (g d • v) := by rw [h]
      _ = r0 • v := by rw [smul_smul]
  have hv1 : v = ∑ j, ((ggSWord X (ψw.map some) (Pi.single (some i) 1) j : ℤ) : ZMod p) • h' j := by
    have hm : (ψw.map (fun j => φ' (some j))).prod = ((ψw.map some).map φ').prod := by
      rw [List.map_map, Function.comp_def]
    rw [hv, hW', hψw, hm]
    exact (ggExtDatum_word hD (ψw.map some) (some i)).1
  have hvmem : (fun j => ggSWord X (ψw.map some) (Pi.single (some i) 1) j) ∈ ggLCoroots X :=
    ⟨ψw, i, rfl⟩
  have hcoeff : (fun o => ((ggSWord X ψ (Pi.single k 1) o : ℤ) : ZMod p)) =
      fun o => r0 * ((ggSWord X (ψw.map some) (Pi.single (some i) 1) o : ℤ) : ZMod p) := by
    apply latc_linearIndependent_coeff hD.indep
    rw [← hd, hdv, hv1, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro o _
    rw [smul_smul]
  exact (hnp (fun o => ggSWord X (ψw.map some) (Pi.single (some i) 1) o) hvmem
    (Units.mk0 r0 hr0)) (by
      funext o
      rw [congrFun hcoeff o, Units.val_mk0])

theorem ggFork_false_of_lattice {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {B L D J : Subgroup G} {x : G} (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagOn Bs L)
    {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M fun i j => X (some i) (some j))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    (hReal : ∀ o, GGRealized p Bs (φ' o)) (hxBs : x ∈ Bs)
    (hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0)
    (ψ : List (Option Λ)) (k : Option Λ)
    (ha : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) = 0)
    (hnp : ∀ v ∈ ggLCoroots X, ∀ r : (ZMod p)ˣ,
      (fun i => ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p)) ≠
        fun i => (r : ZMod p) * (v i : ZMod p)) : False := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have h847 : GGFixedRealizedInL p Bs L x := ggFixedRealizedInL_of_config hL hP hcfg hInn
  have hW : GGReflConjSimple p (ggAutomizer L Bs) (fun i : Λ => φ' (some i)) :=
    latc_reflConjSimple hD hM hC hp2 hAL
  have hψ : (ψ.map φ').prod ∈ ggAutomizer ⊤ Bs := by
    exact Subgroup.list_prod_mem (ggAutomizer ⊤ Bs) (fun z hz => by
      rw [List.mem_map] at hz
      obtain ⟨o, -, rfl⟩ := hz
      exact Subgroup.subset_closure (hD.mem o))
  have hr : GGIsReflection p (φ' k) := latc_gen_refl hD hp2 k
  have hxmem : x ∈ ggFixG Bs ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) :=
    latc_mem_ggFixG hD hxBs hx ψ k ha
  have hnot : ∀ w ∈ ggAutomizer L Bs, ∀ i : Λ,
      (ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹ ≠ w * φ' (some i) * w⁻¹ :=
    latc_not_conj hD hp2 hAL hnp
  exact ggCell_false_of_witness (Fact.out : p.Prime) h847 hW hψ hr (hReal k) hxmem hnot

end Datum

end CFSG.StandardType
