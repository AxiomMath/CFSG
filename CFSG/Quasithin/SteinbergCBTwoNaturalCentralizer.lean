module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Matrix Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def diagHom : (V ≃ₗ[ZMod 2] V) →* ((V × V) ≃ₗ[ZMod 2] (V × V)) where
  toFun g := g.prodCongr g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diagHom_apply (g : V ≃ₗ[ZMod 2] V) (x : V × V) : diagHom g x = (g x.1, g x.2) :=
  rfl

@[expose] def blockMap (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : (V × V) →ₗ[ZMod 2] (V × V) :=
  LinearMap.prod (M 0 0 • LinearMap.fst (ZMod 2) V V + M 0 1 • LinearMap.snd (ZMod 2) V V)
    (M 1 0 • LinearMap.fst (ZMod 2) V V + M 1 1 • LinearMap.snd (ZMod 2) V V)

theorem blockMap_apply (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (x : V × V) :
    blockMap M x = (M 0 0 • x.1 + M 0 1 • x.2, M 1 0 • x.1 + M 1 1 • x.2) :=
  rfl

theorem blockMap_mul (M N : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    blockMap (V := V) (M * N) = blockMap M ∘ₗ blockMap N := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, blockMap_apply, Matrix.mul_apply, Fin.sum_univ_two, add_smul,
    mul_smul, smul_add]
  ext <;> simp only <;> abel

theorem blockMap_one : blockMap (V := V) 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [blockMap_apply]

theorem blockMap_injective [Nontrivial V] :
    Function.Injective (blockMap (V := V)) := by
  intro M N h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hinj := smul_left_injective (ZMod 2) hv
  have h1 := congrArg (fun f : (V × V) →ₗ[ZMod 2] (V × V) => f (v, 0)) h
  have h2 := congrArg (fun f : (V × V) →ₗ[ZMod 2] (V × V) => f (0, v)) h
  simp only [blockMap_apply, smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact hinj h1.1
  · exact hinj h2.1
  · exact hinj h1.2
  · exact hinj h2.2

@[expose] def blockHom : GL (Fin 2) (ZMod 2) →* ((V × V) ≃ₗ[ZMod 2] (V × V)) where
  toFun A := LinearEquiv.ofLinearMap (blockMap (A : Matrix (Fin 2) (Fin 2) (ZMod 2)))
    (blockMap (↑A⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod 2)))
    (by rw [← blockMap_mul, Units.mul_inv, blockMap_one])
    (by rw [← blockMap_mul, Units.inv_mul, blockMap_one])
  map_one' := LinearEquiv.ext fun x => by
    change blockMap ((1 : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) x = x
    rw [Units.val_one, blockMap_one]
    rfl
  map_mul' A B := LinearEquiv.ext fun x => by
    change blockMap (↑(A * B) : Matrix (Fin 2) (Fin 2) (ZMod 2)) x =
      blockMap (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
        (blockMap (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) x)
    rw [Units.val_mul, blockMap_mul]
    rfl

theorem blockHom_apply (A : GL (Fin 2) (ZMod 2)) (x : V × V) :
    blockHom A x = blockMap (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) x :=
  rfl

theorem exists_eq_smul_id_of_commute [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) {f : V →ₗ[ZMod 2] V}
    (hf : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V), f (g v) = g (f v)) :
    ∃ a : ZMod 2, f = a • LinearMap.id := by
  let b := Module.finBasis (ZMod 2) V
  have : Nontrivial (Fin (finrank (ZMod 2) V)) := Fin.nontrivial_iff_two_le.2 hV
  obtain ⟨a, ha⟩ := LinearMap.commute_transvections_iff_of_basis b (f := f) fun i j r hij => by
    have h0 : b.coord i (r • b j) = 0 := by
      rw [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij, smul_zero]
    refine LinearMap.ext fun v => ?_
    have := hf (LinearEquiv.transvection h0) v
    rw [LinearEquiv.transvection.apply] at this
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact this
  refine ⟨(a : ZMod 2), ?_⟩
  rw [ha]
  rfl

theorem blockMap_commute_diag (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (g : V ≃ₗ[ZMod 2] V)
    (x : V × V) : blockMap M (diagHom g x) = diagHom g (blockMap M x) := by
  simp only [blockMap_apply, diagHom_apply, map_add, map_smul]

theorem mem_centralizer_iff_commute {φ : (V × V) ≃ₗ[ZMod 2] (V × V)} :
    φ ∈ centralizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))) ↔
      ∀ (g : V ≃ₗ[ZMod 2] V) (x : V × V), φ (diagHom g x) = diagHom g (φ x) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h g x
    have := congrArg (fun f : (V × V) ≃ₗ[ZMod 2] (V × V) => f x) (h (diagHom g) ⟨g, rfl⟩)
    exact this.symm
  · rintro h _ ⟨g, rfl⟩
    exact LinearEquiv.ext fun x => (h g x).symm

theorem exists_blockMap_of_mem_centralizer [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) {φ : (V × V) ≃ₗ[ZMod 2] (V × V)}
    (hφ : φ ∈ centralizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V)))) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 2), (φ : (V × V) →ₗ[ZMod 2] (V × V)) = blockMap M := by
  have hc := mem_centralizer_iff_commute.1 hφ
  have hblock : ∀ (p : (V × V) →ₗ[ZMod 2] V) (q : V →ₗ[ZMod 2] V × V),
      (∀ (g : V ≃ₗ[ZMod 2] V) (y : V × V), p (diagHom g y) = g (p y)) →
      (∀ (g : V ≃ₗ[ZMod 2] V) (v : V), q (g v) = diagHom g (q v)) →
      ∃ a : ZMod 2, p ∘ₗ (φ : (V × V) →ₗ[ZMod 2] (V × V)) ∘ₗ q = a • LinearMap.id := by
    intro p q hp hq
    refine exists_eq_smul_id_of_commute hV fun g v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hq, hc, hp]
  have hfst : ∀ (g : V ≃ₗ[ZMod 2] V) (y : V × V),
      LinearMap.fst (ZMod 2) V V (diagHom g y) = g (LinearMap.fst (ZMod 2) V V y) :=
    fun _ _ => rfl
  have hsnd : ∀ (g : V ≃ₗ[ZMod 2] V) (y : V × V),
      LinearMap.snd (ZMod 2) V V (diagHom g y) = g (LinearMap.snd (ZMod 2) V V y) :=
    fun _ _ => rfl
  have hinl : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      LinearMap.inl (ZMod 2) V V (g v) = diagHom g (LinearMap.inl (ZMod 2) V V v) :=
    fun g v => by simp [diagHom_apply]
  have hinr : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      LinearMap.inr (ZMod 2) V V (g v) = diagHom g (LinearMap.inr (ZMod 2) V V v) :=
    fun g v => by simp [diagHom_apply]
  obtain ⟨a, ha⟩ := hblock _ _ hfst hinl
  obtain ⟨b, hb⟩ := hblock _ _ hfst hinr
  obtain ⟨c, hc'⟩ := hblock _ _ hsnd hinl
  obtain ⟨d, hd⟩ := hblock _ _ hsnd hinr
  refine ⟨!![a, b; c, d], LinearMap.ext fun x => ?_⟩
  have hx : φ x = φ (LinearMap.inl (ZMod 2) V V x.1) + φ (LinearMap.inr (ZMod 2) V V x.2) := by
    rw [← map_add]
    congr 1
    simp
  have ea := congrArg (fun f : V →ₗ[ZMod 2] V => f x.1) ha
  have eb := congrArg (fun f : V →ₗ[ZMod 2] V => f x.2) hb
  have ec := congrArg (fun f : V →ₗ[ZMod 2] V => f x.1) hc'
  have ed := congrArg (fun f : V →ₗ[ZMod 2] V => f x.2) hd
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.fst_apply, LinearMap.snd_apply] at ea eb ec ed
  rw [blockMap_apply]
  change φ x = _
  rw [hx]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, ea, eb]
    simp
  · rw [Prod.snd_add, ec, ed]
    simp

theorem range_blockHom_eq_centralizer [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) :
    (blockHom (V := V)).range =
      centralizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact mem_centralizer_iff_commute.2 fun g x => blockMap_commute_diag _ g x
  · intro φ hφ
    obtain ⟨M, hM⟩ := exists_blockMap_of_mem_centralizer hV hφ
    obtain ⟨N, hN⟩ := exists_blockMap_of_mem_centralizer hV (inv_mem hφ)
    have hMN : M * N = 1 := blockMap_injective (V := V) (by
      rw [blockMap_mul, ← hM, ← hN, blockMap_one]
      refine LinearMap.ext fun x => ?_
      change φ (φ⁻¹ x) = x
      exact LinearEquiv.apply_symm_apply φ x)
    have hNM : N * M = 1 := blockMap_injective (V := V) (by
      rw [blockMap_mul, ← hM, ← hN, blockMap_one]
      refine LinearMap.ext fun x => ?_
      change φ⁻¹ (φ x) = x
      exact LinearEquiv.symm_apply_apply φ x)
    refine ⟨⟨M, N, hMN, hNM⟩, LinearEquiv.ext fun x => ?_⟩
    rw [blockHom_apply]
    change blockMap M x = (φ : (V × V) →ₗ[ZMod 2] (V × V)) x
    rw [hM]

theorem blockHom_injective [Nontrivial V] : Function.Injective (blockHom (V := V)) := by
  intro A B h
  apply Units.ext
  apply blockMap_injective (V := V)
  refine LinearMap.ext fun x => ?_
  have := congrArg (fun f : (V × V) ≃ₗ[ZMod 2] (V × V) => f x) h
  exact this

theorem involution_cases_gl_two : ∀ C : Matrix (Fin 2) (Fin 2) (ZMod 2), C * C = 1 → C ≠ 1 →
    C = !![0, 1; 1, 0] ∨ C = !![1, 1; 0, 1] ∨ C = !![1, 0; 1, 1] := by
  decide

theorem nat_card_gl_two_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  rfl

theorem exists_linearEquiv_apply_eq [FiniteDimensional (ZMod 2) V] {v w : V} (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ g : V ≃ₗ[ZMod 2] V, g v = w := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V v hv).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V w hw))
  refine ⟨g, ?_⟩
  have h := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← h]
  change ((LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V w hw)
    ((LinearEquiv.coord (ZMod 2) V v hv) ⟨v, Submodule.mem_span_singleton_self v⟩) : V) = w
  rw [LinearEquiv.coord_self, LinearEquiv.toSpanNonzeroSingleton_one]

theorem transitive_and_card_of_range [FiniteDimensional (ZMod 2) V]
    {j : V →ₗ[ZMod 2] V × V} (hj : Function.Injective j)
    (hjg : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V), diagHom g (j v) = j (g v)) :
    (∀ x ∈ LinearMap.range j, ∀ y ∈ LinearMap.range j, x ≠ 0 → y ≠ 0 →
      ∃ s ∈ (diagHom (V := V)).range, s x = y) ∧
    Nat.card {x : V × V // x ∈ LinearMap.range j ∧ x ≠ 0} = Nat.card V - 1 := by
  constructor
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ hv hw
    have hv' : v ≠ 0 := fun h => hv (by rw [h, map_zero])
    have hw' : w ≠ 0 := fun h => hw (by rw [h, map_zero])
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq hv' hw'
    exact ⟨diagHom g, ⟨g, rfl⟩, by rw [hjg, hg]⟩
  · have e : {v : V // v ≠ 0} ≃ {x : V × V // x ∈ LinearMap.range j ∧ x ≠ 0} :=
      { toFun := fun v => ⟨j v, ⟨v, rfl⟩, fun h => v.2 (hj (h.trans (map_zero j).symm))⟩
        invFun := fun x => ⟨x.2.1.choose, fun h => x.2.2 (by
          rw [← x.2.1.choose_spec, h, map_zero])⟩
        left_inv := fun v => Subtype.ext (hj (Exists.choose_spec (p := fun w => j w = j v) _))
        right_inv := fun x => Subtype.ext x.2.1.choose_spec }
    classical
    have : Finite V := Module.finite_of_finite (ZMod 2)
    let _ : Fintype V := Fintype.ofFinite V
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, Nat.card_eq_fintype_card]

theorem nq_two_natural_binary_space_centralizer [FiniteDimensional (ZMod 2) V] {n : ℕ}
    (hn : 2 ≤ n) (hV : finrank (ZMod 2) V = n) :
    (∀ (A : GL (Fin 2) (ZMod 2)) (x : V × V),
      blockHom A x = ((A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 • x.1 +
          (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1 • x.2,
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 • x.1 +
          (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1 • x.2)) ∧
    Function.Injective (blockHom (V := V)) ∧
    (blockHom (V := V)).range =
      centralizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))) ∧
    ∀ B : Subgroup ((V × V) ≃ₗ[ZMod 2] (V × V)),
      B ≤ centralizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))) →
      IsPGroup 2 B → B ≠ ⊥ →
      Nat.card B = 2 ∧
      ((⨅ b ∈ B, LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)) = LinearMap.range (LinearMap.inl (ZMod 2) V V) ∨
        (⨅ b ∈ B, LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)) = LinearMap.range (LinearMap.inr (ZMod 2) V V) ∨
        (⨅ b ∈ B, LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)) =
          LinearMap.range (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[ZMod 2] V × V)) ∧
      (∀ x ∈ (⨅ b ∈ B, LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)),
        ∀ y ∈ (⨅ b ∈ B, LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)),
          x ≠ 0 → y ≠ 0 → ∃ s ∈ (diagHom (V := V)).range, s x = y) ∧
      Nat.card {x : V × V // x ∈ (⨅ b ∈ B,
          LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
            Submodule (ZMod 2) (V × V)) ∧ x ≠ 0} = 2 ^ n - 1 := by
  classical
  have hV2 : 2 ≤ finrank (ZMod 2) V := hV ▸ hn
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite ((V × V) ≃ₗ[ZMod 2] (V × V)) :=
    Finite.of_injective (fun e : (V × V) ≃ₗ[ZMod 2] (V × V) => (e : V × V → V × V))
      DFunLike.coe_injective
  refine ⟨fun A x => rfl, blockHom_injective, range_blockHom_eq_centralizer hV2,
    fun B hBC hB2 hB1 => ?_⟩
  have hcardC : Nat.card (centralizer ((diagHom (V := V)).range :
      Set ((V × V) ≃ₗ[ZMod 2] (V × V)))) = 6 := by
    rw [← range_blockHom_eq_centralizer hV2, ← nat_card_gl_two_two]
    exact (Nat.card_congr (MonoidHom.ofInjective blockHom_injective).toEquiv).symm
  have hcardB : Nat.card B = 2 := by
    obtain ⟨m, hm⟩ := hB2.exists_card_eq
    have hdvd : 2 ^ m ∣ 6 := hm ▸ hcardC ▸ card_dvd_of_le hBC
    have hm1 : m ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hB1 (Subgroup.card_eq_one.1 (by rw [hm, pow_zero]))
    rw [hm, show m = 1 by omega, pow_one]
  refine ⟨hcardB, ?_⟩
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b * b = 1 := by
    have h := pow_card_eq_one' (G := B) (x := ⟨b, hbB⟩)
    rw [hcardB, pow_two] at h
    exact congrArg Subtype.val h
  have hBb : B = zpowers b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbB) ?_
    rw [hcardB, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1']
  have hfix : (⨅ c ∈ B, LinearMap.ker ((c : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) :
      Submodule (ZMod 2) (V × V)) =
      LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) := by
    apply le_antisymm (iInf₂_le b hbB)
    intro x hx
    simp only [Submodule.mem_iInf]
    intro c hc
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [hBb] at hc
    have hstab : zpowers b ≤ MulAction.stabilizer ((V × V) ≃ₗ[ZMod 2] (V × V)) x :=
      Subgroup.zpowers_le.2 hx
    exact hstab hc
  obtain ⟨C, rfl⟩ : b ∈ (blockHom (V := V)).range := by
    rw [range_blockHom_eq_centralizer hV2]
    exact hBC hbB
  have hC2 : (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) * C = 1 := by
    have h : C * C = 1 := blockHom_injective (by rw [map_mul, hb2, map_one])
    exact congrArg Units.val h
  have hC1 : (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 := fun h => hb1' (by
    rw [show C = 1 from Units.ext h, map_one])
  have hker : ∀ x : V × V, x ∈ LinearMap.ker
      (((blockHom (V := V) C : (V × V) ≃ₗ[ZMod 2] (V × V)) : (V × V) →ₗ[ZMod 2] (V × V)) -
        LinearMap.id) ↔
      blockMap (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) x = x := fun x => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hcardV : Nat.card V = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]
  have hinl : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      diagHom g (LinearMap.inl (ZMod 2) V V v) = LinearMap.inl (ZMod 2) V V (g v) :=
    fun g v => by simp [diagHom_apply]
  have hinr : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      diagHom g (LinearMap.inr (ZMod 2) V V v) = LinearMap.inr (ZMod 2) V V (g v) :=
    fun g v => by simp [diagHom_apply]
  have hdiag : ∀ (g : V ≃ₗ[ZMod 2] V) (v : V),
      diagHom g ((LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[ZMod 2] V × V) v) =
        (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[ZMod 2] V × V) (g v) :=
    fun g v => by simp [diagHom_apply]
  have hdiag_inj : Function.Injective
      (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[ZMod 2] V × V) := fun v w h =>
    congrArg Prod.fst h
  rw [hfix]
  rcases involution_cases_gl_two _ hC2 hC1 with h | h | h
  ·
    have hK : LinearMap.ker
        (((blockHom (V := V) C : (V × V) ≃ₗ[ZMod 2] (V × V)) : (V × V) →ₗ[ZMod 2] (V × V)) -
          LinearMap.id) =
        LinearMap.range (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[ZMod 2] V × V) := by
      ext x
      rw [hker, blockMap_apply, h, LinearMap.mem_range]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, one_smul, zero_add, add_zero,
        LinearMap.prod_apply]
      constructor
      · intro hx
        exact ⟨x.1, Prod.ext rfl (congrArg Prod.fst hx).symm⟩
      · rintro ⟨v, rfl⟩
        rfl
    rw [hK]
    obtain ⟨h1, h2⟩ := transitive_and_card_of_range hdiag_inj hdiag
    exact ⟨Or.inr (Or.inr rfl), h1, by rw [h2, hcardV]⟩
  ·
    have hK : LinearMap.ker
        (((blockHom (V := V) C : (V × V) ≃ₗ[ZMod 2] (V × V)) : (V × V) →ₗ[ZMod 2] (V × V)) -
          LinearMap.id) =
        LinearMap.range (LinearMap.inl (ZMod 2) V V) := by
      ext x
      rw [hker, blockMap_apply, h, LinearMap.mem_range]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, one_smul, zero_add,
        LinearMap.inl_apply]
      constructor
      · intro hx
        have h2 : x.2 = 0 := by
          have := congrArg Prod.fst hx
          simpa using this
        exact ⟨x.1, Prod.ext rfl h2.symm⟩
      · rintro ⟨v, rfl⟩
        simp
    rw [hK]
    obtain ⟨h1, h2⟩ := transitive_and_card_of_range LinearMap.inl_injective hinl
    exact ⟨Or.inl rfl, h1, by rw [h2, hcardV]⟩
  ·
    have hK : LinearMap.ker
        (((blockHom (V := V) C : (V × V) ≃ₗ[ZMod 2] (V × V)) : (V × V) →ₗ[ZMod 2] (V × V)) -
          LinearMap.id) =
        LinearMap.range (LinearMap.inr (ZMod 2) V V) := by
      ext x
      rw [hker, blockMap_apply, h, LinearMap.mem_range]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, one_smul, add_zero,
        LinearMap.inr_apply]
      constructor
      · intro hx
        have h1 : x.1 = 0 := by
          have := congrArg Prod.snd hx
          simpa using this
        exact ⟨x.2, Prod.ext h1.symm rfl⟩
      · rintro ⟨v, rfl⟩
        simp
    rw [hK]
    obtain ⟨h1, h2⟩ := transitive_and_card_of_range LinearMap.inr_injective hinr
    exact ⟨Or.inr (Or.inl rfl), h1, by rw [h2, hcardV]⟩

end CFSG.Quasithin.SteinbergCB
