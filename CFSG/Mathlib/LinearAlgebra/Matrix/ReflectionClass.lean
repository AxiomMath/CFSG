module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank


public section

namespace Matrix.GeneralLinearGroup

open Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

private noncomputable def rootLine (x : GeneralLinearGroup n K) : Submodule K (n → K) :=
  LinearMap.range (Matrix.toLin' (x : Matrix n n K) - 1)

private lemma toLin'_injective_of_unit (g : GeneralLinearGroup n K) :
    Function.Injective (Matrix.toLin' (g : Matrix n n K)) := by
  intro x y hxy
  have h := congrArg (fun z => Matrix.toLin' ((g⁻¹ : GeneralLinearGroup n K) : Matrix n n K) z) hxy
  simpa [Matrix.toLin'_mul, ← coe_mul] using h

private lemma toLin'_surjective_of_unit (g : GeneralLinearGroup n K) :
    Function.Surjective (Matrix.toLin' (g : Matrix n n K)) := by
  intro y
  refine ⟨Matrix.toLin' ((g⁻¹ : GeneralLinearGroup n K) : Matrix n n K) y, ?_⟩
  simp

private lemma rootLine_finrank (x : GeneralLinearGroup n K) :
    Module.finrank K (rootLine x) = ((x : Matrix n n K) - 1).rank := by
  have h : Matrix.toLin' ((x : Matrix n n K) - 1) =
      Matrix.toLin' (x : Matrix n n K) - 1 := by
    rw [map_sub, Matrix.toLin'_one]
    ext v
    rfl
  rw [rootLine, ← h, Matrix.rank]
  rfl

private lemma rootLine_map_eq_neg {x : GeneralLinearGroup n K} (hx2 : x * x = 1)
    {v : n → K} (hv : v ∈ rootLine x) :
    Matrix.toLin' (x : Matrix n n K) v = -v := by
  rcases hv with ⟨w, rfl⟩
  have hcomp : Matrix.toLin' (x : Matrix n n K)
      (Matrix.toLin' (x : Matrix n n K) w) = w := by
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← coe_mul, hx2, coe_one,
      Matrix.toLin'_one]
    rfl
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hcomp]
  abel

private lemma mem_rootLine_of_map_eq_neg {x : GeneralLinearGroup n K}
    (h2 : (2 : K) ≠ 0) {v : n → K}
    (hv : Matrix.toLin' (x : Matrix n n K) v = -v) : v ∈ rootLine x := by
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := @add_halves K _ ⟨h2⟩ 1
  refine ⟨-(1 / 2 : K) • v, ?_⟩
  change Matrix.toLin' (x : Matrix n n K) (-(1 / 2 : K) • v) -
    (-(1 / 2 : K) • v) = v
  rw [map_smul, hv]
  simp only [smul_neg, neg_smul, neg_neg, sub_neg_eq_add]
  rw [← add_smul, hhalf, one_smul]


private lemma two_ne_zero_of_card_ne_zero {G : Subgroup (GeneralLinearGroup n K)}
    (hG : (Nat.card G : K) ≠ 0) {c : GeneralLinearGroup n K} (hc2 : c * c = 1)
    (hcr : ((c : Matrix n n K) - 1).rank = 1)
    (hgen : Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹} = G) : (2 : K) ≠ 0 := by
  classical
  have hnt : Nontrivial K := by
    rcases subsingleton_or_nontrivial K with h | h
    · exact False.elim (hG (Subsingleton.elim _ _))
    · exact h
  have hcG : c ∈ G := by
    rw [← hgen]
    exact Subgroup.subset_closure ⟨1, G.one_mem, by simp⟩
  have hcne : c ≠ 1 := by
    intro hc
    have hz : ((c : Matrix n n K) - 1).rank = 0 := by
      rw [hc, coe_one, sub_self]
      exact @Matrix.rank_zero n n K _ _ hnt
    rw [hcr] at hz
    exact Nat.one_ne_zero hz
  have horder : orderOf c = 2 := by
    exact orderOf_eq_prime (by simpa [pow_two] using hc2) hcne
  have hdvd : 2 ∣ Nat.card G := horder ▸ Subgroup.orderOf_dvd_natCard G hcG
  obtain ⟨m, hm⟩ := hdvd
  intro h2
  apply hG
  rw [hm, Nat.cast_mul]
  simp [h2]

private noncomputable def lineMap (g : GeneralLinearGroup n K) (L : Submodule K (n → K)) :
    Submodule K (n → K) :=
  L.map (Matrix.toLin' (g : Matrix n n K))

private lemma lineMap_one (L : Submodule K (n → K)) : lineMap 1 L = L := by
  rw [lineMap, coe_one, Matrix.toLin'_one, Submodule.map_id]

private lemma lineMap_mul (g h : GeneralLinearGroup n K) (L : Submodule K (n → K)) :
    lineMap (g * h) L = lineMap g (lineMap h L) := by
  rw [lineMap, lineMap, lineMap, coe_mul, Matrix.toLin'_mul, Submodule.map_comp]

private lemma lineMap_inv_cancel (g : GeneralLinearGroup n K) (L : Submodule K (n → K)) :
    lineMap g (lineMap g⁻¹ L) = L := by
  rw [← lineMap_mul, mul_inv_cancel, lineMap_one]

private lemma lineMap_inv_cancel' (g : GeneralLinearGroup n K) (L : Submodule K (n → K)) :
    lineMap g⁻¹ (lineMap g L) = L := by
  rw [← lineMap_mul, inv_mul_cancel, lineMap_one]

private lemma lineMap_finrank (g : GeneralLinearGroup n K) (L : Submodule K (n → K)) :
    Module.finrank K (lineMap g L) = Module.finrank K L := by
  apply le_antisymm
  · exact Submodule.finrank_map_le (Matrix.toLin' (g : Matrix n n K)) L
  · calc Module.finrank K L
        = Module.finrank K (lineMap g⁻¹ (lineMap g L)) := by rw [lineMap_inv_cancel' g L]
      _ ≤ Module.finrank K (lineMap g L) :=
          Submodule.finrank_map_le (Matrix.toLin' ((g⁻¹ : GeneralLinearGroup n K) :
            Matrix n n K)) (lineMap g L)

private lemma rootLine_conj (g x : GeneralLinearGroup n K) :
    rootLine (g * x * g⁻¹) = lineMap g (rootLine x) := by
  rw [rootLine, rootLine, lineMap]
  let Y : (n → K) →ₗ[K] (n → K) := Matrix.toLin' (g : Matrix n n K)
  let X : (n → K) →ₗ[K] (n → K) := Matrix.toLin' (x : Matrix n n K)
  let Z : (n → K) →ₗ[K] (n → K) :=
    Matrix.toLin' ((g⁻¹ : GeneralLinearGroup n K) : Matrix n n K)
  have hYZ : Y.comp Z = 1 := by
    rw [← Matrix.toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, Matrix.toLin'_one]
    ext v
    rfl
  have hprod : Matrix.toLin' (↑(g * x * g⁻¹)) = Y.comp (X.comp Z) := by
    rw [coe_mul, coe_mul, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_assoc]
  have h : Matrix.toLin' (↑(g * x * g⁻¹)) - 1 = Y.comp ((X - 1).comp Z) := by
    rw [hprod]
    symm
    calc Y.comp ((X - 1).comp Z)
        = Y.comp (X.comp Z - (1 : (n → K) →ₗ[K] (n → K)).comp Z) := by
          rw [LinearMap.sub_comp]
      _ = Y.comp (X.comp Z) - Y.comp ((1 : (n → K) →ₗ[K] (n → K)).comp Z) := by
          rw [LinearMap.comp_sub]
      _ = Y.comp (X.comp Z) - Y.comp Z := by rfl
      _ = Y.comp (X.comp Z) - 1 := by rw [hYZ]
  have htop : Z.range = ⊤ :=
    LinearMap.range_eq_top.mpr (toLin'_surjective_of_unit g⁻¹)
  rw [h, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top (X - 1) htop]

private lemma lineMap_rootLine {x : GeneralLinearGroup n K} (hx2 : x * x = 1) :
    lineMap x (rootLine x) = rootLine x := by
  have hconj := rootLine_conj x x
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_right hx2).symm
  have hx : x * x * x⁻¹ = x := by
    rw [hx2, one_mul, hxinv]
  rw [hx] at hconj
  exact hconj.symm

private lemma eq_one_or_eq_neg_one_of_map_eq_smul {x : GeneralLinearGroup n K}
    (hx2 : x * x = 1) {v : n → K} (hv0 : v ≠ 0) {d : K}
    (hd : Matrix.toLin' (x : Matrix n n K) v = d • v) : d = 1 ∨ d = -1 := by
  have hcomp : Matrix.toLin' (x : Matrix n n K)
      (Matrix.toLin' (x : Matrix n n K) v) = v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← coe_mul, hx2, coe_one,
      Matrix.toLin'_one]
    rfl
  rw [hd, map_smul, hd] at hcomp
  have hd2 : d * d = 1 := by
    apply smul_left_injective K hv0
    simpa [smul_smul] using hcomp
  exact sq_eq_one_iff.mp (by simpa [pow_two] using hd2)


private noncomputable def lineOrbit (G : Subgroup (GeneralLinearGroup n K)) [Fintype G]
    (ℓ : Submodule K (n → K)) : Finset (Submodule K (n → K)) :=
  (Finset.univ : Finset G).image (fun g : G => lineMap (g : GeneralLinearGroup n K) ℓ)

private lemma lineOrbit_map_mem {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {g : G} {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) : lineMap (g : GeneralLinearGroup n K) L ∈ lineOrbit G ℓ := by
  rw [lineOrbit, Finset.mem_image] at hL ⊢
  obtain ⟨k, -, hk⟩ := hL
  refine ⟨g * k, Finset.mem_univ _, ?_⟩
  change lineMap ((g : GeneralLinearGroup n K) * (k : GeneralLinearGroup n K)) ℓ =
    lineMap (g : GeneralLinearGroup n K) L
  rw [lineMap_mul, hk]

private noncomputable def orbitRep (G : Subgroup (GeneralLinearGroup n K)) [Fintype G]
    (ℓ : Submodule K (n → K)) (L : Submodule K (n → K)) : G :=
  if h : L ∈ lineOrbit G ℓ then Classical.choose (Finset.mem_image.mp h) else 1

private lemma orbitRep_spec {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {L : Submodule K (n → K)} (hL : L ∈ lineOrbit G ℓ) :
    lineMap ((orbitRep G ℓ L : G) : GeneralLinearGroup n K) ℓ = L := by
  rw [orbitRep, dif_pos hL]
  exact (Classical.choose_spec (Finset.mem_image.mp hL)).2

private noncomputable def lineVector (G : Subgroup (GeneralLinearGroup n K)) [Fintype G]
    (ℓ : Submodule K (n → K)) (a : n → K) (L : Submodule K (n → K)) : n → K :=
  Matrix.toLin' (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) : Matrix n n K) a

private lemma lineVector_mem {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {L : Submodule K (n → K)} (ha : a ∈ ℓ)
    (hL : L ∈ lineOrbit G ℓ) : lineVector G ℓ a L ∈ L := by
  have hmem : Matrix.toLin' (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) :
      Matrix n n K) a ∈ lineMap ((orbitRep G ℓ L : G) : GeneralLinearGroup n K) ℓ :=
    Submodule.mem_map_of_mem (f := Matrix.toLin'
      (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) : Matrix n n K)) ha
  rwa [orbitRep_spec (G := G) (ℓ := ℓ) hL] at hmem

private lemma lineVector_ne_zero {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {L : Submodule K (n → K)}
    (ha0 : a ≠ 0) : lineVector G ℓ a L ≠ 0 := by
  intro hzero
  apply ha0
  have h : Matrix.toLin' (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) : Matrix n n K) a =
      Matrix.toLin' (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) : Matrix n n K) 0 := by
    simpa [lineVector] using hzero
  exact toLin'_injective_of_unit (g := (((orbitRep G ℓ L : G) : GeneralLinearGroup n K))) h

private lemma span_lineVector {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {L : Submodule K (n → K)}
    (ha : ℓ = Submodule.span K {a}) (hL : L ∈ lineOrbit G ℓ) :
    Submodule.span K {lineVector G ℓ a L} = L := by
  rw [lineVector]
  have hmap := Submodule.map_span (Matrix.toLin'
    (((orbitRep G ℓ L : G) : GeneralLinearGroup n K) : Matrix n n K))
    ({a} : Set (n → K))
  rw [Set.image_singleton] at hmap
  rw [← hmap, ← ha]
  exact orbitRep_spec (G := G) (ℓ := ℓ) hL

private lemma exists_lineCoeff {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K}
    (ha : ℓ = Submodule.span K {a}) (g : G) {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) :
    ∃ d : K, Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
        (lineVector G ℓ a L) =
      d • lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L) := by
  have hLg : lineMap (g : GeneralLinearGroup n K) L ∈ lineOrbit G ℓ :=
    lineOrbit_map_mem hL
  let v : n → K := Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
    (lineVector G ℓ a L)
  let w : n → K := lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L)
  have hmap := Submodule.map_span (Matrix.toLin'
    ((g : GeneralLinearGroup n K) : Matrix n n K))
    ({lineVector G ℓ a L} : Set (n → K))
  rw [Set.image_singleton] at hmap
  have h1 : Submodule.span K {v} = lineMap (g : GeneralLinearGroup n K) L := by
    rw [show v = Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
      (lineVector G ℓ a L) from rfl, ← hmap, span_lineVector ha hL]
    rfl
  have h2 : Submodule.span K {w} = lineMap (g : GeneralLinearGroup n K) L := by
    rw [show w = lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L) from rfl]
    exact span_lineVector ha hLg
  have hspan : Submodule.span K {v} = Submodule.span K {w} := by rw [h1, h2]
  obtain ⟨z, hz⟩ :=
    (Submodule.span_singleton_eq_span_singleton (x := v) (y := w)).mp hspan
  refine ⟨((z⁻¹ : Kˣ) : K), ?_⟩
  change v = ((z⁻¹ : Kˣ) : K) • w
  rw [← hz, Units.smul_def, smul_smul]
  simp

private noncomputable def lineCoeff (G : Subgroup (GeneralLinearGroup n K)) [Fintype G]
    (ℓ : Submodule K (n → K)) (a : n → K) (_ha0 : a ≠ 0)
    (ha : ℓ = Submodule.span K {a}) (g : G) (L : Submodule K (n → K)) : K :=
  if h : L ∈ lineOrbit G ℓ then
    Classical.choose (exists_lineCoeff (G := G) (ℓ := ℓ) (a := a) ha g h)
  else 1

private lemma lineCoeff_spec {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {g : G} {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) :
    Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
        (lineVector G ℓ a L) =
      lineCoeff G ℓ a ha0 ha g L •
        lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L) := by
  rw [lineCoeff, dif_pos hL]
  exact Classical.choose_spec (exists_lineCoeff (G := G) (ℓ := ℓ) (a := a) ha g hL)

private lemma lineCoeff_unique {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {g : G} {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) {d : K}
    (hd : Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
        (lineVector G ℓ a L) =
      d • lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L)) :
    d = lineCoeff G ℓ a ha0 ha g L := by
  have hspec := lineCoeff_spec (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    (g := g) hL
  have hv : lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L) ≠ 0 :=
    lineVector_ne_zero (G := G) (ℓ := ℓ) (a := a) ha0
  apply smul_left_injective K hv
  change d • lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L) =
    lineCoeff G ℓ a ha0 ha g L •
      lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K) L)
  rw [← hd, hspec]


private noncomputable def orbitChar (G : Subgroup (GeneralLinearGroup n K)) [Fintype G]
    (ℓ : Submodule K (n → K)) (a : n → K) (ha0 : a ≠ 0)
    (ha : ℓ = Submodule.span K {a}) (g : G) : K :=
  ∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha g L

private lemma lineCoeff_one {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) : lineCoeff G ℓ a ha0 ha 1 L = 1 := by
  symm
  apply lineCoeff_unique (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    (g := 1) hL
  change Matrix.toLin' ((1 : GeneralLinearGroup n K) : Matrix n n K)
      (lineVector G ℓ a L) =
    1 • lineVector G ℓ a (lineMap (1 : GeneralLinearGroup n K) L)
  rw [coe_one, Matrix.toLin'_one, lineMap_one, one_smul]
  rfl

private lemma lineCoeff_mul {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} (g h : G) {L : Submodule K (n → K)}
    (hL : L ∈ lineOrbit G ℓ) :
    lineCoeff G ℓ a ha0 ha (g * h) L =
      lineCoeff G ℓ a ha0 ha g (lineMap (h : GeneralLinearGroup n K) L) *
        lineCoeff G ℓ a ha0 ha h L := by
  have hh : lineMap (h : GeneralLinearGroup n K) L ∈ lineOrbit G ℓ :=
    lineOrbit_map_mem hL
  have hgh : lineMap (g : GeneralLinearGroup n K)
      (lineMap (h : GeneralLinearGroup n K) L) ∈ lineOrbit G ℓ :=
    lineOrbit_map_mem hh
  have hmap : lineMap (((g * h : G) : GeneralLinearGroup n K)) L =
      lineMap (g : GeneralLinearGroup n K) (lineMap (h : GeneralLinearGroup n K) L) := by
    change lineMap ((g : GeneralLinearGroup n K) * (h : GeneralLinearGroup n K)) L = _
    rw [lineMap_mul]
  have htoLin : Matrix.toLin' (((g * h : G) : GeneralLinearGroup n K) : Matrix n n K) =
      (Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)).comp
        (Matrix.toLin' ((h : GeneralLinearGroup n K) : Matrix n n K)) := by
    change Matrix.toLin' (((g : GeneralLinearGroup n K) * (h : GeneralLinearGroup n K) :
      GeneralLinearGroup n K) : Matrix n n K) = _
    rw [coe_mul, Matrix.toLin'_mul]
  symm
  apply lineCoeff_unique (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    (g := g * h) hL
  calc Matrix.toLin' (((g * h : G) : GeneralLinearGroup n K) : Matrix n n K)
        (lineVector G ℓ a L)
      = Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
          (Matrix.toLin' ((h : GeneralLinearGroup n K) : Matrix n n K)
            (lineVector G ℓ a L)) := by rw [htoLin, LinearMap.comp_apply]
    _ = Matrix.toLin' ((g : GeneralLinearGroup n K) : Matrix n n K)
          (lineCoeff G ℓ a ha0 ha h L • lineVector G ℓ a
            (lineMap (h : GeneralLinearGroup n K) L)) := by
          rw [lineCoeff_spec (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) hL]
    _ = lineCoeff G ℓ a ha0 ha h L • Matrix.toLin'
          ((g : GeneralLinearGroup n K) : Matrix n n K)
          (lineVector G ℓ a (lineMap (h : GeneralLinearGroup n K) L)) := by rw [map_smul]
    _ = lineCoeff G ℓ a ha0 ha h L •
          (lineCoeff G ℓ a ha0 ha g (lineMap (h : GeneralLinearGroup n K) L) •
            lineVector G ℓ a (lineMap (g : GeneralLinearGroup n K)
              (lineMap (h : GeneralLinearGroup n K) L))) := by
          rw [lineCoeff_spec (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) hh]
    _ = (lineCoeff G ℓ a ha0 ha g (lineMap (h : GeneralLinearGroup n K) L) *
          lineCoeff G ℓ a ha0 ha h L) •
          lineVector G ℓ a (lineMap (((g * h : G) : GeneralLinearGroup n K)) L) := by
          rw [hmap, smul_smul, mul_comm]

private lemma orbitChar_reindex {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} (g h : G) :
    (∏ L ∈ lineOrbit G ℓ,
        lineCoeff G ℓ a ha0 ha g (lineMap (h : GeneralLinearGroup n K) L)) =
      ∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha g L := by
  refine Finset.prod_nbij' (fun L => lineMap (h : GeneralLinearGroup n K) L)
    (fun L => lineMap ((h⁻¹ : G) : GeneralLinearGroup n K) L) ?_ ?_ ?_ ?_ ?_
  · intro L hL
    exact lineOrbit_map_mem hL
  · intro L hL
    exact lineOrbit_map_mem (g := h⁻¹) hL
  · intro L hL
    exact lineMap_inv_cancel' (h : GeneralLinearGroup n K) L
  · intro L hL
    exact lineMap_inv_cancel (h : GeneralLinearGroup n K) L
  · intro L hL
    rfl

private lemma orbitChar_mul {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} (g h : G) :
    orbitChar G ℓ a ha0 ha (g * h) =
      orbitChar G ℓ a ha0 ha g * orbitChar G ℓ a ha0 ha h := by
  rw [orbitChar, orbitChar, orbitChar]
  calc
    ∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha (g * h) L
        = ∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha g
            (lineMap (h : GeneralLinearGroup n K) L) *
            lineCoeff G ℓ a ha0 ha h L :=
          Finset.prod_congr rfl fun L hL => lineCoeff_mul (G := G) (ℓ := ℓ) (a := a)
            (ha0 := ha0) (ha := ha) g h hL
    _ = (∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha g
            (lineMap (h : GeneralLinearGroup n K) L)) *
          (∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha h L) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha g L) *
          (∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha h L) := by
          rw [orbitChar_reindex (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) g h]

private lemma orbitChar_one {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} :
    orbitChar G ℓ a ha0 ha 1 = 1 := by
  rw [orbitChar]
  apply Finset.prod_eq_one
  intro L hL
  exact lineCoeff_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) hL

private lemma orbitChar_inv {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} (g : G) :
    orbitChar G ℓ a ha0 ha g⁻¹ = (orbitChar G ℓ a ha0 ha g)⁻¹ := by
  have h := orbitChar_mul (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) g g⁻¹
  rw [mul_inv_cancel, orbitChar_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm


private lemma lineMap_self_involutive {x : GeneralLinearGroup n K} (hx2 : x * x = 1)
    (L : Submodule K (n → K)) : lineMap x (lineMap x L) = L := by
  rw [← lineMap_mul]
  rw [hx2, lineMap_one]

private lemma lineCoeff_eq_one_of_fixed {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {x : G}
    (hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1)
    (hxr : (((x : GeneralLinearGroup n K) : Matrix n n K) - 1).rank = 1)
    (h2 : (2 : K) ≠ 0) {L : Submodule K (n → K)} (hL : L ∈ lineOrbit G ℓ)
    (hLR : rootLine (x : GeneralLinearGroup n K) ≠ L)
    (hfix : lineMap (x : GeneralLinearGroup n K) L = L) :
    lineCoeff G ℓ a ha0 ha x L = 1 := by
  have ha_mem : a ∈ ℓ := by
    rw [ha]
    exact Submodule.mem_span_singleton_self a
  have hv_mem : lineVector G ℓ a L ∈ L := lineVector_mem (G := G) ha_mem hL
  have hv_ne : lineVector G ℓ a L ≠ 0 := lineVector_ne_zero (G := G) (ℓ := ℓ) (a := a) ha0
  have hspec := lineCoeff_spec (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    (g := x) hL
  rw [hfix] at hspec
  rcases eq_one_or_eq_neg_one_of_map_eq_smul hx2 hv_ne hspec with h1 | hneg
  · exact h1
  · exfalso
    have hvroot : lineVector G ℓ a L ∈ rootLine (x : GeneralLinearGroup n K) := by
      apply mem_rootLine_of_map_eq_neg h2
      rw [hspec, hneg]
      exact neg_one_smul K (lineVector G ℓ a L)
    have hrootfin : Module.finrank K (rootLine (x : GeneralLinearGroup n K)) = 1 := by
      rw [rootLine_finrank, hxr]
    have hroot : rootLine (x : GeneralLinearGroup n K) =
        Submodule.span K {lineVector G ℓ a L} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hrootfin hvroot hv_ne
    rw [span_lineVector (G := G) ha hL] at hroot
    exact hLR hroot

private lemma lineCoeff_rootLine_eq_neg {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {x : G}
    (hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1)
    (hR : rootLine (x : GeneralLinearGroup n K) ∈ lineOrbit G ℓ) :
    lineCoeff G ℓ a ha0 ha x (rootLine (x : GeneralLinearGroup n K)) = -1 := by
  have ha_mem : a ∈ ℓ := by
    rw [ha]
    exact Submodule.mem_span_singleton_self a
  have hv_mem : lineVector G ℓ a (rootLine (x : GeneralLinearGroup n K)) ∈
      rootLine (x : GeneralLinearGroup n K) := lineVector_mem (G := G) ha_mem hR
  have hv_ne : lineVector G ℓ a (rootLine (x : GeneralLinearGroup n K)) ≠ 0 :=
    lineVector_ne_zero (G := G) (ℓ := ℓ) (a := a) ha0
  have hspec := lineCoeff_spec (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    (g := x) hR
  rw [lineMap_rootLine hx2] at hspec
  have hneg := rootLine_map_eq_neg hx2 hv_mem
  apply smul_left_injective K hv_ne
  change lineCoeff G ℓ a ha0 ha x (rootLine (x : GeneralLinearGroup n K)) •
      lineVector G ℓ a (rootLine (x : GeneralLinearGroup n K)) =
    (-1 : K) • lineVector G ℓ a (rootLine (x : GeneralLinearGroup n K))
  rw [← hspec, hneg, neg_one_smul]

private lemma orbitChar_product_erase_eq_one {G : Subgroup (GeneralLinearGroup n K)}
    [Fintype G] {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {x : G}
    (hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1)
    (hxr : (((x : GeneralLinearGroup n K) : Matrix n n K) - 1).rank = 1)
    (h2 : (2 : K) ≠ 0) :
    (∏ L ∈ (lineOrbit G ℓ).erase (rootLine (x : GeneralLinearGroup n K)),
        lineCoeff G ℓ a ha0 ha x L) = 1 := by
  have hx2G : x * x = 1 := Subtype.ext hx2
  refine Finset.prod_involution (fun L _ => lineMap (x : GeneralLinearGroup n K) L) ?_ ?_ ?_ ?_
  · intro L hLmem
    have hL : L ∈ lineOrbit G ℓ := (Finset.mem_erase.mp hLmem).2
    have hc := lineCoeff_mul (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
      (g := x) (h := x) hL
    have hone : lineCoeff G ℓ a ha0 ha 1 L = 1 :=
      lineCoeff_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) hL
    rw [hx2G, hone] at hc
    simpa [mul_comm] using hc.symm
  · intro L hLmem hf hfix
    have hL : L ∈ lineOrbit G ℓ := (Finset.mem_erase.mp hLmem).2
    have hne : L ≠ rootLine (x : GeneralLinearGroup n K) := (Finset.mem_erase.mp hLmem).1
    exact hf (lineCoeff_eq_one_of_fixed (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
      (ha := ha) hx2 hxr h2 hL (Ne.symm hne) hfix)
  · intro L hLmem
    have hL : L ∈ lineOrbit G ℓ := (Finset.mem_erase.mp hLmem).2
    have hne : L ≠ rootLine (x : GeneralLinearGroup n K) := (Finset.mem_erase.mp hLmem).1
    refine Finset.mem_erase.mpr ⟨?_, lineOrbit_map_mem (g := x) hL⟩
    intro hmap
    apply hne
    have h := congrArg (lineMap (x : GeneralLinearGroup n K)) hmap
    rw [lineMap_self_involutive hx2 L, lineMap_rootLine hx2] at h
    exact h
  · intro L hLmem
    exact lineMap_self_involutive hx2 L

private lemma orbitChar_product_eq_one_of_not_mem {G : Subgroup (GeneralLinearGroup n K)}
    [Fintype G] {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {x : G}
    (hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1)
    (hxr : (((x : GeneralLinearGroup n K) : Matrix n n K) - 1).rank = 1)
    (h2 : (2 : K) ≠ 0) (hR : rootLine (x : GeneralLinearGroup n K) ∉ lineOrbit G ℓ) :
    (∏ L ∈ lineOrbit G ℓ, lineCoeff G ℓ a ha0 ha x L) = 1 := by
  have hx2G : x * x = 1 := Subtype.ext hx2
  refine Finset.prod_involution (fun L _ => lineMap (x : GeneralLinearGroup n K) L) ?_ ?_ ?_ ?_
  · intro L hL
    have hc := lineCoeff_mul (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
      (g := x) (h := x) hL
    have hone : lineCoeff G ℓ a ha0 ha 1 L = 1 :=
      lineCoeff_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha) hL
    rw [hx2G, hone] at hc
    simpa [mul_comm] using hc.symm
  · intro L hL hf hfix
    refine hf (lineCoeff_eq_one_of_fixed (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
      (ha := ha) hx2 hxr h2 hL ?_ hfix)
    intro hLR
    exact hR (hLR.symm ▸ hL)
  · intro L hL
    exact lineOrbit_map_mem (g := x) hL
  · intro L hL
    exact lineMap_self_involutive hx2 L

private lemma orbitChar_reflection {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {x : G}
    (hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1)
    (hxr : (((x : GeneralLinearGroup n K) : Matrix n n K) - 1).rank = 1)
    (h2 : (2 : K) ≠ 0) :
    orbitChar G ℓ a ha0 ha x =
      if rootLine (x : GeneralLinearGroup n K) ∈ lineOrbit G ℓ then -1 else 1 := by
  by_cases hR : rootLine (x : GeneralLinearGroup n K) ∈ lineOrbit G ℓ
  · rw [if_pos hR, orbitChar,
      ← Finset.mul_prod_erase (lineOrbit G ℓ)
        (fun L => lineCoeff G ℓ a ha0 ha x L) hR,
      orbitChar_product_erase_eq_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
        (ha := ha) hx2 hxr h2, mul_one]
    exact lineCoeff_rootLine_eq_neg (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
      (ha := ha) hx2 hR
  · rw [if_neg hR, orbitChar]
    exact orbitChar_product_eq_one_of_not_mem (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
      (ha := ha) hx2 hxr h2 hR


private lemma mul_sub_one_sq_eq_zero {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {s c : G}
    (hs2 : (s : GeneralLinearGroup n K) * (s : GeneralLinearGroup n K) = 1)
    (hc2 : (c : GeneralLinearGroup n K) * (c : GeneralLinearGroup n K) = 1)
    (hroot : rootLine (s : GeneralLinearGroup n K) = rootLine (c : GeneralLinearGroup n K)) :
    ((((s * c : G) : GeneralLinearGroup n K) : Matrix n n K) - 1) *
        ((((s * c : G) : GeneralLinearGroup n K) : Matrix n n K) - 1) = 0 := by
  let S : (n → K) →ₗ[K] (n → K) := Matrix.toLin' ((s : GeneralLinearGroup n K) :
    Matrix n n K)
  let C : (n → K) →ₗ[K] (n → K) := Matrix.toLin' ((c : GeneralLinearGroup n K) :
    Matrix n n K)
  let L : Submodule K (n → K) := rootLine (s : GeneralLinearGroup n K)
  let A : Matrix n n K := (((s * c : G) : GeneralLinearGroup n K) : Matrix n n K)
  let Nmat : Matrix n n K := A - 1
  let N : (n → K) →ₗ[K] (n → K) := Matrix.toLin' Nmat
  have hSfix : L.map S = L := by
    change lineMap (s : GeneralLinearGroup n K) L = L
    rw [show L = rootLine (s : GeneralLinearGroup n K) from rfl]
    exact lineMap_rootLine hs2
  have hCfix : L.map C = L := by
    change lineMap (c : GeneralLinearGroup n K) L = L
    rw [show L = rootLine (c : GeneralLinearGroup n K) from hroot]
    exact lineMap_rootLine hc2
  have hSC : Matrix.toLin' A = S.comp C := by
    change Matrix.toLin' (((s : GeneralLinearGroup n K) * (c : GeneralLinearGroup n K) :
      GeneralLinearGroup n K) : Matrix n n K) = _
    rw [coe_mul, Matrix.toLin'_mul]
  have hNSC : N = S.comp C - 1 := by
    dsimp only [N, Nmat]
    rw [map_sub, hSC, Matrix.toLin'_one, Module.End.one_eq_id]
  have hNdecomp : N = (S - 1) + S.comp (C - 1) := by
    rw [hNSC]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      Module.End.one_apply, map_sub]
    abel
  have hNrange : N.range ≤ L := by
    rw [hNdecomp]
    refine (LinearMap.range_add_le (S - 1) (S.comp (C - 1))).trans ?_
    apply sup_le
    · exact le_of_eq (by rw [show (S - 1).range = L from rfl])
    · rw [LinearMap.range_comp]
      have hCr : (C - 1).range = L := by
        change rootLine (c : GeneralLinearGroup n K) = L
        exact hroot.symm
      rw [hCr, hSfix]
  have hNker : ∀ v ∈ L, N v = 0 := by
    intro v hv
    have hSv : S v = -v := rootLine_map_eq_neg hs2 hv
    have hCv : C v = -v := by
      apply rootLine_map_eq_neg hc2
      rw [← hroot]
      exact hv
    have hCsub : (C - 1) v = -v - v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hCv]
    have hSsub : (S - 1) v = -v - v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hSv]
    have hneg : -v - v = -(v + v) := by
      rw [sub_eq_add_neg, neg_add_rev]
    have hScomp : S ((C - 1) v) = v + v := by
      rw [hCsub, hneg, map_neg, map_add, hSv]
      abel
    rw [hNdecomp, LinearMap.add_apply]
    change (S - 1) v + S ((C - 1) v) = 0
    rw [hScomp, hSsub]
    abel
  have hNcomp : N.comp N = 0 := by
    apply LinearMap.ext
    intro v
    exact hNker (N v) (hNrange (LinearMap.mem_range_self N v))
  have hNmat2 : Nmat * Nmat = 0 := by
    apply (Matrix.toLin' (R := K) (m := n) (n := n)).injective
    rw [Matrix.toLin'_mul]
    change N.comp N = Matrix.toLin' (0 : Matrix n n K)
    rw [hNcomp, map_zero]
  simpa [Nmat, A] using hNmat2

private lemma eq_of_rootLine_eq {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    (hG : (Nat.card G : K) ≠ 0) {s c : G}
    (hs2 : (s : GeneralLinearGroup n K) * (s : GeneralLinearGroup n K) = 1)
    (hc2 : (c : GeneralLinearGroup n K) * (c : GeneralLinearGroup n K) = 1)
    (hroot : rootLine (s : GeneralLinearGroup n K) = rootLine (c : GeneralLinearGroup n K)) :
    s = c := by
  let A : Matrix n n K := (((s * c : G) : GeneralLinearGroup n K) : Matrix n n K)
  let Nmat : Matrix n n K := A - 1
  have hNmat2 : Nmat * Nmat = 0 := by
    simpa [A, Nmat] using mul_sub_one_sq_eq_zero hs2 hc2 hroot
  have hA : A = 1 + Nmat := by
    dsimp [Nmat]
    abel
  have hpow : ∀ k : ℕ, A ^ k = 1 + k • Nmat := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc A ^ (k + 1) = A ^ k * A := by rw [pow_succ]
          _ = (1 + k • Nmat) * (1 + Nmat) := by rw [ih, hA]
          _ = 1 + (k + 1) • Nmat := by
              rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hNmat2, smul_zero,
                add_zero]
              rw [add_assoc, add_comm Nmat (k • Nmat), ← AddMonoid.nsmul_succ]
  have hcard : A ^ Nat.card G = 1 := by
    have h := pow_card_eq_one' (G := G) (x := s * c)
    have h' : ((((s * c : G) : GeneralLinearGroup n K) ^ Nat.card G :
        GeneralLinearGroup n K) : Matrix n n K) = 1 := by
      rw [← Subgroup.coe_pow, h]
      rfl
    calc A ^ Nat.card G
        = ((((s * c : G) : GeneralLinearGroup n K) ^ Nat.card G :
            GeneralLinearGroup n K) : Matrix n n K) := by
          dsimp [A]
      _ = 1 := h'
  have hNzero : Nmat = 0 := by
    have h := hpow (Nat.card G)
    rw [hcard] at h
    have hz : (Nat.card G) • Nmat = 0 := by
      apply add_left_cancel (a := (1 : Matrix n n K))
      simpa using h.symm
    have hz' : (Nat.card G : K) • Nmat = 0 := by
      rw [Nat.cast_smul_eq_nsmul K (Nat.card G) Nmat]
      exact hz
    exact (smul_eq_zero.mp hz').resolve_left hG
  have hA1 : A = 1 := by
    rw [← sub_eq_zero]
    simpa [Nmat] using hNzero
  have ht1 : s * c = 1 := Subtype.ext (Units.ext hA1)
  have hc2G : c * c = 1 := by
    apply Subtype.ext
    simpa using hc2
  calc s = s * (c * c) := by rw [hc2G, mul_one]
    _ = (s * c) * c := by rw [mul_assoc]
    _ = c := by rw [ht1, one_mul]


private lemma conj_mul_self_of_mul_self {x : GeneralLinearGroup n K} (hx2 : x * x = 1)
    (g : GeneralLinearGroup n K) : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
  calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hx2]; group

private lemma exists_conj_of_rootLine_conj_mem {G : Subgroup (GeneralLinearGroup n K)}
    [Fintype G] (hG : (Nat.card G : K) ≠ 0) {c s : GeneralLinearGroup n K}
    (hc2 : c * c = 1) (hs2 : s * s = 1) (hs : s ∈ G) (hcG : c ∈ G)
    {ℓ : Submodule K (n → K)} (hrootℓ : rootLine s = ℓ) {g : G}
    (hgO : rootLine ((g : GeneralLinearGroup n K) * c *
      (g : GeneralLinearGroup n K)⁻¹) ∈ lineOrbit G ℓ) :
    ∃ k ∈ G, s = k * c * k⁻¹ := by
  let cG : G := ⟨c, hcG⟩
  rw [lineOrbit, Finset.mem_image] at hgO
  obtain ⟨h, -, hh⟩ := hgO
  let y : G := g * cG * g⁻¹
  let z : G := h⁻¹ * y * h
  have hyco : (y : GeneralLinearGroup n K) = (g : GeneralLinearGroup n K) * c *
      (g : GeneralLinearGroup n K)⁻¹ := by
    dsimp only [y, cG]
    rfl
  have hh' : lineMap (h : GeneralLinearGroup n K) ℓ =
      rootLine (y : GeneralLinearGroup n K) := by
    rw [hyco]
    exact hh
  have hzco : (z : GeneralLinearGroup n K) = (h : GeneralLinearGroup n K)⁻¹ *
      (y : GeneralLinearGroup n K) * (h : GeneralLinearGroup n K) := by
    dsimp only [z]
    rfl
  have hzroot : rootLine (z : GeneralLinearGroup n K) = ℓ := by
    calc rootLine (z : GeneralLinearGroup n K)
        = lineMap (h : GeneralLinearGroup n K)⁻¹
            (rootLine (y : GeneralLinearGroup n K)) := by
          rw [hzco]
          simpa only [inv_inv] using rootLine_conj (h : GeneralLinearGroup n K)⁻¹
            (y : GeneralLinearGroup n K)
      _ = lineMap (h : GeneralLinearGroup n K)⁻¹ (lineMap (h : GeneralLinearGroup n K) ℓ) := by
          rw [← hh']
      _ = ℓ := lineMap_inv_cancel' (h : GeneralLinearGroup n K) ℓ
  have hzconj : (z : GeneralLinearGroup n K) =
      (((h⁻¹ * g : G) : GeneralLinearGroup n K)) * c *
        ((((h⁻¹ * g : G) : GeneralLinearGroup n K)))⁻¹ := by
    dsimp only [z, y, cG]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hz2 : (z : GeneralLinearGroup n K) * (z : GeneralLinearGroup n K) = 1 := by
    rw [hzconj]
    exact conj_mul_self_of_mul_self hc2 (((h⁻¹ * g : G) : GeneralLinearGroup n K))
  have hs_eq_z : (⟨s, hs⟩ : G) = z :=
    eq_of_rootLine_eq (G := G) hG hs2 hz2 (by rw [hrootℓ, hzroot])
  refine ⟨(((h⁻¹ * g : G) : GeneralLinearGroup n K)), (h⁻¹ * g).property, ?_⟩
  have hsz : s = (z : GeneralLinearGroup n K) := by
    simpa using congrArg (fun u : G => (u : GeneralLinearGroup n K)) hs_eq_z
  rw [hsz]
  exact hzconj


private lemma orbitChar_conj_eq_one {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {c : GeneralLinearGroup n K} (hc2 : c * c = 1)
    (hcr : ((c : Matrix n n K) - 1).rank = 1) (h2 : (2 : K) ≠ 0) {g x : G}
    (hxco : (x : GeneralLinearGroup n K) = (g : GeneralLinearGroup n K) * c *
      (g : GeneralLinearGroup n K)⁻¹)
    (hnot : rootLine (x : GeneralLinearGroup n K) ∉ lineOrbit G ℓ) :
    orbitChar G ℓ a ha0 ha x = 1 := by
  have hx2 : (x : GeneralLinearGroup n K) * (x : GeneralLinearGroup n K) = 1 := by
    rw [hxco]
    exact conj_mul_self_of_mul_self hc2 (g : GeneralLinearGroup n K)
  have hxr : (((x : GeneralLinearGroup n K) : Matrix n n K) - 1).rank = 1 := by
    rw [← rootLine_finrank (x : GeneralLinearGroup n K), hxco,
      rootLine_conj (g : GeneralLinearGroup n K) c, lineMap_finrank, rootLine_finrank, hcr]
  have hchar := orbitChar_reflection (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
    (ha := ha) (x := x) hx2 hxr h2
  rwa [if_neg hnot] at hchar

private lemma orbitChar_eq_one_on_closure {G : Subgroup (GeneralLinearGroup n K)} [Fintype G]
    {ℓ : Submodule K (n → K)} {a : n → K} {ha0 : a ≠ 0}
    {ha : ℓ = Submodule.span K {a}} {c : GeneralLinearGroup n K} (hc2 : c * c = 1)
    (hcr : ((c : Matrix n n K) - 1).rank = 1) (h2 : (2 : K) ≠ 0) (hcG : c ∈ G)
    (hgen : Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹} = G)
    (hno_gen : ∀ g : G, rootLine ((g : GeneralLinearGroup n K) * c *
      (g : GeneralLinearGroup n K)⁻¹) ∉ lineOrbit G ℓ) :
    ∀ (x : GeneralLinearGroup n K)
      (hx : x ∈ Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹}),
      orbitChar G ℓ a ha0 ha ⟨x, hgen ▸ hx⟩ = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with ⟨g, hgG, rfl⟩
        let gG : G := ⟨g, hgG⟩
        let x : G := gG * (⟨c, hcG⟩ : G) * gG⁻¹
        have hxco : (x : GeneralLinearGroup n K) = (gG : GeneralLinearGroup n K) * c *
            (gG : GeneralLinearGroup n K)⁻¹ := by
          dsimp only [x]
          rfl
        have hnot : rootLine (x : GeneralLinearGroup n K) ∉ lineOrbit G ℓ := by
          rw [hxco]
          exact hno_gen gG
        have hchar := orbitChar_conj_eq_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0)
          (ha := ha) hc2 hcr h2 (g := gG) (x := x) hxco hnot
        have hxeq : x = ⟨g * c * g⁻¹, hgen ▸ Subgroup.subset_closure ⟨g, hgG, rfl⟩⟩ := by
          apply Subtype.ext
          dsimp only [x, gG]
          rfl
        rw [← hxeq]
        exact hchar
    | one =>
        rw [show (⟨1, hgen ▸ Subgroup.one_mem _⟩ : G) = 1 from Subtype.ext rfl]
        exact orbitChar_one (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
    | mul x y hx hy ihx ihy =>
        have h := orbitChar_mul (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
          ⟨x, hgen ▸ hx⟩ ⟨y, hgen ▸ hy⟩
        simpa [ihx, ihy] using h
    | inv x hx ih =>
        have h := orbitChar_inv (G := G) (ℓ := ℓ) (a := a) (ha0 := ha0) (ha := ha)
          ⟨x, hgen ▸ hx⟩
        rw [show (⟨x⁻¹, hgen ▸ Subgroup.inv_mem
            (Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹}) hx⟩ : G) =
            (⟨x, hgen ▸ hx⟩ : G)⁻¹ from Subtype.ext rfl]
        simpa [ih] using h


private lemma exists_conj_aux {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    {G : Subgroup (GeneralLinearGroup n K)} [Fintype G] (hG : (Nat.card G : K) ≠ 0)
    {c : GeneralLinearGroup n K} (hc2 : c * c = 1)
    (hcr : ((c : Matrix n n K) - 1).rank = 1)
    (hgen : Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹} = G) {s : GeneralLinearGroup n K}
    (hs : s ∈ G) (hs2 : s * s = 1) (hsr : ((s : Matrix n n K) - 1).rank = 1) :
    ∃ g ∈ G, s = g * c * g⁻¹ := by
  classical
  have hcG : c ∈ G := by
    rw [← hgen]
    exact Subgroup.subset_closure ⟨1, G.one_mem, by simp⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_ne_zero hG hc2 hcr hgen
  have hpos : 0 < Module.finrank K (rootLine s) := by
    rw [rootLine_finrank s, hsr]
    norm_num
  have hne : rootLine s ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank K (rootLine s) = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨a, ha_mem, ha_ne⟩ := (Submodule.ne_bot_iff (rootLine s)).mp hne
  set ℓ : Submodule K (n → K) := Submodule.span K {a} with hℓ
  have hrootℓ : rootLine s = ℓ := by
    rw [hℓ]
    exact eq_span_singleton_of_mem_of_finrank_eq_one
      (by rw [rootLine_finrank, hsr]) ha_mem ha_ne
  have hℓO : ℓ ∈ lineOrbit G ℓ := by
    rw [lineOrbit, Finset.mem_image]
    exact ⟨1, Finset.mem_univ _, lineMap_one ℓ⟩
  have hsO : rootLine s ∈ lineOrbit G ℓ := by
    rw [hrootℓ]
    exact hℓO
  have hχs : orbitChar G ℓ a ha_ne hℓ ⟨s, hs⟩ = -1 := by
    have h := orbitChar_reflection (G := G) (ℓ := ℓ) (a := a) (ha0 := ha_ne) (ha := hℓ)
      (x := ⟨s, hs⟩) hs2 hsr h2
    rwa [if_pos hsO] at h
  by_contra hno
  have hno_gen : ∀ g : G, rootLine ((g : GeneralLinearGroup n K) * c *
      (g : GeneralLinearGroup n K)⁻¹) ∉ lineOrbit G ℓ := by
    intro g hgO
    exact hno (exists_conj_of_rootLine_conj_mem (G := G) hG (c := c) (s := s)
      hc2 hs2 hs hcG hrootℓ hgO)
  have hgen_one := orbitChar_eq_one_on_closure (G := G) (ℓ := ℓ) (a := a)
    (ha0 := ha_ne) (ha := hℓ) hc2 hcr h2 hcG hgen hno_gen
  have hs_closure : s ∈ Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹} := by
    rw [hgen]
    exact hs
  have hχs1 : orbitChar G ℓ a ha_ne hℓ ⟨s, hs⟩ = 1 := by
    simpa using hgen_one s hs_closure
  have hneg : (-1 : K) = 1 := hχs.symm.trans hχs1
  have htwo : (2 : K) = 0 := by
    calc (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [hneg, sub_self]
  exact h2 htwo


theorem exists_conj_of_closure_conj_eq {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    {G : Subgroup (GeneralLinearGroup n K)} (hG : (Nat.card G : K) ≠ 0) {c : GeneralLinearGroup n K}
    (hc2 : c * c = 1) (hcr : ((c : Matrix n n K) - 1).rank = 1)
    (hgen : Subgroup.closure {x | ∃ g ∈ G, x = g * c * g⁻¹} = G) {s : GeneralLinearGroup n K}
    (hs : s ∈ G) (hs2 : s * s = 1) (hsr : ((s : Matrix n n K) - 1).rank = 1) :
    ∃ g ∈ G, s = g * c * g⁻¹ := by
  classical
  have hcard_ne : Nat.card G ≠ 0 := by
    intro h
    exact hG (by rw [h]; simp)
  have hfin : Finite G := Nat.finite_of_card_ne_zero hcard_ne
  let F : Fintype G := Fintype.ofFinite G
  exact @exists_conj_aux n K _ _ _ G F hG c hc2 hcr hgen s hs hs2 hsr

end Matrix.GeneralLinearGroup

end
