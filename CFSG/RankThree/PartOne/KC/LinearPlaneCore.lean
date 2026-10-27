module

public import Mathlib
public import CFSG.RankThree.PartOne.KC.LinearPlaneMixing
public import CFSG.RankThree.PartOne.KC.LinearPlaneGeneration

public section

namespace CFSG.RankThree.PartOne.KCLinPlane

open Polynomial Module Matrix CFSG CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.Classical

@[expose] def GoodBlock {n : ℕ} {K : Type} [Field K] {x : Module.End K (Fin n → K)}
    (h : primaryFactors x) : Prop :=
  3 ≤ mult x h ∨ (2 ≤ mult x h ∧ 3 < Nat.card (Efac x h))

section GoodSL

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem isQuasisimple_blockImage_of_good {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) (a : primaryFactors x) (hg : GoodBlock a) :
    CFSG.IsQuasisimple (blockImage hx a) := by
  have ha2 : 2 ≤ mult x a := by
    rcases hg with h | ⟨h, _⟩ <;> omega
  have hE : 3 ≤ mult x a ∨ ∃ s : Finset (Efac x a), s.card = 4 := by
    rcases hg with h | ⟨_, h⟩
    · exact Or.inl h
    · right
      have hfin : Finite (Efac x a) := Nat.finite_of_card_ne_zero (by omega)
      have := Fintype.ofFinite (Efac x a)
      have h4 : 4 ≤ (Finset.univ : Finset (Efac x a)).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        omega
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
      exact ⟨t, ht⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx))
    (isQuasisimple_blockSL a ha2 hE)

omit [Finite K] in
theorem blockImage_le_range_toGL_of_good {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) (a : primaryFactors x) (hg : GoodBlock a) :
    blockImage hx a ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* _).range := by
  intro g hg'
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  exact KCUnitary.eq_one_of_perfect_of_comm (isQuasisimple_blockImage_of_good hx a hg).1
    (fun u v : Kˣ => mul_comm u v)
    ((GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp (blockImage hx a).subtype) ⟨g, hg'⟩

end GoodSL

section OneAdd

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def oneAddGL (β : Module.End K (Fin n → K)) (hββ : β * β = 0) :
    GL (Fin n) K :=
  Matrix.GeneralLinearGroup.toLin.symm ⟨1 + β, 1 - β, by
    simp only [add_mul, mul_sub, one_mul, mul_one, hββ]
    abel, by
    simp only [sub_mul, mul_add, one_mul, mul_one, hββ]
    abel⟩

theorem toLin'_oneAddGL (β : Module.End K (Fin n → K)) (hββ : β * β = 0) :
    Matrix.toLin' ((oneAddGL β hββ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + β := by
  have h1 : (Matrix.GeneralLinearGroup.toLin (oneAddGL β hββ) : Module.End K (Fin n → K)) =
      Matrix.toLin' ((oneAddGL β hββ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  rw [← h1, oneAddGL, MulEquiv.apply_symm_apply]

theorem exists_mem_blockImage_one_add {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) {a0 : GL (Fin n) K}
    (hax : Matrix.toLin' (a0 : Matrix (Fin n) (Fin n) K) = x) (h : primaryFactors x)
    (β : Module.End K (Fin n → K)) (hβ : β ∈ commutant x) (hββ : β * β = 0)
    (hkill : ∀ k ∈ primaryFactors x, k ≠ (h : K[X]) → ∀ v ∈ primaryComponent x k, β v = 0)
    (hdet : LinearMap.det (1 + commutantRestrict (h : K[X]) ⟨β, hβ⟩) = 1) :
    ∃ g : GL (Fin n) K, g ∈ blockImage hx h ∧
      ∀ v, Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v + β v := by
  have hg := toLin'_oneAddGL β hββ
  have hcomm : oneAddGL β hββ * a0 = a0 * oneAddGL β hββ := by
    refine Units.ext (Matrix.toLin'.injective ?_)
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul, hg, hax]
    have hβx : β * x = x * β := ((mem_commutant x).mp hβ).eq
    change (1 + β) * x = x * (1 + β)
    rw [add_mul, mul_add, one_mul, mul_one, hβx]
  have hfix : ∀ k : primaryFactors x, k ≠ h → ∀ v ∈ primaryComponent x (k : K[X]),
      Matrix.toLin' ((oneAddGL β hββ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v = v := by
    intro k hk v hv
    rw [hg, LinearMap.add_apply, Module.End.one_apply,
      hkill k k.2 (fun hh => hk (Subtype.ext hh)) v hv, add_zero]
  have hdet' : ∀ r : commutant x, (r : Module.End K (Fin n → K)) =
      Matrix.toLin' ((oneAddGL β hββ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      LinearMap.det (commutantRestrict (h : K[X]) r) = 1 := by
    intro r hr
    have hr' : r = 1 + ⟨β, hβ⟩ := Subtype.ext (by rw [hr, hg]; rfl)
    have : commutantRestrict (h : K[X]) r = 1 + commutantRestrict (h : K[X]) ⟨β, hβ⟩ := by
      rw [hr']
      exact (map_add (commutantRestrictHom (h : K[X])) 1 ⟨β, hβ⟩).trans
        (by rw [map_one])
    rw [this]
    exact hdet
  exact ⟨oneAddGL β hββ, mem_blockImage_of_restrict hx h hax hcomm hfix hdet', fun v => by
    rw [hg, LinearMap.add_apply, Module.End.one_apply]⟩

end OneAdd

section Fixed

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] (E0 : Subgroup (SpecialLinearGroup (Fin n) K))
  [Fintype E0] [IsMulCommutative E0] [Finite K] (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)

local notation "ρ₀" => planeRep E0

include hP hpK

omit [IsMulCommutative E0] [Finite K] hP hpK in
theorem X_sub_one_mem {L : Subgroup ↥E0} (hLne : projLine ρ₀ L ≠ 0) {b : ↥E0} (hbL : b ∈ L) :
    (X - C 1 : K[X]) ∈ primaryFactors (act ρ₀ b) := by
  obtain ⟨v, hv⟩ : ∃ v, projLine ρ₀ L v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hLne (LinearMap.ext fun v => hcon v)
  have hy : projLine ρ₀ L v ∈ LinearMap.range (projLine ρ₀ L) := LinearMap.mem_range_self _ _
  have hfix := fix_range_projLine E0 hbL _ hy
  refine mem_primaryFactors_of_ne_zero (irreducible_X_sub_C 1) (monic_X_sub_C 1) hv ?_
  rw [mem_primaryComponent]
  simp [hfix]

omit [IsMulCommutative E0] [Finite K] in
theorem primaryComponent_X_sub_one {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {b : ↥E0}
    (hbL : b ∈ L) (hb1 : b ≠ 1) :
    primaryComponent (act ρ₀ b) (X - C 1) = LinearMap.range (avgOp ρ₀ L) := by
  ext v
  rw [mem_primaryComponent, range_avgOp ρ₀ (natCard_cast_line hpK (mem_lines.mp hL)),
    mem_fixedSpace]
  constructor
  · intro hv
    have hv' : act ρ₀ b v = v := by
      simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply] at hv
      exact sub_eq_zero.mp hv
    exact fixedSpace_of_apply_eq ρ₀ hP (mem_lines.mp hL) hbL hb1 hv'
  · intro hv
    simp [hv b hbL]

omit [Finite K] in
theorem avgOp_apply_of_mem_primaryComponent {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {b : ↥E0}
    (hbL : b ∈ L) (hb1 : b ≠ 1) (hXmem : (X - C 1 : K[X]) ∈ primaryFactors (act ρ₀ b))
    {k : K[X]} (hk : k ∈ primaryFactors (act ρ₀ b)) (hkX : k ≠ X - C 1) {v : Fin n → K}
    (hv : v ∈ primaryComponent (act ρ₀ b) k) : avgOp ρ₀ L v = 0 := by
  have hw1 : avgOp ρ₀ L v ∈ primaryComponent (act ρ₀ b) k :=
    apply_mem_primaryComponent (commute_act_avgOp E0 b L).symm hv
  have hw2 : avgOp ρ₀ L v ∈ primaryComponent (act ρ₀ b) (X - C 1) := by
    rw [primaryComponent_X_sub_one E0 hP hpK hL hbL hb1]
    exact LinearMap.mem_range_self _ _
  exact eq_zero_of_mem_primaryComponent_ne hk hXmem hkX hw1 hw2

omit [Finite K] in
theorem fixedBlock_mem {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (hLne : projLine ρ₀ L ≠ 0)
    {b : ↥E0} (hbL : b ∈ L) (hb1 : b ≠ 1) (hsq : Squarefree (minpoly K (act ρ₀ b)))
    {g : (Fin n → K) ≃ₗ[K] (Fin n → K)} (hg : g ∈ suppGroup (avgOp ρ₀ L))
    {A : SpecialLinearGroup (Fin n) K}
    (hA : ∀ v, Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) v = g v) :
    SpecialLinearGroup.toGL A ∈ blockImage hsq ⟨X - C 1, X_sub_one_mem E0 hLne hbL⟩ := by
  obtain ⟨hdet, hc, hf⟩ := hg
  have hLc : Nat.card L = p := mem_lines.mp hL
  have hQQ : ∀ v, avgOp ρ₀ L (avgOp ρ₀ L v) = avgOp ρ₀ L v := fun v => by
    simpa using LinearMap.congr_fun (avgOp_mul_avgOp ρ₀ (natCard_cast_line hpK hLc)) v
  have hbQ : ∀ v, act ρ₀ b (avgOp ρ₀ L v) = avgOp ρ₀ L v := fun v => by
    simpa using LinearMap.congr_fun (act_mul_avgOp ρ₀ hbL) v
  have hQb : ∀ v, avgOp ρ₀ L (act ρ₀ b v) = avgOp ρ₀ L v := fun v => by
    simpa using LinearMap.congr_fun (avgOp_mul_act ρ₀ hbL) v
  have hgb : ∀ v, g (act ρ₀ b v) = act ρ₀ b (g v) := by
    intro v
    have h1 : act ρ₀ b v = avgOp ρ₀ L v + act ρ₀ b (v - avgOp ρ₀ L v) := by
      rw [map_sub, hbQ]
      abel
    have h2 : avgOp ρ₀ L (act ρ₀ b (v - avgOp ρ₀ L v)) = 0 := by
      rw [hQb, map_sub, hQQ, sub_self]
    have h3 : g (act ρ₀ b (v - avgOp ρ₀ L v)) = act ρ₀ b (v - avgOp ρ₀ L v) := by
      have := hf (act ρ₀ b (v - avgOp ρ₀ L v))
      rwa [h2, sub_zero] at this
    have h4 : g v = g (avgOp ρ₀ L v) + (v - avgOp ρ₀ L v) :=
      calc g v = g (avgOp ρ₀ L v + (v - avgOp ρ₀ L v)) := by congr 1; abel
        _ = g (avgOp ρ₀ L v) + (v - avgOp ρ₀ L v) := by rw [map_add, hf v]
    calc g (act ρ₀ b v) = g (avgOp ρ₀ L v + act ρ₀ b (v - avgOp ρ₀ L v)) := by rw [← h1]
      _ = g (avgOp ρ₀ L v) + act ρ₀ b (v - avgOp ρ₀ L v) := by rw [map_add, h3]
      _ = act ρ₀ b (g (avgOp ρ₀ L v) + (v - avgOp ρ₀ L v)) := by
        rw [map_add, hc v, hbQ]
      _ = act ρ₀ b (g v) := by rw [← h4]
  have hax : Matrix.toLin' ((SpecialLinearGroup.toGL (b : SpecialLinearGroup (Fin n) K) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = act ρ₀ b := rfl
  have hXmem := X_sub_one_mem E0 hLne hbL
  have hcomm : SpecialLinearGroup.toGL A *
      SpecialLinearGroup.toGL (b : SpecialLinearGroup (Fin n) K) =
      SpecialLinearGroup.toGL (b : SpecialLinearGroup (Fin n) K) * SpecialLinearGroup.toGL A := by
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    change Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)
      (act ρ₀ b v) = act ρ₀ b (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) v)
    rw [hA, hA]
    exact hgb v
  have hfix : ∀ k : primaryFactors (act ρ₀ b), k ≠ ⟨X - C 1, hXmem⟩ →
      ∀ v ∈ primaryComponent (act ρ₀ b) (k : K[X]),
        Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v =
          v := by
    intro k hk v hv
    have h0 := avgOp_apply_of_mem_primaryComponent E0 hP hpK hL hbL hb1 hXmem k.2
      (fun hh => hk (Subtype.ext hh)) hv
    change Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) v = v
    rw [hA]
    have := hf v
    rwa [h0, sub_zero] at this
  refine mem_blockImage_of_restrict hsq ⟨X - C 1, hXmem⟩ hax hcomm hfix ?_
  intro r hr
  have : Fact (Irreducible (X - C 1 : K[X])) := ⟨irreducible_X_sub_C 1⟩
  have hrg : (r : Module.End K (Fin n → K)) = (g : Module.End K (Fin n → K)) :=
    LinearMap.ext fun v => by rw [hr]; exact hA v
  refine det_eq_one_of_restrictScalars (natDegree_X_sub_C 1) _ ?_
  have hW : primaryComponent (act ρ₀ b) (X - C 1) = LinearMap.range (avgOp ρ₀ L) :=
    primaryComponent_X_sub_one E0 hP hpK hL hbL hb1
  have hmaps : primaryComponent (act ρ₀ b) (X - C 1) ≤
      (primaryComponent (act ρ₀ b) (X - C 1)).comap (r : Module.End K (Fin n → K)) :=
    fun v hv => apply_mem_primaryComponent ((mem_commutant _).mp r.2) hv
  have h1 : (commutantRestrict (X - C 1) r).restrictScalars K =
      (r : Module.End K (Fin n → K)).restrict hmaps := rfl
  rw [h1, det_restrict_eq_det _ _ hW (avgOp_mul_avgOp ρ₀ (natCard_cast_line hpK hLc)) _
    (fun v => by rw [hrg]; exact hc v) (fun v => by rw [hrg]; exact hf v) hmaps, hrg]
  exact (det_eq_one_iff g).mp hdet

end Fixed

section Main

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem range_projLine_le_range_avgOp {E0 : Subgroup (SpecialLinearGroup (Fin n) K)}
    [Fintype E0] (hpK : (p : K) ≠ 0) {L : Subgroup ↥E0} (hL : L ∈ lines p E0) :
    LinearMap.range (projLine (planeRep E0) L) ≤ LinearMap.range (avgOp (planeRep E0) L) := by
  have h : projLine (planeRep E0) L =
      avgOp (planeRep E0) L * (1 - avgOp (planeRep E0) ⊤) := by
    unfold projLine
    rw [mul_sub, mul_one, avgOp_mul_top (planeRep E0) hpK (mem_lines.mp hL)]
  rw [h, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

omit [Finite K] in
theorem slAction_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W]
    [Module K W] (b : Basis ι K W) : Function.Injective (slAction b) := by
  intro A B h
  refine Subtype.ext ((Matrix.toLin b b).injective (LinearMap.ext fun x => ?_))
  exact LinearEquiv.congr_fun h x

omit [Finite K] in
theorem toLin'_apply_eq_slAction (A : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) v = slAction (Pi.basisFun K (Fin n)) A v := by
  rw [slAction_apply, Matrix.toLin_eq_toLin']

theorem goodBlock_of_mixing {x : Module.End K (Fin n → K)} {h : K[X]}
    (hh : h ∈ primaryFactors x) {d : ℕ} (hd2 : 2 ≤ d) (hdeg : d ≤ h.natDegree)
    (hmult : 2 ≤ finrank (AdjoinRoot h) (primaryComponent x h)) :
    GoodBlock (⟨h, hh⟩ : primaryFactors x) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  right
  refine ⟨hmult, ?_⟩
  change 3 < Nat.card (AdjoinRoot h)
  rw [natCard_adjoinRoot]
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  calc 3 < 2 ^ 2 := by norm_num
    _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq2 2
    _ ≤ Nat.card K ^ h.natDegree := Nat.pow_le_pow_right (by omega) (hd2.trans hdeg)

theorem eq_top_of_good_blocks_le (hp : p.Prime) (hp3 : 3 < p) (hpK : (p : K) ≠ 0)
    (hpcard : ¬ p ∣ Nat.card K) (hpq : ¬ p ∣ Nat.card K - 1)
    (E0 : Subgroup (SpecialLinearGroup (Fin n) K)) [IsElementaryAbelian p E0]
    (hE0 : Nat.card E0 = p ^ 2) (𝒢 : Subgroup (SpecialLinearGroup (Fin n) K))
    (hblocks : ∀ a ∈ E0, a ≠ 1 →
      ∀ (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
        (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))), GoodBlock h →
        blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL) :
    𝒢 = ⊤ := by
  have : Fintype ↥E0 := Fintype.ofFinite _
  have hP : IsPlane p E0 := isPlane E0 hp hE0
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd2 : 2 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) :=
    two_le_orderOf_natCast hp (by omega) hpcard hpq
  have hd3 : Nat.card K ≤ 3 → 3 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) := fun hq3 =>
    three_le_orderOf_of_le_three hp hp3 hq2 hq3 hd2
  have hidem := planeIdem_idem E0 hP hpK
  have horth : ∀ i j, i ≠ j → planeIdem E0 p i * planeIdem E0 p j = 0 := fun i j h =>
    planeIdem_orth E0 hP hpK h
  have hsum := planeIdem_sum E0 hP hpK
  set A : Finset (PlaneIdx E0 p) :=
    Finset.univ.filter (fun o => o ≠ none ∧ planeIdem E0 p o ≠ 0) with hA
  have hzA : (none : PlaneIdx E0 p) ∉ A := by
    simp [hA]
  have hAne : A.Nonempty := by
    obtain ⟨L, hL, hLne⟩ := exists_active E0 hP hpK
    exact ⟨some ⟨L, hL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Option.some_ne_none _, hLne⟩⟩
  have hinact : ∀ o, o ≠ none → o ∉ A → planeIdem E0 p o = 0 := by
    intro o hon hoA
    by_contra hne
    exact hoA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon, hne⟩)
  have hdim : ∀ o ∈ A, 2 ≤ finrank K (LinearMap.range (planeIdem E0 p o)) := by
    intro o ho
    obtain ⟨hon, hne⟩ := (Finset.mem_filter.mp ho).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hon
    exact hd2.trans (orderOf_le_finrank_range_projLine E0 hP hpK L.2 hne)
  set b₀ := Pi.basisFun K (Fin n) with hb₀
  set G : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)) := 𝒢.map (slAction b₀) with hG
  have hGdet : ∀ g ∈ G, LinearEquiv.det g = 1 := by
    rintro _ ⟨s, -, rfl⟩
    exact det_slAction b₀ s
  have hsupp : ∀ o ∈ A, suppGroup (planeIdem E0 p none + planeIdem E0 p o) ≤ G := by
    intro o ho
    obtain ⟨hon, hne⟩ := (Finset.mem_filter.mp ho).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hon
    have hLne : projLine (planeRep E0) L.1 ≠ 0 := hne
    have hsumL : planeIdem E0 p none + planeIdem E0 p (some L) = avgOp (planeRep E0) L.1 := by
      change projTop (planeRep E0) + projLine (planeRep E0) L.1 = _
      unfold projTop projLine
      abel
    rw [hsumL]
    intro g hg
    obtain ⟨A', hA'⟩ := exists_slAction_eq b₀ ((det_eq_one_iff g).mpr
      ((det_eq_one_iff g).mp hg.1)) 
    obtain ⟨b, hbL, hb1⟩ := exists_ne_one_mem E0 L.2 hP
    have hbp : act (planeRep E0) b ^ p = 1 := by
      rw [← act_pow, hP.pow b, act_one]
    have hsq : Squarefree (minpoly K (act (planeRep E0) b)) :=
      squarefree_minpoly_of_pow_eq_one hpK hbp
    have hXmem := X_sub_one_mem E0 hLne hbL
    have hgood : GoodBlock (⟨X - C 1, hXmem⟩ : primaryFactors (act (planeRep E0) b)) := by
      have : Fact (Irreducible (X - C 1 : K[X])) := ⟨irreducible_X_sub_C 1⟩
      have hmult : mult (act (planeRep E0) b) ⟨X - C 1, hXmem⟩ =
          finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) := by
        have h1 := finrank_primaryComponent (act (planeRep E0) b) (X - C 1)
        rw [natDegree_X_sub_C, one_mul] at h1
        have h2 : finrank K (primaryComponent (act (planeRep E0) b) (X - C 1)) =
            finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) := by
          rw [primaryComponent_X_sub_one E0 hP hpK L.2 hbL hb1]
        exact h1.symm.trans h2
      have hge : orderOf ((Nat.card K : ℕ) : ZMod p) ≤
          finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) :=
        (orderOf_le_finrank_range_projLine E0 hP hpK L.2 hLne).trans
          (Submodule.finrank_mono (range_projLine_le_range_avgOp hpK L.2))
      by_cases hq3 : Nat.card K ≤ 3
      · left
        rw [hmult]
        exact (hd3 hq3).trans hge
      · right
        refine ⟨by rw [hmult]; exact hd2.trans hge, ?_⟩
        change 3 < Nat.card (AdjoinRoot (X - C 1))
        rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
        omega
    have hAv : ∀ v, Matrix.toLin' (A' : Matrix (Fin n) (Fin n) K) v = g v := fun v => by
      rw [toLin'_apply_eq_slAction, hA']
    have hmem := fixedBlock_mem E0 hP hpK L.2 hLne hbL hb1 hsq hg hAv
    have hb1' : (b : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨s, hs𝒢, hs⟩ := hblocks b b.2 hb1' hsq ⟨X - C 1, hXmem⟩ hgood hmem
    have hsA : s = A' := SpecialLinearGroup.toGL_injective hs
    exact ⟨s, hs𝒢, hsA ▸ hA'⟩
  have hmix : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ β : Module.End K (Fin n → K),
      planeIdem E0 p i * β = β ∧ β * planeIdem E0 p j = β ∧ β ≠ 0 ∧
        ∃ u ∈ G, ∀ v, u v = v + β v := by
    intro i hi j hj hij
    obtain ⟨hion, hine⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjon, hjne⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hion
    obtain ⟨M, rfl⟩ := Option.ne_none_iff_exists'.mp hjon
    have hLne : projLine (planeRep E0) L.1 ≠ 0 := hine
    have hMne : projLine (planeRep E0) M.1 ≠ 0 := hjne
    have hLM : L.1 ≠ M.1 := fun h => hij (by rw [Subtype.ext h])
    have hML : M.1 ≠ L.1 := Ne.symm hLM
    obtain ⟨a, ha1, h, hh, hdeg, hLP, hMP⟩ :=
      exists_mixing_block E0 hP hpK L.2 M.2 hLM hLne hMne
    have hxpa : act (planeRep E0) a ^ p = 1 := by rw [← act_pow, hP.pow a, act_one]
    have hsqa := squarefree_minpoly_of_pow_eq_one hpK hxpa
    obtain ⟨β, hβ, hβ1, hβ2, hβ0, hββ, hkill, hdet, hmult⟩ := exists_mixing_unipotent hsqa hh
      (e := projLine (planeRep E0) M.1) (e' := projLine (planeRep E0) L.1)
      (commute_act_projLine E0 a M.1).symm (commute_act_projLine E0 a L.1).symm
      (projLine_mul_self (planeRep E0) hP hpK (mem_lines.mp M.2))
      (projLine_mul_self (planeRep E0) hP hpK (mem_lines.mp L.2))
      (projLine_mul_projLine_of_ne (planeRep E0) hP hpK (mem_lines.mp M.2) (mem_lines.mp L.2) hML)
      hMP hLP
    obtain ⟨g', hg'mem, hg'v⟩ := exists_mem_blockImage_one_add hsqa
      (a0 := SpecialLinearGroup.toGL (a : SpecialLinearGroup (Fin n) K)) rfl ⟨h, hh⟩ β hβ hββ
      hkill hdet
    have hgood := goodBlock_of_mixing hh hd2 hdeg hmult
    have ha1' : (a : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h' => ha1 (Subtype.ext h')
    obtain ⟨s, hs𝒢, hs⟩ := hblocks a a.2 ha1' hsqa ⟨h, hh⟩ hgood hg'mem
    refine ⟨β, hβ1, hβ2, hβ0, slAction b₀ s, ⟨s, hs𝒢, rfl⟩, fun v => ?_⟩
    have hsmat : (s : Matrix (Fin n) (Fin n) K) = (g' : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hs
    rw [← toLin'_apply_eq_slAction, hsmat]
    exact hg'v v
  have hmain := generation_of_blocks (planeIdem E0 p) hidem horth hsum none A hzA hAne hinact
    hdim G hGdet hsupp hmix
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨s', hs'𝒢, hs'⟩ := hmain (slAction b₀ s) (det_slAction b₀ s)
  have : s' = s := slAction_injective b₀ hs'
  exact this ▸ hs'𝒢

end Main

end CFSG.RankThree.PartOne.KCLinPlane
