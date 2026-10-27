module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def ggResIIIdx {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) : Fin (n + 1) → Option Λ :=
  Fin.lastCases none fun i => some (e i)

@[simp] theorem ggResIIIdx_last {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) :
    ggResIIIdx e (Fin.last n) = none := by
  simp [ggResIIIdx]

@[simp] theorem ggResIIIdx_castSucc {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) (i : Fin n) :
    ggResIIIdx e i.castSucc = some (e i) := by
  simp [ggResIIIdx]

theorem ggResIIIdx_surjective {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) :
    Function.Surjective (ggResIIIdx e) := by
  intro o
  cases o with
  | none => exact ⟨Fin.last n, by simp⟩
  | some l => exact ⟨(e.symm l).castSucc, by simp⟩

theorem ggResII_transport {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} [Module.Finite (ZMod p) V]
    {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    {x y : V} (hp2 : p ≠ 2) (hg : ∀ o w, g o w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hLI : LinearIndependent (ZMod p) (fun i : Λ => h (some i)))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hxL : ∀ i : Λ, α (some i) x = 0)
    (hfix : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hxa : α none x ≠ 0) (hyK : ∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) y = 0)
    (hyx : y ∉ Submodule.span (ZMod p) {x}) {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j) (hdiag : ∀ i, C i i = 2)
    {ib ic : Fin n} (hib : e ib = b) (hbc : ib ≠ ic)
    (hrow : ∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then -1 else 0)
    (hcol : ∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then -1 else 0)
    (hKaa : CK none none = 2) (hok : GGResIIShapeOK C ib ic) :
    (∃ t ∈ Subgroup.closure (Set.range g),
        Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
      (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧
        α (some j') (ψ (h (some j))) * α (some j) (ψ⁻¹ (h (some j'))) ∉
          ({0, 1, 2, 3, 4} : Set (ZMod p))) ∨
      ZS.LinWeyl p (Subgroup.closure (Set.range g)) := by
  classical
  set ι := ggResIIIdx e with hιdef
  set g' := g ∘ ι
  set h' := h ∘ ι
  set α' := α ∘ ι
  set x' := (α none x)⁻¹ • x with hx'
  set u := α none (h (some b))
  set v := α (some b) (h none)
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  have haL : ∀ j : Fin n, α none (h (some (e j))) =
      if j.val = ic.val then ((-1 : ℤ) : ZMod p) else if j.val = ib.val then u
        else ((0 : ℤ) : ZMod p) := by
    intro j
    by_cases hj : j = ib
    · rw [hj]
      have : ib.val ≠ ic.val := fun h => hbc (Fin.ext h)
      simp [this, hib, u]
    · have := hK none (some ⟨e j, hne j hj⟩)
      simp only [Option.map_none, Option.map_some] at this
      rw [this, hrow j (hne j hj)]
      have hj' : j.val ≠ ib.val := fun h => hj (Fin.ext h)
      by_cases hjc : j = ic
      · subst hjc
        simp
      · have : j.val ≠ ic.val := fun h => hjc (Fin.ext h)
        simp [hjc, hj', this]
  have hLa : ∀ j : Fin n, α (some (e j)) (h none) =
      if j.val = ic.val then ((-1 : ℤ) : ZMod p) else if j.val = ib.val then v
        else ((0 : ℤ) : ZMod p) := by
    intro j
    by_cases hj : j = ib
    · rw [hj]
      have : ib.val ≠ ic.val := fun h => hbc (Fin.ext h)
      simp [this, hib, v]
    · have := hK (some ⟨e j, hne j hj⟩) none
      simp only [Option.map_none, Option.map_some] at this
      rw [this, hcol j (hne j hj)]
      have hj' : j.val ≠ ib.val := fun h => hj (Fin.ext h)
      by_cases hjc : j = ic
      · subst hjc
        simp
      · have : j.val ≠ ic.val := fun h => hjc (Fin.ext h)
        simp [hjc, hj', this]
  have haa : α none (h none) = 2 := by
    have := hK none none
    simp only [Option.map_none] at this
    rw [this, hKaa]
    norm_num
  have hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h' x' α' := by
    constructor
    · intro k l
      simp only [ggStdTable, Vector.get_ofFn, RingHom.id_apply]
      induction k using Fin.lastCases with
      | last =>
        induction l using Fin.lastCases with
        | last => simp [h', α', ι, ggStdEntry_aa, haa]
        | cast j =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_last, ggResIIIdx_castSucc,
            ggStdEntry_aL, haL]
      | cast i =>
        induction l using Fin.lastCases with
        | last =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_last, ggResIIIdx_castSucc,
            ggStdEntry_La, hLa]
        | cast j =>
          simp only [h', α', ι, Function.comp_apply, ggResIIIdx_castSucc, ggStdEntry_LL, hL, hCe]
    · intro k
      simp only [ggStdTable, Vector.get_ofFn, RingHom.id_apply]
      induction k using Fin.lastCases with
      | last =>
        simp only [α', ι, Function.comp_apply, ggResIIIdx_last, ggStdEntry_ax, x', map_smul,
          smul_eq_mul, Int.cast_one]
        exact inv_mul_cancel₀ hxa
      | cast i =>
        simp only [α', ι, Function.comp_apply, ggResIIIdx_castSucc, ggStdEntry_Lx, x', map_smul,
          smul_eq_mul, hxL, mul_zero, Int.cast_zero]
  have hg' : ∀ k w, g' k w = w - α' k w • h' k := fun k w => hg _ w
  have h2' : ∀ k, α' k (h' k) = 2 := by
    intro k
    induction k using Fin.lastCases with
    | last => simpa [α', h', ι] using haa
    | cast i => simp [α', h', ι, hL, hCe, hdiag]
  have hsep' : ∀ w : V, (∀ k, α' k w = 0) → w = 0 := by
    intro w hw
    have hwL : ∀ i : Λ, α (some i) w = 0 := fun i => by
      simpa [α', ι] using hw (e.symm i).castSucc
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hfix w hwL)
    have hwa : α none (c • x) = 0 := by simpa [α', ι] using hw (Fin.last n)
    rw [map_smul, smul_eq_mul] at hwa
    rcases mul_eq_zero.mp hwa with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 hxa
  have hLI' : LinearIndependent (ZMod p) (fun i : Fin n => h' i.castSucc) := by
    have := hLI.comp e e.injective
    convert this using 1
    funext i
    simp [h', ι]
  have hspan : Submodule.span (ZMod p) (Set.range fun i : Fin n => h' i.castSucc) =
      Submodule.span (ZMod p) (Set.range fun i : Λ => h (some i)) := by
    congr 1
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [h', ι]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [h', ι]⟩
  have hdep' : h' (Fin.last n) ∈
      Submodule.span (ZMod p) (Set.range fun i : Fin n => h' i.castSucc) := by
    rw [hspan]
    by_contra hc
    apply hdep
    rw [linearIndependent_option]
    refine ⟨hLI, fun hc' => hc ?_⟩
    simpa [h', ι, Function.comp_def] using hc'
  have hx'span : Submodule.span (ZMod p) {x'} = Submodule.span (ZMod p) {x} :=
    Submodule.span_singleton_smul_eq (Ne.isUnit (inv_ne_zero hxa)) x
  have hfix' : ∀ w : V, (∀ i : Fin n, α' i.castSucc w = 0) →
      w ∈ Submodule.span (ZMod p) {x'} := by
    intro w hw
    rw [hx'span]
    exact hfix w fun i => by simpa [α', ι] using hw (e.symm i)
  have hyK' : ∀ k : Fin (n + 1), k ≠ ib.castSucc → α' k y = 0 := by
    intro k hk
    induction k using Fin.lastCases with
    | last => simpa [α', ι] using hyK none
    | cast i =>
      have hi : i ≠ ib := fun h => hk (by rw [h])
      simpa [α', ι] using hyK (some ⟨e i, hne i hi⟩)
  have hyx' : y ∉ Submodule.span (ZMod p) {x'} := by rwa [hx'span]
  have hdimA : ((C.det : ℤ) : ZMod p) ≠ 0 → Module.finrank (ZMod p) V = n + 1 := by
    intro hdet
    apply le_antisymm
    ·
      let Φ : V →ₗ[ZMod p] (Fin (n + 1) → ZMod p) := LinearMap.pi fun k => α' k
      have hΦ : Function.Injective Φ := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro w hw
        exact hsep' w fun k => congrFun hw k
      have := LinearMap.finrank_le_finrank_of_injective hΦ
      rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    ·
      have hxnot : x' ∉ Submodule.span (ZMod p) (Set.range fun i : Fin n => h' i.castSucc) := by
        intro hx
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hx
        have hmul : Matrix.mulVec (C.map (Int.cast : ℤ → ZMod p)) c = 0 := by
          funext j
          have := congrArg (α' j.castSucc) hc
          rw [map_sum] at this
          simp only [map_smul, smul_eq_mul, α', h', ι, Function.comp_apply, ggResIIIdx_castSucc,
            hL, hCe] at this
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
          rw [show (α (some (e j))) x' = 0 by simp [x', hxL]] at this
          rw [← this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        have hdet' : (C.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
          have h1 := RingHom.map_det (Int.castRingHom (ZMod p)) C
          rw [RingHom.mapMatrix_apply] at h1
          rw [show (C.map (Int.cast : ℤ → ZMod p)) = C.map (Int.castRingHom (ZMod p)) from rfl,
            ← h1]
          simpa using hdet
        have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet' hmul
        have : x' = 0 := by rw [← hc, hc0]; simp
        have h1 : α none x' = 1 := by simp [x', inv_mul_cancel₀ hxa]
        rw [this, map_zero] at h1
        exact zero_ne_one h1
      have hind := hLI'.finSnoc hxnot
      have := hind.fintype_card_le_finrank
      rwa [Fintype.card_fin] at this
  have hconcl := hok p V g' h' α' x' y u v hp2 hg' h2' hT hsep' hLI' hfix' hdep' hyK' hyx' hdimA
  have hrange : Set.range g' = Set.range g := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ι k, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨k, hk⟩ := ggResIIIdx_surjective e o
      exact ⟨k, by simp [g', ι, hk]⟩
  rcases hconcl with htv | ⟨h5, ψ, hψ, j, j', hj, hj', hP⟩ | hW
  · left
    rwa [hrange] at htv
  · right; left
    refine ⟨h5, ψ, by rwa [hrange] at hψ, e j, e j', hne j hj, hne j' hj', ?_⟩
    simpa [α', h', ι] using hP
  · right; right
    rwa [hrange] at hW

end CFSG.StandardType
