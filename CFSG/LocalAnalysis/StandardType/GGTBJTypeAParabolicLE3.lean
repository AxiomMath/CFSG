module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeParabolic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem cI_mem_closure_singleton_eq {E : Type} [Group E] {g t : E}
    (hg : g * g = 1) (ht : t ∈ Subgroup.closure ({g} : Set E)) : t = 1 ∨ t = g := by
  refine Subgroup.closure_induction (p := fun t _ => t = 1 ∨ t = g) ?_ ?_ ?_ ?_ ht
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  · exact Or.inl rfl
  · intro x y hx hy ihx ihy
    rcases ihx with hx1 | hxg <;> rcases ihy with hy1 | hyg
    · exact Or.inl (by simp [hx1, hy1])
    · exact Or.inr (by simp [hx1, hyg])
    · exact Or.inr (by simp [hxg, hy1])
    · exact Or.inl (by rw [hxg, hyg]; exact hg)
  · intro x hx ih
    rcases ih with hx1 | hxg
    · exact Or.inl (by rw [hx1]; exact inv_one)
    · exact Or.inr (by rw [hxg]; exact inv_eq_of_mul_eq_one_right hg)

private theorem cI_refl_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hr : GGIsReflection p φ) : φ ≠ 1 := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Nonempty ↥Bs := ⟨(1 : ↥Bs)⟩
  rintro rfl
  obtain ⟨-, hc⟩ := hr
  simp only [MulAut.one_apply] at hc
  have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

private theorem cI_reflConjSimple_subsingleton {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {Λ : Type} [Nonempty Λ]
    (φ : Λ → MulAut ↥Bs) (hA : A = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hsub : Subsingleton Λ) :
    GGReflConjSimple p A φ := by
  let i₀ : Λ := Classical.arbitrary Λ
  intro t ht hr
  rw [hA] at ht
  have hrange : Set.range φ = {φ i₀} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg φ (hsub.allEq i i₀))
    · rintro rfl
      exact ⟨i₀, rfl⟩
  rw [hrange] at ht
  have hg : φ i₀ * φ i₀ = 1 := by
    have h := (hrefl i₀).1
    simpa [pow_two] using h
  have ht' : t = 1 ∨ t = φ i₀ := cI_mem_closure_singleton_eq hg ht
  rcases ht' with h | h
  · exact absurd h (cI_refl_ne_one hr)
  · exact ⟨1, Subgroup.one_mem _, i₀, by rw [h]; group⟩

private theorem cI_isElemAbelian {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : IsElemAbelian p Bs := by
  have hcomm : ∀ a b : Bs, a * b = b * a := by
    intro a b
    apply Additive.ofMul.injective
    apply ι.injective
    change ι (Additive.ofMul a + Additive.ofMul b) =
      ι (Additive.ofMul b + Additive.ofMul a)
    rw [map_add, map_add, add_comm]
  have hpow : ∀ b : Bs, b ^ p = 1 := by
    intro b
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_self, zero_smul, ofMul_one, map_zero]
  have h := isElemAbelian_range hcomm hpow Bs.subtype
  rwa [Subgroup.range_subtype] at h

private theorem cI_parabolicRestricted
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n c : ℕ} (hrc : 1 ≤ n - c)
    {M : CoxeterMatrix (Fin n)} {φ : Fin n → MulAut ↥Bs}
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range (φ ∘ Fin.castLE (by omega : n - c ≤ n))))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hBs : IsElemAbelian p Bs)
    {Jset : Set (Fin n)} [Fintype Jset] [DecidableEq Jset]
    (hJlt : ∀ j : Jset, j.val.val < n - c) (eJ : Jset ≃ Fin (n - c))
    (hcast : ∀ i : Fin (n - c), ((eJ.symm i : Jset) : Fin n) = Fin.castLE (by omega : n - c ≤ n) i)
    (hMJ_eq : parMatrix M Jset = (CoxeterMatrix.A (n - c)).reindex eJ.symm) :
    (∃ fJ : (parMatrix M Jset).Group ≃* ↥(ggAutomizer J Bs),
        ∀ j : Jset, (fJ ((parMatrix M Jset).simple j) : MulAut ↥Bs) = φ j) ∧
      (ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j)) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j) := by
  classical
  let MJ : CoxeterMatrix Jset := parMatrix M Jset
  let cs := M.toCoxeterSystem
  let gSub : MJ.Group →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp (parToGroup cs Jset)
  let g : MJ.Group →* MulAut ↥Bs := (Subgroup.subtype (ggAutomizer X Bs)).comp gSub
  have hg_simple : ∀ j : Jset, g (MJ.simple j) = φ j := by
    intro j
    change (f (parToGroup cs Jset (MJ.simple j)) : MulAut Bs) = _
    rw [parToGroup_simple]
    exact hf j
  have hg_inj : Function.Injective g := by
    intro x y h
    exact f.injective.comp (parToGroup_injective cs Jset) (Subtype.ext h)
  have hg_mem : ∀ x : MJ.Group, g x ∈ ggAutomizer J Bs := by
    have hle : Subgroup.closure (Set.range (MJ.simple)) ≤
        Subgroup.comap g (ggAutomizer J Bs) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      change g (MJ.simple j) ∈ ggAutomizer J Bs
      rw [hg_simple, hJ]
      have hj : j.val.val < n - c := hJlt j
      let i : Fin (n - c) := ⟨j.val.val, hj⟩
      have hi : Fin.castLE (by omega : n - c ≤ n) i = j.val := by ext; rfl
      rw [← hi]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    intro x
    have hx : x ∈ Subgroup.closure (Set.range (MJ.simple)) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple,
        (MJ.toCoxeterSystem).subgroup_closure_range_simple]
      exact Subgroup.mem_top x
    exact hle hx
  let g' : MJ.Group →* ↥(ggAutomizer J Bs) :=
    { toFun := fun x => ⟨g x, hg_mem x⟩
      map_one' := by ext; simp [g]
      map_mul' := by intro x y; ext; simp [g] }
  have hg'_inj : Function.Injective g' := by
    intro x y hxy
    apply hg_inj
    exact congrArg (fun z : ggAutomizer J Bs => (z : MulAut Bs)) hxy
  have hg'_surj : Function.Surjective g' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ Subgroup.closure
        (Set.range (φ ∘ Fin.castLE (by omega : n - c ≤ n))) := by
      rw [← hJ]
      exact y.property
    have h : ∃ a : MJ.Group, (g' a : MulAut ↥Bs) = (y : MulAut ↥Bs) := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        refine ⟨MJ.simple (eJ.symm i), ?_⟩
        change g (MJ.simple (eJ.symm i)) = φ (Fin.castLE _ i)
        rw [hg_simple]
        exact congrArg φ (hcast i)
      · exact ⟨1, by change g 1 = 1; exact g.map_one⟩
      · intro x z hx hz ihx ihz
        rcases ihx with ⟨a, ha⟩
        rcases ihz with ⟨b, hb'⟩
        refine ⟨a * b, ?_⟩
        change g (a * b) = x * z
        rw [map_mul]
        exact congrArg₂ (· * ·) ha hb'
      · intro x hx ih
        rcases ih with ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        change g a⁻¹ = x⁻¹
        rw [map_inv]
        exact congrArg Inv.inv ha
    rcases h with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  let fJ : MJ.Group ≃* ↥(ggAutomizer J Bs) :=
    MulEquiv.ofBijective g' ⟨hg'_inj, hg'_surj⟩
  have hfJ : ∀ j : Jset, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j := by
    intro j
    exact hg_simple j
  have hALJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j) := by
    rw [hJ]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨eJ.symm i, ?_⟩
      exact congrArg φ (hcast i)
    · rintro ⟨j, rfl⟩
      refine ⟨eJ j, ?_⟩
      have h := hcast (eJ j)
      rw [Equiv.symm_apply_apply] at h
      exact congrArg φ h.symm
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j) := by
    by_cases hsmall : n - c = 1
    · haveI : Nonempty Jset := ⟨eJ.symm ⟨0, by omega⟩⟩
      have hsub : Subsingleton Jset := ⟨fun a b => eJ.injective (Fin.ext (by
        have ha := (eJ a).isLt
        have hb := (eJ b).isLt
        omega))⟩
      exact cI_reflConjSimple_subsingleton (fun j : Jset => φ j) hALJ
        (fun j => hrefl j.val) hsub
    · have h2 : 2 ≤ n - c := by omega
      intro s hs hr
      exact ggTW_refl_conj_of_typeA hp h2 hBs eJ.symm hMJ_eq
        (ggAutomizer J Bs) fJ (fun j : Jset => φ j) hfJ (fun j => hrefl j.val) s hs hr
  exact ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩

private theorem cI_sideDatum_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n : ℕ} (hrc : 1 ≤ n - 1)
    {M : CoxeterMatrix (Fin n)} (hM : M = CoxeterMatrix.A n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.A n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range (φ ∘ Fin.castLE (by omega : n - 1 ≤ n)))) :
    GGResSideDatum p Bs X J := by
  classical
  let b : Fin n := ⟨n - 1, by omega⟩
  let Jset : Set (Fin n) := {j | j ≠ b}
  have hJlt : ∀ j : Jset, j.val.val < n - 1 := by
    intro j
    have hj : j.val.val ≠ n - 1 := by
      intro hh
      exact j.2 (Fin.ext hh)
    omega
  let eJ : Jset ≃ Fin (n - 1) :=
    { toFun := fun j => ⟨j.val.val, hJlt j⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, by
        intro hh
        have : i.val = n - 1 := by simpa [b] using congrArg Fin.val hh
        omega⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  let MJ : CoxeterMatrix Jset := parMatrix M Jset
  have hMJ_eq : MJ = (CoxeterMatrix.A (n - 1)).reindex eJ.symm := by
    ext j j'
    change M.M j.val j'.val = ((CoxeterMatrix.A (n - 1)).reindex eJ.symm).M j j'
    rw [hM]
    simp [CoxeterMatrix.reindex_apply, CoxeterMatrix.A, eJ, Fin.ext_iff]
  have hWM : GGIsWeylMatrix M := by rw [hM]; exact ggResII_isWeyl_A (by omega)
  have hMC : GGIntCartan M C := by rw [hM, hC]; exact ggIntCartan_A n
  have hWMJ : GGIsWeylMatrix MJ := by
    rw [hMJ_eq]
    exact l05nBL_weyl_reindex (ggResII_isWeyl_A (by omega : 1 ≤ n - 1)) eJ.symm
  have hMJ_sub : ∀ j j' : Jset, MJ.M j j' = M.M j j' := fun _ _ => rfl
  have hBs : IsElemAbelian p Bs := cI_isElemAbelian ι
  obtain ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩ :=
    cI_parabolicRestricted (p := p) (X := X) (J := J) (f := f) (Jset := Jset)
      hp hrc hf hJ hrefl hBs hJlt eJ (fun i => Fin.ext rfl) hMJ_eq
  exact ⟨Fin n, inferInstance, inferInstance, b, M, C, MJ, V, inferInstance, inferInstance,
    ι, φ, h, α, hWM, hMC, hWMJ, hMJ_sub, hlin, hrefl, hpair, ⟨f, hf⟩, hclos,
    ⟨fJ, hfJ⟩, hALJ, hconjJ⟩

private theorem cI_leviSideDatumLE3 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n c : ℕ} (hc : 1 ≤ c) (hc2 : 2 ≤ c) (hc3 : c ≤ 3)
    (hrc : 1 ≤ n - c) (hcr : c ≤ n)
    {M : CoxeterMatrix (Fin n)} (hM : M = CoxeterMatrix.A n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.A n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range (φ ∘ Fin.castLE (by omega : n - c ≤ n)))) :
    GGResLeviSideDatumLE3 p Bs X J := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => n - c ≤ j.val)
  let Jset : Set (Fin n) := {j | j ∉ S}
  have hJlt : ∀ j : Jset, j.val.val < n - c := by
    intro j
    have hj : ¬ (n - c ≤ j.val.val) := by
      intro hle
      exact j.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
    omega
  let eJ : Jset ≃ Fin (n - c) :=
    { toFun := fun j => ⟨j.val.val, hJlt j⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, by
        intro hmem
        have hle : n - c ≤ i.val := (Finset.mem_filter.mp hmem).2
        omega⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  let MJ : CoxeterMatrix Jset := parMatrix M Jset
  have hMJ_eq : MJ = (CoxeterMatrix.A (n - c)).reindex eJ.symm := by
    ext j j'
    change M.M j.val j'.val = ((CoxeterMatrix.A (n - c)).reindex eJ.symm).M j j'
    rw [hM]
    simp [CoxeterMatrix.reindex_apply, CoxeterMatrix.A, eJ, Fin.ext_iff]
  let ef : {j : Fin n // n - c ≤ j.val} ≃ Fin c :=
    { toFun := fun j => ⟨j.val.val - (n - c), by omega⟩
      invFun := fun i => ⟨⟨n - c + i.val, by omega⟩, by show n - c ≤ n - c + i.val; omega⟩
      left_inv := fun j => by
        apply Subtype.ext
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      right_inv := fun i => by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega }
  have hScard : S.card = c := by
    have h1 : S.card = Fintype.card {j : Fin n // n - c ≤ j.val} :=
      (Fintype.card_subtype (p := fun j : Fin n => n - c ≤ j.val)).symm
    rw [h1]
    exact (Fintype.card_congr ef).trans (Fintype.card_fin c)
  have hWM : GGIsWeylMatrix M := by rw [hM]; exact ggResII_isWeyl_A (by omega)
  have hMC : GGIntCartan M C := by rw [hM, hC]; exact ggIntCartan_A n
  have hWMJ : GGIsWeylMatrix MJ := by
    rw [hMJ_eq]
    exact l05nBL_weyl_reindex (ggResII_isWeyl_A hrc) eJ.symm
  have hMJ_sub : ∀ j j' : Jset, MJ.M j j' = M.M j j' := fun _ _ => rfl
  have hS1 : 2 ≤ S.card := by omega
  have hS2 : S.card ≤ 3 := by omega
  have hBs : IsElemAbelian p Bs := cI_isElemAbelian ι
  obtain ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩ :=
    cI_parabolicRestricted (p := p) (X := X) (J := J) (f := f) (Jset := Jset)
      hp hrc hf hJ hrefl hBs hJlt eJ (fun i => Fin.ext rfl) hMJ_eq
  exact ⟨Fin n, inferInstance, inferInstance, S, M, C, MJ, V, inferInstance, inferInstance,
    ι, φ, h, α, hS1, hS2, hWM, hMC, hWMJ, hMJ_sub, hlin, hrefl, hpair, ⟨f, hf⟩, hclos,
    ⟨fJ, hfJ⟩, hALJ, hconjJ⟩

theorem ggTBJTypeAParabolicLE3 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n c : ℕ} (hc : 1 ≤ c) (hc3 : c ≤ 3) (hrc : 1 ≤ n - c) (hcr : c ≤ n)
    {M : CoxeterMatrix (Fin n)} (hM : M = CoxeterMatrix.A n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.A n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range (φ ∘ Fin.castLE (by omega : n - c ≤ n)))) :
    (c = 1 → GGResSideDatum p Bs X J) ∧ (2 ≤ c → GGResLeviSideDatumLE3 p Bs X J) := by
  constructor
  · intro hc1
    subst hc1
    exact cI_sideDatum_one (p := p) (X := X) (J := J) (f := f)
      hp hrc hM hC hlin hrefl hpair hf hclos hJ
  · intro hc2
    exact cI_leviSideDatumLE3 (p := p) (X := X) (J := J) (f := f)
      hp hc hc2 hc3 hrc hcr hM hC hlin hrefl hpair hf hclos hJ

end CFSG.StandardType

end
