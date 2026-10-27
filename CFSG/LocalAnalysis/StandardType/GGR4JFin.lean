module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JFinDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem r4f_reflect_involutive {G : Type} [Group G] [Fact (Nat.Prime 3)]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod 3) V} (hD : GGExtDatum (p := 3) ι X φ' h' α') (o : N) (w : V) :
    ggLin (p := 3) ι (φ' o) (ggLin (p := 3) ι (φ' o) w) = w := by
  rw [hD.lin o, hD.lin o]
  have hα : α' o (w - α' o w • h' o) = -(α' o w) := by
    rw [map_sub, map_smul, smul_eq_mul, hD.pair o o, hD.diag o]
    generalize h : α' o w = a
    clear h
    fin_cases a <;> norm_num <;> rfl
  rw [hα]
  have h1 : (-(α' o w)) • h' o = -((α' o w) • h' o) := neg_smul (α' o w) (h' o)
  rw [h1, sub_neg_eq_add, sub_add_cancel]

private theorem r4f_inv_reflection {G : Type} [Group G] [Fact (Nat.Prime 3)]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod 3) V} (hD : GGExtDatum (p := 3) ι X φ' h' α') (o : N) :
    (ggLin (p := 3) ι (φ' o))⁻¹ = ggLin (p := 3) ι (φ' o) := by
  have hmul : ggLin (p := 3) ι (φ' o) * ggLin (p := 3) ι (φ' o) = 1 := by
    refine LinearEquiv.ext (fun w => ?_)
    rw [LinearEquiv.mul_apply, r4f_reflect_involutive hD o w]
    rfl
  exact inv_eq_of_mul_eq_one_right hmul

private theorem r4f_inv_set_eq_of_inv_eq_self {G : Type} [Group G] (S : Set G)
    (h : ∀ s ∈ S, s⁻¹ = s) : S⁻¹ = S := by
  ext x
  rw [Set.mem_inv]
  constructor
  · intro hx
    have hx' : x = x⁻¹ := by simpa using h x⁻¹ hx
    rwa [hx']
  · intro hx
    have hx' : x⁻¹ = x := by simpa using h x hx
    rwa [hx']

private theorem r4f_closure_eq_of_inv_eq_self {G : Type} [Group G] (S : Set G)
    (hS : S⁻¹ = S) : (Subgroup.closure S : Set G) = Submonoid.closure S := by
  have h := Subgroup.closure_toSubmonoid S
  rw [hS, Set.union_self] at h
  have h' := congrArg (fun M : Submonoid G => (M : Set G)) h
  simpa [Subgroup.coe_toSubmonoid] using h'

private theorem r4f_case {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum (p := 3) ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤)
    (e : Fin 4 ≃ Λ) (ori cell : Bool)
    (hC : ∀ i j : Fin 4, C (e i) (e j) = R4J.caseC ori i j)
    (hb : b = e (R4J.caseB cell)) (hc : c = e (R4J.caseCN cell)) :
    Subgroup.closure (Set.range fun i : Λ => φ' (some i)) ⊓
        Subgroup.closure ((fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none}) =
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j)) ∧
    Nat.card (Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j))) = 48 := by
  classical
  let f : Option (Fin 4) ≃ Option Λ := e.optionCongr
  let X : Matrix R4J.N5 R4J.N5 ℤ := R4J.caseX ori cell
  let SL : Set (MulAut ↥Bs) := Set.range fun i : Λ => φ' (some i)
  let SK : Set (MulAut ↥Bs) := (fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none}
  let SJ : Set (MulAut ↥Bs) := Set.range fun j : {j : Λ // j ≠ b} => φ' (some j)
  let T_L : Set (Matrix R4J.N5 R4J.N5 (ZMod 3)) :=
    Set.range fun i : Fin 4 => R4J.reflM X (some i)
  let T_J : Set (Matrix R4J.N5 R4J.N5 (ZMod 3)) :=
    Set.range fun j : {j : Fin 4 // j ≠ R4J.caseB cell} => R4J.reflM X (some j.1)
  change Subgroup.closure SL ⊓ Subgroup.closure SK = Subgroup.closure SJ ∧
    Nat.card (Subgroup.closure SJ) = 48
  have hX : ∀ o o' : R4J.N5, ggAttachCartan C c (f o) (f o') = X o o' := by
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none => simp [X, R4J.caseX, f]
      | some j =>
        have h1 : ggAttachCartan C c (f none) (f (some j)) = if e j = c then -1 else 0 := by
          simp [f]
        have h2 : X none (some j) = if j = R4J.caseCN cell then -1 else 0 := by
          simp [X, R4J.caseX]
        rw [h1, h2, hc]
        by_cases h : j = R4J.caseCN cell
        · subst h; simp
        · have h' : e j ≠ e (R4J.caseCN cell) := fun he => h (e.injective he)
          simp [h, h']
    | some i =>
      cases o' with
      | none =>
        have h1 : ggAttachCartan C c (f (some i)) (f none) = if e i = c then -1 else 0 := by
          simp [f]
        have h2 : X (some i) none = if i = R4J.caseCN cell then -1 else 0 := by
          simp [X, R4J.caseX]
        rw [h1, h2, hc]
        by_cases h : i = R4J.caseCN cell
        · subst h; simp
        · have h' : e i ≠ e (R4J.caseCN cell) := fun he => h (e.injective he)
          simp [h, h']
      | some j =>
        have h1 : ggAttachCartan C c (f (some i)) (f (some j)) = C (e i) (e j) := by
          simp [f]
        have h2 : X (some i) (some j) = R4J.caseC ori i j := by
          simp [X, R4J.caseX]
        rw [h1, h2]
        exact hC i j
  let bV : Module.Basis R4J.N5 (ZMod 3) V :=
    Module.Basis.mk (v := fun o => h' (f o)) (hD.indep.comp f f.injective) (by
      change ⊤ ≤ Submodule.span (ZMod 3) (Set.range (h' ∘ f))
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, hspan])
  have hbV : ∀ j : R4J.N5, bV j = h' (f j) := by
    intro j
    simp only [bV, Module.Basis.coe_mk]
  let Θ : MulAut ↥Bs →* Matrix R4J.N5 R4J.N5 (ZMod 3) :=
  { toFun := fun φ => LinearMap.toMatrix bV bV (ggLin (p := 3) ι φ)
    map_one' := by simp [map_one]
    map_mul' := by
      intro φ ψ
      rw [map_mul]
      exact LinearMap.toMatrix_mul bV (ggLin (p := 3) ι φ) (ggLin (p := 3) ι ψ) }
  have hgen : ∀ o : R4J.N5, Θ (φ' (f o)) = R4J.reflM X o := by
    intro o
    change LinearMap.toMatrix bV bV (ggLin (p := 3) ι (φ' (f o))) = R4J.reflM X o
    ext i j
    rw [LinearMap.toMatrix_apply]
    rw [hbV j]
    change (bV.repr (ggLin (p := 3) ι (φ' (f o)) (h' (f j)))) i = R4J.reflM X o i j
    rw [hD.lin (f o), map_sub, map_smul]
    have hsub : (bV.repr (h' (f j)) - α' (f o) (h' (f j)) • bV.repr (h' (f o))) i
        = (bV.repr (h' (f j))) i - (α' (f o) (h' (f j))) * (bV.repr (h' (f o))) i := by
      calc (bV.repr (h' (f j)) - α' (f o) (h' (f j)) • bV.repr (h' (f o))) i
          = (bV.repr (h' (f j))) i - (α' (f o) (h' (f j)) • bV.repr (h' (f o))) i :=
            Finsupp.sub_apply _ _ _
        _ = (bV.repr (h' (f j))) i - (α' (f o) (h' (f j))) *
              (bV.repr (h' (f o))) i := by
              rw [Finsupp.smul_apply, smul_eq_mul]
    rw [hsub]
    have hj : (bV.repr (h' (f j))) i = if i = j then 1 else 0 := by
      rw [← congrArg bV.repr (hbV j), Module.Basis.repr_self_apply]
      by_cases h : j = i
      · subst h; simp
      · have h' : i ≠ j := fun hij => h hij.symm
        simp [h, h']
    have ho : (bV.repr (h' (f o))) i = if i = o then 1 else 0 := by
      rw [← congrArg bV.repr (hbV o), Module.Basis.repr_self_apply]
      by_cases h : o = i
      · subst h; simp
      · have h' : i ≠ o := fun hio => h hio.symm
        simp [h, h']
    rw [hj, ho, hD.pair (f o) (f j), hX o j]
    simp only [R4J.reflM, Matrix.of_apply]
    split_ifs <;> ring
  have hφ_inv : ∀ o : Option Λ, (φ' o)⁻¹ = φ' o := by
    intro o
    apply ggLin_injective (p := 3) ι
    rw [map_inv]
    exact r4f_inv_reflection hD o
  have hSL_inv : SL⁻¹ = SL :=
    r4f_inv_set_eq_of_inv_eq_self SL (by rintro x ⟨i, rfl⟩; exact hφ_inv (some i))
  have hSK_inv : SK⁻¹ = SK := by
    apply r4f_inv_set_eq_of_inv_eq_self
    rintro x hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := hx
      exact hφ_inv (some i)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hφ_inv none
  have hSJ_inv : SJ⁻¹ = SJ :=
    r4f_inv_set_eq_of_inv_eq_self SJ (by rintro x ⟨j, rfl⟩; exact hφ_inv (some j.1))
  obtain ⟨y, hy, hstab, hcard⟩ := R4J.r4j_fin_case ori cell
  have hSL_sub : Θ '' SL ⊆ Submonoid.closure T_L := by
    rintro M ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    have hx' : Θ (φ' (some i)) = R4J.reflM X (some (e.symm i)) := by
      simpa [f] using hgen (some (e.symm i))
    rw [hx']
    exact Submonoid.subset_closure ⟨e.symm i, rfl⟩
  have hSK_fix : ∀ M ∈ Θ '' SK, M.mulVec y = y := by
    rintro M ⟨x, hx, rfl⟩
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := hx
      have hx' : Θ (φ' (some i)) = R4J.reflM X (some (e.symm i)) := by
        simpa [f] using hgen (some (e.symm i))
      rw [hx']
      apply hy
      intro h
      exact hi (by
        have h2 : e (e.symm i) = e (R4J.caseB cell) := congrArg e (Option.some.inj h)
        rwa [Equiv.apply_symm_apply, ← hb] at h2)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hx' : Θ (φ' none) = R4J.reflM X none := by simpa [f] using hgen none
      rw [hx']
      exact hy none (by simp)
  have hSJ_sub : T_J ⊆ Θ '' SJ := by
    rintro M ⟨j, rfl⟩
    refine ⟨φ' (some (e j.1)), ⟨⟨e j.1, ?_⟩, rfl⟩, ?_⟩
    · intro h
      exact j.2 (e.injective (h.trans hb))
    · simpa [f] using hgen (some j.1)
  have hSJ_image : Θ '' SJ = T_J := by
    rw [Set.Subset.antisymm_iff]
    refine ⟨?_, hSJ_sub⟩
    rintro M ⟨x, ⟨j, rfl⟩, rfl⟩
    refine ⟨⟨e.symm j.1, ?_⟩, ?_⟩
    · intro h
      exact j.2 (by
        calc j.1 = e (e.symm j.1) := (Equiv.apply_symm_apply e j.1).symm
          _ = e (R4J.caseB cell) := congrArg e h
          _ = b := hb.symm)
    · simpa [f] using (hgen (some (e.symm j.1))).symm
  have hΘ_inj : Function.Injective Θ := by
    intro φ ψ h
    have h2 : (ggLin (p := 3) ι φ : V →ₗ[ZMod 3] V) = (ggLin (p := 3) ι ψ : V →ₗ[ZMod 3] V) :=
      (LinearMap.toMatrix bV bV).injective h
    exact ggLin_injective (p := 3) ι
      (LinearEquiv.ext fun w => congrArg (fun f : V →ₗ[ZMod 3] V => f w) h2)
  have hle : Subgroup.closure SJ ≤ Subgroup.closure SL ⊓ Subgroup.closure SK := by
    apply le_inf
    · apply Subgroup.closure_mono
      rintro x ⟨j, rfl⟩
      exact ⟨j.1, rfl⟩
    · apply Subgroup.closure_mono
      rintro x ⟨j, rfl⟩
      rw [Set.mem_union]
      left
      exact ⟨j.1, j.2, rfl⟩
  have hge : Subgroup.closure SL ⊓ Subgroup.closure SK ≤ Subgroup.closure SJ := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgK⟩ := hg
    have hgL' : g ∈ Submonoid.closure SL :=
      (le_of_eq (r4f_closure_eq_of_inv_eq_self SL hSL_inv)) hgL
    have hmemL : Θ g ∈ Submonoid.closure T_L := by
      have hmap := MonoidHom.map_mclosure Θ SL
      have hmem : Θ g ∈ Submonoid.map Θ (Submonoid.closure SL) := ⟨g, hgL', rfl⟩
      rw [hmap] at hmem
      exact Submonoid.closure_le.mpr hSL_sub hmem
    have hgK' : g ∈ Submonoid.closure SK :=
      (le_of_eq (r4f_closure_eq_of_inv_eq_self SK hSK_inv)) hgK
    have hfixSub : Submonoid.closure (Θ '' SK) ≤
        { carrier := {M : Matrix R4J.N5 R4J.N5 (ZMod 3) | M.mulVec y = y}
          one_mem' := Matrix.one_mulVec y
          mul_mem' := by
            intro a b ha hb
            show (a * b).mulVec y = y
            rw [← Matrix.mulVec_mulVec, show b.mulVec y = y from hb,
              show a.mulVec y = y from ha] } := by
      apply Submonoid.closure_le.mpr
      rintro M hM
      exact hSK_fix M hM
    have hfix : (Θ g).mulVec y = y := by
      have hmap := MonoidHom.map_mclosure Θ SK
      have hmem : Θ g ∈ Submonoid.map Θ (Submonoid.closure SK) := ⟨g, hgK', rfl⟩
      rw [hmap] at hmem
      exact hfixSub hmem
    have hstabg : Θ g ∈ Submonoid.closure T_J := hstab (Θ g) hmemL hfix
    have hsub : Submonoid.closure T_J ≤ Submonoid.map Θ (Subgroup.closure SJ).toSubmonoid := by
      apply Submonoid.closure_le.mpr
      rintro M hM
      obtain ⟨j, rfl⟩ := hM
      refine ⟨φ' (some (e j.1)), Subgroup.subset_closure ⟨⟨e j.1, ?_⟩, rfl⟩, ?_⟩
      · intro h
        exact j.2 (e.injective (h.trans hb))
      · simpa [f] using hgen (some j.1)
    obtain ⟨x, hx, hxg⟩ := hsub hstabg
    have hx_eq : x = g := hΘ_inj hxg
    rwa [hx_eq] at hx
  have hclosure : Subgroup.closure SL ⊓ Subgroup.closure SK = Subgroup.closure SJ :=
    le_antisymm hge hle
  have himg : Θ '' (Subgroup.closure SJ) = (Submonoid.closure T_J : Set _) := by
    rw [r4f_closure_eq_of_inv_eq_self SJ hSJ_inv, ← Submonoid.coe_map,
      MonoidHom.map_mclosure, hSJ_image]
  have hcard_eq : Nat.card (Subgroup.closure SJ) = Nat.card (Submonoid.closure T_J) := by
    have h1 := Nat.card_image_of_injective hΘ_inj (Subgroup.closure SJ)
    rw [himg] at h1
    simpa using h1.symm
  refine ⟨hclosure, ?_⟩
  rw [hcard_eq, hcard]

theorem ggR4J_finite_identity {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hp3 : p = 3) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤)
    (hcell : ∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
        (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
      ((b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2))) :
    Subgroup.closure (Set.range fun i : Λ => φ' (some i)) ⊓
        Subgroup.closure ((fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none}) =
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j)) ∧
    Nat.card (Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j))) = 48 := by
  classical
  subst p
  obtain ⟨e, hori, hcell'⟩ := hcell
  rcases hori with hori | hori
  · rcases hcell' with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact r4f_case hD hspan e true true
        (by intro i j; rw [hori i j]; simp [R4J.caseC])
        (by simpa [R4J.caseB] using hb) (by simpa [R4J.caseCN] using hc)
    · exact r4f_case hD hspan e true false
        (by intro i j; rw [hori i j]; simp [R4J.caseC])
        (by simpa [R4J.caseB] using hb) (by simpa [R4J.caseCN] using hc)
  · rcases hcell' with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact r4f_case hD hspan e false true
        (by intro i j; rw [hori i j]; simp [R4J.caseC, Matrix.transpose_apply])
        (by simpa [R4J.caseB] using hb) (by simpa [R4J.caseCN] using hc)
    · exact r4f_case hD hspan e false false
        (by intro i j; rw [hori i j]; simp [R4J.caseC, Matrix.transpose_apply])
        (by simpa [R4J.caseB] using hb) (by simpa [R4J.caseCN] using hc)

end CFSG.StandardType

end
