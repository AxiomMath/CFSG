module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixChart
public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixAxes
public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixKData
public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixModel
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrder
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem cs6_chart_of_witness
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K) (hcard : Nat.card Bs = 3 ^ 6)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hS2 : S.card = 2) (hΛa : Nat.card Λa = 1)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (htyp : ggTypLE6 ML MK)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hsel : ggSelDep (LinearIndependent (ZMod 3) fun i : Λ => h (Sum.inl i))
      (LinearIndependent (ZMod 3) h))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hdel : GGDeletedConnectedS ML S)
    (hxBs : x ∈ Bs) (hyBs : y ∈ Bs) :
    ∃ (θ : V ≃ₗ[ZMod 3] CS6E) (φL : Fin 6 → MulAut ↥Bs) (a0 : Λa) (ha aa yv : CS6E)
      (jj : Fin 5) (pi : Nat),
      (∀ i, cs6Img ι θ (φL i) = cs6Refl i) ∧
      cs6Img ι θ (φ (Sum.inr a0)) = ggDepARefl ha aa ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φL) ∧
      (∀ a : Λa, a = a0) ∧
      Nat.card ↥(ggAutomizer L Bs) = 51840 ∧ Nat.card ↥(ggAutomizer K Bs) ≤ 3840 ∧
      (cs6PatDet jj pi = 6 → Nat.card ↥(ggAutomizer K Bs) ≤ 720) ∧
      θ (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = cs6X ∧
      θ (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = yv ∧
      CS6CellHyp jj pi ha aa yv := by
  classical
  obtain ⟨e6, he6⟩ := htyp
  have hCLstd : ∀ i j, CL (e6 i) (e6 j) = CartanMatrix.E 6 i j :=
    ggIntCartan_E6_entries_of_type hCLL e6 he6
  have hKL : ∀ i j : {i : Λ // i ∉ S},
      ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (e6.symm i) (e6.symm j) : ℤ) : ZMod 3) := by
    intro i j
    have h1 : ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        (CL (i : Λ) (j : Λ) : ZMod 3) := by
      have hp := hpairK (Sum.inl i) (Sum.inl j)
      have hl := hpairL (i : Λ) (j : Λ)
      simp only [Sum.map_inl, id_eq] at hp
      exact hp.symm.trans hl
    have h2 : CL (i : Λ) (j : Λ) = CartanMatrix.E 6 (e6.symm i) (e6.symm j) := by
      simpa using hCLstd (e6.symm i) (e6.symm j)
    rw [h1, h2]
  have hpairKinl : ∀ (i : {i : Λ // i ∉ S}) (a : Λa),
      α (Sum.inl (i : Λ)) (h (Sum.inr a)) = (CK (Sum.inl i) (Sum.inr a) : ZMod 3) := by
    intro i a
    simpa only [Sum.map_inl, Sum.map_inr, id_eq] using hpairK (Sum.inl i) (Sum.inr a)
  have hpairKinr : ∀ (a : Λa) (i : {i : Λ // i ∉ S}),
      α (Sum.inr a) (h (Sum.inl (i : Λ))) = (CK (Sum.inr a) (Sum.inl i) : ZMod 3) := by
    intro a i
    simpa only [Sum.map_inl, Sum.map_inr, id_eq] using hpairK (Sum.inr a) (Sum.inl i)
  have hpairKinr2 : ∀ (a b : Λa),
      α (Sum.inr a) (h (Sum.inr b)) = (CK (Sum.inr a) (Sum.inr b) : ZMod 3) := by
    intro a b
    simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr a) (Sum.inr b)
  obtain ⟨jj, pi, a0, τ, hτ, ha0, hpi, hpatpair, hKbound, hKbound6⟩ :=
    cs6_Kdata e6 he6 hS2 hΛa hdel hWMK hCKK hKL
  obtain ⟨fL, hfL'⟩ := hfL
  obtain ⟨fK, hfK'⟩ := hfK
  have hcardL : Nat.card ↥(ggAutomizer L Bs) = 51840 :=
    card_ggAutomizer_of_typeE6 (X := L) (Bs := Bs) (M := ML) ⟨e6, he6⟩ fL
  have hKcard_eq : Nat.card MK.Group = Nat.card ↥(ggAutomizer K Bs) :=
    Nat.card_congr fK.toEquiv
  have hcardK : Nat.card ↥(ggAutomizer K Bs) ≤ 3840 := by
    rw [← hKcard_eq]; exact hKbound
  have hcardK6 : cs6PatDet jj pi = 6 → Nat.card ↥(ggAutomizer K Bs) ≤ 720 := by
    intro h6; rw [← hKcard_eq]; exact hKbound6 h6
  let x' : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  let y' : V := ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
  obtain ⟨hx'0, hxker', hyker, hyx⟩ :=
    cs6_axes_facts hH hxBs hyBs hCLL hCKK hlin hpairL hpairK hclosL hclosK
  have hxker : ∀ i : Fin 6, α (Sum.inl (e6 i)) x' = 0 := fun i => hxker' (e6 i)
  have hsel' : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := by
    simpa [ggSelDep] using hsel
  have hdep : ¬ LinearIndependent (ZMod 3) (fun i : Fin 6 => h (Sum.inl (e6 i))) :=
    fun hli => hsel' ((linearIndependent_equiv (R := ZMod 3) e6).mp hli)
  have hpairV : ∀ i j : Fin 6,
      α (Sum.inl (e6 i)) (h (Sum.inl (e6 j))) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpairL (e6 i) (e6 j), hCLstd i j]
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcardV : Nat.card V = 3 ^ 6 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  obtain ⟨θ, hθx, hθh, hθα⟩ :=
    cs6_chart_linear (fun i : Fin 6 => h (Sum.inl (e6 i)))
      (fun i : Fin 6 => α (Sum.inl (e6 i))) x' hpairV hdep hx'0 hxker hcardV
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e6 i))
  have hL : ∀ i, cs6Img ι θ (φL i) = cs6Refl i := by
    intro i
    have h1 := cs6Img_reflection ι θ (φL i) (h (Sum.inl (e6 i))) (α (Sum.inl (e6 i)))
      (fun w => hlin (Sum.inl (e6 i)) w)
    rw [hθh i] at h1
    have h2 : cs6Form θ (α (Sum.inl (e6 i))) = cs6Alpha i :=
      cs6Form_eq θ (α (Sum.inl (e6 i))) (cs6Alpha i) (fun v => hθα i v)
    rw [h2] at h1
    rw [h1]; rfl
  let ha : CS6E := θ (h (Sum.inr a0))
  let aa : CS6E := cs6Form θ (α (Sum.inr a0))
  let yv : CS6E := θ y'
  have hA : cs6Img ι θ (φ (Sum.inr a0)) = ggDepARefl ha aa :=
    cs6Img_reflection ι θ (φ (Sum.inr a0)) (h (Sum.inr a0)) (α (Sum.inr a0))
      (fun w => hlin (Sum.inr a0) w)
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e6.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e6 i, rfl⟩
  have hy : θ (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = yv := rfl
  have hx : θ (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = cs6X := hθx
  have hv : ∀ i : Fin 4, ggDepAdot (cs6Alpha (cs6J jj i)) yv = 0 := by
    intro i
    change ggDepAdot (cs6Alpha (cs6J jj i)) (θ y') = 0
    rw [hθα (cs6J jj i) y', ← hτ i]
    exact hyker (Sum.inl (τ i))
  have hvx : ∃ j : Fin 5, yv j.castSucc ≠ 0 := by
    by_contra hcon
    have hzero : ∀ j : Fin 5, yv j.castSucc = 0 := by
      intro j
      by_contra hj
      exact hcon ⟨j, hj⟩
    have hyveq : yv = yv (Fin.last 5) • cs6X := by
      funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
      · rw [hzero j]
        fin_cases j <;> simp [cs6X]
      · simp [cs6X]
    refine (hyx (yv (Fin.last 5))) ?_
    have h1 : θ y' = yv (Fin.last 5) • θ x' := by
      calc θ y' = yv := rfl
        _ = yv (Fin.last 5) • cs6X := hyveq
        _ = yv (Fin.last 5) • θ x' := by rw [hθx]
    have h2 := congrArg (fun w : CS6E => θ.symm w) h1
    simpa using h2
  have hpair1 : ∀ i : Fin 4,
      ggDepAdot (cs6Alpha (cs6J jj i)) ha = (cs6PatPair jj pi i).1 := by
    intro i
    change ggDepAdot (cs6Alpha (cs6J jj i)) (θ (h (Sum.inr a0))) = (cs6PatPair jj pi i).1
    rw [hθα (cs6J jj i) (h (Sum.inr a0)), ← hτ i]
    rw [hpairKinl (τ i) a0]
    exact (hpatpair i).1
  have hpair2 : ∀ i : Fin 4,
      ggDepAdot aa (cs6Root (cs6J jj i)) = (cs6PatPair jj pi i).2 := by
    intro i
    change ggDepAdot (cs6Form θ (α (Sum.inr a0))) (cs6Root (cs6J jj i)) = (cs6PatPair jj pi i).2
    rw [ggDepAdot_cs6Form]
    have hroot : θ.symm (cs6Root (cs6J jj i)) = h (Sum.inl (e6 (cs6J jj i))) := by
      rw [← hθh (cs6J jj i), LinearEquiv.symm_apply_apply]
    rw [hroot, ← hτ i]
    rw [hpairKinr a0 (τ i)]
    exact (hpatpair i).2
  have hdoty : ggDepAdot aa yv = 0 := by
    change ggDepAdot (cs6Form θ (α (Sum.inr a0))) (θ y') = 0
    rw [ggDepAdot_cs6Form, LinearEquiv.symm_apply_apply]
    exact hyker (Sum.inr a0)
  have hdot2 : ggDepAdot aa ha = 2 := by
    change ggDepAdot (cs6Form θ (α (Sum.inr a0))) (θ (h (Sum.inr a0))) = 2
    rw [ggDepAdot_cs6Form, LinearEquiv.symm_apply_apply]
    rw [hpairKinr2 a0 a0, hCKK.1 (Sum.inr a0)]
    norm_num
  have hcell : CS6CellHyp jj pi ha aa yv := by
    obtain ⟨r, hr, hyr⟩ := cs6_y_cases jj yv hv hvx
    exact ⟨hpi, ⟨r, hr, hyr⟩, hpair1, hpair2, hdoty, hdot2⟩
  exact ⟨θ, φL, a0, ha, aa, yv, jj, pi, hL, hA, hclosL', ha0, hcardL, hcardK,
    hcardK6, hx, hy, hcell⟩

theorem ggResE6Dep_cardSix_rank5
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K) (hOrbK : GGResCentBoundNbrInput)
    (hcard : Nat.card Bs = 3 ^ 6)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hS2 : S.card = 2) (hΛa : Nat.card Λa = 1)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (htyp : ggTypLE6 ML MK)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hsel : ggSelDep (LinearIndependent (ZMod 3) fun i : Λ => h (Sum.inl i))
      (LinearIndependent (ZMod 3) h))
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hdel : GGDeletedConnectedS ML S) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hyBs, -, -, -⟩ := ggE6Dep_nbr_facts hH.1 hH.2.2.2.2.1
  obtain ⟨θ, φL, a0, ha, aa, yv, jj, pi, hL, hA, hclosL', ha0, hcardL, hcardK,
    hcardK6, hx, hy, hcellHyp⟩ :=
    cs6_chart_of_witness hH hcard hS2 hΛa hWML hCLL hWMK hCKK htyp hlin hpairL hpairK
      hsel hfL hfK hclosL hclosK hdel hxBs hyBs
  have hout : CS6Outcome (cs6PatDet jj pi) ha aa yv := cs6_cells jj pi ha aa yv hcellHyp
  have hφaK : φ (Sum.inr a0) ∈ ggAutomizer K Bs := by
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inr ⟨a0, rfl⟩)
  have hφaL : φ (Sum.inr a0) ∈ ggAutomizer L Bs :=
    cs6_outcome_group hH hOrbK hcard ι θ φL (φ (Sum.inr a0)) ha aa yv hL hA hclosL'
      hφaK hcardL hcardK hxBs hyBs hx hy (cs6PatDet jj pi) hcardK6 hout
  have hK_le_L : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    rw [hclosK, Subgroup.closure_le]
    rintro z (hz | hz)
    · obtain ⟨j, rfl⟩ := hz
      rw [hclosL]
      exact Subgroup.subset_closure ⟨(j : Λ), rfl⟩
    · obtain ⟨a, rfl⟩ := hz
      rw [ha0 a]
      exact hφaL
  rw [sup_eq_left.mpr hK_le_L]
  obtain ⟨fL, hfL'⟩ := hfL
  exact ⟨Λ, ML, hWML, fL, fun i => hfL' i ▸ hrefl (Sum.inl i)⟩

end CFSG.StandardType
