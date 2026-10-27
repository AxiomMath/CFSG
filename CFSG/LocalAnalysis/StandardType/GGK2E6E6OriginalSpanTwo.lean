module

public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp

public import CFSG.LocalAnalysis.StandardType.GGResIBasic

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6DependentD5Span
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace E6QTwo

theorem dependent_e6_span_card
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    Nat.card (spanH h) = 3 ^ 5 := by
  classical
  have hge : 5 ≤ finrank (ZMod 3) (spanH h) := five_le_finrank_span hpair
  have hnot : ¬ (Fintype.card (Fin 6) ≤ Set.finrank (ZMod 3) (Set.range h)) :=
    fun hc => hdep ((linearIndependent_iff_card_le_finrank_span).mpr hc)
  have hle : finrank (ZMod 3) (spanH h) ≤ 5 := by
    by_contra h5
    push Not at h5
    apply hnot
    rw [Fintype.card_fin]
    exact h5
  have hfin : finrank (ZMod 3) (spanH h) = 5 := le_antisymm hle hge
  calc Nat.card (spanH h) = 3 ^ finrank (ZMod 3) (spanH h) := natCard_submodule _
    _ = 3 ^ 5 := by rw [hfin]

end E6QTwo

theorem e6_dependent_span_card_and_axis_decomposition
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    Nat.card (E6QTwo.spanH h) = 3 ^ 5 ∧ y ∉ E6QTwo.spanH h ∧
      ∀ v : V, ∃ (c : ZMod 3) (u : V), u ∈ E6QTwo.spanH h ∧ v = c • y + u := by
  classical
  let W : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => h (d5Index i))
  obtain ⟨c, hc⟩ := e6_dependent_d5_span hpair hy hker hdim hdep
  have h0W : h 0 ∈ W := by
    rw [hc]
    exact W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSW : E6QTwo.spanH h = W := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      refine Fin.cases h0W (fun j => ?_) i
      exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_mono
      rintro v ⟨i, rfl⟩
      exact ⟨d5Index i, rfl⟩
  have hWcard : Nat.card W = 3 ^ 5 := by
    rw [E6QTwo.natCard_submodule]
    change 3 ^ Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => h (d5Index i))) = 3 ^ 5
    rw [finrank_span_eq_card (d5_roots_linearIndependent hpair), Fintype.card_fin]
  refine ⟨hSW ▸ hWcard, ?_, ?_⟩
  · rw [hSW]
    exact axis_not_mem_d5_span hpair hy hker
  · intro v
    have hLI := d5_axis_linearIndependent hpair hy hker
    have hcard : Fintype.card (Option (Fin 5)) = Module.finrank (ZMod 3) V := by
      simp [hdim]
    have hspan := hLI.span_eq_top_of_card_eq_finrank' hcard
    have hmem : v ∈ Submodule.span (ZMod 3)
        (Set.range fun o : Option (Fin 5) => o.casesOn' y (fun i => h (d5Index i))) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨d, hd⟩ := hmem
    refine ⟨d none, ∑ i : Fin 5, d (some i) • h (d5Index i), ?_, ?_⟩
    · rw [hSW]
      exact W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Fintype.sum_option] at hd
      simpa only [Option.casesOn'_none, Option.casesOn'_some, add_comm] using hd.symm

theorem GGResHyp.K_simple_roots_kill_y
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hy : y ∈ Bs)
    {Γ : Type} (φ : Γ → MulAut ↥Bs) (h : Γ → V) (α : Γ → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs)
    (hself : ∀ i, α i (h i) = 2)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) :
    ∀ i, α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
  obtain ⟨_, _, _, hKy, _⟩ := (hH.2.2.2.2.1.1 : LargeEvenSHat 3 B y K)
  intro i
  have hfix : φ i (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggAutomizer_apply_eq_of_le_centralizer hKy (hφ i)
  have hfixV := (ggLin_fix_iff (p := 3) ι (φ i) (⟨y, hy⟩ : ↥Bs)).mp hfix
  rw [hlin i] at hfixV
  have hzero : α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • h i = 0 :=
    sub_eq_self.mp hfixV
  have hne : h i ≠ 0 := by
    intro hi
    have hc := hself i
    rw [hi, map_zero] at hc
    exact (by decide : (0 : ZMod 3) ≠ 2) hc
  exact (smul_eq_zero.mp hzero).resolve_right hne

theorem e6_actual_automizer_linear_map_eq
    {G : Type} [Group G] {Bs K : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Fin 6 → MulAut ↥Bs)
    (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
    (hself : ∀ i, α i (h i) = 2)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    (ggAutomizer K Bs).map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hself := by
  rw [hgen, MonoidHom.map_closure]
  unfold E6QTwo.e6Weyl
  have heq : (ggLin (p := 3) ι) '' Set.range φ =
      Set.range (fun i => Module.reflection (hself i)) := by
    ext a
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      ext w
      rw [hlin i, Module.reflection_apply]
    · rintro ⟨i, rfl⟩
      refine ⟨φ i, ⟨i, rfl⟩, ?_⟩
      ext w
      rw [hlin i, Module.reflection_apply]
  rw [heq]

theorem finrank_six_of_card
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hcard : Nat.card Bs = 3 ^ 6) :
    Module.finrank (ZMod 3) V = 6 := by
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
  rw [Nat.card_zmod] at hpow
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hpow.symm.trans hVcard)

theorem closure_fixes_x_of_generators
    {G : Type} [Group G] {Bs K : Subgroup G} {x : G} (hx : x ∈ Bs)
    {S T : Set (MulAut ↥Bs)}
    (hclos : ggAutomizer K Bs = Subgroup.closure (S ∪ T))
    (hS : ∀ ψ ∈ S, ψ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩)
    (hT : ∀ ψ ∈ T, ψ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩) :
    ∀ ψ ∈ ggAutomizer K Bs, ψ (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
  let xB : ↥Bs := ⟨x, hx⟩
  let Fixx : Subgroup (MulAut ↥Bs) :=
    { carrier := {ψ : MulAut ↥Bs | ψ xB = xB}
      one_mem' := rfl
      mul_mem' := by
        intro ψ χ hψ hχ
        change (ψ * χ) xB = xB
        rw [MulAut.mul_apply, hχ, hψ]
      inv_mem' := by
        intro ψ hψ
        change ψ⁻¹ xB = xB
        have h := congrArg (fun b : ↥Bs => ψ⁻¹ b) hψ
        simpa using h.symm }
  have hgen : S ∪ T ⊆ Fixx := by
    rintro ψ (hψ | hψ)
    · exact hS ψ hψ
    · exact hT ψ hψ
  have hle : ggAutomizer K Bs ≤ Fixx := by
    rw [hclos]
    exact (Subgroup.closure_le Fixx).mpr hgen
  intro ψ hψ
  exact hle hψ

theorem addedReflection_fixes_x_of_coroot_mem_spanH_general
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (e6 : Fin 6 ≃ Λ) (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (a : Λa) (hins : h (Sum.inr a) ∈ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i)))) :
    ggLin (p := 3) ι (φ (Sum.inr a))
      (ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs)) := by
  classical
  haveI : Finite ↥Bs := Subtype.finite
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let hL : Fin 6 → V := fun i => h (Sum.inl (e6 i))
  let αL : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e6 i))
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e6 i))
  have hpairE6 : ∀ i j : Fin 6, αL i (hL j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpairL, e6Cartan_reindex e6 hCL hMLeq]
  have hselfL : ∀ i : Fin 6, αL i (hL i) = 2 := by
    intro i
    rw [hpairE6 i i]
    norm_num [CartanMatrix.E₆]
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hdep : ¬ LinearIndependent (ZMod 3) hL := by
    intro hli
    apply hsel
    have hli' : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) := by
      have hcomp := hli.comp e6.symm (fun x y hxy => e6.symm.injective hxy)
      simpa [hL, Function.comp_def] using hcomp
    exact hli'
  have hScard : Nat.card (E6QTwo.spanH hL) = 3 ^ 5 :=
    E6QTwo.dependent_e6_span_card hpairE6 hdep
  obtain ⟨B', hB'⟩ := E6QTwo.exists_bilinForm_span hpairE6 hScard
  let u : V := h (Sum.inr a)
  have huS : u ∈ E6QTwo.spanH hL := hins
  have hφa : α (Sum.inr a) u = 2 := by
    have hp := hpairK (Sum.inr a) (Sum.inr a)
    rw [hCK.1] at hp
    simpa [u] using hp
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφa
    exact (by decide : (0 : ZMod 3) ≠ 2) hφa
  let v : V := -u
  have hvS : v ∈ E6QTwo.spanH hL := by
    exact (E6QTwo.spanH hL).neg_mem huS
  have hv : v ≠ 0 := by
    simpa [v] using neg_ne_zero.mpr hu
  have hvsub : (⟨v, hvS⟩ : E6QTwo.spanH hL) = -(⟨u, huS⟩ : E6QTwo.spanH hL) := by
    ext
    simp [v]
  have huv : B' ⟨u, huS⟩ ⟨u, huS⟩ = B' ⟨v, hvS⟩ ⟨v, hvS⟩ := by
    rw [hvsub]
    simp
  obtain ⟨z, hzW, hzu⟩ :=
    E6QTwo.exists_mem_e6Weyl_apply_eq_of_mem_spanH hpairE6 hselfL hScard hB'
      huS hvS hu hv huv
  have hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e6.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e6 i, rfl⟩
  have hmapL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      E6QTwo.e6Weyl hselfL :=
    e6_actual_automizer_linear_map_eq ι φL hL αL hselfL
      (fun i w => hlin (Sum.inl (e6 i)) w) hgenL
  have hzA : z ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι) := by
    rw [hmapL]
    exact hzW
  obtain ⟨zL, hzL, hzLapply⟩ := Subgroup.mem_map.mp hzA
  have hfixL : ggLin (p := 3) ι zL xV = xV := by
    have hfix := ggResI_automizer_fix hx hLx zL hzL
    dsimp only [xV]
    exact (ggLin_fix_iff (p := 3) ι zL (⟨x, hx⟩ : ↥Bs)).mp hfix
  have hzc : ggLin (p := 3) ι zL u = -u := by
    rw [hzLapply, hzu]
  let Ajoin : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)
  have htopTF : CFSG.StandardType.QTwoLin.TransvectionFree ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) ι)) :=
    ggQ2P3P_transvectionFree ι hH.2.2.2.1
  have hmono : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hjoinle : Ajoin ≤ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) ι) :=
    Subgroup.map_mono hmono
  have hTF : CFSG.StandardType.QTwoLin.TransvectionFree Ajoin :=
    fun g hg => htopTF g (hjoinle hg)
  have hr : Module.reflection (x := u) (f := α (Sum.inr a)) hφa ∈ Ajoin := by
    have hφmem : φ (Sum.inr a) ∈ ggAutomizer K Bs := by
      rw [hclosK]
      exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
    have hmem : ggLin (p := 3) ι (φ (Sum.inr a)) ∈ Ajoin := by
      exact Subgroup.mem_map.mpr ⟨φ (Sum.inr a), Subgroup.mem_sup_right hφmem, rfl⟩
    have heq : ggLin (p := 3) ι (φ (Sum.inr a)) =
        Module.reflection (x := u) (f := α (Sum.inr a)) hφa := by
      ext w
      rw [hlin (Sum.inr a) w, Module.reflection_apply]
    rwa [heq] at hmem
  have hz : ggLin (p := 3) ι zL ∈ Ajoin :=
    Subgroup.mem_map.mpr ⟨zL, Subgroup.mem_sup_left hzL, rfl⟩
  have hfixrefl : Module.reflection (x := u) (f := α (Sum.inr a)) hφa xV = xV :=
    CFSG.StandardType.QTwoLin.reflection_fixes_of_negated_root hTF hφa hr
      hz hzc hfixL
  have heq : ggLin (p := 3) ι (φ (Sum.inr a)) =
      Module.reflection (x := u) (f := α (Sum.inr a)) hφa := by
    ext w
    rw [hlin (Sum.inr a) w, Module.reflection_apply]
  rw [heq]
  exact hfixrefl

theorem false_of_all_added_inside_general
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (e6 : Fin 6 ≃ Λ) (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hinsAll : ∀ a : Λa,
      h (Sum.inr a) ∈ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i))))
    (hmove : ∃ t ∈ ggAutomizer K Bs,
      t (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩) :
    False := by
  classical
  let xB : ↥Bs := ⟨x, hH.1.tableB_facts.2.2.1⟩
  let Sset : Set (MulAut ↥Bs) := Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)
  let Tset : Set (MulAut ↥Bs) := Set.range fun a : Λa => φ (Sum.inr a)
  have hS : ∀ ψ ∈ Sset, ψ xB = xB := by
    rintro ψ ⟨j, rfl⟩
    have hmem : φ (Sum.inl j) ∈ ggAutomizer L Bs := by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    exact ggResI_automizer_fix hH.1.tableB_facts.2.2.1
      hH.1.tableB_facts.2.2.2.1 (φ (Sum.inl j)) hmem
  have hT : ∀ ψ ∈ Tset, ψ xB = xB := by
    rintro ψ ⟨a, rfl⟩
    have hfixV := addedReflection_fixes_x_of_coroot_mem_spanH_general hH ι φ h α hCL hlin
      hpairL hpairK hCK hclosL hclosK hsel e6 hMLeq a (hinsAll a)
    exact (ggLin_fix_iff (p := 3) ι (φ (Sum.inr a)) xB).mpr hfixV
  have hKfix : ∀ ψ ∈ ggAutomizer K Bs, ψ xB = xB :=
    closure_fixes_x_of_generators hH.1.tableB_facts.2.2.1 hclosK hS hT
  obtain ⟨t, ht, hne⟩ := hmove
  exact hne (hKfix t ht)

theorem false_of_all_added_inside
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (hcard : Nat.card Bs = 3 ^ 6)
    (e6 : Fin 6 ≃ Λ) (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hinsAll : ∀ a : Λa,
      h (Sum.inr a) ∈ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i))))
    (hmove : ∃ t ∈ ggAutomizer K Bs,
      t (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩) :
    False := by
  exact false_of_all_added_inside_general hH ι φ h α hCL hlin hpairL hpairK hCK
    hclosL hclosK hsel e6 hMLeq hinsAll hmove

end CFSG.StandardType

end
