module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure l05nBL_Al {G : Type} [Group G] [Finite G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) where
  Λ : Type
  fin : Fintype Λ
  dec : DecidableEq Λ
  S : Finset Λ
  hS1 : 2 ≤ S.card
  hS2 : S.card ≤ 3
  ML : CoxeterMatrix Λ
  CL : Matrix Λ Λ ℤ
  MJL : CoxeterMatrix {i : Λ // i ∉ S}
  V : Type
  [acg : AddCommGroup V]
  [mod : Module (ZMod p) V]
  ι : Additive ↥Bs ≃+ V
  φL : Λ → MulAut ↥Bs
  hL : Λ → V
  αL : Λ → Module.Dual (ZMod p) V
  Λa : Type
  fina : Fintype Λa
  deca : DecidableEq Λa
  hΛa : 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3
  hk : Nat.card Λa = k
  MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)
  CK0 : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ
  φK : {i : Λ // i ∉ S} ⊕ Λa → MulAut ↥Bs
  hK : {i : Λ // i ∉ S} ⊕ Λa → V
  αK : {i : Λ // i ∉ S} ⊕ Λa → Module.Dual (ZMod p) V
  cc : {i : Λ // i ∉ S} → (ZMod p)ˣ
  fL : ML.Group ≃* ↥(ggAutomizer L Bs)
  fK : MK.Group ≃* ↥(ggAutomizer K Bs)
  hWML : GGIsWeylMatrix ML
  hCLL : GGIntCartan ML CL
  hWMJL : GGIsWeylMatrix MJL
  hMJL : ∀ j j' : {i : Λ // i ∉ S}, MJL.M j j' = ML.M j.1 j'.1
  hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i
  hreflL : ∀ i, GGIsReflection p (φL i)
  hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p)
  hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i
  hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL)
  hclosJL : ggAutomizer J Bs =
    Subgroup.closure (Set.range fun j : {i : Λ // i ∉ S} => φL j.1)
  hWMK : GGIsWeylMatrix MK
  hCKK : GGIntCartan MK CK0
  hlinK : ∀ o w, ggLin (p := p) ι (φK o) w = w - αK o w • hK o
  hreflK : ∀ o, GGIsReflection p (φK o)
  hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p)
  hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φK o
  hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK)
  hφK : ∀ j : {i : Λ // i ∉ S}, φK (Sum.inl j) = φL j.1
  hhK : ∀ j : {i : Λ // i ∉ S}, hK (Sum.inl j) = (cc j : ZMod p) • hL j.1
  hαK : ∀ j : {i : Λ // i ∉ S}, αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j.1
  hord : ∀ i j : {i : Λ // i ∉ S}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1

theorem l05nBL_align_order {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {ΛL : Type} [Fintype ΛL] [DecidableEq ΛL]
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK]
    {MJL : CoxeterMatrix ΛL} {MJK : CoxeterMatrix ΛK}
    {fJL : MJL.Group ≃* ↥(ggAutomizer J Bs)} {fJK : MJK.Group ≃* ↥(ggAutomizer J Bs)}
    (σ : ΛL ≃ ΛK) (w : ↥(ggAutomizer J Bs))
    (hσ : ∀ i, fJK (MJK.simple (σ i)) = w * fJL (MJL.simple i) * w⁻¹) :
    ∀ i j, MJK.M (σ i) (σ j) = MJL.M i j := by
  intro i j
  have h1 : orderOf (fJK (MJK.simple (σ i)) * fJK (MJK.simple (σ j))) = MJK.M (σ i) (σ j) := by
    rw [← map_mul]
    exact (orderOf_injective (fJK : MJK.Group →* ↥(ggAutomizer J Bs)) fJK.injective
      (MJK.simple (σ i) * MJK.simple (σ j))).trans (by
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
          CoxeterSystem.orderOf_simple_mul_simple MJK.toCoxeterSystem (σ i) (σ j))
  have h3 : orderOf (fJL (MJL.simple i) * fJL (MJL.simple j)) = MJL.M i j := by
    rw [← map_mul]
    exact (orderOf_injective (fJL : MJL.Group →* ↥(ggAutomizer J Bs)) fJL.injective
      (MJL.simple i * MJL.simple j)).trans (by
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
          CoxeterSystem.orderOf_simple_mul_simple MJL.toCoxeterSystem i j)
  have h2 : fJK (MJK.simple (σ i)) * fJK (MJK.simple (σ j)) =
      w * (fJL (MJL.simple i) * fJL (MJL.simple j)) * w⁻¹ := by
    rw [hσ i, hσ j]; group
  have hconj : ∀ x : ↥(ggAutomizer J Bs), orderOf (w * x * w⁻¹) = orderOf x := by
    intro x
    rw [← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective x
  rw [← h1, h2, hconj, h3]

theorem l05nBL_align (hConj : GGWeylSimpleSystemsConjInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} {Bs L J K : Subgroup G}
    (hL : GGResLeviSideDatumLE3 p Bs L J) (hK : l05nBL_sideSum k p Bs K J) :
    Nonempty (l05nBL_Al k p Bs L J K) := by
  obtain ⟨ΛL, i1L, i2L, S, ML, CL, MJL, VL, i3L, i4L, ιL, φL, hL1, αL,
    hS1, hS2, hWML, hCLL, hWMJL, hMJL, hlinL, hreflL, hpairL, hfLex, hclosL, hfJLex, hclosJL,
    hconjL⟩ := hL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨fJL, hfJL⟩ := hfJLex
  obtain ⟨Λj, i1K, i2K, Λa, i3K, i4K, MK0, CKraw, MJK, VK, i5K, i6K, ιK, φK0, hK0, αK0,
    hcard1, hcard2, hkK, hWMK0, hCKK0, hWMJK, hMJKK, hlinK0, hreflK0, hpairK0, hfK0ex, hclosK0,
    hfJKex, hclosJK, hconjK⟩ := hK
  letI := i1K; letI := i2K; letI := i5K; letI := i6K
  obtain ⟨fK0, hfK0⟩ := hfK0ex
  obtain ⟨fJK, hfJK⟩ := hfJKex
  have hT : ∀ k : Λj, ∃ (u : ↥(ggAutomizer J Bs)) (i : {i : ΛL // i ∉ S}),
      fJK (MJK.simple k) = u * fJL (MJL.simple i) * u⁻¹ := by
    intro k
    have hkA : φK0 (Sum.inl k) ∈ ggAutomizer J Bs := by
      rw [hclosJK]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    obtain ⟨u, hu, i, hui⟩ := hconjL (φK0 (Sum.inl k)) hkA (hreflK0 (Sum.inl k))
    refine ⟨⟨u, hu⟩, i, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, hfJK k, hfJL i] using hui
  obtain ⟨σ, w, hσ⟩ := hConj (Λ := {i : ΛL // i ∉ S}) (Λ' := Λj) MJL MJK
    hWMJL hWMJK (↥(ggAutomizer J Bs)) fJL fJK hT
  have horder : ∀ i j : {i : ΛL // i ∉ S}, MJK.M (σ i) (σ j) = MJL.M i j :=
    l05nBL_align_order σ w hσ
  have hbij : Function.Bijective ((ιK.symm.trans ιL).toAddMonoidHom.toZModLinearMap p) :=
    (ιK.symm.trans ιL).bijective
  let e : VK ≃ₗ[ZMod p] VL := LinearEquiv.ofBijective _ hbij
  have he : ∀ x : VK, e x = ιL (ιK.symm x) := by
    intro x
    rw [LinearEquiv.ofBijective_apply]
    rfl
  let u : MulAut ↥Bs := (w : MulAut ↥Bs)⁻¹
  let W : VL ≃ₗ[ZMod p] VL := ggLin (p := p) ιL u
  let φK2 : Λj ⊕ Λa → MulAut ↥Bs := fun k => u * φK0 k * u⁻¹
  let hKt : Λj ⊕ Λa → VL := fun k => e (hK0 k)
  let αKt : Λj ⊕ Λa → Module.Dual (ZMod p) VL := fun k => (αK0 k).comp e.symm.toLinearMap
  let hK2 : Λj ⊕ Λa → VL := fun k => W (hKt k)
  let αK2 : Λj ⊕ Λa → Module.Dual (ZMod p) VL := fun k => (αKt k).comp W.symm.toLinearMap
  have hφKσ : ∀ i : {i : ΛL // i ∉ S},
      φK0 (Sum.inl (σ i)) = (w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹ := by
    intro i
    have h2 := congrArg (fun x : ↥(ggAutomizer J Bs) => (x : MulAut ↥Bs)) (hσ i)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hfJK, hfJL] using h2
  have hφ2 : ∀ i : {i : ΛL // i ∉ S}, φK2 (Sum.inl (σ i)) = φL i := by
    intro i
    show u * φK0 (Sum.inl (σ i)) * u⁻¹ = φL i
    rw [hφKσ i]
    show (w : MulAut ↥Bs)⁻¹ * ((w : MulAut ↥Bs) * φL i * (w : MulAut ↥Bs)⁻¹) *
      ((w : MulAut ↥Bs)⁻¹)⁻¹ = φL i
    group
  have hlin_t : ∀ k v, ggLin (p := p) ιL (φK0 k) v = v - αKt k v • hKt k := by
    intro k v
    have hes : ∀ x : VL, e.symm x = ιK (ιL.symm x) := by
      intro x
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he]
      simp
    have htrans : ggLin (p := p) ιL (φK0 k) v =
        e (ggLin (p := p) ιK (φK0 k) (e.symm v)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [htrans, hlinK0 k (e.symm v)]
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hlin2 : ∀ k v, ggLin (p := p) ιL (φK2 k) v = v - αK2 k v • hK2 k := by
    intro k v
    have h := l05nBL_lin_conj (p := p) ιL u (φK0 k) (hlin_t k) v
    simpa only [φK2, αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply] using h
  have hpair2 : ∀ k k', αK2 k (hK2 k') = (CKraw k k' : ZMod p) := by
    intro k k'
    simpa only [αK2, hK2, hKt, αKt, W, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using hpairK0 k k'
  have hrefl2 : ∀ k, GGIsReflection p (φK2 k) := fun k => l05nBL_refl_conj (hreflK0 k) u
  have huJ : u ∈ ggAutomizer J Bs := by
    show (w : MulAut ↥Bs)⁻¹ ∈ ggAutomizer J Bs
    exact Subgroup.inv_mem _ w.2
  have huK : u ∈ ggAutomizer K Bs := by
    have h2 : Subgroup.closure (Set.range fun j : Λj => φK0 (Sum.inl j)) ≤
        Subgroup.closure (Set.range φK0) := by
      rw [Subgroup.closure_le]
      rintro γ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨Sum.inl j, rfl⟩
    have h3 : (w : MulAut ↥Bs) ∈ Subgroup.closure (Set.range φK0) := h2 (hclosJK ▸ w.2)
    rw [← hclosK0] at h3
    simpa [u] using Subgroup.inv_mem _ h3
  have hlam : ∀ i : {i : ΛL // i ∉ S}, ∃ c : (ZMod p)ˣ,
      hK2 (Sum.inl (σ i)) = (c : ZMod p) • hL1 i.1 ∧
      αK2 (Sum.inl (σ i)) = (↑(c⁻¹) : ZMod p) • αL i.1 := by
    intro i
    have hf : αL i.1 (hL1 i.1) = 2 := by
      rw [hpairL i.1 i.1, hCLL.1 i.1]
      norm_num
    have hf' : αK2 (Sum.inl (σ i)) (hK2 (Sum.inl (σ i))) = 2 := by
      rw [hpair2 (Sum.inl (σ i)) (Sum.inl (σ i)), hCKK0.1 (Sum.inl (σ i))]
      norm_num
    have hcomm : ∀ v, αL i.1 v • hL1 i.1 = αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) := by
      intro v
      have h1 := hlinL i.1 v
      have h2 := hlin2 (Sum.inl (σ i)) v
      rw [hφ2 i] at h2
      have hh : v - αL i.1 v • hL1 i.1 = v - αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) :=
        h1.symm.trans h2
      have hh1 : αL i.1 v • hL1 i.1 - v =
          αK2 (Sum.inl (σ i)) v • hK2 (Sum.inl (σ i)) - v := by
        simpa [neg_sub] using congrArg Neg.neg hh
      simpa [sub_add_cancel] using congrArg (fun t => t + v) hh1
    exact l05nBL_rankOne hp2 hf hf' hcomm
  let cc : (i : {i : ΛL // i ∉ S}) → (ZMod p)ˣ := fun i => (hlam i).choose
  have hcc : ∀ i, hK2 (Sum.inl (σ i)) = (cc i : ZMod p) • hL1 i.1 ∧
      αK2 (Sum.inl (σ i)) = (↑((cc i)⁻¹) : ZMod p) • αL i.1 := fun i => (hlam i).choose_spec
  let τ : ({i : ΛL // i ∉ S} ⊕ Λa) ≃ (Λj ⊕ Λa) :=
    Equiv.sumCongr σ (Equiv.refl Λa)
  let MK : CoxeterMatrix ({i : ΛL // i ∉ S} ⊕ Λa) := MK0.reindex τ.symm
  let CK0 : Matrix ({i : ΛL // i ∉ S} ⊕ Λa)
      ({i : ΛL // i ∉ S} ⊕ Λa) ℤ := fun o o' => CKraw (τ o) (τ o')
  let φK : ({i : ΛL // i ∉ S} ⊕ Λa) → MulAut ↥Bs := fun o => φK2 (τ o)
  let hK : ({i : ΛL // i ∉ S} ⊕ Λa) → VL := fun o => hK2 (τ o)
  let αK : ({i : ΛL // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) VL :=
    fun o => αK2 (τ o)
  have hWMK : GGIsWeylMatrix MK := l05nBL_weyl_reindex hWMK0 τ.symm
  have hCKK : GGIntCartan MK CK0 := l05nBL_intCartan_reindex hCKK0 τ
  have hlinK : ∀ o w, ggLin (p := p) ιL (φK o) w = w - αK o w • hK o :=
    fun o w => hlin2 (τ o) w
  have hreflK : ∀ o, GGIsReflection p (φK o) := fun o => hrefl2 (τ o)
  have hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p) :=
    fun o o' => hpair2 (τ o) (τ o')
  have hφK : ∀ j : {i : ΛL // i ∉ S}, φK (Sum.inl j) = φL j.1 := fun j => hφ2 j
  have hhK : ∀ j : {i : ΛL // i ∉ S},
      hK (Sum.inl j) = (cc j : ZMod p) • hL1 j.1 := fun j => (hcc j).1
  have hαK : ∀ j : {i : ΛL // i ∉ S},
      αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j.1 := fun j => (hcc j).2
  have hord : ∀ i j : {i : ΛL // i ∉ S},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 := by
    intro i j
    rw [show MK.M (Sum.inl i) (Sum.inl j) = MK0.M (Sum.inl (σ i)) (Sum.inl (σ j)) from by
          rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]; rfl,
      ← hMJKK, horder, hMJL]
  let fK : MK.Group ≃* ↥(ggAutomizer K Bs) :=
    (MK0.reindexGroupEquiv τ.symm).trans (fK0.trans (MulAut.conj ⟨u, huK⟩))
  have hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φK o := by
    intro o
    show ((fK0.trans (MulAut.conj ⟨u, huK⟩))
      ((MK0.reindexGroupEquiv τ.symm) (MK.simple o)) : MulAut ↥Bs) = φK2 (τ o)
    rw [show (MK0.reindexGroupEquiv τ.symm) (MK.simple o) = MK0.simple (τ o) from rfl,
      MulEquiv.trans_apply, MulAut.conj_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hfK0]
  have hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    have hclosK2 : ggAutomizer K Bs = Subgroup.closure (Set.range φK2) := by
      have hrange : Set.range φK2 = (MulAut.conj u).toMonoidHom '' Set.range φK0 := by
        ext γ; constructor
        · rintro ⟨k, rfl⟩
          exact ⟨φK0 k, ⟨k, rfl⟩, (MulAut.conj_apply u (φK0 k)).symm⟩
        · rintro ⟨γ, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, MulAut.conj_apply u (φK0 k)⟩
      rw [hrange, ← MonoidHom.map_closure (MulAut.conj u).toMonoidHom (Set.range φK0),
        ← hclosK0]
      exact (l05nBL_closure_conj (ggAutomizer K Bs) u huK).symm
    have hrange : Set.range φK = Set.range φK2 := by
      ext γ; constructor
      · rintro ⟨o, rfl⟩
        exact ⟨τ o, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨τ.symm k, by simp [φK]⟩
    rw [hclosK2, hrange]
  exact ⟨ΛL, i1L, i2L, S, hS1, hS2, ML, CL, MJL, VL, ιL, φL, hL1, αL,
    Λa, i3K, i4K, ⟨hcard1, hcard2⟩, hkK, MK, CK0, φK, hK, αK, cc, fL, fK,
    hWML, hCLL, hWMJL, hMJL, hlinL, hreflL, hpairL, hfL, hclosL, hclosJL,
    hWMK, hCKK, hlinK, hreflK, hpairK, hfK, hclosK, hφK, hhK, hαK, hord⟩

end CFSG.StandardType

end
