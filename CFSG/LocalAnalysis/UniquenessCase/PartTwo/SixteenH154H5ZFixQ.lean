module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_normalizer_fix_summands {Q : Type} [CommGroup Q] [Finite Q]
    {Λ : Subgroup (MulAut Q)} (hcenter : Subgroup.center ↥Λ = ⊥) {k : ℕ}
    (I : Fin k → Subgroup Q) (hspan : (⨆ i, I i) = ⊤)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ y ∈ I i, g y ∈ I i)
    (hfull : ∀ i, ∀ φ : MulAut ↥(I i), ∃ g ∈ Λ, ∀ y : ↥(I i), g (y : Q) = (φ y : Q))
    (hfaith : ∀ i, ∀ g ∈ Λ, (∀ y ∈ I i, g y = y) → g = 1)
    {x : MulAut Q} (hxN : ∀ g ∈ Λ, x * g * x⁻¹ ∈ Λ) (hxI : ∀ i, ∀ y ∈ I i, x y ∈ I i) :
    x ∈ Λ := by
  cases k with
  | zero =>
      have hbot : (⊥ : Subgroup Q) = ⊤ := by
        rw [← hspan]
        exact (iSup_of_empty I).symm
      have htriv : ∀ y : Q, y = 1 := fun y =>
        Subgroup.mem_bot.mp (by rw [hbot]; exact Subgroup.mem_top y)
      have hx1 : x = 1 := MulEquiv.ext fun y => by simp [htriv (x y), htriv y]
      rw [hx1]
      exact Subgroup.one_mem Λ
  | succ k =>
      let f : ∀ i : Fin (k + 1), ↥(I i) →* ↥(I i) := fun i =>
        { toFun := fun y => ⟨x (y : Q), hxI i (y : Q) y.2⟩
          map_one' := by apply Subtype.ext; simp
          map_mul' := fun a b => by apply Subtype.ext; simp }
      have hinj : ∀ i, Function.Injective (f i) := by
        intro i a b hab
        apply Subtype.ext
        apply x.injective
        have h := congrArg (fun w : ↥(I i) => (w : Q)) hab
        simpa [f] using h
      let φ : ∀ i : Fin (k + 1), MulAut ↥(I i) := fun i =>
        MulEquiv.ofBijective (f i)
          ⟨hinj i, (Finite.injective_iff_surjective (f := f i)).mp (hinj i)⟩
      have hφ : ∀ i (y : ↥(I i)), (φ i y : Q) = x (y : Q) := by
        intro i y
        rfl
      have hxIinv : ∀ i, ∀ y ∈ I i, x⁻¹ y ∈ I i := by
        intro i y hy
        have hsurj : Function.Surjective (f i) :=
          (Finite.injective_iff_surjective (f := f i)).mp (hinj i)
        obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
        have hzy : x (z : Q) = y := by
          have h := congrArg (fun w : ↥(I i) => (w : Q)) hz
          simpa [f] using h
        have hzinv : x⁻¹ y = (z : Q) :=
          (congrArg (fun w => x⁻¹ w) hzy.symm).trans (MulEquiv.symm_apply_apply x (z : Q))
        rw [hzinv]
        exact z.2
      have hex : ∀ i, ∃ g : MulAut Q, g ∈ Λ ∧ ∀ y : ↥(I i), g (y : Q) = (φ i y : Q) :=
        fun i => hfull i (φ i)
      choose l hl using hex
      have hl_mem : ∀ i, l i ∈ Λ := fun i => (hl i).1
      have hl_apply : ∀ i (y : ↥(I i)), l i (y : Q) = (φ i y : Q) := fun i => (hl i).2
      have hconj : ∀ i (g : MulAut Q), g ∈ Λ → x * g * x⁻¹ = l i * g * (l i)⁻¹ := by
        intro i g hg
        have ha : x * g * x⁻¹ ∈ Λ := hxN g hg
        have hb : l i * g * (l i)⁻¹ ∈ Λ :=
          Λ.mul_mem (Λ.mul_mem (hl_mem i) hg) (Λ.inv_mem (hl_mem i))
        have hfix : ∀ y ∈ I i,
            ((l i * g * (l i)⁻¹)⁻¹ * (x * g * x⁻¹)) y = y := by
          intro y hy
          have hxinv_mem : x⁻¹ y ∈ I i := hxIinv i y hy
          have hgmem : g (x⁻¹ y) ∈ I i := hstab i g hg (x⁻¹ y) hxinv_mem
          have h1 : l i (x⁻¹ y) = y :=
            (hl_apply i ⟨x⁻¹ y, hxinv_mem⟩).trans
              ((hφ i ⟨x⁻¹ y, hxinv_mem⟩).trans (MulEquiv.apply_symm_apply x y))
          have hlinv : (l i)⁻¹ y = x⁻¹ y :=
            (congrArg (fun z => (l i)⁻¹ z) h1).symm.trans
              (MulEquiv.symm_apply_apply (l i) (x⁻¹ y))
          have hay_eq : (x * g * x⁻¹) y = (l i * g * (l i)⁻¹) y := by
            have hL : (x * g * x⁻¹) y = x (g (x⁻¹ y)) := by
              simp only [MulAut.mul_apply]
            have hR : (l i * g * (l i)⁻¹) y = l i (g ((l i)⁻¹ y)) := by
              simp only [MulAut.mul_apply]
            rw [hL, hR, hlinv]
            exact ((hl_apply i ⟨g (x⁻¹ y), hgmem⟩).trans
              (hφ i ⟨g (x⁻¹ y), hgmem⟩)).symm
          calc ((l i * g * (l i)⁻¹)⁻¹ * (x * g * x⁻¹)) y
              = (l i * g * (l i)⁻¹)⁻¹ ((x * g * x⁻¹) y) := by
                simp only [MulAut.mul_apply]
            _ = (l i * g * (l i)⁻¹)⁻¹ ((l i * g * (l i)⁻¹) y) := by rw [hay_eq]
            _ = y := MulEquiv.symm_apply_apply _ _
        have hone : (l i * g * (l i)⁻¹)⁻¹ * (x * g * x⁻¹) = 1 :=
          hfaith i _ (Λ.mul_mem (Λ.inv_mem hb) ha) hfix
        exact (inv_mul_eq_one.mp hone).symm
      have hl_eq_all : ∀ i j : Fin (k + 1), l i = l j := by
        intro i j
        have hc_mem : (l j)⁻¹ * l i ∈ Λ :=
          Λ.mul_mem (Λ.inv_mem (hl_mem j)) (hl_mem i)
        have hc_comm : ∀ g : MulAut Q, g ∈ Λ →
            g * ((l j)⁻¹ * l i) = ((l j)⁻¹ * l i) * g := by
          intro g hg
          have hij : l i * g * (l i)⁻¹ = l j * g * (l j)⁻¹ :=
            (hconj i g hg).symm.trans (hconj j g hg)
          have hconj_c : ((l j)⁻¹ * l i) * g * ((l j)⁻¹ * l i)⁻¹ = g := by
            have hstep : ((l j)⁻¹ * l i) * g * ((l j)⁻¹ * l i)⁻¹
                = (l j)⁻¹ * (l i * g * (l i)⁻¹) * l j := by group
            rw [hstep, hij]
            group
          calc g * ((l j)⁻¹ * l i)
              = (((l j)⁻¹ * l i) * g * ((l j)⁻¹ * l i)⁻¹) * ((l j)⁻¹ * l i) :=
                (congrArg (fun z => z * ((l j)⁻¹ * l i)) hconj_c).symm
            _ = ((l j)⁻¹ * l i) * g := by group
        have hc_center : (⟨(l j)⁻¹ * l i, hc_mem⟩ : ↥Λ) ∈ Subgroup.center ↥Λ := by
          rw [Subgroup.mem_center_iff]
          intro g'
          apply Subtype.ext
          simpa using hc_comm (g' : MulAut Q) g'.2
        have hc_one : (⟨(l j)⁻¹ * l i, hc_mem⟩ : ↥Λ) = 1 := by
          have hmem : (⟨(l j)⁻¹ * l i, hc_mem⟩ : ↥Λ) ∈ (⊥ : Subgroup ↥Λ) := by
            rw [← hcenter]
            exact hc_center
          exact Subgroup.mem_bot.mp hmem
        have hc_val : (l j)⁻¹ * l i = 1 := by
          simpa using congrArg Subtype.val hc_one
        exact (inv_mul_eq_one.mp hc_val).symm
      have hx_eq : x = l 0 := by
        have hS : (⊤ : Subgroup Q) ≤
            MonoidHom.eqLocus x.toMonoidHom (l 0).toMonoidHom := by
          rw [← hspan]
          apply iSup_le
          intro i y hy
          change x y = l 0 y
          have h1 : l i y = x y := (hl_apply i ⟨y, hy⟩).trans (hφ i ⟨y, hy⟩)
          calc x y = l i y := h1.symm
            _ = l 0 y := congrArg (fun z : MulAut Q => z y) (hl_eq_all i 0)
        exact MulEquiv.ext fun y => hS (Subgroup.mem_top y)
      rw [hx_eq]
      exact hl_mem 0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
