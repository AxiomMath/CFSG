module

public import CFSG.OddTranspositions.O4FibresConfig
public import CFSG.OddTranspositions.FixKS5

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table
open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

noncomputable section

@[expose] def Yten : Subgroup PSigmaL225 := Subgroup.closure (Set.range y)

theorem mem_FixK_iff {q : PSL2 K25} : q ∈ FixK ↔ q = psl2FieldAut K25 frob25 q :=
  Iff.rfl

theorem frob25_mem_FixK {q : PSL2 K25} (hq : q ∈ FixK) :
    psl2FieldAut K25 frob25 q ∈ FixK := by
  rw [mem_FixK_iff] at hq ⊢
  rw [← MulAut.mul_apply, ← map_mul, frob25_mul_self, map_one, MulAut.one_apply]
  exact hq.symm

theorem right_mem_of_mem {x : PSigmaL225} (hx : x ∈ Yten) :
    x.right = 1 ∨ x.right = frob25 := by
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Or.inr (y_right i)
  | one => exact Or.inl (SemidirectProduct.one_right)
  | mul x y hx hy ihx ihy =>
      rw [SemidirectProduct.mul_right]
      rcases ihx with hx1 | hx1 <;> rcases ihy with hy1 | hy1 <;>
        rw [hx1, hy1] <;> simp [frob25_mul_self]
  | inv x hx ihx =>
      rw [SemidirectProduct.inv_right]
      rcases ihx with h1 | h1
      · rw [h1]; simp
      · rw [h1, show frob25⁻¹ = frob25 from
            inv_eq_of_mul_eq_one_right frob25_mul_self]
        exact Or.inr rfl

theorem left_mem_FixK_of_mem {x : PSigmaL225} (hx : x ∈ Yten) : x.left ∈ FixK := by
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact (leftY i).2
  | one =>
      rw [SemidirectProduct.one_left]
      exact FixK.one_mem
  | mul x y hx hy ihx ihy =>
      rw [SemidirectProduct.mul_left]
      rcases right_mem_of_mem hx with h | h
      · rw [h]
        simpa using FixK.mul_mem ihx ihy
      · rw [h]
        exact FixK.mul_mem ihx (frob25_mem_FixK ihy)
  | inv x hx ihx =>
      rw [SemidirectProduct.inv_left]
      rcases right_mem_of_mem hx with h | h
      · rw [h]
        simpa using FixK.inv_mem ihx
      · rw [h, show frob25⁻¹ = frob25 from
            inv_eq_of_mul_eq_one_right frob25_mul_self]
        exact frob25_mem_FixK (FixK.inv_mem ihx)

theorem left_mem_FixK (w : Yten) : (w : PSigmaL225).left ∈ FixK :=
  left_mem_FixK_of_mem w.2

@[expose] noncomputable def leftHomYten : Yten →* FixK where
  toFun w := ⟨(w : PSigmaL225).left, left_mem_FixK w⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    change ((a * b : Yten) : PSigmaL225).left =
      ((a : PSigmaL225).left) * ((b : PSigmaL225).left)
    rw [Subgroup.coe_mul, SemidirectProduct.mul_left]
    congr 1
    rcases right_mem_of_mem a.2 with h | h
    · rw [h]; simp
    · rw [h]
      exact (mem_FixK_iff.mp (left_mem_FixK b)).symm

theorem leftHomYten_surjective : Function.Surjective leftHomYten := by
  have hpre : FixK.subtype ⁻¹' Set.range (fun i : Fin 10 => (y i).left) =
      Set.range (fun i : Fin 10 => leftY i) := by
    ext q
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hclosureFix :
      Subgroup.closure (Set.range (fun i : Fin 10 => leftY i)) = ⊤ := by
    have h := Subgroup.closure_preimage_eq_top
      (s := Set.range (fun i : Fin 10 => (y i).left))
    rw [closure_left_y_eq_FixK] at h
    rw [← hpre]
    exact h
  have htop : leftHomYten.range = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hclosureFix, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨y i, Subgroup.subset_closure (Set.mem_range_self i)⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact MonoidHom.range_eq_top.mp htop

theorem not_isSolvable_Yten : ¬ Group.IsSolvable Yten := by
  intro hsol
  exact not_isSolvable_FixK
    (@Group.isSolvable_of_surjective Yten FixK _ _ leftHomYten leftHomYten_surjective hsol)

end

section Config

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}
variable {X : Subgroup G} {R : Subgroup X} [R.Normal]

def HW (hQ : Config D u w v z a K₁ S') (hKX : thirdK D z ≤ X) : Subgroup G :=
  Subgroup.closure ((Subtype.val : X → G) '' W D u X R (u_mem_X_config hQ hKX))

theorem HW_le_X (hQ : Config D u w v z a K₁ S') (hKX : thirdK D z ≤ X) :
    HW (R := R) (hQ := hQ) hKX ≤ X := by
  rw [HW, Subgroup.closure_le]
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem HW_le_H (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    (hR : Group.IsSolvable R) (hKX : thirdK D z ≤ X)
    (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    HW (R := R) (hQ := hQ) hKX ≤ Halpha D hC.alpha := by
  rw [HW, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.subset_closure
    (W_subset_DalphaStar_config hC hQ htri hu hv hKX hR hPX y hy)

theorem not_isSolvable_Halpha_of_config (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S')
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha)
    (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ¬ Group.IsSolvable (Halpha D hC.alpha) := by
  classical
  obtain ⟨e, _he, _heu, himg⟩ := W_eq_preimage_ten hC hQ htri hu hKX hPX
  let Wsub : Subgroup G := HW (R := R) (hQ := hQ) hKX
  have hWX : Wsub ≤ X := HW_le_X hQ hKX
  have hWH : Wsub ≤ Halpha D hC.alpha := HW_le_H hC hQ htri hu hv hR hKX hPX
  let f : Wsub →* PSigmaL225 :=
    e.toMonoidHom.comp ((QuotientGroup.mk' R).comp (Subgroup.inclusion hWX))
  let Wset : Set X := W D u X R (u_mem_X_config hQ hKX)
  let gen : Wset → Wsub := fun w =>
    ⟨(w.1 : G), Subgroup.subset_closure ⟨w.1, w.2, rfl⟩⟩
  have hgen_top : Subgroup.closure (Set.range gen) = ⊤ := by
    have hpre : Wsub.subtype ⁻¹' ((Subtype.val : X → G) '' Wset) = Set.range gen := by
      ext q
      constructor
      · rintro ⟨w, hw, hwq⟩
        exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w.1, w.2, rfl⟩
    have h := Subgroup.closure_preimage_eq_top
      (s := (Subtype.val : X → G) '' Wset)
    change Subgroup.closure (Wsub.subtype ⁻¹' ((Subtype.val : X → G) '' Wset)) = ⊤ at h
    rw [← hpre]
    exact h
  have hgen_mem : ∀ w : Wset, f (gen w) ∈ Yten := by
    intro w
    have hinc : Subgroup.inclusion hWX (gen w) = w.1 := Subtype.ext rfl
    have hf : f (gen w) = e (QuotientGroup.mk' R w.1) := by
      simp [f, hinc]
    rw [hf]
    have hzset : QuotientGroup.mk' R w.1 ∈
        {z : X ⧸ R | ∃ y : X, y ∈ W D u X R (u_mem_X_config hQ hKX) ∧
          QuotientGroup.mk' R y = z} := ⟨w.1, w.2, rfl⟩
    have heimg : e (QuotientGroup.mk' R w.1) ∈
        e '' {z : X ⧸ R | ∃ y : X, y ∈ W D u X R (u_mem_X_config hQ hKX) ∧
          QuotientGroup.mk' R y = z} := ⟨_, hzset, rfl⟩
    rw [himg] at heimg
    exact Subgroup.subset_closure heimg
  have hfr : ∀ x : Wsub, f x ∈ Yten := by
    intro x
    have hx : x ∈ Subgroup.closure (Set.range gen) := by
      rw [hgen_top]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨w, rfl⟩ := hz
        exact hgen_mem w
    | one =>
        rw [map_one]
        exact Yten.one_mem
    | mul a b ha hb iha ihb =>
        rw [map_mul]
        exact Yten.mul_mem iha ihb
    | inv a ha iha =>
        rw [map_inv]
        exact Yten.inv_mem iha
  let φ : Wsub →* Yten := f.codRestrict Yten hfr
  have hY : ∀ i : Fin 10, ∃ x : Wsub, φ x =
      ⟨y i, Subgroup.subset_closure (Set.mem_range_self i)⟩ := by
    intro i
    have hyi : y i ∈ e '' {z : X ⧸ R | ∃ y : X,
        y ∈ W D u X R (u_mem_X_config hQ hKX) ∧ QuotientGroup.mk' R y = z} := by
      rw [himg]
      exact Set.mem_range_self i
    obtain ⟨z, ⟨w, hw, hwz⟩, hz⟩ := hyi
    refine ⟨⟨(w : G), Subgroup.subset_closure ⟨w, hw, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change f ⟨(w : G), Subgroup.subset_closure ⟨w, hw, rfl⟩⟩ = y i
    have hinc : Subgroup.inclusion hWX
        ⟨(w : G), Subgroup.subset_closure ⟨w, hw, rfl⟩⟩ = w := Subtype.ext rfl
    have hfx : f ⟨(w : G), Subgroup.subset_closure ⟨w, hw, rfl⟩⟩ =
        e (QuotientGroup.mk' R w) := by
      simp [f, hinc]
    rw [hfx, hwz, hz]
  let yY : Fin 10 → Yten := fun i => ⟨y i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hle : Yten ≤ (φ.range).map Yten.subtype := by
    change Subgroup.closure (Set.range y) ≤ (φ.range).map Yten.subtype
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hY i
    exact Subgroup.mem_map.mpr ⟨φ x, ⟨x, rfl⟩, congrArg Subtype.val hx⟩
  have hEq : (φ.range).map Yten.subtype = Yten :=
    le_antisymm (by rintro _ ⟨v, -, rfl⟩; exact v.2) hle
  have htop : φ.range = ⊤ := by
    apply eq_top_iff.mpr
    intro w
    have hw : (w : PSigmaL225) ∈ (φ.range).map Yten.subtype := by
      rw [hEq]; exact w.2
    obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
    have hvw' : v = w := Subtype.ext hvw
    simpa [hvw'] using hv
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp htop
  intro hHsol
  have hHWsol : Group.IsSolvable Wsub :=
    @Group.isSolvable_of_isSolvable_injective Wsub (Halpha D hC.alpha) _ _
      (Subgroup.inclusion hWH) (Subgroup.inclusion_injective hWH) hHsol
  have hYsol : Group.IsSolvable Yten :=
    @Group.isSolvable_of_surjective Wsub Yten _ _ φ hφsurj hHWsol
  exact not_isSolvable_Yten hYsol

end Config

end CFSG.OddTranspositions.QZ

end
