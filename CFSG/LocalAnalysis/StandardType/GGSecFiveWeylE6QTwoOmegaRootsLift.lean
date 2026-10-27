module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsLiftBasic

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem exists_rootRefl_mem_map_of_card_192
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hW : Nat.card (e6Weyl hα) = 51840) (ι : Additive ↥Bs ≃+ V) {A AL : Subgroup (MulAut ↥Bs)}
    (hmap : A.map (ggLin (p := 3) ι) = e6Weyl hα) (hALA : AL ≤ A) (hALcard : Nat.card AL = 192)
    (hALr : GGReflGenerated 3 AL) {x y : ↥Bs} (hALx : ∀ φ ∈ AL, φ x = x)
    (hy : B (ι (Additive.ofMul y)) (ι (Additive.ofMul y)) = 2) :
    ∃ (w : V) (hw : B w w = 2), rootRefl (B := B) w hw ∈ AL.map (ggLin (p := 3) ι) ∧
      B w (ι (Additive.ofMul x)) = 0 ∧ B w (ι (Additive.ofMul y)) ≠ 0 := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective ((↑) : (V ≃ₗ[ZMod 3] V) → V → V) DFunLike.coe_injective
  by_contra hno
  have hgen : ∀ φ ∈ AL, ggLin (p := 3) ι φ ∈ e6Weyl hα := by
    intro φ hφ
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (hALA hφ)
  have hSOf : ∀ v ∈ SOf (B := B) ι AL, B v (ι (Additive.ofMul y)) = 0 := by
    intro v hv
    obtain ⟨hv2, hmem⟩ := (mem_SOf_iff (B := B) (ι := ι) (A := AL)).mp hv
    have hvx : B v (ι (Additive.ofMul x)) = 0 := by
      obtain ⟨φ, hφ, hφv⟩ := Subgroup.mem_map.mp hmem
      have hfix : rootRefl (B := B) v hv2 (ι (Additive.ofMul x)) = ι (Additive.ofMul x) := by
        rw [← hφv, ggLin_apply_ofMul, hALx φ hφ]
      exact (rootRefl_fix_iff hv2 _).mp hfix
    by_contra hvy
    exact hno ⟨v, hv2, hmem, hvx, hvy⟩
  have hfix : ∀ g ∈ AL.map (ggLin (p := 3) ι), g (ι (Additive.ofMul y)) = ι (Additive.ofMul y) := by
    intro g hg
    rw [GGReflGenerated] at hALr
    rw [hALr, MonoidHom.map_closure] at hg
    refine Subgroup.closure_induction (p := fun a _ => a (ι (Additive.ofMul y)) =
      ι (Additive.ofMul y)) ?_ ?_ ?_ ?_ hg
    · rintro a ⟨φ, ⟨hφL, hφr⟩, rfl⟩
      obtain ⟨v, hv, hveq⟩ := exists_root_of_ggIsReflection hP hV hB hα ι hφr (hgen φ hφL)
      rw [hveq, rootRefl_fix_iff hv]
      exact hSOf v ((mem_SOf_iff (B := B) (ι := ι) (A := AL)).mpr
        ⟨hv, by rw [← hveq]; exact Subgroup.mem_map_of_mem _ hφL⟩)
    · rfl
    · intro a b _ _ ha hb
      rw [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      calc (a⁻¹) (ι (Additive.ofMul y)) = a⁻¹ (a (ι (Additive.ofMul y))) := by rw [ha]
        _ = (a⁻¹ * a) (ι (Additive.ofMul y)) := by rw [LinearEquiv.mul_apply]
        _ = ι (Additive.ofMul y) := by rw [inv_mul_cancel]; rfl
  let S' : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (MulAction.stabilizer (e6Weyl hα) (ι (Additive.ofMul y))).map
      (Subgroup.subtype (e6Weyl hα))
  have hcardS' : Nat.card S' =
      Nat.card (MulAction.stabilizer (e6Weyl hα) (ι (Additive.ofMul y))) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (e6Weyl hα))
  have hle : AL.map (ggLin (p := 3) ι) ≤ S' := by
    intro g hg
    have hgW : g ∈ e6Weyl hα := by
      rw [← hmap]
      exact Subgroup.map_mono hALA hg
    refine Subgroup.mem_map.mpr ⟨⟨g, hgW⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact hfix g hg
  have hdvd : Nat.card (AL.map (ggLin (p := 3) ι)) ∣
      Nat.card (MulAction.stabilizer (e6Weyl hα) (ι (Additive.ofMul y))) := by
    rw [← hcardS']
    exact Subgroup.card_dvd_of_le hle
  have hcardmap : Nat.card (AL.map (ggLin (p := 3) ι)) = 192 := by
    rw [Subgroup.card_map_of_injective (ggLin_injective (p := 3) ι), hALcard]
  have hy0 : ι (Additive.ofMul y) ≠ 0 := by
    intro h0
    rw [h0] at hy
    simp at hy
    exact absurd hy (by decide)
  rcases stabilizer_cases hP hV hB hα hW hy0 with ⟨-, h720⟩ | ⟨h0, -⟩ | ⟨h1, -⟩
  · rw [h720, hcardmap] at hdvd
    norm_num at hdvd
  · rw [hy] at h0
    exact absurd h0 (by decide)
  · rw [hy] at h1
    exact absurd h1 (by decide)

theorem card_closure_comm_eq
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (ι : Additive ↥Bs ≃+ V) {AK : Subgroup (MulAut ↥Bs)} {y : ↥Bs}
    (hy : B (ι (Additive.ofMul y)) (ι (Additive.ofMul y)) = 2) (hAKy : ∀ φ ∈ AK, φ y = y)
    (hiso : ∀ φ ∈ AK, ∀ u w : V,
      B (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ w) = B u w)
    (hK : ∀ (w : V) (hw : B w w = 2), B w (ι (Additive.ofMul y)) = 0 →
      rootRefl (B := B) w hw ∈ AK.map (ggLin (p := 3) ι)) :
    Nat.card (Subgroup.closure {b : ↥Bs | ∃ φ ∈ AK, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4 ∧
      y ∉ Subgroup.closure {b : ↥Bs | ∃ φ ∈ AK, ∃ c : ↥Bs, b = φ c * c⁻¹} := by
  classical
  let y' : V := ι (Additive.ofMul y)
  let S : Set ↥Bs := {b : ↥Bs | ∃ φ ∈ AK, ∃ c : ↥Bs, b = φ c * c⁻¹}
  let C : Subgroup ↥Bs := Subgroup.closure S
  let f : ↥Bs → V := fun b => ι (Additive.ofMul b)
  have hf_mul : ∀ a b : ↥Bs, f (a * b) = f a + f b := by
    intro a b
    simp only [f, ofMul_mul, map_add]
  have hf_inv : ∀ b : ↥Bs, f b⁻¹ = - f b := by
    intro b
    simp only [f, ofMul_inv, map_neg]
  let img : AddSubgroup V :=
    { carrier := {v : V | ∃ b ∈ C, f b = v}
      add_mem' := by
        intro a b ha hb
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        exact ⟨a' * b', C.mul_mem ha' hb', hf_mul a' b'⟩
      zero_mem' := ⟨1, C.one_mem, by simp [f]⟩
      neg_mem' := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨a⁻¹, C.inv_mem ha, hf_inv a⟩ }
  let P : Submodule (ZMod 3) V := LinearMap.ker (B.flip y')
  let H : Subgroup ↥Bs :=
    { carrier := {b : ↥Bs | f b ∈ P}
      one_mem' := by
        change f 1 ∈ P
        rw [show f 1 = 0 from by simp [f]]
        exact P.zero_mem
      mul_mem' := by
        intro a b ha hb
        change f (a * b) ∈ P
        rw [hf_mul]
        exact P.add_mem ha hb
      inv_mem' := by
        intro a ha
        change f a⁻¹ ∈ P
        rw [hf_inv]
        exact P.neg_mem ha }
  have hS_sub : S ⊆ H := by
    intro b hb
    obtain ⟨φ, hφ, c, rfl⟩ := hb
    show f (φ c * c⁻¹) ∈ P
    change (B.flip y') (f (φ c * c⁻¹)) = 0
    have hsub : f (φ c * c⁻¹) = ggLin (p := 3) ι φ (f c) - f c := by
      simpa [f] using (ggLin_apply_ofMul_sub (p := 3) ι φ c).symm
    have hfix : ggLin (p := 3) ι φ y' = y' := by
      have := (ggLin_fix_iff (p := 3) ι φ y).mp (hAKy φ hφ)
      simpa [y'] using this
    have h1 : (B.flip y') (ggLin (p := 3) ι φ (f c)) = (B.flip y') (f c) := by
      rw [LinearMap.BilinForm.flip_apply, LinearMap.BilinForm.flip_apply]
      have h := hiso φ hφ (f c) y'
      rw [hfix] at h
      exact h
    rw [hsub, map_sub, h1]
    exact sub_self _
  have hC_le_H : C ≤ H := (Subgroup.closure_le H).mpr hS_sub
  have hfC : ∀ b ∈ C, f b ∈ P := fun b hb => hC_le_H hb
  have hroot_mem : ∀ (w : V), B w w = 2 → B w y' = 0 → w ∈ img := by
    intro w hw hwy
    obtain ⟨φ, hφ, hφw⟩ := hK w hw hwy
    let c : ↥Bs := Additive.toMul (ι.symm w)
    have hc : f c = w := by
      simp [f, c]
    have hb : φ c * c⁻¹ ∈ C := Subgroup.subset_closure ⟨φ, hφ, c, rfl⟩
    refine ⟨φ c * c⁻¹, hb, ?_⟩
    have hsub : f (φ c * c⁻¹) = ggLin (p := 3) ι φ (f c) - f c := by
      simpa [f] using (ggLin_apply_ofMul_sub (p := 3) ι φ c).symm
    rw [hsub, hc, hφw, rootRefl_apply, hw]
    have hcoef : (1 : ZMod 3) - 2 - 1 = 1 := by decide
    calc w - (2 : ZMod 3) • w - w = ((1 : ZMod 3) - 2 - 1) • w := by module
      _ = (1 : ZMod 3) • w := by rw [hcoef]
      _ = w := one_smul _ _
  have hspan_le : Submodule.span (ZMod 3) {w : V | B w w = 2 ∧ B w y' = 0} ≤
      AddSubgroup.toZModSubmodule 3 img := by
    rw [Submodule.span_le]
    rintro w ⟨hw, hwy⟩
    exact (AddSubgroup.mem_toZModSubmodule 3).mpr (hroot_mem w hw hwy)
  have himg_le_P : img ≤ P.toAddSubgroup := by
    rintro v ⟨b, hb, rfl⟩
    exact hfC b hb
  have hSmod_le : AddSubgroup.toZModSubmodule 3 img ≤ P := by
    intro v hv
    exact himg_le_P ((AddSubgroup.mem_toZModSubmodule 3).mp hv)
  have hP_le : P ≤ AddSubgroup.toZModSubmodule 3 img := by
    intro u hu
    have hu' : B u y' = 0 := by
      have h : (B.flip y') u = 0 := LinearMap.mem_ker.mp hu
      rwa [LinearMap.BilinForm.flip_apply] at h
    exact hspan_le ((perp_facts hP hV hB hα hy).2 u hu')
  have hSmod_eq : AddSubgroup.toZModSubmodule 3 img = P := le_antisymm hSmod_le hP_le
  have hcard_img_C : Nat.card ↥img = Nat.card ↥C := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun v => ⟨Additive.toMul (ι.symm v.1), ?_⟩
        invFun := fun b => ⟨f b, ⟨b.1, b.2, rfl⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨b, hb, hfb⟩ := v.2
      have hv : v.1 = ι (Additive.ofMul b) := hfb.symm
      rw [hv, AddEquiv.symm_apply_apply]
      exact hb
    · intro v
      apply Subtype.ext
      simp [f]
    · intro b
      apply Subtype.ext
      simp [f]
  have hcard_img_P : Nat.card ↥img = Nat.card ↥P := by
    refine Nat.card_congr ?_
    exact Equiv.subtypeEquivRight (fun v => by
      rw [← hSmod_eq, AddSubgroup.mem_toZModSubmodule])
  have hPcard : Nat.card ↥P = 3 ^ 4 := by
    have hne : (B.flip y') ≠ 0 := by
      intro h0
      have h1 : (B.flip y') y' = 0 := by rw [h0]; rfl
      rw [LinearMap.BilinForm.flip_apply, hy] at h1
      exact absurd h1 (by decide)
    have h := card_ker_mul_eq_of_ne_zero (p := 3) hne
    rw [hV] at h
    have h243 : Nat.card ↥P * 3 = 243 := by
      change Nat.card ↥(LinearMap.ker (B.flip y')) * 3 = 243
      simpa using h
    omega
  have hcardC : Nat.card ↥C = 3 ^ 4 := by
    rw [← hcard_img_C, hcard_img_P, hPcard]
  refine ⟨hcardC, ?_⟩
  intro hyC
  have hyimg : y' ∈ img := ⟨y, hyC, rfl⟩
  have hyP : y' ∈ P := by
    rw [← hSmod_eq, AddSubgroup.mem_toZModSubmodule]
    exact hyimg
  have h0 : (B.flip y') y' = 0 := LinearMap.mem_ker.mp hyP
  rw [LinearMap.BilinForm.flip_apply, hy] at h0
  exact absurd h0 (by decide)

end CFSG.StandardType.E6QTwo

end
