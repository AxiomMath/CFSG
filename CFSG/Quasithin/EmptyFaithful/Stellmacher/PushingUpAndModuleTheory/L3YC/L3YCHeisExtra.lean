module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCHeisMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

namespace Stellmacher.PU.L3YC

theorem isExtraspecial_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.IsExtraspecial 2 H) : CFSG.IsExtraspecial 2 G := by
  have hc : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
    Subgroup.map_center_eq e
  let q : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
    QuotientGroup.congr _ _ e hc
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.IsExtraspecial.center_order_p 2 H
  · have hq := CFSG.IsExtraspecial.quotient_elementary_abelian 2 H
    exact
      { is_comm := ⟨fun a b => q.injective (by
          rw [map_mul, map_mul]
          exact hq.toIsMulCommutative.is_comm.comm _ _)⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => q.injective (by
          rw [map_pow, map_one]
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hq.exponent_dvd_p (q a)) }
  · have := CFSG.IsExtraspecial.quotient_nontrivial 2 H
    exact q.toEquiv.nontrivial

def axg (j : Fin 3) : Heis := ⟨Pi.single j 1, 0, 0⟩
def byg (i : Fin 3) : Heis := ⟨0, Pi.single i 1, 0⟩
def cwg : Heis := ⟨0, 0, 1⟩

theorem heis_top (T : Subgroup Heis) (hax : ∀ j, axg j ∈ T) (hby : ∀ i, byg i ∈ T)
    (hcw : cwg ∈ T) : T = ⊤ := by
  refine top_unique fun h _ => ?_
  have hA : ∀ (t : ZMod 2) (j : Fin 3), (⟨t • Pi.single j 1, 0, 0⟩ : Heis) ∈ T := by
    intro t j
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · convert T.one_mem using 1
      ext <;> simp
    · simpa [axg] using hax j
  have hB : ∀ (t : ZMod 2) (j : Fin 3), (⟨0, t • Pi.single j 1, 0⟩ : Heis) ∈ T := by
    intro t j
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · convert T.one_mem using 1
      ext <;> simp
    · simpa [byg] using hby j
  have hC : ∀ t : ZMod 2, (⟨0, 0, t⟩ : Heis) ∈ T := by
    intro t
    have ht : t = 0 ∨ t = 1 := by revert t; decide
    rcases ht with rfl | rfl
    · exact T.one_mem
    · exact hcw
  have hAx : ∀ x : Fin 3 → ZMod 2, (⟨x, 0, 0⟩ : Heis) ∈ T := by
    intro x
    have : (⟨x, 0, 0⟩ : Heis) = ⟨x 0 • Pi.single 0 1, 0, 0⟩ * ⟨x 1 • Pi.single 1 1, 0, 0⟩ *
        ⟨x 2 • Pi.single 2 1, 0, 0⟩ := by
      ext i
      · fin_cases i <;> simp
      · simp
      · simp
    rw [this]
    exact T.mul_mem (T.mul_mem (hA _ _) (hA _ _)) (hA _ _)
  have hBy : ∀ y : Fin 3 → ZMod 2, (⟨0, y, 0⟩ : Heis) ∈ T := by
    intro y
    have : (⟨0, y, 0⟩ : Heis) = ⟨0, y 0 • Pi.single 0 1, 0⟩ * ⟨0, y 1 • Pi.single 1 1, 0⟩ *
        ⟨0, y 2 • Pi.single 2 1, 0⟩ := by
      ext i
      · simp
      · fin_cases i <;> simp
      · simp
    rw [this]
    exact T.mul_mem (T.mul_mem (hB _ _) (hB _ _)) (hB _ _)
  have : h = ⟨h.x, 0, 0⟩ * ⟨0, h.y, 0⟩ * ⟨0, 0, h.w + h.x ⬝ᵥ h.y⟩ := by
    ext
    · simp
    · simp
    · simp only [Heis.mul_w, Heis.mul_x, Heis.mul_y, dotProduct_zero, zero_dotProduct, add_zero, zero_add]
      rw [show h.x ⬝ᵥ h.y + (h.w + h.x ⬝ᵥ h.y) = h.w + (h.x ⬝ᵥ h.y + h.x ⬝ᵥ h.y) by ring,
        Heis.zmod2_add_self, add_zero]
  rw [this]
  exact T.mul_mem (T.mul_mem (hAx _) (hBy _)) (hC _)

theorem cwg_eq : cwg = (byg 0 * axg 0)⁻¹ * (axg 0 * byg 0) := by
  ext i
  · simp [cwg, byg, axg, Heis.zmod2_add_self]
  · simp [cwg, byg, axg, Heis.zmod2_add_self]
  · simp [cwg, byg, axg, Heis.zmod2_add_self]

theorem transvection_row (j : Fin 3) (hne : (0 : Fin 5) ≠ ⟨j.val + 1, by omega⟩) :
    SpecialLinearGroup.transvection hne (1 : ZMod 2) = heisHom (axg j) := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection, heisHom_coe]
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [heisMat, Matrix.single_apply, axg]

theorem transvection_col (i : Fin 3) (hne : (⟨i.val + 1, by omega⟩ : Fin 5) ≠ 4) :
    SpecialLinearGroup.transvection hne (1 : ZMod 2) = heisHom (byg i) := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection, heisHom_coe]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [heisMat, Matrix.single_apply, byg]

theorem pCore_extraspecial_of_config {B : Type} [Group B]
    (θ : B →* SpecialLinearGroup (Fin 5) (ZMod 2)) (hθ : Function.Injective θ)
    (α : B →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαk : α.ker = CFSG.pCore 2 B)
    (hblk : ∀ x : B, blkAt 1 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 1 3 ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hc : IsCross 1 3 k l), ∃ p ∈ CFSG.pCore 2 B,
      θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) :
    CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 B) ∧ Nat.card ↥(CFSG.pCore 2 B) = 2 ^ 7 := by
  set N := CFSG.pCore 2 B with hN
  have hS : N.map θ = heisHom.range := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hα1 : α x = 1 := by
        rw [← MonoidHom.mem_ker, hαk]
        exact hx
      obtain ⟨hb1, hbf⟩ := hblk x
      have hb : blkAt 1 3 (by norm_num) ((θ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
        rw [hb1, hα1]
        rfl
      obtain ⟨h, hh⟩ := eq_heisMat_of_blockForm hbf hb
      exact ⟨h, Subtype.ext hh.symm⟩
    · have hax : ∀ j : Fin 3, heisHom (axg j) ∈ N.map θ := by
        intro j
        have hne : (0 : Fin 5) ≠ ⟨j.val + 1, by omega⟩ := by
          intro h
          have := congrArg Fin.val h
          simp at this
        obtain ⟨p, hp, hpθ⟩ := hcross 0 ⟨j.val + 1, by omega⟩ (Or.inl ⟨by simp, by simp, by
          simp; omega⟩)
        refine ⟨p, hp, ?_⟩
        rw [hpθ]
        exact transvection_row j hne
      have hby : ∀ i : Fin 3, heisHom (byg i) ∈ N.map θ := by
        intro i
        have hne : (⟨i.val + 1, by omega⟩ : Fin 5) ≠ 4 := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        obtain ⟨p, hp, hpθ⟩ := hcross ⟨i.val + 1, by omega⟩ 4 (Or.inr ⟨by simp, by simp; omega,
          by simp⟩)
        refine ⟨p, hp, ?_⟩
        rw [hpθ]
        exact transvection_col i hne
      have hcw : heisHom cwg ∈ N.map θ := by
        rw [cwg_eq, map_mul, map_inv, map_mul, map_mul]
        exact (N.map θ).mul_mem ((N.map θ).inv_mem ((N.map θ).mul_mem (hby 0) (hax 0)))
          ((N.map θ).mul_mem (hax 0) (hby 0))
      have hT : (N.map θ).comap heisHom = ⊤ :=
        heis_top _ (fun j => hax j) (fun i => hby i) hcw
      rintro _ ⟨h, rfl⟩
      have : h ∈ (N.map θ).comap heisHom := hT ▸ Subgroup.mem_top h
      exact this
  let e : ↥N ≃* Heis :=
    (Subgroup.equivMapOfInjective N θ hθ).trans
      ((MulEquiv.subgroupCongr hS).trans (MonoidHom.ofInjective heisHom_injective).symm)
  exact ⟨isExtraspecial_of_mulEquiv e Heis.isExtraspecial,
    by rw [Nat.card_congr e.toEquiv]; exact Heis.card_heis⟩

end Stellmacher.PU.L3YC

end CFSG.Quasithin
