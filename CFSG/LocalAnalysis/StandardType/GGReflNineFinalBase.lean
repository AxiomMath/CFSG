
module

public import CFSG.LocalAnalysis.StandardType.GGReflNineSound
public import CFSG.LocalAnalysis.StandardType.GGReflNineChart
public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepChart
public import Certificates.Data.CFSGNative.NineAll.Check

@[expose] public section

namespace CFSG.NineAll

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem a1_of_conj {p : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (ε : V ≃ₗ[ZMod p] W) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (x : V) (xw : W) (hεx : ε x = xw)
    (h : ∃ t' ∈ A.map (rxConj ε).toMonoidHom, GGLinRefl t' ∧ t' xw ≠ xw ∧
      (∀ g ∈ A.map (rxConj ε).toMonoidHom, g * t' = t' * g) ∧
      ∀ s ∈ A.map (rxConj ε).toMonoidHom, GGLinRefl s → s xw ≠ xw → s = t') :
    ∃ t ∈ A, GGLinRefl t ∧ t x ≠ x ∧ (∀ g ∈ A, g * t = t * g) ∧
      ∀ s ∈ A, GGLinRefl s → s x ≠ x → s = t := by
  obtain ⟨t', ht'mem, ht'r, ht'm, ht'c, ht'u⟩ := h
  obtain ⟨t, htA, rfl⟩ := Subgroup.mem_map.mp ht'mem
  have hmv : ∀ g : V ≃ₗ[ZMod p] V, g x = x ↔ rxConj ε g xw = xw := by
    intro g
    rw [← hεx, rxConj_apply, LinearEquiv.symm_apply_apply]
    constructor
    · intro hg
      rw [hg]
    · intro hg
      exact ε.injective hg
  refine ⟨t, htA, (rxConj_isRefl ε t).mp ht'r, fun hx => ht'm ((hmv t).mp hx), ?_, ?_⟩
  · intro g hg
    apply (rxConj ε).injective
    rw [map_mul, map_mul]
    exact ht'c _ (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  · intro s hsA hsr hsm
    apply (rxConj ε).injective
    exact ht'u _ (Subgroup.mem_map.mpr ⟨s, hsA, rfl⟩) ((rxConj_isRefl ε s).mpr hsr)
      (fun hx => hsm ((hmv s).mpr hx))

theorem nine_core
    (P0 : Pt) [Fact P0.p.Prime] {Bstab : ℕ} {T : NTables} (hp2 : P0.p ≠ 2)
    (hok : verifyAllN P0 Bstab T = true) (G : ℕ → Refl) (hgens : P0.gens = (List.range 8).map G)
    {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V] (ε : V ≃ₗ[ZMod P0.p] P0.V)
    (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod P0.p) V) (x : V)
    (r : Fin 8 → (V ≃ₗ[ZMod P0.p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod P0.p] V)) (hrA : ∀ i, r i ∈ A)
    (hεh : ∀ i : Fin 8, ε (h i) = P0.vec (G i).h)
    (hεα : ∀ (i : Fin 8) w, α i w = P0.dot (P0.vec (G i).f) (ε w)) (hεx : ε x = P0.vec P0.x)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ P0.bound)
    (hstab : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x) ≤ Bstab)
    (t : V ≃ₗ[ZMod P0.p] V) (htA : t ∈ A) (htr : GGLinRefl t) (htm : t x ≠ x) :
    ZS.LinWeyl P0.p A ∨ ∃ t' ∈ A, GGLinRefl t' ∧ t' x ≠ x ∧ (∀ g ∈ A, g * t' = t' * g) ∧
      ∀ s ∈ A, GGLinRefl s → s x ≠ x → s = t' := by
  have hfr : ∀ r' ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r'.f) w • P0.vec r'.h := by
    intro r' hr'
    rw [hgens] at hr'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr'
    have hi' : i < 8 := List.mem_range.mp hi
    refine ⟨r ⟨i, hi'⟩, hrA _, fun w => ?_⟩
    rw [hr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hεh ⟨i, hi'⟩,
      hεα ⟨i, hi'⟩ (ε.symm w), LinearEquiv.apply_symm_apply]
  have hctx := ctxN_of_conj (T := T) hp2 (verifyAllN_elim hok).1 ε x hεx A hfr hrg hnt hcard hstab
  have hmem : rxConj ε t ∈ A.map (rxConj ε).toMonoidHom := Subgroup.mem_map.mpr ⟨t, htA, rfl⟩
  have htm' : rxConj ε t (P0.vec P0.x) ≠ P0.vec P0.x :=
    moving_conj ε x (P0.vec P0.x) 1 one_ne_zero (by rw [one_smul]; exact hεx) t htm
  rcases hctx.classification (verifyAllN_elim hok).2 hmem ((rxConj_isRefl ε t).mpr htr) htm' with hw | hA1
  · exact Or.inl (linWeyl_of_conj ε A hw)
  · exact Or.inr (a1_of_conj ε A x (P0.vec P0.x) hεx hA1)

theorem vec9_hvec (i : ℕ) (j : Fin 9) :
    ((((hvec8 i).getD j 0 : ℕ)) : ZMod 3) = (nineFrame9 ()).vec (hvec8 i ++ [0]) j := by
  show _ = ((((hvec8 i ++ [0]).getD j.val 0 : ℕ)) : ZMod 3)
  by_cases hj : j.val < 8
  · rw [getD_append_left' (hvec8 i) [0] j.val (by rw [pk5_hvec8_length]; exact hj)]
  · have hj8 : j.val = 8 := by have := j.isLt; omega
    rw [hj8, getD_append_right' (hvec8 i) [0] 8 (by rw [pk5_hvec8_length])
      (by simp [pk5_hvec8_length]), pk5_hvec8_length, Nat.sub_self,
      List.getD_eq_default (hvec8 i) 0 (by simp [pk5_hvec8_length])]
    simp

theorem vec9_alpha (i : Fin 8) (j : Fin 9) :
    (((alpha8 i.val).getD j 0 : ℕ) : ZMod 3) +
        (if j.val = 8 then (if (i : ℕ) = 0 then (1 : ZMod 3) else 0) else 0) =
      (nineFrame9 ()).vec (alpha8 i.val ++ [if i.val = 0 then 1 else 0]) j := by
  show _ = ((((alpha8 i.val ++ [if i.val = 0 then 1 else 0]).getD j.val 0 : ℕ)) : ZMod 3)
  by_cases hj : j.val < 8
  · rw [getD_append_left' (alpha8 i.val) _ j.val (by rw [pk5_alpha8_length]; exact hj),
      if_neg (by omega), add_zero]
  · have hj8 : j.val = 8 := by have := j.isLt; omega
    rw [hj8, getD_append_right' (alpha8 i.val) _ 8 (by rw [pk5_alpha8_length])
      (by simp [pk5_alpha8_length]), pk5_alpha8_length, Nat.sub_self,
      List.getD_eq_default (alpha8 i.val) 0 (by simp [pk5_alpha8_length]), if_pos rfl]
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0]
    · simp [hi0]

end CFSG.NineAll

namespace CFSG.StandardType

open CFSG.NineAll CFSG.TwoNodeSmall CFSG.ReflExt

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lr6NineAll_of_frames
    (h8 : ∃ T, verifyAllN (nineFrame8 ()) nineBstab T = true)
    (h9 : ∃ T, verifyAllN (nineFrame9 ()) nineBstab T = true) : LR6NineAll := by
  intro p _ hp3 V _ _ _ hdim h α x r hF hr A hrA hrg hnt hcard hstab hmov
  subst hp3
  obtain ⟨t, htA, htr, htm⟩ := hmov
  have hcard' : Nat.card A ≤ bound9 := le_trans hcard (le_of_eq (by decide +kernel))
  have hstab' : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) ≤ nineBstab :=
    le_trans hstab (le_of_eq (by decide +kernel))
  obtain ⟨D, u, hD, ⟨C0⟩⟩ := ninedep_chart hdim h α x hF
  rcases hD with rfl | rfl
  ·
    obtain ⟨T, hT⟩ := h8
    haveI : Fact (nineFrame8 ()).p.Prime := ⟨Nat.prime_three⟩
    exact nine_core (nineFrame8 ()) (by show (3 : ℕ) ≠ 2; decide) hT (fun k => ⟨alpha8 k, hvec8 k⟩) rfl
      C0.e h α x r hr A hrA (fun i => funext fun j => C0.h_eq i j)
      (fun i w => by
        rw [C0.α_eq i w]
        apply Finset.sum_congr rfl
        intro j _
        have hj : j.val ≠ 8 := by have := j.isLt; omega
        rw [if_neg hj, add_zero]
        rfl)
      (funext fun j => by rw [C0.x_eq j]; fin_cases j <;> rfl)
      hrg hnt hcard' hstab' t htA htr htm
  ·
    obtain ⟨C1⟩ := ninedep_chart_norm h α x u C0 hF.fix
    obtain ⟨T, hT⟩ := h9
    haveI : Fact (nineFrame9 ()).p.Prime := ⟨Nat.prime_three⟩
    exact nine_core (nineFrame9 ()) (by show (3 : ℕ) ≠ 2; decide) hT
      (fun k => ⟨alpha8 k ++ [if k = 0 then 1 else 0], hvec8 k ++ [0]⟩) rfl
      C1.e h α x r hr A hrA
      (fun i => funext fun j => by rw [C1.h_eq i j]; exact vec9_hvec i.val j)
      (fun i w => by
        rw [C1.α_eq i w]
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun z => z * C1.e w j) (vec9_alpha i j))
      (funext fun j => C1.x_eq j)
      hrg hnt hcard' hstab' t htA htr htm

end CFSG.StandardType

end
