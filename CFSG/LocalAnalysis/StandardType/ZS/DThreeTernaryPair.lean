module

public import CFSG.Fischer.Classification.Orthogonal3.Local
import CFSG.Fischer.Classification.Recognition.R3Order
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification

theorem exists_mem_reflGroup_act_eq_pair {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f) (hm : 5 ≤ m)
    {a b a' b' : Fin m → ZMod 3} (ha : f a a = 1) (hb : f b b = 1) (hab : f a b = 0)
    (ha' : f a' a' = 1) (hb' : f b' b' = 1) (hab' : f a' b' = 0) :
    ∃ g ∈ F3.reflGroup f, F3.act g a = a' ∧ F3.act g b = b' := by
  obtain ⟨g₁, hg₁, hg₁a⟩ := Recognition.R3.exists_mem_act_eq hf (by omega) ha ha'
  have hiso₁ := F3.isIsom_of_mem hf hg₁
  have hb₁ : f (F3.act g₁ b) (F3.act g₁ b) = 1 := by
    rw [hiso₁.norm, hb]
  have hb₁a' : f (F3.act g₁ b) a' = 0 := by
    rw [← hg₁a, hiso₁ b a, hf.symm b a]
    exact hab
  have hb'a' : f b' a' = 0 := by
    rw [hf.symm b' a']
    exact hab'
  let x₁ : F3.perpOne f a' := ⟨F3.act g₁ b, F3.mem_perpOne.2 hb₁a'⟩
  let x₂ : F3.perpOne f a' := ⟨b', F3.mem_perpOne.2 hb'a'⟩
  let e : F3.perpOne f a' ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne ha', Module.finrank_fin_fun])
  let f' : LinearMap.BilinForm (ZMod 3) (Fin (m - 1) → ZMod 3) := restrictForm f e
  have hf' : IsF3Form f' := isF3Form_restrictForm hf ha' e
  have hx₁ : f' (e x₁) (e x₁) = 1 := by
    change restrictForm f e (e x₁) (e x₁) = 1
    rw [restrictForm_apply]
    exact hb₁
  have hx₂ : f' (e x₂) (e x₂) = 1 := by
    change restrictForm f e (e x₂) (e x₂) = 1
    rw [restrictForm_apply]
    exact hb'
  obtain ⟨g', hg', hact'⟩ := Recognition.R3.exists_mem_act_eq hf' (by omega) hx₁ hx₂
  have hrange : (perpToGL e).range = F3.reflGroup f' := range_perpToGL e (restrictForm_apply e)
  have hg'range : g' ∈ (perpToGL e).range := by
    rw [hrange]
    exact hg'
  rw [MonoidHom.mem_range] at hg'range
  obtain ⟨g₂, hg₂⟩ := hg'range
  have hact₂ : F3.act (g₂ : GL (Fin m) (ZMod 3)) (F3.act g₁ b) = b' := by
    have h := act_perpToGL e g₂ x₁
    rw [hg₂, hact'] at h
    exact (congrArg Subtype.val (e.injective h)).symm
  have ha₂ : F3.act (g₂ : GL (Fin m) (ZMod 3)) a' = a' :=
    F3.act_eq_of_mem_reflGroupPerp hf g₂.2
  refine ⟨(g₂ : GL (Fin m) (ZMod 3)) * g₁,
    mul_mem (F3.reflGroupPerp_le_reflGroup a' g₂.2) hg₁, ?_, ?_⟩
  · rw [F3.act_mul, hg₁a, ha₂]
  · rw [F3.act_mul, hact₂]

end CFSG.StandardType.ZS
