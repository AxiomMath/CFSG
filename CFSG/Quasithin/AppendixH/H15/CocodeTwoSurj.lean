module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoNorm
public import CFSG.Quasithin.AppendixH.Common.OctadYAct

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem surj_24 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 24) :
    ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 8)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf (MY Γ (Yd d a b O)) :=
  exists_hom_alt8 hM.cfg.octad (Subgroup.ext (mem_mY_24 hM hd))

theorem surj_23 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 23) :
    ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf (MY Γ (Yd d a b O)) :=
  exists_hom_alt7 hM.cfg.octad hM.cfg.a_O (mem_mY_23 hM hd)

theorem surj_22a (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22)
    (hΓ : Γ = M22g a b) :
    ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 6)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf (MY Γ (Yd d a b O)) :=
  exists_hom_alt6 hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne (mem_mY_22a hM hd hΓ)

theorem surj_22b (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22)
    (hΓ : Γ ≠ M22g a b) :
    ∃ π : ↥(MY Γ (Yd d a b O)) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf (MY Γ (Yd d a b O)) := by
  have hΓ2 : Γ = M2ab a b := by
    rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨_, h1, h2⟩
    · exact absurd (h24.symm.trans hd) (by norm_num)
    · exact absurd (h23.symm.trans hd) (by norm_num)
    · exact (eq_M22g_or_eq_M2ab hM.cfg.ne h1 h2).resolve_left hΓ
  exact exists_hom_perm6 hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne (mem_mY_22b hM hd hΓ2)

end CFSG.ASVolI.AppH
