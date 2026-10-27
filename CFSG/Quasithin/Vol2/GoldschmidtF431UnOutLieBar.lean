module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

section Bar

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev fbar : MulAut (Xg h) := fa h (barE h)

@[expose] def Pfx : Subgroup (Xg h) where
  carrier := {x | x ∈ Psy h ∧ fbar h x = x}
  mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨(Psy h).mul_mem ha hb, by rw [map_mul, ha', hb']⟩
  one_mem' := ⟨(Psy h).one_mem, map_one _⟩
  inv_mem' := fun ⟨ha, ha'⟩ => ⟨(Psy h).inv_mem ha, by rw [map_inv, ha']⟩

theorem mem_Pfx {x : Xg h} : x ∈ Pfx h ↔ x ∈ Psy h ∧ fbar h x = x := Iff.rfl

theorem fbar_mul_fa (φ : K ≃+* K) : fbar h * fa h φ = fa h φ * fbar h := by
  rw [fa_mul, fa_mul, aut_comm h]

theorem fbar_fa_apply (φ : K ≃+* K) (x : Xg h) : fbar h (fa h φ x) = fa h φ (fbar h x) := by
  have := congrArg (fun α : MulAut (Xg h) => α x) (fbar_mul_fa h φ)
  exact this

theorem fStab_Pfx [CharP K 2] : FStab h (Pfx h) := by
  intro φ x
  rw [mem_Pfx, mem_Pfx, fStab_Psy h φ x, fbar_fa_apply]
  exact and_congr_right fun _ => (fa h φ).injective.eq_iff

theorem fbar_mul_cj (s : Xg h) : fbar h * cj h s = cj h (fbar h s) * fbar h := by
  have e := fa_mul_cj_mul_inv h (barE h) s
  rw [← e]
  group

theorem cj_fa_comm_fbar_iff (s : Xg h) (φ : K ≃+* K) :
    cj h s * fa h φ * fbar h = fbar h * (cj h s * fa h φ) ↔ fbar h s = s := by
  have e1 : cj h s * fa h φ * fbar h = cj h s * fbar h * fa h φ := by
    rw [mul_assoc, ← fbar_mul_fa h φ, ← mul_assoc]
  have e2 : fbar h * (cj h s * fa h φ) = cj h (fbar h s) * fbar h * fa h φ := by
    rw [← mul_assoc, fbar_mul_cj]
  rw [e1, e2, mul_left_inj, mul_left_inj]
  constructor
  · intro e
    exact ((conj_inj h).1 e).symm
  · intro e
    rw [e]

theorem spTf_Ssd (F : Subgroup (K ≃+* K)) [CharP K 2] :
    spTf (Ssd h (Psy h) (fStab_Psy h) F) (fbar h) = Ssd h (Pfx h) (fStab_Pfx h) F := by
  ext α
  rw [spTf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs, φ, hφ, rfl⟩, hc⟩
    exact ⟨s, ⟨hs, (cj_fa_comm_fbar_iff h s φ).1 hc⟩, φ, hφ, rfl⟩
  · rintro ⟨s, ⟨hs, hfs⟩, φ, hφ, rfl⟩
    exact ⟨⟨s, hs, φ, hφ, rfl⟩, (cj_fa_comm_fbar_iff h s φ).2 hfs⟩

end Bar

end CFSG.Quasithin.H13.F431.Un.OL
