module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexMono

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex

theorem conj_mem_autStab_of_mem {G : Type} [Group G] {P : Subgroup G} {p : G} (hp : p ∈ P) :
    (MulAut.conj p : MulAut G) ∈ autStab P := fun x => by
  show x ∈ P ↔ p * x * p⁻¹ ∈ P
  constructor
  · exact fun hx => P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  · intro h
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) h) hp
    simpa [mul_assoc] using this

@[expose] def d3PsiInn : D →* ↥(MulAut.conj : D →* MulAut D).range :=
  (MulAut.conj : D →* MulAut D).rangeRestrict

@[simp] theorem coe_d3PsiInn (x : D) : (d3PsiInn x : MulAut D) = MulAut.conj x := rfl

section K3

theorem conj_mem_K3 (x : D) : (MulAut.conj x : MulAut D) ∈ autStab d4H ⊔ autStab d4N := by
  have hx : (MulAut.conj x : MulAut D) ∈ (d4H ⊔ d4N).map (MulAut.conj : D →* MulAut D) :=
    ⟨x, by rw [d4H_sup_d4N]; exact Subgroup.mem_top x, rfl⟩
  rw [Subgroup.map_sup] at hx
  have h1 : d4H.map (MulAut.conj : D →* MulAut D) ≤ autStab d4H := by
    rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_autStab_of_mem hh
  have h2 : d4N.map (MulAut.conj : D →* MulAut D) ≤ autStab d4N := by
    rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_autStab_of_mem hh
  exact sup_le_sup h1 h2 hx

theorem inn_le_K3 : (MulAut.conj : D →* MulAut D).range ≤ autStab d4H ⊔ autStab d4N := by
  rintro _ ⟨x, rfl⟩
  exact conj_mem_K3 x

@[expose] noncomputable def d3Psi : D →* ↥(autStab d4H ⊔ autStab d4N) :=
  (MulAut.conj : D →* MulAut D).codRestrict _ conj_mem_K3

@[simp] theorem coe_d3Psi (x : D) : (d3Psi x : MulAut D) = MulAut.conj x := rfl

end K3

section Act

theorem d3Psi_smul (x : D) (v : HexVtx) : d3Psi x • v = x • v := by
  rcases v with p | l
  · exact congrArg Sum.inl (conj_smul_pt x p)
  · exact congrArg Sum.inr (conj_smul_ln x l)

theorem hexPtK3 :
    HexPt ↥(autStab d4H ⊔ autStab d4N) hexGraph (Sum.inl 0) (Sum.inl hexB0F) :=
  HexPt.mono d3Psi d3Psi_smul hexPtD

theorem hexLnK3 :
    HexLn ↥(autStab d4H ⊔ autStab d4N) hexGraph (Sum.inr 0) (Sum.inl hexY0F) (Sum.inr hexM0F) :=
  HexLn.mono d3Psi d3Psi_smul hexLnD

theorem cover_K3 (a : HexVtx) :
    ∃ y : ↥(autStab d4H ⊔ autStab d4N),
      y • (Sum.inl 0 : HexVtx) = a ∨ y • (Sum.inr 0 : HexVtx) = a := by
  obtain ⟨y, hy⟩ := hexGeometryD.cover a
  exact ⟨d3Psi y, by simpa only [d3Psi_smul] using hy⟩

end Act

end CFSG.Quasithin.D4Hex
