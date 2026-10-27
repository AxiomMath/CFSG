module

public import CFSG.Quasithin.Background.RonanH155Std
public import CFSG.Quasithin.Background.RonanH155Tconj
public import CFSG.Quasithin.Background.RonanH154Main

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.RonanH154

theorem normal_form_plus_T
    {a b : Fin 24} (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ Γ : Subgroup P24} (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O)
    (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B) (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O)
    (hTS : ∀ g ∈ T₀, g • S = S) (hL : M22g a b ≤ Γ) (hΓ : Γ = M2ab a b)
    (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ) :
    ∃ c ∈ AutPerm, c a = 0 ∧ c b = 1 ∧ c • O = Ostd ∧ c • S = Sstd ∧ c • B = Bstd ∧
      conjSubg c Γ = mog22plus ∧ conjSubg c T₀ ⊓ mog22plus = P2 := by
  obtain ⟨c, hc, hca, hO', hS', hB', hT⟩ :=
    normal_form hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ.le hSyl
  have hcΓ : conjSubg c Γ = M2ab (c a) (c b) := by
    rw [hΓ]
    exact M2ab_conj hc a b
  have hplus : conjSubg c Γ = mog22plus := by
    rcases hca with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hcΓ, h0, h1, M2ab_zero_one]
    · rw [hcΓ, h0, h1, M2ab_one_zero]
  have hT' : conjSubg c T₀ ⊓ mog22plus = P2 := by
    rcases hT with ⟨h1, -⟩ | ⟨-, h2⟩
    · exfalso
      have h3 : mog22 = mog22plus := h1.symm.trans hplus
      exact ePerm_notMem_mog22 (by rw [h3]; exact ePerm_mem_mog22plus)
    · exact h2
  rcases hca with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨c, hc, h0, h1, hO', hS', hB', hplus, hT'⟩
  · refine ⟨ePerm * c, AutPerm.mul_mem ePerm_mem_mog22plus.1 hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h0, ePerm_one]
    · rw [Equiv.Perm.mul_apply, h1, ePerm_zero]
    · rw [mul_smul, hO', ePerm_smul_Ostd]
    · rw [mul_smul, hS', ePerm_smul_Sstd]
    · rw [mul_smul, hB', ePerm_smul_Bstd]
    · rw [conjSubg_mul, hplus, conjSubg_eq_self ePerm_mem_mog22plus]
    · have e1 : conjSubg ePerm mog22plus = mog22plus := conjSubg_eq_self ePerm_mem_mog22plus
      have e2 : conjSubg ePerm P2 = P2 := conjSubg_eq_self ePerm_mem_P2
      calc conjSubg (ePerm * c) T₀ ⊓ mog22plus
          = conjSubg ePerm (conjSubg c T₀) ⊓ conjSubg ePerm mog22plus := by rw [conjSubg_mul, e1]
        _ = conjSubg ePerm (conjSubg c T₀ ⊓ mog22plus) := (conjSubg_inf _ _ _).symm
        _ = conjSubg ePerm P2 := by rw [hT']
        _ = P2 := e2

theorem main155 {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ)
    (hreal : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24)
      (golayC ⊔ Subgroup.zpowers (pairVec a b))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Γ = M2ab a b → Concl155 ρ a b O S B T₀ := by
  intro hΓ
  obtain ⟨c, hc, hca, hcb, hcO, hcS, hcB, hcΓ, hcT⟩ :=
    normal_form_plus_T hab hO haO hbO hS hBS haB hbB hTO hTS hL hΓ hSyl
  obtain ⟨φ, hφ, e, he⟩ := exists_iso_of_conj hc hca hcb hcΓ hreal
  have key := Concl155_of_transport c hc hcΓ ρ Rc φ hφ e he a b O S B T₀
  rw [hca, hcb, hcO, hcS, hcB] at key
  exact key (std155 (conjSubg c T₀) hcT)

end CFSG.Quasithin.RonanH155
