module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChainOct24
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoChainOct22
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoFrame
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoVec
public import CFSG.Quasithin.AppendixH.Common.OctadFixLe
public import CFSG.Quasithin.Background.RonanH143NF

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
  CFSG.Quasithin.AppendixH.H14

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem conj_mem_mog22plus {a b : Fin 24} (hab : a ≠ b) {τ : S24}
    (hτ : τ ∈ M24g) (h0 : τ 0 = a) (h1 : τ 1 = b) {Γ : Subgroup S24}
    (hΓ : Γ ≤ M2ab a b) (x : ↥Γ) : τ⁻¹ * (x : S24) * τ ∈ mog22plus := by
  have hmem : τ⁻¹ * (x : S24) * τ ∈ M2ab 0 1 := by
    rw [mem_M2ab_iff 0 1 (by decide)]
    obtain ⟨hxM, hxcase⟩ := (mem_M2ab_iff a b hab (x : S24)).1 (hΓ x.2)
    refine ⟨?_, ?_⟩
    · exact M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hτ) hxM) hτ
    · have hτa : τ⁻¹ a = 0 := by rw [← h0]; simp
      have hτb : τ⁻¹ b = 1 := by rw [← h1]; simp
      rcases hxcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        exact ⟨by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, ha, hτa],
          by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hb, hτb]⟩
      · right
        exact ⟨by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, ha, hτb],
          by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hb, hτa]⟩
  have hM01 : M2ab 0 1 = mog22plus := CFSG.Quasithin.RonanH143.M2ab_zero_one
  rwa [hM01] at hmem

theorem offender_unique (hM : MCtx false d a b O Tr S B T₀ Γ ρ β)
    {A : Subgroup (MulAut V)} (hAT : A ≤ rImg ρ (T₀ ⊓ Γ)) (hA : H.IsFOneOffender ρ.range A) :
    A = rImg ρ (octFix O) := by
  haveI : Finite V := mctx_finite hM
  have hρ : Function.Injective ρ := mctx_rho_injective hM
  have hAρ : A ≤ ρ.range := hA.1.1
  have hA1 : A ≠ ⊥ := hA.1.2.1
  have hA2 : IsElemAbelian2 A := hA.1.2.2
  have hF : rkIdx (fixV A) ≤ rk ↥A + 1 := hA.2
  have hex : ∃ O' : Finset (Fin 24), IsOctad O' ∧ octFix O' ≤ Γ ∧ A = rImg ρ (octFix O') := by
    by_cases hd : d = 22
    · obtain ⟨τ, hτ, -, h0, h1⟩ :=
        exists_flag_pair hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne
      rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨h22, _, h2⟩
      · exact absurd (h24.symm.trans hd) (by norm_num)
      · exact absurd (h23.symm.trans hd) (by norm_num)
      · have hreal : IsMathModule false 22 a b Γ ρ := by
          rw [← hd]; exact ⟨β, hM.real⟩
        have hγ : ∀ γ : ↥Γ, τ⁻¹ * (γ : S24) * τ ∈ mog22plus :=
          fun γ => conj_mem_mog22plus hM.cfg.ne hτ h0 h1 h2 γ
        obtain ⟨e, he0⟩ := exists_equiv_cocode22 hM.cfg.ne hτ h0 h1 h2 hreal
        exact chain_octad22 hτ (mctx_le_M24 hM) ρ hρ e hγ
          (fun γ v => he0 γ v (hγ γ)) hAρ hA2 hA1 hF
    · have hΓ : Γ ≤ AutPerm := mctx_le_M24 hM
      obtain ⟨e, he⟩ := exists_equiv_cocode (d := d) hd hΓ ⟨β, hM.real⟩
      exact chain_octad24 hΓ ρ hρ e he hAρ hA2 hA1 hF
  obtain ⟨O', hO', hle, hAeq⟩ := hex
  have hstep : octFix O' ≤ octStab O := by
    intro x hx
    have hxΓ : x ∈ Γ := hle hx
    have hxA : ρ ⟨x, hxΓ⟩ ∈ A := by
      rw [hAeq, rImg]
      exact Subgroup.mem_map.2 ⟨⟨x, hxΓ⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have hxT : ρ ⟨x, hxΓ⟩ ∈ rImg ρ (T₀ ⊓ Γ) := hAT hxA
    rw [rImg] at hxT
    obtain ⟨y, hy, hyρ⟩ := Subgroup.mem_map.1 hxT
    have hyeq : y = ⟨x, hxΓ⟩ := hρ hyρ
    have hyT : (y : S24) ∈ T₀ ⊓ Γ := Subgroup.mem_subgroupOf.1 hy
    have hval : (y : S24) = x := congrArg Subtype.val hyeq
    rw [hval] at hyT
    have hxT0 : x ∈ T₀ := (Subgroup.mem_inf.1 hyT).1
    exact mctx_mY_le hM (mctx_T_le_mY hM (Subgroup.mem_inf.2 ⟨hxT0, hxΓ⟩))
  have hOeq : O' = O := eq_of_octFix_le_octStab hM.cfg.octad hO' hstep
  rw [hOeq] at hAeq
  exact hAeq

end CFSG.ASVolI.AppH


