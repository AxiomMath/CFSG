module

public import CFSG.Quasithin.Background.E1Sec7Two

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

section Induction

variable {Q : Type*} [Group Q] [Finite Q]

theorem inEFor_of_quotient {i : ℕ} {N : Subgroup Q} [N.Normal]
    (hIH : InE i (⊤ : Subgroup (Q ⧸ N))) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hNM : ∀ Ω : Set (Subgroup Q), IsInvColl ⊤ Ω →
      N ≤ eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set Q))) :
    InEFor i ⊤ T := by
  intro Ω hΩ
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set W := weakClosure T Ω with hW
  set M : Subgroup Q := eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (W : Set Q)) with hM
  have hM1 : eGen i ⊤ T Ω ≤ M := le_sup_left
  have hM2 : Subgroup.normalizer (W : Set Q) ≤ M := fun x hx =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩
  have hTM : T ≤ M := (le_normalizer_weakClosure hΩ).trans hM2
  have hTb : IsSylowIn 2 (T.map π) ⊤ := isSylowIn_two_map_top hπs hT
  have hΩb : IsInvColl ⊤ (Subgroup.map π '' Ω) := isInvColl_map_of_surjective π hπs hΩ
  have hIHT := hIH _ hTb _ hΩb
  have hMπ : ⊤ ≤ M.map π := by
    refine hIHT.symm.trans_le (sup_le ?_ ?_)
    ·
      refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_
      obtain ⟨A₀, hA₀, rfl⟩ := hB
      obtain ⟨n, hn, hnA⟩ := exists_mem_conj_le_of_map_le hT
        (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) hBT
      have hAΩ : conjSub n A₀ ∈ Ω := hΩ.conj A₀ hA₀ n (Subgroup.mem_top n)
      have hAT : conjSub n A₀ ≤ T := by
        intro y hy
        rw [mem_conjSub_iff] at hy
        have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
        have := hnA _ hy
        rwa [e] at this
      have hAeq : (conjSub n A₀).map π = A₀.map π := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have hy' : y ∈ conjSub n A₀ := hy
          rw [mem_conjSub_iff] at hy'
          refine ⟨n⁻¹ * y * n, hy', ?_⟩
          have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
          simp [hπn]
        · rintro _ ⟨a, ha, rfl⟩
          refine ⟨n * a * n⁻¹, mem_conjSub_of_mem ha, ?_⟩
          have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
          simp [hπn]
      have hK' : IsE i ⊤ (T.map π) ((conjSub n A₀).map π) K := by
        rw [hAeq]
        exact hK
      obtain ⟨J, hJ, hJK⟩ := ten_seven hT hAT (hΩ.isElemAbelian _ hAΩ) hK'
      have hJM : J ≤ M := (le_eGen hAΩ hAT hJ).trans hM1
      calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := le_twoResidual_sup_of_isSylowIn hK.2.2.1
        _ ≤ (twoResidual J).map π ⊔ T.map π := by
          rw [hJK]
          exact sup_le_sup le_rfl inf_le_left
        _ ≤ M.map π := sup_le (Subgroup.map_mono ((twoResidual_le J).trans hJM))
          (Subgroup.map_mono hTM)
    ·
      intro x hx
      rw [weakClosure_map_quotient hT hΩ] at hx
      obtain ⟨g, rfl⟩ := hπs x
      obtain ⟨g', hg', hg'x⟩ := exists_mem_normalizer_of_mem_normalizer_map hT hΩ hx.2
      exact ⟨g', hM2 hg', hg'x⟩
  have hNM : N ≤ M := hNM Ω hΩ
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨m, hm, hmq⟩ := hMπ (Subgroup.mem_top (π q))
  have h1 : m⁻¹ * q ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
    change (π m)⁻¹ * π q = 1
    rw [hmq]
    exact inv_mul_cancel _
  have e : q = m * (m⁻¹ * q) := by group
  rw [e]
  exact M.mul_mem hm (hNM h1)

end Induction

end E1

end CFSG.Quasithin
