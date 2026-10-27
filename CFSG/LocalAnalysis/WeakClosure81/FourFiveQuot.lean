module

public import CFSG.Quasithin.Background.E1SolvProduct
public import CFSG.Quasithin.Background.E1Sec7Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

theorem fourFive_eGen_map_le {N T : Subgroup Q} [N.Normal] (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) (j : ℕ) :
    E1.eGen j ⊤ (T.map (QuotientGroup.mk' N)) (Subgroup.map (QuotientGroup.mk' N) '' Ω) ≤
      (E1.eGen j ⊤ T Ω ⊔ T).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_
  obtain ⟨A₀, hA₀, rfl⟩ := hB
  obtain ⟨n, hn, hnA⟩ := E1.exists_mem_conj_le_of_map_le hT
    (E1.isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) hBT
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
  have hK' : E1.IsE j ⊤ (T.map π) ((conjSub n A₀).map π) K := by
    rw [hAeq]; exact hK
  obtain ⟨J, hJ, hJK⟩ := E1.ten_seven hT hAT (hΩ.isElemAbelian _ hAΩ) hK'
  calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := E1.le_twoResidual_sup_of_isSylowIn hK.2.2.1
    _ ≤ (twoResidual J).map π ⊔ T.map π := by
        rw [hJK]
        exact sup_le_sup le_rfl inf_le_left
    _ ≤ (E1.eGen j ⊤ T Ω ⊔ T).map π := by
        refine sup_le ?_ ?_
        · exact (Subgroup.map_mono ((twoResidual_le J).trans (E1.le_eGen hAΩ hAT hJ))).trans
            (Subgroup.map_mono le_sup_left)
        · exact Subgroup.map_mono le_sup_right

theorem fourFive_step {N T : Subgroup Q} [N.Normal] (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) (j : ℕ)
    (hN : (N : Set Q) ⊆ (E1.eGen j ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q))
    (hbar : ((E1.eGen j ⊤ (T.map (QuotientGroup.mk' N))
        (Subgroup.map (QuotientGroup.mk' N) '' Ω) : Subgroup (Q ⧸ N)) : Set (Q ⧸ N)) *
      (Subgroup.normalizer (E1.weakClosure (T.map (QuotientGroup.mk' N))
        (Subgroup.map (QuotientGroup.mk' N) '' Ω) : Set (Q ⧸ N)) : Set (Q ⧸ N)) =
        Set.univ) :
    ((E1.eGen j ⊤ T Ω : Subgroup Q) : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro g
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set Tbar : Subgroup (Q ⧸ N) := T.map π with hTbar
  set Ωbar : Set (Subgroup (Q ⧸ N)) := Subgroup.map π '' Ω with hΩbar
  have hTbar' : IsSylowIn 2 Tbar ⊤ := E1.isSylowIn_two_map_top hπs hT
  have hΩbar' : E1.IsInvColl ⊤ Ωbar := E1.isInvColl_map_of_surjective π hπs hΩ
  set E : Subgroup Q := E1.eGen j ⊤ T Ω with hE
  set W : Subgroup Q := E1.weakClosure T Ω with hW
  set Nrm : Subgroup Q := Subgroup.normalizer (W : Set Q) with hNrm
  have hTN : T ≤ Nrm := E1.le_normalizer_weakClosure hΩ
  have hTE : T ≤ Subgroup.normalizer (E : Set Q) := E1.le_normalizer_eGen j hΩ
  obtain ⟨ebar, hebar, nbar, hnbar, hgn⟩ := by
    have hmem : π g ∈
        (E1.eGen j ⊤ Tbar Ωbar : Set (Q ⧸ N)) *
          (Subgroup.normalizer (E1.weakClosure Tbar Ωbar : Set (Q ⧸ N)) : Set (Q ⧸ N)) := by
      rw [hbar]
      exact Set.mem_univ _
    rwa [Set.mem_mul] at hmem
  obtain ⟨m, hm, hmeb⟩ := fourFive_eGen_map_le (N := N) hT hΩ j hebar
  have hEsup : (↑(E ⊔ T) : Set Q) = (E : Set Q) * (T : Set Q) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E T hTE
  have hm' : m ∈ (E : Set Q) * (T : Set Q) := hEsup ▸ hm
  rw [Set.mem_mul] at hm'
  obtain ⟨e, he, t, ht, het⟩ := hm'
  have hnbar' : nbar ∈ Subgroup.normalizer (W.map π : Set (Q ⧸ N)) := by
    rw [← E1.weakClosure_map_quotient hT hΩ]
    exact hnbar
  obtain ⟨gn, hgn'⟩ := hπs nbar
  obtain ⟨nn, hnn, hnnbar⟩ := E1.exists_mem_normalizer_of_mem_normalizer_map hT hΩ
    (g := gn) (by rw [hgn']; exact hnbar')
  have hπeq : π (e * t * nn) = π g := by
    have h1 : π (e * t) = ebar := by rw [het, hmeb]
    rw [map_mul, h1, hnnbar, hgn']
    exact hgn
  set ρ : Q := g * (e * t * nn)⁻¹ with hρdef
  have hρ : ρ ∈ N := by
    rw [hρdef, ← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hπeq]
    exact mul_inv_cancel _
  have hρ₁ : e⁻¹ * ρ * e ∈ N := by
    simpa using Subgroup.Normal.conj_mem inferInstance ρ hρ e⁻¹
  obtain ⟨e₃, he₃, n₃, hn₃, he₃n₃⟩ := by
    have := hN hρ₁
    rwa [Set.mem_mul] at this
  refine Set.mem_mul.mpr ⟨e * e₃, E.mul_mem he he₃, n₃ * t * nn,
    Nrm.mul_mem (Nrm.mul_mem hn₃ (hTN ht)) hnn, ?_⟩
  have hkey : (e * e₃) * (n₃ * t * nn) = g := by
    have h1 : (e * e₃) * (n₃ * t * nn) = e * (e₃ * n₃) * t * nn := by group
    rw [h1, he₃n₃, hρdef]
    group
  exact hkey

end CFSG.LocalAnalysis.WeakClosure81
