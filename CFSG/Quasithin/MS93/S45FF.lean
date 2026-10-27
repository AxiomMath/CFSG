module

public import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S4AFcAbs

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S4A.F CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem isC1_of_offender (h14 : MS14AS) (hSQ : SQTKQuot) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) {A B : Subgroup (puAmalgam h.le).Universal}
    (hAs : A ≤ stab (puAmalgam h.le) δ)
    (hAn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal))
    (hBA : B ≤ A)
    (hBn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (B : Set (puAmalgam h.le).Universal))
    (hAc : ⁅A, A⁆ ≤ B) (hA2 : ∀ a ∈ A, a ^ 2 ∈ B) {Y : Subgroup (puAmalgam h.le).Universal}
    (hYs : Y ≤ stab (puAmalgam h.le) δ) (hY2 : ∀ y ∈ Y, y ^ 2 ∈ Qv (puAmalgam h.le) δ)
    (hYc : ⁅Y, Y⁆ ≤ Qv (puAmalgam h.le) δ)
    (hYq : Fintype.card F ≤ (Qv (puAmalgam h.le) δ).relIndex Y)
    {N : Subgroup (puAmalgam h.le).Universal} (hBN : B ≤ N) (hNA : N ≤ A) (hNY : ⁅N, Y⁆ ≤ B)
    (hNidx : N.relIndex A ≤ Fintype.card F)
    (hnt : ¬ ⁅A, Ltil h.le L δ⁆ ≤ ⁅A, Qv (puAmalgam h.le) δ⁆ ⊔ B) :
    IsC1 h.le L (Fintype.card F) δ A B := by
  have h20 := h.hyp20
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨β, hδβ⟩ := exists_adj _ δ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hAs)
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hδ
  have hψs : Function.Surjective (toSL3 ψ₀) := toSL3_surjective hψ₀s
  have hsq := sqtkGroup_SL3_of_sqtkQuot h hSQ hφ
  set Q := (Qv (puAmalgam h.le) δ).subgroupOf (stab _ δ) with hQdef
  have hQ : (toSL3 ψ₀).ker = Q := by
    ext g
    rw [MonoidHom.mem_ker, toSL3_eq_one_iff hψ₀, hQdef, Subgroup.mem_subgroupOf,
      ← stab_inf_centralizer_uloc h hφ hδ]
    constructor
    · intro hg
      refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := hg v hv
      have h2 : (g : (puAmalgam h.le).Universal) * v = v * g := by
        calc (g : (puAmalgam h.le).Universal) * v =
            ((g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹) * g := by
              group
          _ = v * g := by rw [h1]
      exact h2.symm
    · rintro ⟨-, hgc⟩ v hv
      rw [← Subgroup.mem_centralizer_iff.mp hgc v hv, mul_inv_cancel_right]
  have hQ2 : IsPGroup 2 Q := by
    have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
      rw [← isMVtx_iff_of_adj _ hδβ]
      exact hδ
    have h1 : IsPGroup 2 (Qv (puAmalgam h.le) δ) :=
      (isPGroup_qv _ h20 hβH).to_le (qv_le_qv _ h20 hδ hδβ)
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hQs).symm
  set Lh := (Ltil h.le L δ).subgroupOf (stab _ δ) with hLhdef
  have hLh : ⁅Lh, Lh⁆ = Lh := by
    apply Subgroup.map_injective (stab (puAmalgam h.le) δ).subtype_injective
    rw [Subgroup.map_commutator, hLhdef, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (ltil_le_stab h δ), ltil_perfect h hδ]
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := stab _ δ) hAn hBA hBn
    (fun v hv w hw => hAc (Subgroup.commutator_mem_commutator hv hw))
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact hA2 _ v.2
  set A' := Y.subgroupOf (stab _ δ) with hA'def
  have hA'2 : ∀ a ∈ A', toSL3 ψ₀ a ^ 2 = 1 := by
    intro a ha
    rw [← map_pow, ← MonoidHom.mem_ker, hQ, hQdef, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hY2 _ (Subgroup.mem_subgroupOf.mp ha)
  have hA'c : ∀ a ∈ A', ∀ b ∈ A', toSL3 ψ₀ a * toSL3 ψ₀ b = toSL3 ψ₀ b * toSL3 ψ₀ a := by
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ (toSL3 ψ₀).ker := by
      rw [hQ, hQdef, Subgroup.mem_subgroupOf]
      exact hYc (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb))
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hab
    exact hab
  have hqA : Nat.card F ≤ Nat.card (A'.map (toSL3 ψ₀)) := by
    have e1 : Nat.card (A'.map (toSL3 ψ₀)) = (toSL3 ψ₀).ker.relIndex A' := by
      rw [← MonoidHom.domRestrict_range, ← Subgroup.index_ker, MonoidHom.ker_domRestrict]
      rfl
    rw [e1, hQ, hQdef, hA'def, Subgroup.relIndex_subgroupOf hYs, Nat.card_eq_fintype_card]
    exact hYq
  have hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (A'.map ρ)) := by
    set Nt : Subgroup X := (N.subgroupOf A).map π with hNt
    have hNtA : Nt ≤ fixV (A'.map ρ) := by
      rintro _ ⟨m, hm, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [hρ]
      have hm' : (m : (puAmalgam h.le).Universal) ∈ N := Subgroup.mem_subgroupOf.mp hm
      have ha' : (a : (puAmalgam h.le).Universal) ∈ Y := Subgroup.mem_subgroupOf.mp ha
      have h1 : π (conjOn hAn a m * m⁻¹) = 1 := by
        refine (hπk _).mpr ?_
        have e : ((conjOn hAn a m * m⁻¹ : ↥A) : (puAmalgam h.le).Universal) =
            ⁅(a : (puAmalgam h.le).Universal), (m : (puAmalgam h.le).Universal)⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
        rw [e]
        refine hNY ?_
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator ha' hm'
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    have hpreN : pre π Nt = N := pre_map hπk hBN hNA
    have h1 := card_pre hπk hBA hπs Nt
    have h2 := card_pre hπk hBA hπs (⊤ : Subgroup X)
    rw [hpreN] at h1
    rw [pre_top, Subgroup.card_top] at h2
    have h3 := Subgroup.relIndex_mul_relIndex B N A hBN hNA
    rw [← h2, ← h3, h1, mul_comm]
    calc N.relIndex A * Nat.card Nt
        ≤ Fintype.card F * Nat.card Nt := Nat.mul_le_mul_right _ hNidx
      _ ≤ Nat.card F * Nat.card (fixV (A'.map ρ)) := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hNtA)
  have hN : ¬ commV (Lh.map ρ) ≤ commV (Q.map ρ) := by
    intro hle
    apply hnt
    have h1 := pre_mono (π := π) hle
    rw [pre_commV hρ hπk hBA hπs (ltil_le_stab h δ), pre_commV hρ hπk hBA hπs hQs] at h1
    exact le_sup_left.trans h1
  have hi := fix_commV_ker_ff h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ hQ2 ρ hLh hA'2 hA'c hqA hidx
    hN
  obtain ⟨C, hKC, hCfix, hPC, hPiC, F', iF', fF', hFF', τ, β', hτs, hβ's, hβ'k, hβ'e⟩ :=
    natSplit_quot_ff h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ ρ hA'2 hA'c hqA hidx
      (fun h' => hN ((G6.commV_mono (Subgroup.map_le_range ρ Lh)).trans h'))
  have hKq := pre_commV hρ hπk hBA hπs hQs
  have hKP : pre π (commV ρ.range) = ⁅A, stab (puAmalgam h.le) δ⁆ ⊔ B := by
    have := pre_commV hρ hπk hBA hπs (le_refl (stab (puAmalgam h.le) δ))
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  let _ : Fintype F' := Fintype.ofFinite F'
  refine ⟨?_, pre π C, ?_, pre_le C, ?_, ?_, ?_, F', iF', inferInstance,
    (specialLinearGroupEquivStatedSL 3 F').toMonoidHom.comp τ, ?_, ?_, ?_⟩
  · calc ⁅⁅A, Qv (puAmalgam h.le) δ⁆, puTrans h.le L δ⁆
        ≤ ⁅pre π (commV (Q.map ρ)), Ltil h.le L δ⁆ :=
          Subgroup.commutator_mono (hKq ▸ le_sup_left) le_rfl
      _ ≤ B :=
          commutator_pre_le_of_centralize hρ hπk (ltil_le_stab h δ)
            fun l hl x hx => hi l (Subgroup.mem_subgroupOf.mpr hl) x hx
  · rw [← hKq]
    exact pre_mono hKC
  · rw [← hKq]
    exact commutator_pre_le_of_fix hρ hCfix
  · rw [← hKP, ← pre_sup hπs, hPC, pre_top]
  · rw [← hKP, ← pre_inf, hPiC, hKq]
  · rw [Fintype.card_eq_nat_card, hFF', Nat.card_eq_fintype_card]
  · exact (specialLinearGroupEquivStatedSL 3 F').surjective.comp hτs
  · rw [← hKP, ← hKq]
    exact isSumOfNaturalModulesVia_pre hρ hπs (fun k x hx => commV_inv ρ k hx)
      (G6.commV_mono (Subgroup.map_le_range ρ Q)) τ β' hβ's hβ'k hβ'e

end CFSG.Quasithin.MS93.S45
