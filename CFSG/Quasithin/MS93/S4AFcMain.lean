module

public import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S4AFcAbs

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A.F CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem isC1_of_crit_ff (h14 : MS14AS) (hSQ : SQTKQuot) (hC : CentHyp (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {μ δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ δ)
    (hVab : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    {N : Subgroup (puAmalgam h.le).Universal} (hZN : ZM (puAmalgam h.le) δ ≤ N)
    (hNV : N ≤ Vv (puAmalgam h.le) δ) (hNA : ⁅N, ZM (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) δ)
    (hNidx : N.relIndex (Vv (puAmalgam h.le) δ) ≤ Fintype.card F) :
    IsC1 h.le L (Fintype.card F) δ (Vv (puAmalgam h.le) δ) (ZM (puAmalgam h.le) δ) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hδ : IsMVtx _ δ := hc'.1
  have hδβ := adj_geo_one_of_isCritical _ hb0 hc'
  have hAs : ZM (puAmalgam h.le) μ ≤ stab _ δ :=
    (zm_le_qv_geo_one _ h20 hb0 hc').trans (qv_le_stab_of_adj _ hδβ.symm)
  have hZV := zm_le_vv h hδ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have : Finite ↥(Vv (puAmalgam h.le) δ) := Finite.of_injective _
    (Subgroup.inclusion_injective ((vv_le_qv h hb hδ).trans hQs))
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h hφ hδ
  obtain ⟨ψμ, -, hψμ⟩ := exists_natural_Uloc h hφ hc.1
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
    have hβH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) δ μ 1) := by
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
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := stab _ δ)
    (stab_le_normalizer_vv h δ) hZV (stab_le_normalizer_zm _ δ)
    (fun v hv w hw => hVab (Subgroup.commutator_mem_commutator hv hw))
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact sq_mem_zm_of_mem_vv h hfull hVab v.2
  set A := (ZM (puAmalgam h.le) μ).subgroupOf (stab _ δ) with hAdef
  have hA2 : ∀ a ∈ A, toSL3 ψ₀ a ^ 2 = 1 := by
    intro a ha
    have h1 : (a : (puAmalgam h.le).Universal) ^ 2 = 1 := by
      refine sq_eq_one_of_mem_zv h hfull (ρ := μ) ?_
      rw [zv_of_isMVtx _ hc.1]
      exact Subgroup.mem_subgroupOf.mp ha
    have h2 : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])
    rw [← map_pow, h2, map_one]
  have hAc : ∀ a ∈ A, ∀ b ∈ A, toSL3 ψ₀ a * toSL3 ψ₀ b = toSL3 ψ₀ b * toSL3 ψ₀ a := by
    intro a ha b hb
    have ha' := Subgroup.mem_subgroupOf.mp ha
    have hb' := Subgroup.mem_subgroupOf.mp hb
    have h1 : (a : (puAmalgam h.le).Universal) * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hc.1 ha') _
        (zm_le_qv_self _ hc.1 hb0 hb')).symm
    have h2 : a * b = b * a := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h1])
    rw [← map_mul, ← map_mul, h2]
  have hqA : Nat.card F ≤ Nat.card (A.map (toSL3 ψ₀)) := by
    obtain ⟨-, hcard, hrel, -, -, hne⟩ := s35_core h hC hφ hc hψμ hψ₀
    have h1 : Module.finrank F (fixN (natImage ψμ (ZM (puAmalgam h.le) δ))) < 3 := by
      have := Submodule.finrank_lt (fixN_ne_top hne)
      rwa [Module.finrank_fin_fun] at this
    change Nat.card F ≤ Nat.card (natImage ψ₀ (ZM (puAmalgam h.le) μ))
    rw [hcard, hrel]
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (by omega)
  have hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (A.map ρ)) := by
    set Nt : Subgroup X := (N.subgroupOf (Vv (puAmalgam h.le) δ)).map π with hNt
    have hNtA : Nt ≤ fixV (A.map ρ) := by
      rintro _ ⟨n, hn, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [hρ]
      have hn' : (n : (puAmalgam h.le).Universal) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have ha' : (a : (puAmalgam h.le).Universal) ∈ ZM (puAmalgam h.le) μ :=
        Subgroup.mem_subgroupOf.mp ha
      have h1 : π (conjOn (stab_le_normalizer_vv h δ) a n * n⁻¹) = 1 := by
        refine (hπk _).mpr ?_
        have e : ((conjOn (stab_le_normalizer_vv h δ) a n * n⁻¹ : ↥(Vv (puAmalgam h.le) δ)) :
            (puAmalgam h.le).Universal) =
            ⁅(a : (puAmalgam h.le).Universal), (n : (puAmalgam h.le).Universal)⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
        rw [e]
        refine hNA ?_
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator ha' hn'
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    have hpreN : pre π Nt = N := pre_map hπk hZN hNV
    have h1 := card_pre hπk hZV hπs Nt
    have h2 := card_pre hπk hZV hπs (⊤ : Subgroup X)
    rw [hpreN] at h1
    rw [pre_top, Subgroup.card_top] at h2
    have h3 := Subgroup.relIndex_mul_relIndex (ZM (puAmalgam h.le) δ) N
      (Vv (puAmalgam h.le) δ) hZN hNV
    rw [← h2, ← h3, h1, mul_comm]
    calc N.relIndex (Vv (puAmalgam h.le) δ) * Nat.card Nt
        ≤ Fintype.card F * Nat.card Nt := Nat.mul_le_mul_right _ hNidx
      _ ≤ Nat.card F * Nat.card (fixV (A.map ρ)) := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hNtA)
  have hN : ¬ commV (Lh.map ρ) ≤ commV (Q.map ρ) := by
    intro hle
    apply not_commutator_ltil_le h hfull hb hδ hδβ hX2 hπs hπk hρ
    have h1 := pre_mono (π := π) hle
    rw [pre_commV hρ hπk hZV hπs (ltil_le_stab h δ), pre_commV hρ hπk hZV hπs hQs] at h1
    exact le_sup_left.trans h1
  have hi := fix_commV_ker_ff h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ hQ2 ρ hLh hA2 hAc hqA hidx
    hN
  obtain ⟨C, hKC, hCfix, hPC, hPiC, F', iF', fF', hFF', τ, β', hτs, hβ's, hβ'k, hβ'e⟩ :=
    natSplit_quot_ff h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ ρ hA2 hAc hqA hidx
      (fun h' => hN ((G6.commV_mono (Subgroup.map_le_range ρ Lh)).trans h'))
  have hKq := pre_commV hρ hπk hZV hπs hQs
  have hKP : pre π (commV ρ.range) =
      ⁅Vv (puAmalgam h.le) δ, stab (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ := by
    have := pre_commV hρ hπk hZV hπs (le_refl (stab (puAmalgam h.le) δ))
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  let _ : Fintype F' := Fintype.ofFinite F'
  refine ⟨?_, pre π C, ?_, pre_le C, ?_, ?_, ?_, F', iF', inferInstance,
    (specialLinearGroupEquivStatedSL 3 F').toMonoidHom.comp τ, ?_, ?_, ?_⟩
  · calc ⁅⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆, puTrans h.le L δ⁆
        ≤ ⁅pre π (commV (Q.map ρ)), Ltil h.le L δ⁆ :=
          Subgroup.commutator_mono (hKq ▸ le_sup_left) le_rfl
      _ ≤ ZM (puAmalgam h.le) δ :=
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

end Vertex

theorem s4CFFc_of (h14 : MS14AS) (hSQ : SQTKQuot) (h32 : S32) : S4CFFc := by
  intro G _ _ M T L h F _ _ φ hyp μ δ hc hVab N hZN hNV hNA hNidx
  exact isC1_of_crit_ff h h14 hSQ (centHyp_of_S32 h32 h) hyp.2.2 hyp.2.1 hc hVab hZN hNV hNA
    hNidx

end CFSG.Quasithin.MS93.S4A
