module

public import CFSG.Quasithin.MS93.S4L461B
public import CFSG.Quasithin.MS93.S4L461C

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section SelfDual

variable (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include h hU hC

theorem false_of_offender_centerOf_flat (h14 : MS14AS) (hSQ : SQTKQuot)
    (hb4 : critDist (puAmalgam h.le) = 4) {x : Vtx (puAmalgam h.le)}
    (hx : IsMVtx _ x) {As : Subgroup (puAmalgam h.le).Universal}
    (hAf : As ≤ S34F.flat h x)
    (hA : IsOffenderOn (puAmalgam h.le) x (centerOf (Vv _ x)) As)
    (hD : ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Dloc h.le L x)
    (hne : ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≠ ⊥) : False := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, F, _, _, φ, hF, hφs, hφ⟩ := S34F.exists_natural_flat h hU
  have hsq : SQTKGroup (SL3 F) := S43F.sqtkGroup_SL3_of_flat h hSQ hφs
  obtain ⟨ψ, hψs, hψ⟩ := S34F.exists_natural_flat_at h hφs hφ hx
  have hfinS : Finite ↥(stab (puAmalgam h.le) x) := finite_stab h hx
  have hXs : S34F.flat h x ≤ stab (puAmalgam h.le) x := S43F.flat_le_stab h x
  have hfinX : Finite ↥(S34F.flat h x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hXs)
  have hVQ : Vv (puAmalgam h.le) x ≤ Qv _ x := vv_le_qv h hb hx
  have hVX : Vv (puAmalgam h.le) x ≤ S34F.flat h x := hVQ.trans (S43F.qv_le_flat h hx)
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ x := hVX.trans hXs
  have hfinV : Finite ↥(Vv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  set V := Vv (puAmalgam h.le) x with hVdef
  set K' := ⁅V, V⁆ with hK'def
  have h39x : K' ≤ centerOf V := S34F.s39_flat h hU hC hb4 hx
  have hK'V : K' ≤ V := h39x.trans inf_le_left
  have hK's : K' ≤ stab (puAmalgam h.le) x := hK'V.trans hVs
  have hVn := stab_le_normalizer_vv h x
  have hK'n : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (K' : Set _) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [hK'def, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hVn hg)]
  have hfinKQ : Finite ↥(K' ⊔ Qv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hK's (qv_le_stab _ x)))
  have hLK : ⁅K', Ltil h.le L x⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have := hD.trans (le_of_eq (h.puTrans_Dq hx))
    exact this.trans inf_le_right
  obtain ⟨K'', -, hK''K', hK''n, hidx, hK'X⟩ :=
    exists_inv_index_two (X := S34F.flat h x) (L := Ltil h.le L x)
      (Q := Qv (puAmalgam h.le) x) (K₀ := ⊥) (K' := K')
      (fun k hk k' hk' => (Subgroup.mem_centralizer_iff.mp (h39x hk).2 k' (hK'V hk')).symm)
      (fun k hk => sq_eq_one_of_mem_commutator h39x
        (fun a ha => sq_mem_commutator_vv h hb0 ha) hk)
      (isPGroup_qv_of_isMVtx h hx) bot_le (fun hle => hne (le_bot_iff.mp hle))
      (S43F.flat_eq_ltil_sup_qv h hx)
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)
      (hXs.trans hK'n) (hXs.trans (stab_le_normalizer_qv _ x)) hLK
  have hK''V : V ≤ Subgroup.normalizer (K'' : Set _) := hVX.trans hK''n
  set Ut := vvPerp (X := puAmalgam h.le) x K'' with hUtdef
  have hUt : ∀ v, v ∈ Ut ↔ v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ K'' := fun v => mem_vvPerp_iff hK''V
  have hNU : centerOf V ≤ Ut := by
    intro v hv
    rw [hUt]
    refine ⟨hv.1, fun w hw => ?_⟩
    have : ⁅v, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hv.2 w hw).symm
    rw [this]; exact Subgroup.one_mem _
  have hUtV : Ut ≤ V := vvPerp_le x K''
  have hUtn : S34F.flat h x ≤ Subgroup.normalizer (Ut : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ S34F.flat h x, ∀ v ∈ Ut, y * v * y⁻¹ ∈ Ut := by
      intro y hy v hv
      rw [hUt] at hv ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn (hXs hy)) v).mp hv.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVn (hXs (Subgroup.inv_mem _ hy))) w).mp hw
      have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hK''n hy) _).mp (hv.2 _ hw')
    intro v
    constructor
    · exact key g hg v
    · intro hv
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
      simpa [mul_assoc] using this
  obtain ⟨-, hAQ, hA2, hAc, C₀, -, hC₀V, hC₀A, hC₀i⟩ := hA
  have hker := toSL3_eq_one_iff_mem_qv_flat h hU hx hψ
  have hVL := sd_group h14 hSQ hsq hF (X := S34F.flat h x) (V := V) (K' := K') (K'' := K'')
    (Ut := Ut) (Bh := ⊥) (A := As) (Lg := Ltil h.le L x) (C₀ := C₀ ⊔ Ut)
    (toSL3 ψ) (toSL3_surjective hψs) (pow_two_pow_eq_one_of_toSL3_eq_one_flat h hU hx hψ)
    (hXs.trans hVn) hK'V (h39x.trans inf_le_right) le_rfl hK''K' hK''n hidx hK'X hUt bot_le
    (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge)
    (S43F.ltil_le_flat h x) (ltil_perfect h hx)
    (by rw [Subgroup.commutator_bot_left]; exact bot_le) hAf
    (fun a ha => by
      rw [← map_pow]
      exact (hker _).mpr (by simpa using hA2 a ha))
    (fun a b ha hb' => by
      have h1 : toSL3 ψ ⁅a, b⁆ = 1 := (hker _).mpr (by
        have := hAc a ha b hb'
        simpa [commutatorElement_def] using this)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1)
    (by
      obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
      exact ⟨⟨a, hAf haA⟩, haA, fun h1 => haQ ((hker _).mp h1)⟩)
    (by rw [bot_sup_eq]; exact le_sup_right) (sup_le hC₀V hUtV)
    (by
      rw [bot_sup_eq]
      exact S4A.commutator_sup_le_of (hC₀A.trans hNU)
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAf.trans hUtn))
        (hC₀V.trans (hVX.trans hUtn)) (hUtV.trans (hVX.trans hUtn)))
    (by
      have h1 : (C₀ ⊔ Ut).relIndex V ≤ C₀.relIndex V :=
        Subgroup.relIndex_le_of_le_left le_sup_left (by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      have h2 := card_natImage_eq_relIndex_flat h hU hx hψ hAf
      exact h1.trans (hC₀i.trans h2.ge))
  have hcrit := commutator_vv_le_of_ltil_flat h hb hx (K := K'')
    ((S43F.ltil_le_flat h x).trans hK''n) hK''V hVL
  have : K'' = K' := le_antisymm hK''K' hcrit
  rw [this, Subgroup.relIndex_self] at hidx
  omega

theorem commutator_vv_ne_bot_flat (h43 : S34G.S43b4Flat) (hb4 : critDist (puAmalgam h.le) = 4)
    {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≠ ⊥ := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  intro hbot
  obtain ⟨x', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hx
  refine h43 _ M T L h hU hC hb4 x x' ⟨hc, ?_⟩
  rw [geo_rev_two hb4 hc]
  have habel : Vv (puAmalgam h.le) x ≤ centerOf (Vv _ x) :=
    le_inf le_rfl ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot)
  exact habel.trans (centerOf_vv_le_qv h.hyp20 hC hb hx (isMVtx_geo_two' hb4 hc)
    (dist_geo_crit hb4 hc (by omega)))

theorem centerOf_vv_le_bloc_of_isSL3U (h14 : MS14AS) (hSQ : SQTKQuot)
    (hb4 : critDist (puAmalgam h.le) = 4) {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α := by
  have h43 := S34G.s43b4Flat_of h14 hSQ
  by_contra hN
  have hNall : ∀ y : Vtx (puAmalgam h.le), IsMVtx _ y →
      ¬ centerOf (Vv (puAmalgam h.le) y) ≤ Bloc h.le L y :=
    fun y hy => not_centerOf_le_bloc_of_smul h hα hy hN
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hα
  have hγ := isMVtx_geo_two' hb4 hc
  rcases exists_offender_centerOf_flat h hU hC h43 hb4 hc (hNall α hα) (hNall _ hγ) with
    ⟨A, hAf, hA⟩ | ⟨A, hAf, hA⟩
  · exact false_of_offender_centerOf_flat h hU hC h14 hSQ hb4 hα hAf hA
      (commutator_vv_le_dloc_of_not_flat h hU hC hb4 hα (hNall α hα))
      (commutator_vv_ne_bot_flat h hU hC h43 hb4 hα)
  · exact false_of_offender_centerOf_flat h hU hC h14 hSQ hb4 hγ hAf hA
      (commutator_vv_le_dloc_of_not_flat h hU hC hb4 hγ (hNall _ hγ))
      (commutator_vv_ne_bot_flat h hU hC h43 hb4 hγ)

end SelfDual

end CFSG.Quasithin.MS93.S4L
