module

public import CFSG.Quasithin.MS93.S46I461

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section GroupAux2

variable {𝔾 : Type} [Group 𝔾]

theorem sq_eq_one_of_mem_sup {A B : Subgroup 𝔾} (hA : ∀ a ∈ A, a ^ 2 = 1)
    (hB : ∀ b ∈ B, b ^ 2 = 1) (hc : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x) {x : 𝔾}
    (hx : x ∈ A ⊔ B) : x ^ 2 = 1 := by
  have hmem : ∀ y ∈ Subgroup.closure ((A : Set 𝔾) ∪ B), y ∈ A ⊔ B := fun y hy => by
    rw [Subgroup.sup_eq_closure]; exact hy
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact hA z hz
    · exact hB z hz
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (hc a (hmem a ha) b (hmem b hb)) 2), iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

end GroupAux2

section I462

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

omit hφ in
theorem stab_le_normalizer_bloc (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (Bloc h.le L δ : Set _) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← bloc_smul h g δ, (mem_stab _).mp hg]

theorem commutator_vv_le_uloc_of_offender (h14 : MS14AS) (hSQ : SQTKQuot)
    (hsq : SQTKGroup (SL3 F)) (h39 : S39) (h461 : I461) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x)
    {As : Subgroup (puAmalgam h.le).Universal}
    (hA : IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, hF⟩ := hφ.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hx
  have hfinS : Finite ↥(stab (puAmalgam h.le) x) := finite_stab h hx
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ x := (vv_le_qv h hb hx).trans (qv_le_stab _ x)
  have hfinV : Finite ↥(Vv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  set V := Vv (puAmalgam h.le) x with hVdef
  set U := Uloc h.le L x with hUdef
  by_contra hnot
  have h39x : ⁅V, V⁆ ≤ centerOf V := h39 G M T L h hb4 hfull x hx
  have hUZ : U ≤ ZM (puAmalgam h.le) x := uloc_le_zm h hfull hx
  have hZN : ZM (puAmalgam h.le) x ≤ centerOf V := zm_le_centerOf_vv h hb hx
  set K' := ⁅V, V⁆ ⊔ U with hK'def
  have hK'N : K' ≤ centerOf V := sup_le h39x (hUZ.trans hZN)
  have hK'V : K' ≤ V := hK'N.trans inf_le_left
  have hK's : K' ≤ stab (puAmalgam h.le) x := hK'V.trans hVs
  have hVn := stab_le_normalizer_vv h x
  have hUn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (U : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) x
  have hK'n : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (K' : Set _) := by
    have hcn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup _) : Set _) := by
      refine le_normalizer_of_map_conj_le fun g hg => ?_
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hVn hg)]
    exact (le_inf hcn hUn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hfinKQ : Finite ↥(K' ⊔ Qv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hK's (qv_le_stab _ x)))
  have hBx : centerOf V ≤ Bloc h.le L x := h461 G M T L F φ ⟨h, hmin, hb4, hφ⟩ x hx
  have hLK : ⁅K', Ltil h.le L x⁆ ≤ U := by
    refine commutator_le_of_perfect (ltil_perfect h hx) (B := ZM (puAmalgam h.le) x) ?_ ?_
      ((ltil_le_stab h x).trans hUn) (hK's.trans hUn)
    · exact (Subgroup.commutator_mono (hK'N.trans hBx) le_rfl).trans
        (commutator_bloc_le h hb hx)
    · rw [commutator_zm_eq_uloc h hfull hx (ltil_le_stab h x)]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h x).trans hUn)
  have hcom : ∀ k ∈ K', ∀ k' ∈ K', k * k' = k' * k := fun k hk k' hk' =>
    (Subgroup.mem_centralizer_iff.mp (hK'N hk).2 k' (hK'V hk')).symm
  have hK'2 : ∀ k ∈ K', k ^ 2 = 1 := fun k hk =>
    sq_eq_one_of_mem_sup (fun a ha => sq_eq_one_of_mem_commutator h39x
      (fun b hb' => sq_mem_commutator_vv h hb0 hb') ha)
      (fun u hu => (isElemAbelian_zm _ h.hyp20 hb0 hx).2 u (hUZ hu)) hcom hk
  obtain ⟨K'', hUK'', hK''K', hK''n, hidx, hK'X⟩ :=
    exists_inv_index_two (X := stab (puAmalgam h.le) x) (L := Ltil h.le L x)
      (Q := Qv (puAmalgam h.le) x) (K₀ := U) (K' := K') hcom hK'2
      (isPGroup_qv_of_isMVtx h hx) le_sup_right
      (fun hle => hnot (le_sup_left.trans hle)) (stab_eq_ltil_sup_qv h hfull hx) hUn hK'n
      (stab_le_normalizer_qv _ x) hLK
  have hK''V : V ≤ Subgroup.normalizer (K'' : Set _) := hVs.trans hK''n
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
  have hUtn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (Ut : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ stab (puAmalgam h.le) x, ∀ v ∈ Ut, y * v * y⁻¹ ∈ Ut := by
      intro y hy v hv
      rw [hUt] at hv ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn hy) v).mp hv.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hy)) w).mp hw
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
  obtain ⟨⟨ρ, hxρ, hAρ⟩, hAQ, hA2, hAc, C₀, hBC₀, hC₀V, hC₀A, hC₀i⟩ := hA
  have hAs : As ≤ stab (puAmalgam h.le) x := hAρ.trans (qv_le_stab_of_adj _ hxρ.symm)
  have hker := toSL3_eq_one_iff_mem_qv h hφ hx hψ
  have hBn := stab_le_normalizer_bloc h x
  have hVL := sd_group h14 hSQ hsq hF (X := stab (puAmalgam h.le) x) (V := V) (K' := K')
    (K'' := K'') (Ut := Ut) (Bh := Bloc h.le L x) (A := As) (Lg := Ltil h.le L x)
    (C₀ := C₀ ⊔ Ut)
    (toSL3 ψ) (toSL3_surjective hψs) (pow_two_pow_eq_one_of_toSL3_eq_one h hφ hx hψ)
    hVn hK'V (hK'N.trans inf_le_right) le_sup_left hK''K' hK''n hidx hK'X hUt
    (bloc_le_vv h x) hBn (ltil_le_stab h x) (ltil_perfect h hx)
    ((commutator_bloc_le h hb hx).trans (hZN.trans hNU)) hAs
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
      exact ⟨⟨a, hAs haA⟩, haA, fun h1 => haQ ((hker _).mp h1)⟩)
    (sup_le_sup_right hBC₀ _) (sup_le hC₀V hUtV)
    (S4A.commutator_sup_le_of (hC₀A.trans le_sup_left)
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hAs.trans hUtn)).trans le_sup_right)
      (hC₀V.trans (hVs.trans ((le_inf hBn hUtn).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _))))
      (hUtV.trans (hVs.trans ((le_inf hBn hUtn).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)))))
    (by
      have h1 : (C₀ ⊔ Ut).relIndex V ≤ C₀.relIndex V :=
        Subgroup.relIndex_le_of_le_left le_sup_left (by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      have h2 := card_natImage_eq_relIndex h hφ hx hψ hAs
      exact h1.trans (hC₀i.trans h2.ge))
  have hcrit := commutator_vv_le_of_ltil h hfull hb hx (K := K'') hK''n hVL
  have : K'' = K' := le_antisymm hK''K' (sup_le hcrit hUK'')
  rw [this, Subgroup.relIndex_self] at hidx
  omega

end I462

theorem i462_of (h39 : S39) (h461 : I461) (h14 : MS14AS) (hSQ : SQTKQuot) : I462 := by
  intro G _ _ M T L F _ _ φ c α As hα hA
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  exact commutator_vv_le_uloc_of_offender h hφ h14 hSQ (sqtkGroup_SL3 h hφ hSQ) h39 h461 hmin
    hb4 hα hA

end CFSG.Quasithin.MS93.S46
