module

public import CFSG.Quasithin.MS93.S46I466aQIII
public import CFSG.Quasithin.MS93.S46I466aQ23
public import CFSG.Quasithin.MS93.S46I466bReal

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix commutatorElement

section Typ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))

include h hφ hC in
theorem card_natImage_zm_of_lt {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hS : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α α' 1)) < Fintype.card F ^ 2)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) :
    Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) α')) = Fintype.card F ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') =
        Fintype.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      1 ≤ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤ 2 := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨-, -, hw1, hwf, hf2, -, h7, h8, h9⟩ := crit_dims h hφ hC hc hψ hψ'
  have hlt := relIndex_zm_lt_of_lt h hφ hC hc hS
  rw [relIndex_zm_comm h hφ hC hc, h7] at hlt
  have hq2 := two_le_card_field (F := F)
  rw [← Nat.card_eq_fintype_card] at hlt hq2 ⊢
  have hf : 3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) = 1 := by
    have : 3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) < 2 :=
      (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
    omega
  refine ⟨?_, h8, hw1, hwf.trans hf2⟩
  rw [h9, h7, hf, pow_one]

include h hφ hC in
theorem critR_eq_critR_of_card {α α' α'' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hc' : IsCritical (puAmalgam h.le) α α'')
    (hgeo : geo (puAmalgam h.le) α α'' 1 = geo _ α α' 1)
    (hS : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α α' 1)) < Fintype.card F ^ 2)
    (h2 : Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F)
    (h2' : Nat.card ↥(critR (puAmalgam h.le) α α'') = Fintype.card F) :
    critR (puAmalgam h.le) α α' = critR _ α α'' := by
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hS' : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α α'' 1)) < Fintype.card F ^ 2 := by
    rw [hgeo]; exact hS
  obtain ⟨hE1, hR1, -, -⟩ := card_natImage_zm_of_lt h hφ hC hc hS hψ
  obtain ⟨hE2, hR2, -, -⟩ := card_natImage_zm_of_lt h hφ hC hc' hS' hψ
  have hq2 := two_le_card_field (F := F)
  have hw1 : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 1 := by
    rw [h2] at hR1
    exact (Nat.pow_right_injective hq2 (hR1.symm.trans (pow_one _).symm))
  have hw2 : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α''))) = 1 := by
    rw [h2'] at hR2
    exact (Nat.pow_right_injective hq2 (hR2.symm.trans (pow_one _).symm))
  set E := natImage ψ (Qv (puAmalgam h.le) β) with hEdef
  set E₁ := natImage ψ (ZM (puAmalgam h.le) α') with hE₁def
  set E₂ := natImage ψ (ZM (puAmalgam h.le) α'') with hE₂def
  have hE₁E : E₁ ≤ E := natImage_mono (zm_le_qv_geo_one _ h.hyp20 hb0 hc)
  have hE₂E : E₂ ≤ E := by
    have := natImage_mono (φ := ψ) (zm_le_qv_geo_one _ h.hyp20 hb0 hc')
    rwa [hgeo] at this
  have hEcard : Nat.card E < Fintype.card F ^ 2 := by
    rw [hEdef, card_natImage_eq_relIndex h hφ hc.1 hψ hβs]
    exact hS
  have hcomm : commN E₁ = commN E₂ := by
    by_contra hne
    have hinf : commN E₁ ⊓ commN E₂ = ⊥ := by
      by_contra hbot
      have h1 : commN E₁ ⊓ commN E₂ = commN E₁ :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by
          rw [hw1]
          exact Submodule.one_le_finrank_iff.mpr hbot)
      have h2 : commN E₁ ⊓ commN E₂ = commN E₂ :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by
          rw [hw2]
          exact Submodule.one_le_finrank_iff.mpr hbot)
      exact hne (h1.symm.trans h2)
    have hmeet : ∀ g ∈ E₁, g ∈ E₂ → g = 1 := by
      intro g hg1 hg2
      refine eq_one_of_mulVec_eq_self fun x => ?_
      have hx : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ commN E₁ ⊓ commN E₂ :=
        ⟨sub_mem_commN hg1 x, sub_mem_commN hg2 x⟩
      rw [hinf, Submodule.mem_bot, sub_eq_zero] at hx
      exact hx
    have hinj : Function.Injective (fun p : ↥E₁ × ↥E₂ =>
        (⟨(p.1 : SL3 F) * p.2, E.mul_mem (hE₁E p.1.2) (hE₂E p.2.2)⟩ : ↥E)) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have e : (a : SL3 F) * b = a' * b' := congrArg Subtype.val hab
      have hm : (a' : SL3 F)⁻¹ * a = b' * (b : SL3 F)⁻¹ := by
        calc (a' : SL3 F)⁻¹ * a = (a' : SL3 F)⁻¹ * (a * b) * (b : SL3 F)⁻¹ := by group
          _ = (a' : SL3 F)⁻¹ * (a' * b') * (b : SL3 F)⁻¹ := by rw [e]
          _ = b' * (b : SL3 F)⁻¹ := by group
      have h1 := hmeet _ (E₁.mul_mem (E₁.inv_mem a'.2) a.2)
        (hm ▸ E₂.mul_mem b'.2 (E₂.inv_mem b.2))
      have haa : (a : SL3 F) = a' := by
        rw [mul_eq_one_iff_eq_inv] at h1
        exact (inv_injective h1).symm
      have hbb : (b : SL3 F) = b' := by
        rw [haa] at e
        exact mul_left_cancel e
      exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hE1, hE2, ← sq] at this
    omega
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZs' : ZM (puAmalgam h.le) α'' ≤ stab _ α :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc'
  obtain ⟨hR₁, hR₁U⟩ := critR_eq_commutator_uloc h hφ hc
  obtain ⟨hR₂, hR₂U⟩ := critR_eq_commutator_uloc h hφ hc'
  ext x
  rw [hR₁, hR₂]
  constructor
  · intro hx
    have hxU := hR₁U hx
    have := (mem_commutator_iff_natVec hψ hZs ⟨x, hxU⟩).mp hx
    rw [← hE₁def, hcomm] at this
    exact (mem_commutator_iff_natVec hψ hZs' ⟨x, hxU⟩).mpr this
  · intro hx
    have hxU := hR₂U hx
    have := (mem_commutator_iff_natVec hψ hZs' ⟨x, hxU⟩).mp hx
    rw [← hE₂def, ← hcomm] at this
    exact (mem_commutator_iff_natVec hψ hZs ⟨x, hxU⟩).mpr this

include h hφ in
theorem zm_inf_dloc_le_zloc' {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    ZM (puAmalgam h.le) μ ⊓ Dloc h.le L μ ≤ Zloc h.le L μ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rintro z ⟨hz, hzD⟩
  obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hμ hz
  have huD : u ∈ Dloc h.le L μ := by
    have := (Dloc h.le L μ).mul_mem hzD ((Dloc h.le L μ).inv_mem (zloc_le_dloc h μ hζ))
    simpa [mul_assoc] using this
  have hu1 : u = 1 := by
    have : u ∈ Uloc h.le L μ ⊓ Dloc h.le L μ := ⟨hu, huD⟩
    rwa [uloc_inf_dloc_eq_bot h hφ μ, Subgroup.mem_bot] at this
  rw [hu1, one_mul]
  exact hζ

include h hφ hC in
theorem critR_le_zloc_of_card_sq (hb4 : critDist (puAmalgam h.le) = 4)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
    {α α' α'' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (h3 : Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F ^ 2)
    (hc'' : IsCritical (puAmalgam h.le) α α'') (hgeo : geo (puAmalgam h.le) α α'' 1 = geo _ α α' 1)
    (hS : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α α' 1)) < Fintype.card F ^ 2)
    (h2 : Nat.card ↥(critR (puAmalgam h.le) α α'') = Fintype.card F) :
    critR (puAmalgam h.le) α α'' ≤ Zloc h.le L (geo _ α α' 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  set γ := geo (puAmalgam h.le) α α' 2 with hγdef
  set A := critR (puAmalgam h.le) α α'' with hAdef
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hγ : IsMVtx _ γ := isMVtx_geo_two' hb4 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by norm_num)
  have hAU : A ≤ Usup (puAmalgam h.le) α β := by
    have := critR_le_usup_one h hc''
    rwa [hgeo] at this
  have hAZ : A ≤ ZH (puAmalgam h.le) β := hAU.trans (h464 α β hc.1 hαβ)
  have hAT : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal) :=
    (Subgroup.le_centralizer_iff.mp (hAZ.trans (zh_le_centralizer _ β))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAc : ∀ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α δ' →
      geo (puAmalgam h.le) α δ' 1 = β → A ≤ ⁅XM (puAmalgam h.le) α, XM _ δ'⁆ := by
    intro δ' hcδ hgδ
    have hS' : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α δ' 1)) <
        Fintype.card F ^ 2 := by
      rw [hgδ]; exact hS
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
    obtain ⟨-, hR, hw1, hw2⟩ := card_natImage_zm_of_lt h hφ hC hcδ hS' hψ
    have hle : A ≤ critR (puAmalgam h.le) α δ' := by
      rcases (by omega : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) δ'))) = 1 ∨
          Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) δ'))) = 2) with hw | hw
      · rw [hw, pow_one] at hR
        exact (critR_eq_critR_of_card h hφ hC hc'' hcδ (hgδ.trans hgeo.symm)
          (by rw [hgeo]; exact hS) h2 hR).le
      · rw [hw] at hR
        have hsq' : Nat.card ↥(Usup (puAmalgam h.le) α (geo _ α δ' 1)) = Fintype.card F ^ 2 := by
          rw [hgδ]; exact hsq α β hc.1 hαβ
        rw [critR_eq_usup_of_card_sq h hcδ hsq' hR, hgδ]
        exact hAU
    exact hle.trans (Subgroup.commutator_mono (zm_le_xm _ h20 hb0 hc.1)
      (zm_le_xm _ h20 hb0 (hcδ.isMVtx_right _ h20)))
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hR' : critR (puAmalgam h.le) α' α = Usup _ α' (geo _ α' α 1) := by
    refine critR_eq_usup_of_card_sq h hc'
      (hsq α' _ hc'.1 (adj_geo_one_of_isCritical _ hb0 hc')) ?_
    rw [critR, Subgroup.commutator_comm]
    exact h3
  obtain ⟨Z, hZ⟩ := zc23_of_critR_eq h hC hc hR'
  have hG : ∀ γ ρ : Vtx (puAmalgam h.le), IsMVtx _ γ → (puAmalgam h.le).treeGraph.Adj γ ρ →
      Gen23At (puAmalgam h.le) γ ρ := fun γ ρ hγ hγρ => gen23At_of h hfull hγ hγρ
  have hN := ms23_step4 (puAmalgam h.le) h20 (by omega) hC hG hαβ hAT hAc hc rfl hZ
  have hAZγ : A ≤ ZM (puAmalgam h.le) γ := hAZ.trans (zh_le_zm _ hβγ.symm)
  have hAQ : A ≤ Qv (puAmalgam h.le) γ := hAZγ.trans (zm_le_qv_self _ hγ hb0)
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ
  have hYn : stab (puAmalgam h.le) γ ≤
      Subgroup.normalizer ((A ⊓ Uloc h.le L γ : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    (le_inf hN hUn).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hγ
  have hLs := ltil_le_stab h γ
  have hcomm : ⁅A, Ltil h.le L γ⁆ ≤ A ⊓ Uloc h.le L γ := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hN)) ?_
    refine (Subgroup.commutator_mono hAZγ le_rfl).trans ?_
    rw [commutator_zm_eq_uloc h hfull hγ hLs]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hUn)
  have hD : A ≤ Dloc h.le L γ := by
    rcases eq_or_eq_of_natural hψs statedSL3_transitive hψ bot_le inf_le_right hYn with hY | hY
    · exact le_dloc_of_commutator_le h hγ hAQ ((hcomm.trans hY.le).trans bot_le)
    · exfalso
      have := finite_usup h hc.1 hαβ
      have : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hAU)
      have h1 := Subgroup.card_le_of_le (inf_le_left : A ⊓ Uloc h.le L γ ≤ A)
      rw [hY, card_eq_of_natural hψ, h2, Nat.card_eq_fintype_card] at h1
      have := card_field_lt_pow_three (F := F)
      omega
  exact (le_inf hAZγ hD).trans (zm_inf_dloc_le_zloc' h hφ hγ)

end Typ

end CFSG.Quasithin.MS93.S46
