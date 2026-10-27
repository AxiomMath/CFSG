module

public import CFSG.Quasithin.MS93.S4A441B3
public import CFSG.Quasithin.MS93.S4A431D
public import CFSG.Quasithin.MS93.S46I466aQIII
public import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S46Ker

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S4A.F
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem ptStab_entry_ne_zero {g : SL3 F} (hg : g ∈ (ptStab : Subgroup (SL3 F))) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h0
  have hdet := g.2
  rw [Matrix.det_fin_three, hg.1, hg.2, h0] at hdet
  simp at hdet

theorem off_axis_mul_ptStab {g k : SL3 F} (hk : k ∈ (ptStab : Subgroup (SL3 F)))
    (hg : (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0) :
    ((((g * k : SL3 F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 := by
  rw [mulVec_e0] at hg ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hk.1, hk.2,
    mul_zero, add_zero]
  exact mul_ne_zero hg (ptStab_entry_ne_zero hk)

theorem lnStab_entry_ne_zero {σ : SL3 F} (h0 : ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h1 : ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h2
  have hdet := σ.2
  rw [Matrix.det_fin_three, h0, h1, h2] at hdet
  simp at hdet

theorem off_axis_lnStab_mul {σ k : SL3 F}
    (h0 : ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h1 : ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (hk : (((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0) :
    ((((σ * k : SL3 F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 := by
  rw [mulVec_e0] at hk ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, h0, h1,
    zero_mul, zero_add]
  exact mul_ne_zero (lnStab_entry_ne_zero h0 h1) hk

end Lin

section Bad

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem exists_secD_of_forall_le_qv (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {α α' μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hμ : μ ∈ nablaSet h.le L α)
    (hQUD : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    (hT : ((rootGroup 0 2 : Subgroup (SL3 F)) ≤ natImage ψ (ZM (puAmalgam h.le) α') ∧
        Fintype.card F ≤ Nat.card ↥(critR (puAmalgam h.le) α α')) ∨
      ((∀ t ∈ (rootGroup 0 2 : Subgroup (SL3 F)), ∃ σ : SL3 F,
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
          σ * t * σ⁻¹ ∈ natImage ψ (ZM (puAmalgam h.le) α')) ∧
        Fintype.card F ^ 2 ≤ Nat.card ↥(critR (puAmalgam h.le) α α')))
    (hB : ∀ k : ↥(stab (puAmalgam h.le) α),
      (((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 →
        ZM (puAmalgam h.le) ((k : 𝔘) • μ) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) :
    ∃ (dual : Bool) (C : Subgroup 𝔘),
      Uloc h.le L α ≤ C ∧ ⁅C, stab (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α ∧
      ⁅conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ), Qv (puAmalgam h.le) α⁆ ≤
        Uloc h.le L α ⊔ Dloc h.le L α ∧
      IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
        (conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ)) C ψ dual 1 ∧
      ∀ w ∈ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ),
        ∀ g ∈ stab (puAmalgam h.le) α, w⁻¹ * (g * w * g⁻¹) ∈ C →
          w⁻¹ * (g * w * g⁻¹) ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hα : IsMVtx _ α := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα' : IsMVtx _ α' := hc'.1
  obtain ⟨hdμ, hμB⟩ := hμ
  have hμM : IsMVtx _ μ := by
    rcases isMVtx_of_dist_le_two h hα hdμ.le with hM | hadj
    · exact hM
    · rw [dist_eq_one_of_adj _ hadj] at hdμ
      omega
  obtain ⟨W, hW⟩ : ∃ W, W = conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ) := ⟨_, rfl⟩
  rw [← hW]
  have hWn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (W : Set 𝔘) := by
    rw [hW]; exact le_normalizer_conjCl _ _
  have hZμV : ZM (puAmalgam h.le) μ ≤ Vv (puAmalgam h.le) α := by
    have := zv_le_vv h (α := α) (ρ := μ) hdμ.le
    rwa [zv_of_isMVtx _ hμM] at this
  have hZμW : ZM (puAmalgam h.le) μ ≤ W := by
    rw [hW]; exact le_conjCl _ _
  have hWV : W ≤ Vv (puAmalgam h.le) α := by
    rw [hW]; exact conjCl_le_of_le_normalizer hZμV (stab_le_normalizer_vv h α)
  have hVQ : Vv (puAmalgam h.le) α ≤ Qv (puAmalgam h.le) α := vv_le_qv h (by omega) hα
  have hWs : W ≤ stab (puAmalgam h.le) α := hWV.trans (hVQ.trans (qv_le_stab _ α))
  have hVab : ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ = ⊥ := vv_comm_eq_bot h hb hα
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb'
    have h1 : ⁅a, b⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator (hWV ha) (hWV hb')
      rwa [hVab, Subgroup.mem_bot] at this
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  have hZαW : ZM (puAmalgam h.le) α ≤ W := by
    rw [hW]; exact zm_le_conjCl_zm h hdμ
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hDn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Dloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_dloc h α
  have hUn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Uloc h.le L α : Set 𝔘) :=
    stab_le_normalizer_uloc h α
  have hZDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer ((ZM (puAmalgam h.le) α ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf hZn hDn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hUDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer ((Uloc h.le L α ⊔ Dloc h.le L α : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf hUn hDn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hZUD : ZM (puAmalgam h.le) α ⊔ Dloc h.le L α = Uloc h.le L α ⊔ Dloc h.le L α := by
    apply le_antisymm
    · rw [zm_eq_uloc_sup_zloc h hfull hα]
      exact sup_le (sup_le_sup_left (zloc_le_dloc h α) _) le_sup_right
    · exact sup_le_sup_right (uloc_le_zm h hfull hα) _
  obtain ⟨Zk, hZk⟩ : ∃ Zk, Zk = W ⊓ (ZM (puAmalgam h.le) α ⊔ Dloc h.le L α) := ⟨_, rfl⟩
  have hZkW : Zk ≤ W := hZk ▸ inf_le_left
  have hZkn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Zk : Set 𝔘) :=
    hZk ▸ le_normalizer_inf hWn hZDn
  obtain ⟨X, _, π, ρ₀, hπs, hπk, hρ₀⟩ := exists_quotient_conj (K := stab (puAmalgam h.le) α)
    hWn hZkW hZkn (fun v hv w hw => by
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr (hWab v hv w hw)]
      exact Zk.one_mem)
  have : Finite ↥(stab (puAmalgam h.le) α) := finite_stab h hα
  have : Finite ↥W := Finite.of_injective _ (Subgroup.inclusion_injective hWs)
  have : Finite X := Finite.of_surjective π hπs
  have hπk' : ∀ v : ↥W, π v = 1 ↔ (v : 𝔘) ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
    intro v
    rw [hπk, hZk, Subgroup.mem_inf, hZUD]
    exact ⟨fun h' => h'.2, fun h' => ⟨v.2, h'⟩⟩
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow, hπk', Subgroup.coe_pow, ← hZUD]
    refine Subgroup.mem_sup_left (sq_mem_zm_of_mem_vv h hfull ?_ (hWV v.2))
    rw [hVab]
    exact bot_le
  have hZμs : ZM (puAmalgam h.le) μ ≤ stab (puAmalgam h.le) α := hZμW.trans hWs
  have hWQ : ⁅W, Qv (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
    rw [hW]
    exact commutator_conjCl_le hUDn (stab_le_normalizer_qv _ α) (hZμs.trans hUDn) hQUD
  have hQtriv : ∀ k : ↥(stab (puAmalgam h.le) α), (k : 𝔘) ∈ Qv (puAmalgam h.le) α → ρ₀ k = 1 := by
    intro k hk
    ext x
    obtain ⟨v, rfl⟩ := hπs x
    rw [MulAut.one_apply, hρ₀]
    have h1 : π (conjOn hWn k v * v⁻¹) = 1 := by
      rw [hπk']
      have e : ((conjOn hWn k v * v⁻¹ : ↥W) : 𝔘) = ⁅(k : 𝔘), (v : 𝔘)⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
      rw [e]
      have h2 := Subgroup.commutator_mem_commutator hk v.2
      rw [Subgroup.commutator_comm] at h2
      exact hWQ h2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have hψt : Function.Surjective (toSL3 ψ) := toSL3_surjective hψs
  have hker : (toSL3 ψ).ker ≤ ρ₀.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    exact hQtriv k ((S46.toSL3_eq_one_iff_mem_qv h hφ hα hψ k).mp hk)
  obtain ⟨ρ, hρ⟩ := exists_lift_of_ker_le hψt hker
  have hrange : ρ.range = ρ₀.range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨k, rfl⟩ := hψt g
      exact ⟨k, (hρ k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨toSL3 ψ k, hρ k⟩
  have hnt : ∃ (g : SL3 F) (x : X), ρ g x ≠ x := by
    by_contra hall
    push Not at hall
    apply hμB
    rw [zv_of_isMVtx _ hμM]
    intro z hz
    have hzl : ∀ l ∈ Ltil h.le L α, ⁅z, l⁆ ∈ ZM (puAmalgam h.le) α ⊔ Dloc h.le L α := by
      intro l hl
      have hlS : l ∈ stab (puAmalgam h.le) α := ltil_le_stab h α hl
      have h1 := hall (toSL3 ψ ⟨l, hlS⟩) (π ⟨z, hZμW hz⟩)
      rw [hρ, hρ₀] at h1
      have h2 : π (⟨z, hZμW hz⟩ * (conjOn hWn ⟨l, hlS⟩ ⟨z, hZμW hz⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      rw [hπk'] at h2
      have e : ((⟨z, hZμW hz⟩ * (conjOn hWn ⟨l, hlS⟩ ⟨z, hZμW hz⟩)⁻¹ : ↥W) : 𝔘) = ⁅z, l⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
        group
      rw [e] at h2
      rwa [hZUD]
    have hzl' := commutator_mem_zm_of_mem_zm_sup_dloc h hα hWab hWs hWn (hZμW hz) hzl
    refine Subgroup.subset_closure ⟨hZμV hz, fun l hl => ?_⟩
    rw [zv_of_isMVtx _ hα]
    exact hzl' l hl
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subgroup 𝔘,
      K₀ = ((ptStab : Subgroup (SL3 F)).comap (toSL3 ψ)).map (stab (puAmalgam h.le) α).subtype :=
    ⟨_, rfl⟩
  have hK₀s : K₀ ≤ stab (puAmalgam h.le) α := hK₀ ▸ Subgroup.map_subtype_le _
  have hmemK₀ : ∀ k : ↥(stab (puAmalgam h.le) α), toSL3 ψ k ∈ (ptStab : Subgroup (SL3 F)) →
      (k : 𝔘) ∈ K₀ := fun k hk => hK₀ ▸ ⟨k, hk, rfl⟩
  have hK₀W : conjCl K₀ (ZM (puAmalgam h.le) μ) ≤ W :=
    conjCl_le_of_le_normalizer hZμW (hK₀s.trans hWn)
  obtain ⟨W₀, hW₀d⟩ : ∃ W₀ : Subgroup X,
      W₀ = ((conjCl K₀ (ZM (puAmalgam h.le) μ)).subgroupOf W).map π := ⟨_, rfl⟩
  have hW₀ : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ W₀, ρ g w ∈ W₀ := by
    intro g hg w hw
    obtain ⟨k₁, rfl⟩ := hψt g
    rw [hW₀d] at hw ⊢
    obtain ⟨v, hv, rfl⟩ := hw
    rw [hρ, hρ₀]
    refine ⟨conjOn hWn k₁ v, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjOn_apply]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjCl K₀ _ (hmemK₀ k₁ hg)) _).mp
      (Subgroup.mem_subgroupOf.mp hv)
  have hgen : G6.submoduleClosure ρ.range W₀ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := hπs x
    have hle : conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ) ≤
        pre π (G6.submoduleClosure ρ.range W₀) := by
      refine iSup₂_le fun k hk => ?_
      rintro _ ⟨z, hz, rfl⟩
      have hzW : z ∈ W := hZμW hz
      have hkz : (MulAut.conj k).toMonoidHom z ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWn hk) z).mp hzW
      refine mem_pre.mpr ⟨hkz, ?_⟩
      have e : π ⟨(MulAut.conj k).toMonoidHom z, hkz⟩ = ρ (toSL3 ψ ⟨k, hk⟩) (π ⟨z, hzW⟩) := by
        rw [hρ, hρ₀]
        rfl
      rw [e]
      have hz0 : π ⟨z, hzW⟩ ∈ W₀ := by
        rw [hW₀d]
        exact ⟨⟨z, hzW⟩, Subgroup.mem_subgroupOf.mpr (le_conjCl _ _ hz), rfl⟩
      exact (le_iSup₂ (f := fun g (_ : g ∈ ρ.range) => W₀.map (g : MulAut X).toMonoidHom)
        (ρ (toSL3 ψ ⟨k, hk⟩)) ⟨_, rfl⟩) ⟨π ⟨z, hzW⟩, hz0, rfl⟩
    have hv0 : (v : 𝔘) ∈ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ) := by
      rw [← hW]
      exact v.2
    obtain ⟨_, hv'⟩ := mem_pre.mp (hle hv0)
    exact hv'
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : Subgroup 𝔘, W₁ = Subgroup.closure {y | ∃ k : ↥(stab (puAmalgam h.le) α),
      (((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 ∧
        ∃ z ∈ ZM (puAmalgam h.le) μ, (k : 𝔘) * z * (k : 𝔘)⁻¹ = y} := ⟨_, rfl⟩
  have hW₁W : W₁ ≤ W := by
    rw [hW₁, Subgroup.closure_le]
    rintro _ ⟨k, -, z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWn k.2) z).mp (hZμW hz)
  have hd' : 1 < (puAmalgam h.le).treeGraph.dist α' α := by rw [hc'.2.1]; omega
  have hadj21 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 2)
      (geo (puAmalgam h.le) α' α 1) := (adj_geo _ hd').symm
  have hM2 : IsMVtx _ (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hW₁Q : W₁ ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [hW₁, Subgroup.closure_le]
    rintro _ ⟨k, hk, z, hz, rfl⟩
    refine qv_le_qv _ h20 hM2 hadj21 (hB k hk ?_)
    rw [zm_smul]
    exact ⟨z, hz, rfl⟩
  have hoff : wOff ρ W₀ ≤ (W₁.subgroupOf W).map π := by
    refine iSup₂_le fun g hg => ?_
    obtain ⟨k₁, rfl⟩ := hψt g
    rintro _ ⟨y, hy, rfl⟩
    rw [hW₀d] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hρ, hρ₀]
    refine ⟨conjOn hWn k₁ v, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjOn_apply]
    have hle : conjCl K₀ (ZM (puAmalgam h.le) μ) ≤
        W₁.comap (MulAut.conj (k₁ : 𝔘)).toMonoidHom := by
      refine iSup₂_le fun k hk => ?_
      rw [hK₀] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_comap, hW₁]
      refine Subgroup.subset_closure ⟨k₁ * k', ?_, z, hz, ?_⟩
      · rw [map_mul]
        exact off_axis_mul_ptStab (Subgroup.mem_comap.mp hk') hg
      · simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          Subgroup.coe_subtype]
        group
    exact hle (Subgroup.mem_subgroupOf.mp hv)
  have hcommOff : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀) ≤
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ((W₁.subgroupOf W).map π) := by
    rw [G6.commOn_le_iff]
    intro x hx u hu
    exact G6.mem_commOn_of_mem hx (hoff hu)
  have hkey : ∀ z' : ↥(stab (puAmalgam h.le) α), (z' : 𝔘) ∈ ZM (puAmalgam h.le) α' →
      ∀ w : ↥W, (w : 𝔘) ∈ W₁ → ∃ y : ↥W,
        (y : 𝔘) ∈ Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) ∧
          ρ₀ z' (π w) * (π w)⁻¹ = π y := by
    intro z' hz' w hw
    refine ⟨conjOn hWn z' w * w⁻¹, ?_, ?_⟩
    · have e : ((conjOn hWn z' w * w⁻¹ : ↥W) : 𝔘) = ⁅(z' : 𝔘), (w : 𝔘)⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply, commutatorElement_def]
      rw [e, Usup, zv_of_isMVtx _ hα']
      exact Subgroup.commutator_mem_commutator hz' (hW₁Q hw)
    · rw [hρ₀, map_mul, map_inv]
  have hRle : critR (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans hZn)
  have hRU : critR (puAmalgam h.le) α α' ≤
      Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) := by
    have := S46.critR_le_usup_one h hc'
    rwa [critR, Subgroup.commutator_comm] at this
  have hadj01 : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hsq := card_usup_eq_sq h hφ hC hb hα' hadj01
  have hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) (wOff ρ W₀)) ≤
      Nat.card F := by
    rcases hT with ⟨hTE, hRq⟩ | ⟨hTc, hRq⟩
    ·
      obtain ⟨Y, hY⟩ : ∃ Y : Subgroup 𝔘,
          Y = Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) ⊓ W := ⟨_, rfl⟩
      have hYW : Y ≤ W := hY ▸ inf_le_right
      have hle : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) ((W₁.subgroupOf W).map π) ≤
          (Y.subgroupOf W).map π := by
        rw [G6.commOn_le_iff]
        rintro _ ⟨t, ht, rfl⟩ _ ⟨w, hw, rfl⟩
        obtain ⟨z', hz', rfl⟩ := mem_natImage.mp (hTE ht)
        obtain ⟨y, hyU, hy⟩ := hkey z' hz' w (Subgroup.mem_subgroupOf.mp hw)
        rw [hρ, hy]
        exact ⟨y, Subgroup.mem_subgroupOf.mpr (hY ▸ ⟨hyU, y.2⟩), rfl⟩
      have h1 := B1More.card_map_mul_card_inf_ker (Y.subgroupOf W) π
      have h2 : Nat.card ↥(Y.subgroupOf W) ≤ Fintype.card F ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYW).toEquiv, ← hsq]
        have : Finite ↥(Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1)) :=
          Nat.finite_of_card_ne_zero (by rw [hsq]; exact pow_ne_zero _ Fintype.card_ne_zero)
        exact Subgroup.card_le_of_le (hY ▸ inf_le_left)
      have hRW : critR (puAmalgam h.le) α α' ≤ W := hRle.trans hZαW
      have h3 : Nat.card ↥(critR (puAmalgam h.le) α α') ≤
          Nat.card ↥(Y.subgroupOf W ⊓ π.ker) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRW).toEquiv]
        refine Subgroup.card_le_of_le fun r hr => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf] at hr ⊢
          exact hY ▸ ⟨hRU hr, r.2⟩
        · rw [MonoidHom.mem_ker, hπk', ← hZUD]
          exact Subgroup.mem_sup_left (hRle (Subgroup.mem_subgroupOf.mp hr))
      have hq0 : 0 < Fintype.card F := Fintype.card_pos
      have h4 : Nat.card ↥((Y.subgroupOf W).map π) * Fintype.card F ≤
          Fintype.card F * Fintype.card F := by
        calc Nat.card ↥((Y.subgroupOf W).map π) * Fintype.card F
            ≤ Nat.card ↥((Y.subgroupOf W).map π) * Nat.card ↥(Y.subgroupOf W ⊓ π.ker) :=
              Nat.mul_le_mul_left _ (hRq.trans h3)
          _ = Nat.card ↥(Y.subgroupOf W) := h1
          _ ≤ Fintype.card F * Fintype.card F := by rw [← sq]; exact h2
      have h5 := Nat.le_of_mul_le_mul_right h4 hq0
      rw [← Nat.card_eq_fintype_card] at h5
      exact (Subgroup.card_le_of_le (hcommOff.trans hle)).trans h5
    ·
      have hRsq : Nat.card ↥(critR (puAmalgam h.le) α' α) = Fintype.card F ^ 2 := by
        have : Finite ↥(Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1)) :=
          Nat.finite_of_card_ne_zero (by rw [hsq]; exact pow_ne_zero _ Fintype.card_ne_zero)
        have e : critR (puAmalgam h.le) α' α = critR (puAmalgam h.le) α α' := by
          rw [critR, critR, Subgroup.commutator_comm]
        rw [e]
        exact le_antisymm (hsq ▸ Subgroup.card_le_of_le hRU) hRq
      have hRUe := S46.critR_eq_usup_of_card_sq h hc' hsq hRsq
      have hfixE : ∀ z' : ↥(stab (puAmalgam h.le) α), (z' : 𝔘) ∈ ZM (puAmalgam h.le) α' →
          ∀ y ∈ (W₁.subgroupOf W).map π, ρ₀ z' y = y := by
        rintro z' hz' _ ⟨w, hw, rfl⟩
        obtain ⟨y, hyU, hy⟩ := hkey z' hz' w (Subgroup.mem_subgroupOf.mp hw)
        have hy1 : π y = 1 := by
          rw [hπk', ← hZUD]
          refine Subgroup.mem_sup_left (hRle ?_)
          rw [← hRUe] at hyU
          rwa [critR, Subgroup.commutator_comm] at hyU
        rwa [hy1, mul_inv_eq_one] at hy
      have hY₁σ : ∀ k₁ : ↥(stab (puAmalgam h.le) α),
          ((toSL3 ψ k₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 →
          ((toSL3 ψ k₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 →
          ∀ y ∈ (W₁.subgroupOf W).map π, ρ₀ k₁ y ∈ (W₁.subgroupOf W).map π := by
        rintro k₁ h0 h1 _ ⟨w, hw, rfl⟩
        rw [hρ₀]
        refine ⟨conjOn hWn k₁ w, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjOn_apply]
        have hle : W₁ ≤ W₁.comap (MulAut.conj (k₁ : 𝔘)).toMonoidHom := by
          conv_lhs => rw [hW₁]
          rw [Subgroup.closure_le]
          rintro _ ⟨k, hk, z, hz, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, hW₁]
          refine Subgroup.subset_closure ⟨k₁ * k, ?_, z, hz, ?_⟩
          · rw [map_mul]
            exact off_axis_lnStab_mul h0 h1 hk
          · simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
        exact hle (Subgroup.mem_subgroupOf.mp hw)
      have hbot : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ)
          ((W₁.subgroupOf W).map π) ≤ ⊥ := by
        rw [G6.commOn_le_iff]
        rintro _ ⟨t, ht, rfl⟩ y hy
        obtain ⟨σ, h0, h1, hσ⟩ := hTc t ht
        obtain ⟨k₁, rfl⟩ := hψt σ
        obtain ⟨z', hz', hz't⟩ := mem_natImage.mp hσ
        have et : t = (toSL3 ψ k₁)⁻¹ * toSL3 ψ z' * toSL3 ψ k₁ := by rw [hz't]; group
        rw [et, map_mul, map_mul, map_inv, hρ, hρ, Subgroup.mem_bot,
          mul_inv_eq_one, MulAut.mul_apply, MulAut.mul_apply,
          hfixE z' hz' _ (hY₁σ k₁ h0 h1 y hy), MulAut.inv_apply, MulEquiv.symm_apply_apply]
      have h1 := (Subgroup.card_le_of_le (hcommOff.trans hbot))
      rw [Subgroup.card_bot] at h1
      exact h1.trans Nat.card_pos
  obtain ⟨-, hinf, hsup, dual, β, hβb, hβe⟩ := ms16_of_nontrivial hn hX2 hnt hW₀ hgen hR
  have hρ₀r : ∀ k : ↥(stab (puAmalgam h.le) α), ρ₀ k ∈ ρ.range := fun k => ⟨toSL3 ψ k, hρ k⟩
  have hPinv : ∀ (k : ↥(stab (puAmalgam h.le) α)), ∀ x ∈ commV ρ.range, ρ₀ k x ∈ commV ρ.range := by
    intro k x hx
    rw [← hρ k]
    exact S46.commV_inv ρ (toSL3 ψ k) hx
  have hβk : ∀ p : ↥(commV ρ.range), β p = 1 ↔ (p : X) ∈ (⊥ : Subgroup X) := by
    intro p
    rw [Subgroup.mem_bot, ← map_one β, hβb.1.eq_iff]
    exact ⟨fun h' => by rw [h']; rfl, fun h' => Subtype.ext h'⟩
  have hnat : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α) (pre π (commV ρ.range))
      (pre π (⊥ : Subgroup X)) ψ dual 1 := by
    cases dual with
    | false =>
      have h1 := isSumOfNaturalModulesVia_pre hρ₀ hπs hPinv bot_le (toSL3 ψ) β hβb.2 hβk
        (fun k p => by
          apply Multiplicative.toAdd.injective
          rw [toAdd_ofAdd, hβe (toSL3 ψ k) p _ (by rw [coe_resRho_apply, hρ])]
          rfl)
      have e : (specialLinearGroupEquivStatedSL 3 F).toMonoidHom.comp (toSL3 ψ) = ψ := by
        ext a : 1
        simp [toSL3]
      rwa [e] at h1
    | true =>
      have h1 := isSumOfNaturalModulesVia_pre hρ₀ hπs hPinv bot_le
        (transposeInv.comp (toSL3 ψ)) β hβb.2 hβk
        (fun k p => by
          apply Multiplicative.toAdd.injective
          rw [toAdd_ofAdd, hβe (toSL3 ψ k) p _ (by rw [coe_resRho_apply, hρ])]
          rfl)
      refine D432.isSumOfNaturalModulesVia_of_natAct_eq (φ := D432.dualSL ψ) (d := false)
        (fun a => ?_) h1
      rw [natAct_true, natAct_false, D432.toSL3_dualSL, coe_transposeInv]
  obtain ⟨C, hCd⟩ : ∃ C : Subgroup 𝔘, C = pre π (fixV ρ.range) := ⟨_, rfl⟩
  have hCW : C ≤ W := hCd ▸ pre_le _
  have hCn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (C : Set 𝔘) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    rintro _ ⟨c, hc0, rfl⟩
    rw [hCd] at hc0 ⊢
    obtain ⟨hcW, hcF⟩ := mem_pre.mp hc0
    have hkc : (MulAut.conj k).toMonoidHom c ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWn hk) c).mp hcW
    refine mem_pre.mpr ⟨hkc, ?_⟩
    have e : π ⟨(MulAut.conj k).toMonoidHom c, hkc⟩ = ρ₀ ⟨k, hk⟩ (π ⟨c, hcW⟩) := by
      rw [hρ₀]
      rfl
    rw [e, (mem_fixV.mp hcF) _ (hρ₀r ⟨k, hk⟩)]
    exact hcF
  have hZkbot : pre π (⊥ : Subgroup X) = Zk := pre_bot hπk hZkW
  have hZkUD : Zk ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
    rw [hZk, hZUD]
    exact inf_le_right
  have hsec := isSumOfNaturalModulesVia_transfer hnat (B := C) (V := W) (U := W)
    (by rw [hCd, ← pre_sup hπs, hsup, pre_top]) (by rw [hCd, ← pre_inf, hinf]) le_rfl
    (sup_eq_left.mpr hCW) hWn hCn (((pre_le _).trans hWs).trans hCn)
  rw [inf_eq_right.mpr hCW] at hsec
  refine ⟨dual, C, ?_, ?_, hWQ, hsec, ?_⟩
  ·
    refine (le_inf ((uloc_le_zm h hfull hα).trans hZαW) ?_).trans
      (hZk ▸ hCd ▸ le_pre hπk hZkW _)
    rw [hZUD]
    exact le_sup_left
  ·
    have h1 := commutator_pre_le_of_fix hρ₀ (C := fixV ρ.range) (S := ⊥) fun k c hc => by
      rw [(mem_fixV.mp hc) _ (hρ₀r k), mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [← hCd, hZkbot] at h1
    exact h1.trans hZkUD
  ·
    intro w hw g hg hmem
    rw [hCd] at hmem
    obtain ⟨hmW, hmF⟩ := mem_pre.mp hmem
    have e : (⟨w⁻¹ * (g * w * g⁻¹), hmW⟩ : ↥W) = (⟨w, hw⟩ : ↥W)⁻¹ * conjOn hWn ⟨g, hg⟩ ⟨w, hw⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply])
    have hcV : π ⟨w⁻¹ * (g * w * g⁻¹), hmW⟩ ∈ commV ρ.range := by
      rw [e, map_mul, map_inv, ← hρ₀, mul_comm]
      exact Subgroup.subset_closure ⟨ρ₀ ⟨g, hg⟩, hρ₀r _, π ⟨w, hw⟩, rfl⟩
    have h1 : π ⟨w⁻¹ * (g * w * g⁻¹), hmW⟩ = 1 := by
      have : π ⟨w⁻¹ * (g * w * g⁻¹), hmW⟩ ∈ commV ρ.range ⊓ fixV ρ.range := ⟨hcV, hmF⟩
      rwa [hinf, Subgroup.mem_bot] at this
    exact (hπk' _).mp h1

theorem exists_good_conj_or_secD_of_coords (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {α α' μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hμ : μ ∈ nablaSet h.le L α)
    (hQUD : ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {u d : 𝔘} (hu : u ∈ Uloc h.le L α) (hd : d ∈ Dloc h.le L α) {c : F} (hc0 : c ≠ 0)
    (huc : natVec hψ ⟨u, hu⟩ = c • ![1, 0, 0])
    (hax : ∀ v ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')), v 2 = 0)
    (hT : ((rootGroup 0 2 : Subgroup (SL3 F)) ≤ natImage ψ (ZM (puAmalgam h.le) α') ∧
        Fintype.card F ≤ Nat.card ↥(critR (puAmalgam h.le) α α')) ∨
      ((∀ t ∈ (rootGroup 0 2 : Subgroup (SL3 F)), ∃ σ : SL3 F,
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
          ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
          σ * t * σ⁻¹ ∈ natImage ψ (ZM (puAmalgam h.le) α')) ∧
        Fintype.card F ^ 2 ≤ Nat.card ↥(critR (puAmalgam h.le) α α'))) :
    (∃ k ∈ stab (puAmalgam h.le) α,
        (∃ w ∈ ZM (puAmalgam h.le) α', ⁅k * (u * d) * k⁻¹, w⁆ ∉ Dloc h.le L α) ∧
          ¬ ZM (puAmalgam h.le) (k • μ) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) ∨
      ∃ (dual : Bool) (C : Subgroup 𝔘),
        Uloc h.le L α ≤ C ∧ ⁅C, stab (puAmalgam h.le) α⁆ ≤ Uloc h.le L α ⊔ Dloc h.le L α ∧
        ⁅conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ), Qv (puAmalgam h.le) α⁆ ≤
          Uloc h.le L α ⊔ Dloc h.le L α ∧
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
          (conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ)) C ψ dual 1 ∧
        ∀ w ∈ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) μ),
          ∀ g ∈ stab (puAmalgam h.le) α, w⁻¹ * (g * w * g⁻¹) ∈ C →
            w⁻¹ * (g * w * g⁻¹) ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  by_cases hB : ∀ k : ↥(stab (puAmalgam h.le) α),
      (((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0 →
        ZM (puAmalgam h.le) ((k : 𝔘) • μ) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)
  · exact Or.inr (exists_secD_of_forall_le_qv h hφ hC hb hc hμ hQUD hψs hψ hT hB)
  · left
    push Not at hB
    obtain ⟨k, hk, hkQ⟩ := hB
    refine ⟨k, k.2, exists_commutator_not_mem_dloc h hφ hc.1 hψ hu hd k fun hfix => hk ?_, hkQ⟩
    have h1 := hax _ hfix
    rw [huc, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc0

end Bad


end CFSG.Quasithin.MS93.S4A.C441
