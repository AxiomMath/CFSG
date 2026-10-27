module

public import CFSG.Quasithin.MS93.S4AFAbs
public import CFSG.Quasithin.MS93.S4AFSec
public import CFSG.Quasithin.MS93.S4A431
public import CFSG.Quasithin.MS93.S46Qj

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

theorem stab_inf_centralizer_uloc {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) :
    stab (puAmalgam h.le) δ ⊓ Subgroup.centralizer (Uloc h.le L δ : Set _) = Qv _ δ := by
  have h1 := puTrans_inf_centralizer (hTM := h.le) (K := M) (K' := Uq M T L) le_rfl
    (Uq_le h.L_le) Subgroup.le_normalizer (le_normalizer_Uq h.le_normalizer) hδ
  rw [QjAux.inf_centralizer_Uq_eq h hφ, ← h.qv_eq hδ, puTrans_self h.le hδ] at h1
  exact h1.symm

theorem sq_eq_one_of_mem_zv (hfull : IsSL3Full M T L) {ρ : Vtx (puAmalgam h.le)} {z : _}
    (hz : z ∈ Zv (puAmalgam h.le) ρ) : z ^ 2 = 1 := by
  by_cases hρ : IsMVtx (puAmalgam h.le) ρ
  · rw [zv_of_isMVtx _ hρ, ← xm_eq_zm h hfull hρ] at hz
    exact sq_eq_one_of_mem_omegaOneCenterOf hz
  · rw [zv_of_not_isMVtx _ hρ] at hz
    exact sq_eq_one_of_mem_omegaOneCenterOf hz

theorem sq_mem_zm_of_mem_vv (hfull : IsSL3Full M T L) {δ : Vtx (puAmalgam h.le)}
    (hVc : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    {v : _} (hv : v ∈ Vv (puAmalgam h.le) δ) : v ^ 2 ∈ ZM (puAmalgam h.le) δ := by
  set S : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {v | v ∈ Vv (puAmalgam h.le) δ ∧ v ^ 2 ∈ ZM (puAmalgam h.le) δ}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have e : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
          simp only [sq, commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha2
          (hVc (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hb))) hb2
      one_mem' := ⟨Subgroup.one_mem _, by rw [one_pow]; exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        rw [inv_pow]
        exact Subgroup.inv_mem _ ha2 } with hS
  have hle : Vv (puAmalgam h.le) δ ≤ S := by
    refine iSup₂_le fun ρ hρ => ?_
    intro z hz
    refine ⟨zv_le_vv h hρ hz, ?_⟩
    rw [sq_eq_one_of_mem_zv h hfull hz]
    exact Subgroup.one_mem _
  exact (hle hv).2

theorem vv_ne_vi_one (hb : 2 < critDist (puAmalgam h.le)) {δ β : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β) :
    Vv (puAmalgam h.le) δ ≠ Vi (puAmalgam h.le) β 1 := by
  intro heq
  have h20 := h.hyp20
  have hβ : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hδβ]
    exact hδ
  have hZδ : ZM (puAmalgam h.le) δ ≤ Vi (puAmalgam h.le) β 1 := by
    rw [← zv_of_isMVtx _ hδ]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist β ρ ≤ 1}) => Zv (puAmalgam h.le) ρ) δ
      (by rw [Set.mem_ofPred_eq, tdist_comm, (SimpleGraph.dist_eq_one_iff_adj).mpr hδβ])
      le_rfl
  have hViQ : Vi (puAmalgam h.le) β 1 ≤ Qv _ β := by
    rw [← heq]
    exact (vv_le_qv h hb hδ).trans (qv_le_qv _ h20 hδ hδβ)
  have hbot := ms21_iii _ h20 hδ hδβ hViQ (heq ▸ stab_le_normalizer_vv h δ)
    (stab_le_normalizer_of_smul (F := fun ρ => Vi (puAmalgam h.le) ρ 1) _
      (fun g ρ => vi_smul _ g ρ 1) β)
  have hZ : ZH (puAmalgam h.le) β ≤ ⊥ := hbot ▸ (zh_le_zm _ hδβ).trans hZδ
  exact zh_ne_bot _ h20 hβ (le_bot_iff.mp hZ)

theorem not_commutator_ltil_le (hfull : IsSL3Full M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ β : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β)
    {X : Type} [CommGroup X] [Finite X] (hX2 : ∀ x : X, x ^ 2 = 1)
    {π : ↥(Vv (puAmalgam h.le) δ) →* X} (hπs : Function.Surjective π)
    (hπk : ∀ v : ↥(Vv (puAmalgam h.le) δ),
      π v = 1 ↔ (v : (puAmalgam h.le).Universal) ∈ ZM (puAmalgam h.le) δ)
    {ρ : ↥(stab (puAmalgam h.le) δ) →* MulAut X}
    (hρ : ∀ k v, ρ k (π v) = π (conjOn (stab_le_normalizer_vv h δ) k v)) :
    ¬ ⁅Vv (puAmalgam h.le) δ, Ltil h.le L δ⁆ ≤
      ⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ := by
  intro hle
  have h20 := h.hyp20
  have hZV := zm_le_vv h hδ
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (vv_le_qv h hb hδ).trans (qv_le_stab _ δ)
  have hVn := stab_le_normalizer_vv h δ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have hRn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn (stab_le_normalizer_qv _ δ))
      (stab_le_normalizer_zm _ δ)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hRV : ⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ ≤
      Vv (puAmalgam h.le) δ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hVn)) hZV
  have hV1 := vv_le_vi_sup_commutator h hfull hδ hδβ
  have hVNR : Vv (puAmalgam h.le) δ ≤ Vi (puAmalgam h.le) β 1 ⊔
      (⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ) :=
    hV1.trans (sup_le_sup_left hle _)
  have hNV : Vi (puAmalgam h.le) β 1 ≤ Vv _ δ := by
    refine iSup₂_le fun ρ hρ => zv_le_vv h ?_
    have := dist_triangle (puAmalgam h.le) δ β ρ
    rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hδβ] at this
    exact this.trans (by simp only [Set.mem_ofPred_eq] at hρ; omega)
  have hZN : ZM (puAmalgam h.le) δ ≤ Vi (puAmalgam h.le) β 1 := by
    rw [← zv_of_isMVtx _ hδ]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist β ρ ≤ 1}) => Zv (puAmalgam h.le) ρ) δ
      (by rw [Set.mem_ofPred_eq, tdist_comm, (SimpleGraph.dist_eq_one_iff_adj).mpr hδβ])
      le_rfl
  have hNn : stab (puAmalgam h.le) β ≤
      Subgroup.normalizer (Vi (puAmalgam h.le) β 1 : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun ρ => Vi (puAmalgam h.le) ρ 1) _
      (fun g ρ => vi_smul _ g ρ 1) β
  have hQβ : Qv (puAmalgam h.le) δ ≤ stab _ β :=
    (qv_le_qv _ h20 hδ hδβ).trans (qv_le_stab _ β)
  set Nt : Subgroup X := ((Vi (puAmalgam h.le) β 1 ⊓ Vv _ δ).subgroupOf (Vv _ δ)).map π
    with hNt
  set Q₀ := ((Qv (puAmalgam h.le) δ).subgroupOf (stab _ δ)).map ρ with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := by
    have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
      rw [← isMVtx_iff_of_adj _ hδβ]
      exact hδ
    have h1 : IsPGroup 2 (Qv (puAmalgam h.le) δ) :=
      (isPGroup_qv _ h20 hβH).to_le (qv_le_qv _ h20 hδ hδβ)
    have h2 : IsPGroup 2 ((Qv (puAmalgam h.le) δ).subgroupOf (stab _ δ)) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe hQs).symm
    exact h2.map ρ
  have hNtinv : ∀ a ∈ Q₀, ∀ x ∈ Nt, a x ∈ Nt := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨n, hn, rfl⟩
    rw [hρ]
    refine ⟨conjOn (stab_le_normalizer_vv h δ) q n, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjOn_apply]
    have hn' := Subgroup.mem_subgroupOf.mp hn
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hVn q.2) _).mp n.2⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNn (hQβ (Subgroup.mem_subgroupOf.mp hq))) _).mp hn'.1
  have hpreR := pre_commV hρ hπk hZV hπs hQs
  have hsup : commV Q₀ ⊔ Nt = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := hπs x
    have hv : (v : (puAmalgam h.le).Universal) ∈ ((Vi (puAmalgam h.le) β 1 ⊔
        (⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ) :
          Subgroup _) : Set _) := hVNR v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hNV.trans hVs).trans hRn)] at hv
    obtain ⟨m, hm, r, hr, hmr⟩ := hv
    have hrV : r ∈ Vv (puAmalgam h.le) δ := hRV hr
    have hmV : m ∈ Vv (puAmalgam h.le) δ := hNV hm
    have hr' : r ∈ pre π (commV Q₀) := by rw [hpreR]; exact hr
    obtain ⟨_, hrC⟩ := mem_pre.mp hr'
    have e : v = ⟨m, hmV⟩ * ⟨r, hrV⟩ := Subtype.ext hmr.symm
    rw [e, map_mul, mul_comm]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hrC) (Subgroup.mem_sup_right ?_)
    exact ⟨⟨m, hmV⟩, Subgroup.mem_subgroupOf.mpr ⟨hm, hmV⟩, rfl⟩
  have htop := eq_top_of_commV_sup hX2 hQ₀2 hNtinv hsup
  have hVN : Vv (puAmalgam h.le) δ ≤ Vi (puAmalgam h.le) β 1 := by
    intro v hv
    have h1 : v ∈ pre π Nt := mem_pre.mpr ⟨hv, by rw [htop]; trivial⟩
    rw [hNt, pre_map hπk (le_inf hZN hZV) inf_le_right] at h1
    exact h1.1
  exact vv_ne_vi_one h hb hδ hδβ (le_antisymm hVN hNV)

theorem sqtkGroup_SL3_of_sqtkQuot (hSQ : SQTKQuot) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) : SQTKGroup (SL3 F) := by
  set ψL : ↥L →* SL3 F := (toSL3 φ).comp (Subgroup.inclusion h.L_le) with hψL
  have hψLs : Function.Surjective ψL := fun y => by
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφ.2.1 (specialLinearGroupEquivStatedSL 3 F y)
    refine ⟨⟨ℓ, hℓL⟩, ?_⟩
    have e1 : ψL ⟨ℓ, hℓL⟩ = (specialLinearGroupEquivStatedSL 3 F).symm (φ ℓ) := rfl
    rw [e1, hℓ, MulEquiv.symm_apply_apply]
  exact hSQ ↥L (SL3 F) (InternalSec.sqtkGroup_mono h.sqtk h.L_le) ψL hψLs isQuasisimple_SL3

theorem isC1_of_crit (h14 : MS14AS) (hSQ : SQTKQuot) (hC : CentHyp (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {μ δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ δ)
    (hVab : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    (hsmall : (ZM (puAmalgam h.le) δ).relIndex
        (⁅Vv (puAmalgam h.le) δ, ZM (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) δ) ≤
      Fintype.card F) :
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
  have hcomm : Nat.card (commV (A.map ρ)) ≤ Nat.card F := by
    rw [← card_pre hπk hZV hπs, pre_commV hρ hπk hZV hπs hAs, Nat.card_eq_fintype_card]
    exact hsmall
  have hN : ¬ commV (Lh.map ρ) ≤ commV (Q.map ρ) := by
    intro hle
    apply not_commutator_ltil_le h hfull hb hδ hδβ hX2 hπs hπk hρ
    have h1 := pre_mono (π := π) hle
    rw [pre_commV hρ hπk hZV hπs (ltil_le_stab h δ), pre_commV hρ hπk hZV hπs hQs] at h1
    exact le_sup_left.trans h1
  have hi := fix_commV_ker h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ hQ2 ρ hLh hA2 hAc hqA hcomm hN
  obtain ⟨C, hKC, hCfix, hPC, hPiC, F', iF', fF', hFF', τ, β', hτs, hβ's, hβ'k, hβ'e⟩ :=
    natSplit_quot h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ ρ hA2 hAc hqA hcomm
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

theorem s4CFF_of (h14 : MS14AS) (hSQ : SQTKQuot) (h32 : S32) : S4CFF := by
  intro G _ _ M T L h F _ _ φ hyp μ δ hc hVab hsmall
  exact isC1_of_crit h h14 hSQ (centHyp_of_S32 h32 h) hyp.2.2 hyp.2.1 hc hVab hsmall

end CFSG.Quasithin.MS93.S4A
