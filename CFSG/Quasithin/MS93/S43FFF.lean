module

public import CFSG.Quasithin.MS93.S43FC1
public import CFSG.Quasithin.MS93.S4AFMain
import CFSG.Quasithin.MS93.S34FCore
import CFSG.Quasithin.MS93.S34GB

public section

namespace CFSG.Quasithin.MS93.S43F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S4A.F CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Kernel

variable (h : PUHyp M T L) (hU : IsSL3U M T L)
include h hU

theorem inf_centralizer_Uq_eq_of_isSL3U :
    M ⊓ Subgroup.centralizer (Uq M T L : Set G) = pCoreOf 2 M := by
  obtain ⟨-, -, n, F, _, _, a, hn, has, hnat⟩ := hU
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  refine le_antisymm ?_ (le_inf (pCoreOf_le' M) (S34F.pCoreOf_le_centralizer_Uq h))
  have hKn : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (Uq M T L : Set G) :
      Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKn ?_
  have hker := QjAux.ker_le_pCore_of_surjective_sl3 h.quasisimple hF (toSL3_surjective has)
  rintro ⟨k, hkM, hkC⟩
  obtain ⟨e, he⟩ := QjAux.exists_pow_mem_of_mem_sup (h.le.trans h.le_normalizer) h.isPGroup
    (h.eq_sup ▸ hkM)
  have hkeC : k ^ 2 ^ e ∈ Subgroup.centralizer (Uq M T L : Set G) := Subgroup.pow_mem _ hkC _
  have hψ1 : toSL3 a ⟨k ^ 2 ^ e, he⟩ = 1 := by
    refine (toSL3_eq_one_iff hnat _).mpr fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp hkeC v hv
    show k ^ 2 ^ e * v * (k ^ 2 ^ e)⁻¹ = v
    rw [← this, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := isPGroup_cfsgPCore ↥L ⟨_, hker hψ1⟩
  have hc' : (k ^ 2 ^ e) ^ 2 ^ c = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hc
    simpa using this
  refine ⟨e + c, Subtype.ext ?_⟩
  simp [pow_add, pow_mul, hc']

theorem stab_inf_centralizer_uloc_of_isSL3U {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    stab (puAmalgam h.le) δ ⊓ Subgroup.centralizer (Uloc h.le L δ : Set _) = Qv _ δ := by
  have h1 := puTrans_inf_centralizer (hTM := h.le) (K := M) (K' := Uq M T L) le_rfl
    (Uq_le h.L_le) Subgroup.le_normalizer (le_normalizer_Uq h.le_normalizer) hδ
  rw [inf_centralizer_Uq_eq_of_isSL3U h hU, ← h.qv_eq hδ, puTrans_self h.le hδ] at h1
  exact h1.symm

theorem flat_inf_centralizer_uloc {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    S34F.flat h δ ⊓ Subgroup.centralizer (Uloc h.le L δ : Set _) = Qv _ δ := by
  have h1 := stab_inf_centralizer_uloc_of_isSL3U h hU hδ
  refine le_antisymm ((inf_le_inf_right _ (flat_le_stab h δ)).trans h1.le) ?_
  exact le_inf (qv_le_flat h hδ) (h1.ge.trans inf_le_right)

end Kernel

section Exp

variable (h : PUHyp M T L)
include h

theorem sq_eq_one_of_mem_zv_gen {ρ : Vtx (puAmalgam h.le)} {z : (puAmalgam h.le).Universal}
    (hz : z ∈ Zv (puAmalgam h.le) ρ) : z ^ 2 = 1 := by
  by_cases hρ : IsMVtx (puAmalgam h.le) ρ
  · rw [zv_of_isMVtx _ hρ] at hz
    exact (isElemAbelian_zm _ h.hyp20 h.critDist_pos hρ).2 z hz
  · rw [zv_of_not_isMVtx _ hρ] at hz
    exact sq_eq_one_of_mem_omegaOneCenterOf hz

theorem sq_mem_zm_of_mem_vv_gen {δ : Vtx (puAmalgam h.le)}
    (hVc : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    {v : (puAmalgam h.le).Universal} (hv : v ∈ Vv (puAmalgam h.le) δ) :
    v ^ 2 ∈ ZM (puAmalgam h.le) δ := by
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
    rw [sq_eq_one_of_mem_zv_gen h hz]
    exact Subgroup.one_mem _
  exact (hle hv).2

end Exp

section Nontrivial

variable (h : PUHyp M T L)
include h

theorem not_commutator_ltil_le_flat (hb : 2 < critDist (puAmalgam h.le))
    {δ β : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β)
    {X : Type} [CommGroup X] [Finite X] (hX2 : ∀ x : X, x ^ 2 = 1)
    {π : ↥(Vv (puAmalgam h.le) δ) →* X} (hπs : Function.Surjective π)
    (hπk : ∀ v : ↥(Vv (puAmalgam h.le) δ),
      π v = 1 ↔ (v : (puAmalgam h.le).Universal) ∈ ZM (puAmalgam h.le) δ)
    {ρ : ↥(S34F.flat h δ) →* MulAut X}
    (hρ : ∀ k v, ρ k (π v) =
      π (conjOn ((flat_le_stab h δ).trans (stab_le_normalizer_vv h δ)) k v)) :
    ¬ ⁅Vv (puAmalgam h.le) δ, Ltil h.le L δ⁆ ≤
      ⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ := by
  intro hle
  have h20 := h.hyp20
  have hZV := zm_le_vv h hδ
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (vv_le_qv h hb hδ).trans (qv_le_stab _ δ)
  have hVn := stab_le_normalizer_vv h δ
  have hQs : Qv (puAmalgam h.le) δ ≤ stab _ δ := qv_le_stab _ δ
  have hQf : Qv (puAmalgam h.le) δ ≤ S34F.flat h δ := qv_le_flat h hδ
  have hfs := flat_le_stab h δ
  have hRn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn (stab_le_normalizer_qv _ δ))
      (stab_le_normalizer_zm _ δ)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hRV : ⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆ ⊔ ZM (puAmalgam h.le) δ ≤
      Vv (puAmalgam h.le) δ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hVn)) hZV
  have hV1 := S34G.vv_le_vi_sup_commutator_gen h hδ hδβ
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
  set Q₀ := ((Qv (puAmalgam h.le) δ).subgroupOf (S34F.flat h δ)).map ρ with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := by
    have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
      rw [← isMVtx_iff_of_adj _ hδβ]
      exact hδ
    have h1 : IsPGroup 2 (Qv (puAmalgam h.le) δ) :=
      (isPGroup_qv _ h20 hβH).to_le (qv_le_qv _ h20 hδ hδβ)
    have h2 : IsPGroup 2 ((Qv (puAmalgam h.le) δ).subgroupOf (S34F.flat h δ)) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe hQf).symm
    exact h2.map ρ
  have hNtinv : ∀ a ∈ Q₀, ∀ x ∈ Nt, a x ∈ Nt := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨n, hn, rfl⟩
    rw [hρ]
    refine ⟨conjOn (hfs.trans (stab_le_normalizer_vv h δ)) q n, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjOn_apply]
    have hn' := Subgroup.mem_subgroupOf.mp hn
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hVn (hfs q.2)) _).mp n.2⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNn (hQβ (Subgroup.mem_subgroupOf.mp hq))) _).mp hn'.1
  have hpreR := pre_commV hρ hπk hZV hπs hQf
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

theorem sqtkGroup_SL3_of_flat (hSQ : SQTKQuot) {F : Type} [Field F] [Fintype F]
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)} (hφs : Function.Surjective φ) :
    SQTKGroup (SL3 F) :=
  hSQ ↥(L ⊔ pCoreOf 2 M) (SL3 F)
    (InternalSec.sqtkGroup_mono h.sqtk (sup_le h.L_le (pCoreOf_le' M))) (toSL3 φ)
    (toSL3_surjective hφs) S46.isQuasisimple_SL3

end Nontrivial

section Main

theorem isC1Flat_of_crit (h14 : MS14AS) (hSQ : SQTKQuot) (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)}
    (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1)
    (hb : 2 < critDist (puAmalgam h.le)) {μ δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ δ)
    (hVab : ⁅Vv (puAmalgam h.le) δ, Vv (puAmalgam h.le) δ⁆ ≤ ZM (puAmalgam h.le) δ)
    (hsmall : (ZM (puAmalgam h.le) δ).relIndex
        (⁅Vv (puAmalgam h.le) δ, ZM (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) δ) ≤
      Fintype.card F) :
    IsC1Flat h (Fintype.card F) δ (Vv (puAmalgam h.le) δ) (ZM (puAmalgam h.le) δ) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hδ : IsMVtx _ δ := hc'.1
  have hδβ := adj_geo_one_of_isCritical _ hb0 hc'
  have hAf : ZM (puAmalgam h.le) μ ≤ S34F.flat h δ := S34F.zm_le_flat h hU hc
  have hZV := zm_le_vv h hδ
  have hQf : Qv (puAmalgam h.le) δ ≤ S34F.flat h δ := qv_le_flat h hδ
  have hfs := flat_le_stab h δ
  have : Finite ↥(stab (puAmalgam h.le) δ) := finite_stab h hδ
  have : Finite ↥(S34F.flat h δ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hfs)
  have : Finite ↥(Vv (puAmalgam h.le) δ) := Finite.of_injective _
    (Subgroup.inclusion_injective ((vv_le_qv h hb hδ).trans (qv_le_stab _ δ)))
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := S34F.exists_natural_flat_at h hφs hφ hδ
  obtain ⟨ψμ, -, hψμ⟩ := S34F.exists_natural_flat_at h hφs hφ hc.1
  have hψs : Function.Surjective (toSL3 ψ₀) := toSL3_surjective hψ₀s
  have hsq := sqtkGroup_SL3_of_flat h hSQ hφs
  set Q := (Qv (puAmalgam h.le) δ).subgroupOf (S34F.flat h δ) with hQdef
  have hQ : (toSL3 ψ₀).ker = Q := by
    ext g
    rw [MonoidHom.mem_ker, toSL3_eq_one_iff hψ₀, hQdef, Subgroup.mem_subgroupOf,
      ← flat_inf_centralizer_uloc h hU hδ]
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
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hQf).symm
  set Lh := (Ltil h.le L δ).subgroupOf (S34F.flat h δ) with hLhdef
  have hLh : ⁅Lh, Lh⁆ = Lh := by
    apply Subgroup.map_injective (S34F.flat h δ).subtype_injective
    rw [Subgroup.map_commutator, hLhdef, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (ltil_le_flat h δ), ltil_perfect h hδ]
  obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := S34F.flat h δ)
    (hfs.trans (stab_le_normalizer_vv h δ)) hZV (hfs.trans (stab_le_normalizer_zm _ δ))
    (fun v hv w hw => hVab (Subgroup.commutator_mem_commutator hv hw))
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact sq_mem_zm_of_mem_vv_gen h hVab v.2
  set A := (ZM (puAmalgam h.le) μ).subgroupOf (S34F.flat h δ) with hAdef
  have hA2 : ∀ a ∈ A, toSL3 ψ₀ a ^ 2 = 1 := by
    intro a ha
    have h1 : (a : (puAmalgam h.le).Universal) ^ 2 = 1 := by
      refine sq_eq_one_of_mem_zv_gen h (ρ := μ) ?_
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
    obtain ⟨-, hcard', hrel, -, -, hne⟩ := S34F.s35_core_flat h hU hC hcard hc hψμ hψ₀
    have h1 : Module.finrank F (fixN (natImage ψμ (ZM (puAmalgam h.le) δ))) < 3 := by
      have := Submodule.finrank_lt (fixN_ne_top hne)
      rwa [Module.finrank_fin_fun] at this
    change Nat.card F ≤ Nat.card (natImage ψ₀ (ZM (puAmalgam h.le) μ))
    rw [hcard', hrel]
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (by omega)
  have hcomm : Nat.card (commV (A.map ρ)) ≤ Nat.card F := by
    rw [← card_pre hπk hZV hπs, pre_commV hρ hπk hZV hπs hAf, Nat.card_eq_fintype_card]
    exact hsmall
  have hN : ¬ commV (Lh.map ρ) ≤ commV (Q.map ρ) := by
    intro hle
    apply not_commutator_ltil_le_flat h hb hδ hδβ hX2 hπs hπk hρ
    have h1 := pre_mono (π := π) hle
    rw [pre_commV hρ hπk hZV hπs (ltil_le_flat h δ), pre_commV hρ hπk hZV hπs hQf] at h1
    exact le_sup_left.trans h1
  have hi := fix_commV_ker h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ hQ2 ρ hLh hA2 hAc hqA hcomm hN
  obtain ⟨C, hKC, hCfix, hPC, hPiC, F', iF', fF', hFF', τ, β', hτs, hβ's, hβ'k, hβ'e⟩ :=
    natSplit_quot h14 hSQ hsq hFn hX2 (toSL3 ψ₀) hψs hQ ρ hA2 hAc hqA hcomm
      (fun h' => hN ((G6.commV_mono (Subgroup.map_le_range ρ Lh)).trans h'))
  have hKq := pre_commV hρ hπk hZV hπs hQf
  have hKP : pre π (commV ρ.range) =
      ⁅Vv (puAmalgam h.le) δ, S34F.flat h δ⁆ ⊔ ZM (puAmalgam h.le) δ := by
    have := pre_commV hρ hπk hZV hπs (le_refl (S34F.flat h δ))
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  let _ : Fintype F' := Fintype.ofFinite F'
  refine ⟨?_, pre π C, ?_, pre_le C, ?_, ?_, ?_, F', iF', inferInstance,
    (specialLinearGroupEquivStatedSL 3 F').toMonoidHom.comp τ, ?_, ?_, ?_⟩
  · calc ⁅⁅Vv (puAmalgam h.le) δ, Qv (puAmalgam h.le) δ⁆, Ltil h.le L δ⁆
        ≤ ⁅pre π (commV (Q.map ρ)), Ltil h.le L δ⁆ :=
          Subgroup.commutator_mono (hKq ▸ le_sup_left) le_rfl
      _ ≤ ZM (puAmalgam h.le) δ :=
          commutator_pre_le_of_centralize hρ hπk (ltil_le_flat h δ)
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

end Main

end CFSG.Quasithin.MS93.S43F
