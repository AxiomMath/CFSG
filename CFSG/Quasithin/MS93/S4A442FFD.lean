module

public import CFSG.Quasithin.MS93.S4A442Stmt
public import CFSG.Quasithin.MS93.S4A442P1
public import CFSG.Quasithin.MS93.S45FF
public import CFSG.Quasithin.MS93.S4A44Nabla
public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.MS93.S4A431G
public import CFSG.Quasithin.MS93.S4AFcMain

public section

namespace CFSG.Quasithin.MS93.S4A.P442

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A.F
open scoped commutatorElement

section Grp

variable {G : Type} [Group G]

private def commSub' (H Y N : Subgroup G) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup G where
  carrier := {v | v ∈ H ∧ ∀ y ∈ Y, ⁅v, y⁆ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN ha) _).mp (hb' y hy)) (ha' y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) _).mp (N.inv_mem (ha' y hy))

private theorem commutator_sup_le_of' {A B Y N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅A, Y⁆ ≤ N) (hB : ⁅B, Y⁆ ≤ N) : ⁅A ⊔ B, Y⁆ ≤ N := by
  have hK : A ⊔ B ≤ commSub' (A ⊔ B) Y N (sup_le hAN hBN) := by
    refine sup_le (fun v hv => ⟨Subgroup.mem_sup_left hv, fun y hy =>
      hA (Subgroup.commutator_mem_commutator hv hy)⟩) (fun v hv => ⟨Subgroup.mem_sup_right hv,
      fun y hy => hB (Subgroup.commutator_mem_commutator hv hy)⟩)
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hK hv).2 y hy

private theorem le_normalizer_commutator'' {Z A B : Subgroup G}
    (hA : Z ≤ Subgroup.normalizer (A : Set G)) (hB : Z ≤ Subgroup.normalizer (B : Set G)) :
    Z ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hA hz),
    map_conj_eq_of_mem_normalizer (hB hz)]

theorem commutator_eq_commutator_commutator {A L : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hA : ⁅A, A⁆ = ⊥) :
    ⁅A, L⁆ = ⁅⁅A, L⁆, L⁆ := by
  have hAL : ⁅A, L⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hLA
  have hLAL : L ≤ Subgroup.normalizer ((⁅A, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator'' hLA Subgroup.le_normalizer
  have hle : ⁅⁅A, L⁆, L⁆ ≤ ⁅A, L⁆ := Subgroup.le_normalizer_iff_commutator_le_left.mp hLAL
  refine le_antisymm ?_ hle
  have hLN : L ≤ Subgroup.normalizer ((⁅⁅A, L⁆, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator'' hLAL Subgroup.le_normalizer
  have hAc : A ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hA
  have hAN : A ≤ Subgroup.normalizer ((⁅⁅A, L⁆, L⁆ : Subgroup G) : Set G) := by
    refine le_normalizer_of_map_conj_le fun a ha => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ A := hAL (hle hx)
    have e : (MulAut.conj a).toMonoidHom x = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [(Subgroup.mem_centralizer_iff.mp (hAc ha) x hxA).symm, mul_inv_cancel_right]
    rw [e]
    exact hx
  have h1 : ⁅⁅L, A⁆, L⁆ ≤ ⁅⁅A, L⁆, L⁆ := by rw [Subgroup.commutator_comm L A]
  have key : ⁅⁅L, L⁆, A⁆ ≤ ⁅⁅A, L⁆, L⁆ := three_subgroups_le hLN hLN hAN h1 le_rfl
  rwa [hLp, Subgroup.commutator_comm L A] at key

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem not_commutator_le_of_conf (h14 : MS14AS) (hSQ : SQTKQuot) (hC : CentHyp 𝔛)
    (hb : 4 < critDist 𝔛)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    {α α' δ : Vtx 𝔛} (hconf : Conf442 𝔛 α α' δ)
    (hidx : (Qv 𝔛 α).relIndex (Vv 𝔛 δ) ≤ Fintype.card F) :
    ¬ ⁅ZM 𝔛 (geo 𝔛 α α' 2), Vv 𝔛 δ ⊓ Qv 𝔛 α⁆ ≤ ZM 𝔛 δ ⊔ Dloc h.le L δ := by
  intro hR
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := ms21_v _ h20
  obtain ⟨hc, hA, -, hdδ, hpath⟩ := hconf
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hc.2.1
  set γ := geo 𝔛 α α' 2 with hγdef
  have hδ2 : geo 𝔛 α δ (2 * (n - 1)) = δ := by
    rw [show 2 * (n - 1) = (puAmalgam h.le).treeGraph.dist α δ by omega, geo_dist]
  have hcδ : IsCritical 𝔛 δ γ := by
    have := hpath (n - 1) (by omega) (by omega)
    rwa [hδ2, show critDist 𝔛 - 2 * (n - 1) = 2 by omega] at this
  have hδ : IsMVtx 𝔛 δ := hcδ.1
  have hcγ : IsCritical 𝔛 γ δ := ms22_iii _ h20 hb0 hC hcδ
  have hγ : IsMVtx 𝔛 γ := hcγ.1
  have hQs : Qv 𝔛 δ ≤ stab 𝔛 δ := qv_le_stab _ δ
  have hVs : Vv 𝔛 δ ≤ stab 𝔛 δ := (vv_le_qv h (by omega) hδ).trans hQs
  have hVn : stab 𝔛 δ ≤ Subgroup.normalizer (Vv 𝔛 δ : Set 𝔘) := stab_le_normalizer_vv h δ
  have hZn : stab 𝔛 δ ≤ Subgroup.normalizer (ZM 𝔛 δ : Set 𝔘) := stab_le_normalizer_zm _ δ
  have hDn : stab 𝔛 δ ≤ Subgroup.normalizer (Dloc h.le L δ : Set 𝔘) :=
    stab_le_normalizer_dloc h δ
  have hQn : stab 𝔛 δ ≤ Subgroup.normalizer (Qv 𝔛 δ : Set 𝔘) := stab_le_normalizer_qv _ δ
  have hLs : Ltil h.le L δ ≤ stab 𝔛 δ := ltil_le_stab h δ
  have hLp : ⁅Ltil h.le L δ, Ltil h.le L δ⁆ = Ltil h.le L δ := ltil_perfect h hδ
  have hZV : ZM 𝔛 δ ≤ Vv 𝔛 δ := zm_le_vv h hδ
  have hVab : ⁅Vv 𝔛 δ, Vv 𝔛 δ⁆ = ⊥ := vv_comm_eq_bot h hb hδ
  have hVc : ⁅Vv 𝔛 δ, Vv 𝔛 δ⁆ ≤ ZM 𝔛 δ := by rw [hVab]; exact bot_le
  have hZL : ⁅ZM 𝔛 δ, Ltil h.le L δ⁆ ≤ ZM 𝔛 δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hZn)
  set B := ZM 𝔛 δ ⊔ (Vv 𝔛 δ ⊓ Dloc h.le L δ) with hBdef
  have hBn : stab 𝔛 δ ≤ Subgroup.normalizer (B : Set 𝔘) :=
    (le_inf hZn ((le_inf hVn hDn).trans (Subgroup.inf_normalizer_le_normalizer_inf))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hBV : B ≤ Vv 𝔛 δ := sup_le hZV inf_le_left
  have hBs : B ≤ stab 𝔛 δ := hBV.trans hVs
  have hBL : ⁅B, Ltil h.le L δ⁆ ≤ ZM 𝔛 δ := by
    refine commutator_sup_le_of' (hZV.trans hVs |>.trans hZn) ((inf_le_left.trans hVs).trans hZn)
      hZL ?_
    have : ⁅Vv 𝔛 δ ⊓ Dloc h.le L δ, Ltil h.le L δ⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (inf_le_right.trans (dloc_le_centralizer_ltil h hδ))
    rw [this]
    exact bot_le
  have hYs : ZM 𝔛 γ ≤ stab 𝔛 δ := zm_le_stab_of_isCritical _ h20 hb0 hcδ
  have hY2 : ∀ y ∈ ZM 𝔛 γ, y ^ 2 ∈ Qv 𝔛 δ := by
    intro y hy
    have : y ^ 2 = 1 := sq_eq_one_of_mem_zv h hfull (ρ := γ) (by rwa [zv_of_isMVtx _ hγ])
    rw [this]
    exact (Qv 𝔛 δ).one_mem
  have hYc : ⁅ZM 𝔛 γ, ZM 𝔛 γ⁆ ≤ Qv 𝔛 δ := by
    have hZab : ZM 𝔛 γ ≤ Subgroup.centralizer (ZM 𝔛 γ : Set 𝔘) :=
      (zm_le_centralizer_qv _ h20 hγ).trans (Subgroup.centralizer_le (zm_le_qv_self _ hγ hb0))
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZab]
    exact bot_le
  have hYq : Fintype.card F ≤ (Qv 𝔛 δ).relIndex (ZM 𝔛 γ) := by
    obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h hφ hγ
    obtain ⟨ψδ, -, hψδ⟩ := exists_natural_Uloc h hφ hδ
    obtain ⟨-, -, hrel, -, -, hne⟩ := s35_core h hC hφ hcγ hψγ hψδ
    have h1 : Module.finrank F (fixN (natImage ψγ (ZM 𝔛 δ))) < 3 := by
      have := Submodule.finrank_lt (fixN_ne_top hne)
      rwa [Module.finrank_fin_fun] at this
    rw [hrel, ← Nat.card_eq_fintype_card]
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (by omega)
  have hR' : ⁅Vv 𝔛 δ ⊓ Qv 𝔛 α, ZM 𝔛 γ⁆ ≤ B := by
    intro x hx
    have hxV : x ∈ Vv 𝔛 δ := (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hYs.trans hVn)) hx
    have hxZD : x ∈ ZM 𝔛 δ ⊔ Dloc h.le L δ := by
      rw [Subgroup.commutator_comm] at hx
      exact hR hx
    have hDZ : Dloc h.le L δ ≤ Subgroup.normalizer (ZM 𝔛 δ : Set 𝔘) :=
      ((dloc_le_qv h hδ).trans hQs).trans hZn
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDZ] at hxZD
    obtain ⟨z, hz, d, hdD, rfl⟩ := hxZD
    have hdV : d ∈ Vv 𝔛 δ := by
      have := (Vv 𝔛 δ).mul_mem ((Vv 𝔛 δ).inv_mem (hZV hz)) hxV
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right ⟨hdV, hdD⟩)
  have hNY : ⁅(Vv 𝔛 δ ⊓ Qv 𝔛 α) ⊔ B, ZM 𝔛 γ⁆ ≤ B :=
    commutator_sup_le_of' ((inf_le_left.trans hVs).trans hBn) (hBs.trans hBn) hR'
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hYs.trans hBn))
  have : Finite ↥(stab 𝔛 δ) := finite_stab h hδ
  have : Finite ↥(Vv 𝔛 δ) := Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hNidx : ((Vv 𝔛 δ ⊓ Qv 𝔛 α) ⊔ B).relIndex (Vv 𝔛 δ) ≤ Fintype.card F := by
    have hne : ∀ H' : Subgroup 𝔘, H'.relIndex (Vv 𝔛 δ) ≠ 0 :=
      fun H' => Subgroup.index_ne_zero_of_finite
    calc ((Vv 𝔛 δ ⊓ Qv 𝔛 α) ⊔ B).relIndex (Vv 𝔛 δ)
        ≤ (Vv 𝔛 δ ⊓ Qv 𝔛 α).relIndex (Vv 𝔛 δ) :=
          Subgroup.relIndex_le_of_le_left le_sup_left (hne _)
      _ = (Qv 𝔛 α).relIndex (Vv 𝔛 δ) := by rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ Fintype.card F := hidx
  have hVQn : stab 𝔛 δ ≤ Subgroup.normalizer ((⁅Vv 𝔛 δ, Qv 𝔛 δ⁆ : Subgroup 𝔘) : Set 𝔘) :=
    le_normalizer_commutator'' hVn hQn
  have hVQV : ⁅Vv 𝔛 δ, Qv 𝔛 δ⁆ ≤ Vv 𝔛 δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hVn)
  have hnt : ¬ ⁅Vv 𝔛 δ, Ltil h.le L δ⁆ ≤ ⁅Vv 𝔛 δ, Qv 𝔛 δ⁆ ⊔ B := by
    intro hle
    obtain ⟨β, hδβ⟩ := exists_adj _ δ
    obtain ⟨X, _, π, ρ, hπs, hπk, hρ⟩ := exists_quotient_conj (K := stab 𝔛 δ) hVn hZV hZn
      (fun v hv w hw => hVc (Subgroup.commutator_mem_commutator hv hw))
    have : Finite X := Finite.of_surjective π hπs
    have hX2 : ∀ x : X, x ^ 2 = 1 := by
      intro x
      obtain ⟨v, rfl⟩ := hπs x
      rw [← map_pow]
      refine (hπk _).mpr ?_
      rw [Subgroup.coe_pow]
      exact sq_mem_zm_of_mem_vv h hfull hVc v.2
    apply not_commutator_ltil_le h hfull (by omega) hδ hδβ hX2 hπs hπk hρ
    rw [commutator_eq_commutator_commutator hLp (hLs.trans hVn) hVab]
    refine (Subgroup.commutator_mono hle le_rfl).trans ?_
    refine commutator_sup_le_of' ((hVQV.trans hVs).trans
      ((le_inf hVQn hZn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)))
      (hBs.trans ((le_inf hVQn hZn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _))) ?_
      (hBL.trans le_sup_right)
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hVQn)).trans le_sup_left
  have hIs := S45.isC1_of_offender h h14 hSQ hφ hδ hVs hVn hBV hBn (by rw [hVab]; exact bot_le)
    (fun a ha => Subgroup.mem_sup_left (sq_mem_zm_of_mem_vv h hfull hVc ha)) hYs hY2 hYc hYq
    le_sup_right (sup_le (inf_le_left) hBV) hNY hNidx hnt
  obtain ⟨hIa, C', -, -, -, -, -, F', iF', -, ψ', -, hψ's, hnat⟩ := hIs
  set K' := ⁅Vv 𝔛 δ, Qv 𝔛 δ⁆ ⊔ B with hK'def
  set P' := ⁅Vv 𝔛 δ, stab 𝔛 δ⁆ ⊔ B with hP'def
  have hK'n : stab 𝔛 δ ≤ Subgroup.normalizer (K' : Set 𝔘) :=
    (le_inf hVQn hBn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hP'n : stab 𝔛 δ ≤ Subgroup.normalizer (P' : Set 𝔘) :=
    (le_inf (le_normalizer_commutator'' hVn Subgroup.le_normalizer) hBn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKP : K' ≤ P' := sup_le_sup_right (Subgroup.commutator_mono le_rfl hQs) _
  have hVQL : ⁅⁅Vv 𝔛 δ, Qv 𝔛 δ⁆, Ltil h.le L δ⁆ ≤ ZM 𝔛 δ := by
    have hab : ⁅⁅Vv 𝔛 δ, Qv 𝔛 δ⁆, ⁅Vv 𝔛 δ, Qv 𝔛 δ⁆⁆ = ⊥ :=
      le_bot_iff.mp (hVab ▸ Subgroup.commutator_mono hVQV hVQV)
    rw [commutator_eq_commutator_commutator hLp (hLs.trans hVQn) hab]
    exact (Subgroup.commutator_mono hIa le_rfl).trans hBL
  have hKL : ⁅K', Ltil h.le L δ⁆ ≤ ZM 𝔛 δ :=
    commutator_sup_le_of' ((hVQV.trans hVs).trans hZn) (hBs.trans hZn) hVQL hBL
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isMVtx _ hc.1 hδ
  have hcδ' : IsCritical 𝔛 δ (k • α') := by
    rw [← hk]
    exact (isCritical_smul _ k α α').mpr hc
  have hgeo2 : geo 𝔛 δ (k • α') 2 = k • γ := by rw [← hk, geo_smul]
  have hgeo2' : geo 𝔛 (k • α') δ 2 = k • geo 𝔛 α' α 2 := by rw [← hk, geo_smul]
  set N' := conjCl (stab 𝔛 δ) (ZM 𝔛 (geo 𝔛 δ (k • α') 2)) with hN'def
  have hN'Q : N' ≤ Qv 𝔛 (geo 𝔛 (k • α') δ 2) := by
    rw [hN'def, hgeo2, hgeo2', qv_smul, ← hk, ← map_conj_conjCl_zm h]
    exact Subgroup.map_mono hA
  have hdδ2 : (puAmalgam h.le).treeGraph.dist δ (geo 𝔛 δ (k • α') 2) = 2 :=
    dist_geo _ (by rw [hcδ'.2.1]; omega)
  have hgM : IsMVtx 𝔛 (geo 𝔛 δ (k • α') 2) := isMVtx_geo_two _ h20 hb0 hcδ'
  have hZgV : ZM 𝔛 (geo 𝔛 δ (k • α') 2) ≤ Vv 𝔛 δ := by
    have := zv_le_vv h (α := δ) (ρ := geo 𝔛 δ (k • α') 2) hdδ2.le
    rwa [zv_of_isMVtx _ hgM] at this
  have hN'V : N' ≤ Vv 𝔛 δ := conjCl_le_of_le_normalizer hZgV hVn
  have hN'n : stab 𝔛 δ ≤ Subgroup.normalizer (N' : Set 𝔘) := le_normalizer_conjCl _ _
  have hZN' : ZM 𝔛 δ ≤ N' := zm_le_conjCl_zm h hdδ2
  have hN'ab : ⁅N', N'⁆ = ⊥ := le_bot_iff.mp (hVab ▸ Subgroup.commutator_mono hN'V hN'V)
  have hYn : stab 𝔛 δ ≤ Subgroup.normalizer (((N' ⊔ K') ⊓ P' : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf ((le_inf hN'n hK'n).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _))
      hP'n).trans Subgroup.inf_normalizer_le_normalizer_inf
  rcases eq_or_eq_of_natural hψ's statedSL3_transitive hnat (Y := (N' ⊔ K') ⊓ P')
      (le_inf le_sup_right hKP) inf_le_right hYn with hII | hI
  ·
    have h1 : ⁅N', Ltil h.le L δ⁆ ≤ (N' ⊔ K') ⊓ P' :=
      le_inf ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hN'n)).trans
        le_sup_left) ((Subgroup.commutator_mono hN'V hLs).trans le_sup_left)
    rw [hII] at h1
    have h2 : ⁅N', Ltil h.le L δ⁆ ≤ ZM 𝔛 δ := by
      rw [commutator_eq_commutator_commutator hLp (hLs.trans hN'n) hN'ab]
      exact (Subgroup.commutator_mono h1 le_rfl).trans hKL
    apply (geo_two_mem_nablaSet h hfull hC (by omega) hV hcδ').2
    rw [zv_of_isMVtx _ hgM]
    intro x hx
    have hxN : x ∈ N' := le_conjCl _ _ hx
    exact (mem_bloc_iff h (by omega) hδ).mpr
      ⟨hN'V hxN, fun l hl => h2 (Subgroup.commutator_mem_commutator hxN hl)⟩
  ·
    have hP' : P' ≤ N' ⊔ K' := hI ▸ inf_le_left
    apply not_vcirc_le_qv_of_isCritical h hfull (by omega) hV hcδ'
    refine le_trans ?_ hN'Q
    rw [Vcirc, commutator_eq_commutator_commutator hLp (hLs.trans hVn) hVab]
    calc ⁅⁅Vv 𝔛 δ, Ltil h.le L δ⁆, Ltil h.le L δ⁆
        ≤ ⁅N' ⊔ K', Ltil h.le L δ⁆ := Subgroup.commutator_mono
          (((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans hP') le_rfl
      _ ≤ N' := commutator_sup_le_of' Subgroup.le_normalizer
          ((sup_le (hVQV.trans hVs) hBs).trans hN'n)
          (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hN'n))
          (hKL.trans hZN')

end Vertex

theorem _root_.CFSG.Quasithin.MS93.S4A.s442FFD_of (h14 : MS14AS) (hSQ : SQTKQuot) (h32 : S32)
    (h43 : S43) : S442FFD := by
  intro G _ _ M T L h F _ _ φ hH hb α α' δ hconf hidx
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  exact not_commutator_le_of_conf h hH.2.2 h14 hSQ (centHyp_of_S32 h32 h) hb
    (h43 G M T L h hH.1 hH.2.1 hfull) hconf hidx

end CFSG.Quasithin.MS93.S4A.P442
