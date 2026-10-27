module

public import CFSG.Quasithin.MS93.S4A441L
public import CFSG.Quasithin.MS93.S4A42W

public section

namespace CFSG.Quasithin.MS93.S4A.L441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

section Grp

variable {G : Type*} [Group G]

theorem conjCl_le_of_le_normalizer' {H K N : Subgroup G} (hK : K ≤ N)
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : conjCl H K ≤ N := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨k, hk, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hH hg) k).mp (hK hk)

theorem commutator_conjCl_zpowers_le {H K N : Subgroup G} {w : G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hKH : K ≤ H) (hw : w ∈ H)
    (hgen : ∀ g ∈ H, ∀ z ∈ K, ⁅g * z * g⁻¹, w⁆ ∈ N) :
    ⁅conjCl H K, Subgroup.zpowers w⁆ ≤ N := by
  let S : Subgroup G :=
    { carrier := {v | v ∈ H ∧ ⁅v, w⁆ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, ?_⟩
        have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN ha) _).mp hb') ha'
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, ?_⟩
        have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) _).mp (N.inv_mem ha') }
  have hWS : conjCl H K ≤ S := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨H.mul_mem (H.mul_mem hg (hKH hz)) (H.inv_mem hg), hgen g hg z hz⟩
  let Y : Subgroup G :=
    { carrier := {y | y ∈ H ∧ ∀ v ∈ conjCl H K, ⁅v, y⁆ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H.mul_mem ha hb, fun v hv => ?_⟩
        have e : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (ha' v hv) ((Subgroup.mem_normalizer_iff.mp (hHN ha) _).mp (hb' v hv))
      one_mem' := ⟨H.one_mem, fun v _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H.inv_mem ha, fun v hv => ?_⟩
        have e : ⁅v, a⁻¹⁆ = a⁻¹ * ⁅v, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) _).mp
          (N.inv_mem (ha' v hv)) }
  have hwY : Subgroup.zpowers w ≤ Y := Subgroup.zpowers_le.mpr ⟨hw, fun v hv => (hWS hv).2⟩
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hwY hy).2 v hv

end Grp

section Sec

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] def IsSecD {F : Type} [Field F] (γ : Vtx (puAmalgam hTM))
    (ψ : ↥(stab (puAmalgam hTM) γ) →* ↥(StatedSL 3 F)) (dual : Bool)
    (W C : Subgroup (puAmalgam hTM).Universal) : Prop :=
  Uloc hTM L γ ≤ C ∧ ⁅C, stab (puAmalgam hTM) γ⁆ ≤ Uloc hTM L γ ⊔ Dloc hTM L γ ∧
    ⁅W, Qv (puAmalgam hTM) γ⁆ ≤ Uloc hTM L γ ⊔ Dloc hTM L γ ∧
    IsSumOfNaturalModulesVia (stab (puAmalgam hTM) γ) W C ψ dual 1 ∧
    ∀ w ∈ W, ∀ g ∈ stab (puAmalgam hTM) γ, w⁻¹ * (g * w * g⁻¹) ∈ C →
      w⁻¹ * (g * w * g⁻¹) ∈ Uloc hTM L γ ⊔ Dloc hTM L γ

end Sec

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem commutator_conjCl_qv_le (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1)
    (hWQL : ⁅⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), Qv 𝔛 γ⁆, Ltil h.le L γ⁆ ≤ ZM 𝔛 γ) :
    ⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), Qv 𝔛 γ⁆ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hβH : ¬ IsMVtx 𝔛 β := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hVQ : Vv 𝔛 γ ≤ Qv 𝔛 γ := vv_le_qv h (by omega) hγ
  have hUn : stab 𝔛 γ ≤ Subgroup.normalizer (Uloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hUDn : stab 𝔛 γ ≤
      Subgroup.normalizer ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf hUn hDn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hZcQγ := zm_le_centralizer_qv _ h20 hγ
  have hZcQα := zm_le_centralizer_qv _ h20 hα
  have hQαβ : Qv 𝔛 α ≤ Qv 𝔛 β := qv_le_qv _ h20 hα hαβ
  have hQβγ : Qv 𝔛 β ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hβγ
  have hQγβ : Qv 𝔛 γ ≤ Qv 𝔛 β := qv_le_qv _ h20 hγ hβγ.symm
  have hQβα : Qv 𝔛 β ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαβ.symm
  have hQαs : Qv 𝔛 α ≤ stab 𝔛 γ := hQαβ.trans hQβγ
  have hZαs : ZM 𝔛 α ≤ stab 𝔛 γ := (hZαV.trans hVQ).trans hQs
  have hQαU : ¬ Qv 𝔛 α ≤ Subgroup.centralizer (Uloc h.le L γ : Set 𝔘) := by
    intro hle
    have h1 : Qv 𝔛 α ≤ Qv 𝔛 γ := fun y hy =>
      S46.stab_inf_centralizer_uloc_le_qv h hφ hγ ⟨hQαs hy, hle hy⟩
    have h2 : Qv 𝔛 α = Qv 𝔛 γ := qv_eq_of_le h hγ hα h1
    have h3 : ZM 𝔛 α = ZM 𝔛 γ := by
      rw [← xm_eq_zm h hfull hα, ← xm_eq_zm h hfull hγ, XM, XM, h2]
    apply hH
    rw [h3, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZcQγ]
    exact bot_le
  have hgen : ∀ z ∈ ZM 𝔛 α, ∀ y ∈ Qv 𝔛 γ, ⁅z, y⁆ ∈ Uloc h.le L γ ⊔ Dloc h.le L γ := by
    intro z hz y hy
    have hzW : z ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) := le_conjCl _ _ hz
    have hwZ : ⁅z, y⁆ ∈ ZM 𝔛 α := by
      have hy' : y ∈ stab 𝔛 α := hQβα (hQγβ hy)
      have h1 : y * z⁻¹ * y⁻¹ ∈ ZM 𝔛 α :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α hy') _).mp
          (Subgroup.inv_mem _ hz)
      have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hz h1
    have hzQ : z ∈ Qv 𝔛 γ := hVQ (hZαV hz)
    refine mem_uloc_sup_dloc h hfull hγ hψs hψ ?_ ?_ hQαs ?_ ?_ ?_ hQαU
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hzQ hy)
        (Subgroup.inv_mem _ hzQ)) (Subgroup.inv_mem _ hy)
    · intro l hl
      have := hWQL (Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator hzW hy) hl)
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ this
    · intro y' hy'
      exact Subgroup.mem_centralizer_iff.mp (hZcQα hwZ) y' hy'
    · exact (hQγβ.trans hQβα).trans (stab_le_normalizer_qv _ α)
    · exact (isPGroup_qv _ h20 hβH).to_le hQαβ
  let N : Subgroup 𝔘 :=
    { carrier := {w | w ∈ stab 𝔛 γ ∧ ∀ y ∈ Qv 𝔛 γ, ⁅w, y⁆ ∈ Uloc h.le L γ ⊔ Dloc h.le L γ}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hUDn ha) _).mp (hb' y hy))
          (ha' y hy)
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hUDn (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ (ha' y hy)) }
  have hNn : stab 𝔛 γ ≤ Subgroup.normalizer (N : Set 𝔘) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rintro _ ⟨w, ⟨hw, hw'⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hw) (Subgroup.inv_mem _ hg),
      fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Qv 𝔛 γ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ γ (Subgroup.inv_mem _ hg)) y).mp hy
    have e : ⁅g * w * g⁻¹, y⁆ = g * ⁅w, g⁻¹ * y * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hUDn hg) _).mp (hw' _ hy')
  have hZN : ZM 𝔛 α ≤ N := fun z hz => ⟨hZαs hz, hgen z hz⟩
  have hWN : conjCl (stab 𝔛 γ) (ZM 𝔛 α) ≤ N := conjCl_le_of_le_normalizer' hZN hNn
  rw [Subgroup.commutator_le]
  intro w hw y hy
  exact (hWN hw).2 y hy

theorem card_uloc_inf_sup_dloc_le {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ)
    {R : Subgroup 𝔘} [Finite ↥R] (hRs : R ≤ stab 𝔛 μ) :
    Nat.card ↥(Uloc h.le L μ ⊓ (R ⊔ Dloc h.le L μ)) ≤ Nat.card ↥R := by
  have hb0 := h.critDist_pos
  have hDn : stab 𝔛 μ ≤ Subgroup.normalizer (Dloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) μ
  have hDs : Dloc h.le L μ ≤ stab 𝔛 μ := puTrans_le_stab h.le _ μ
  have hUs : Uloc h.le L μ ≤ stab 𝔛 μ :=
    (uloc_le_zm h hfull hμ).trans ((zm_le_qv_self _ hμ hb0).trans (qv_le_stab _ μ))
  have : Finite ↥(stab 𝔛 μ) := finite_stab h hμ
  have hfinD : Finite ↥(Dloc h.le L μ) := Finite.of_injective _ (Subgroup.inclusion_injective hDs)
  have hZD : Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
    have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hφ.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]
  set Tt := Uloc h.le L μ ⊓ (R ⊔ Dloc h.le L μ) with hTdef
  have hfinT : Finite ↥Tt := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left.trans hUs))
  have hTD : Tt ⊓ Dloc h.le L μ = ⊥ := by
    rw [eq_bot_iff, ← hZD]
    exact inf_le_inf_right _ inf_le_left
  have hfinTD : Finite ↥(Tt ⊔ Dloc h.le L μ) := Finite.of_injective _
    (Subgroup.inclusion_injective (sup_le (inf_le_left.trans hUs) hDs))
  have h1 := card_mul_card_le_card_sup' hTD
  have hfinRD : Finite ↥(R ⊔ Dloc h.le L μ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hRs hDs))
  have h2 := Subgroup.card_le_of_le (sup_le inf_le_right le_sup_right :
    Tt ⊔ Dloc h.le L μ ≤ R ⊔ Dloc h.le L μ)
  have h3 := card_sup_le_mul (hRs.trans hDn)
  have hpos : 0 < Nat.card ↥(Dloc h.le L μ) := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right ((h1.trans h2).trans h3) hpos

theorem commutator_mem_dloc_of_conj {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ)
    {x : 𝔘} (hxs : x ∈ stab 𝔛 μ) {K' : Subgroup 𝔘} (hK'Q : ⁅K', Qv 𝔛 μ⁆ ≤ Dloc h.le L μ)
    (hF : ∀ k ∈ stab 𝔛 μ, x⁻¹ * (k * x * k⁻¹) ∈ K')
    {R' : Subgroup 𝔘} [Finite ↥R'] (hR's : R' ≤ stab 𝔛 μ)
    (hxR : ∀ y ∈ Qv 𝔛 μ, ⁅x, y⁆ ∈ R' ⊔ Dloc h.le L μ) (hR : Nat.card ↥R' < Fintype.card F ^ 3)
    (hxUD : ∀ y ∈ Qv 𝔛 μ, ⁅x, y⁆ ∈ Uloc h.le L μ ⊔ Dloc h.le L μ) :
    ∀ y ∈ Qv 𝔛 μ, ⁅x, y⁆ ∈ Dloc h.le L μ := by
  classical
  have hb0 := h.critDist_pos
  have hUn : stab 𝔛 μ ≤ Subgroup.normalizer (Uloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hDn : stab 𝔛 μ ≤ Subgroup.normalizer (Dloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) μ
  have hQs : Qv 𝔛 μ ≤ stab 𝔛 μ := qv_le_stab _ μ
  have hDs : Dloc h.le L μ ≤ stab 𝔛 μ := puTrans_le_stab h.le _ μ
  have hZs : ZM 𝔛 μ ≤ stab 𝔛 μ := (zm_le_qv_self _ hμ hb0).trans hQs
  have hUZ : Uloc h.le L μ ≤ ZM 𝔛 μ := uloc_le_zm h hfull hμ
  have hUs : Uloc h.le L μ ≤ stab 𝔛 μ := hUZ.trans hZs
  have : Finite ↥(stab 𝔛 μ) := finite_stab h hμ
  have hfinD : Finite ↥(Dloc h.le L μ) := Finite.of_injective _ (Subgroup.inclusion_injective hDs)
  have hZD : Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
    have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hφ.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]
  set R := Subgroup.closure {r | ∃ y ∈ Qv 𝔛 μ, ⁅x, y⁆ = r} with hRdef
  have hRR' : R ≤ R' ⊔ Dloc h.le L μ :=
    (Subgroup.closure_le _).mpr fun _ ⟨y, hy, hr⟩ => hr ▸ hxR y hy
  have hkR : ∀ k ∈ stab 𝔛 μ, ∀ r ∈ R, k * r * k⁻¹ ∈ R ⊔ Dloc h.le L μ := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨y, hy, rfl⟩ := hr
      have hy' : k * y * k⁻¹ ∈ Qv 𝔛 μ :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ hk) y).mp hy
      have hcD : ⁅x⁻¹ * (k * x * k⁻¹), k * y * k⁻¹⁆ ∈ Dloc h.le L μ :=
        hK'Q (Subgroup.commutator_mem_commutator (hF k hk) hy')
      have e : k * ⁅x, y⁆ * k⁻¹ =
          (x * ⁅x⁻¹ * (k * x * k⁻¹), k * y * k⁻¹⁆ * x⁻¹) * ⁅x, k * y * k⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hDn hxs) _).mp hcD)
        (Subgroup.subset_closure ⟨_, hy', rfl⟩)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hRDn : stab 𝔛 μ ≤ Subgroup.normalizer ((R ⊔ Dloc h.le L μ : Subgroup 𝔘) : Set 𝔘) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hkR k hk a ha
    · rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDn hk) d).mp hd)
  set Tt := Uloc h.le L μ ⊓ (R ⊔ Dloc h.le L μ) with hTdef
  have hTn : stab 𝔛 μ ≤ Subgroup.normalizer (Tt : Set 𝔘) := le_normalizer_inf hUn hRDn
  have hfinT : Finite ↥Tt := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left.trans hUs))
  have hTcard : Nat.card ↥Tt ≤ Nat.card ↥R' := by
    have hle : Tt ≤ Uloc h.le L μ ⊓ (R' ⊔ Dloc h.le L μ) :=
      inf_le_inf_left _ (sup_le hRR' le_sup_right)
    have hfinT' : Finite ↥(Uloc h.le L μ ⊓ (R' ⊔ Dloc h.le L μ)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans hUs))
    exact (Subgroup.card_le_of_le hle).trans (card_uloc_inf_sup_dloc_le h hfull hφ hμ hR's)
  have hTZ : Tt ≤ Zloc h.le L μ := by
    by_contra hne
    have hUT := uloc_le_of_normal h hfull hφ hμ (Y := Tt) (inf_le_left.trans hUZ) hTn hne
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
    have h1 := Subgroup.card_le_of_le hUT
    rw [card_eq_of_natural hψ, Nat.card_eq_fintype_card (α := F)] at h1
    omega
  have hT1 : Tt = ⊥ := by
    rw [eq_bot_iff, ← uloc_inf_zloc h hfull μ]
    exact le_inf inf_le_left hTZ
  intro y hy
  have hset : ((Uloc h.le L μ ⊔ Dloc h.le L μ : Subgroup _) : Set 𝔘) =
      (Uloc h.le L μ : Set 𝔘) * (Dloc h.le L μ : Set 𝔘) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)
  have hxy' : ⁅x, y⁆ ∈ ((Uloc h.le L μ ⊔ Dloc h.le L μ : Subgroup _) : Set 𝔘) := hxUD y hy
  rw [hset, Set.mem_mul] at hxy'
  obtain ⟨u, hu, d, hd, hud⟩ := hxy'
  have huT : u ∈ Tt := by
    refine ⟨hu, ?_⟩
    have : u = ⁅x, y⁆ * d⁻¹ := by rw [← hud]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨y, hy, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd))
  rw [hT1, Subgroup.mem_bot] at huT
  rw [← hud, huT, one_mul]
  exact hd

theorem exists_ms17i_of_same (h17 : MS17i) (hb : 4 < critDist 𝔛) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ) {W C K : Subgroup 𝔘}
    (hWV : W ≤ Vv 𝔛 γ) (hWn : stab 𝔛 γ ≤ Subgroup.normalizer (W : Set 𝔘))
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1)
    (hWC : IsSumOfNaturalModulesVia (stab 𝔛 γ) W C ψ false 1)
    (hUC : Uloc h.le L γ ≤ C) (hDWC : Dloc h.le L γ ⊓ W ≤ C)
    (hCG : ⁅C, stab 𝔛 γ⁆ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ)
    (hWQ : ⁅W, Qv 𝔛 γ⁆ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ)
    (hCK : ∀ w ∈ W, ∀ g ∈ stab 𝔛 γ, w⁻¹ * (g * w * g⁻¹) ∈ C → w⁻¹ * (g * w * g⁻¹) ∈ K)
    (hKQ : ⁅K, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {x : 𝔘} (hxα : x ∈ ZM 𝔛 α) (hxW : x ∈ W) (hxC : x ∉ C) {y₀ : 𝔘} (hy₀ : y₀ ∈ Qv 𝔛 γ)
    (hxy₀ : ⁅x, y₀⁆ ∉ Dloc h.le L γ) :
    ∃ U' : Subgroup 𝔘, x ∈ U' ∧ U' ≤ W ∧
      stab 𝔛 γ ≤ Subgroup.normalizer (U' : Set 𝔘) ∧
      ⁅⁅Qv 𝔛 γ, stab 𝔛 γ⁆, U'⁆ ≤ Dloc h.le L γ ∧
      ∀ w ∈ Qv 𝔛 γ, (∃ u ∈ U', ⁅u, w⁆ ∉ Dloc h.le L γ) →
        Uloc h.le L γ ≤ ⁅U', Subgroup.zpowers w⁆ ⊔ Dloc h.le L γ := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h (by omega) hγ).trans hQs
  have hWs : W ≤ stab 𝔛 γ := hWV.trans hVs
  have hZs : ZM 𝔛 γ ≤ stab 𝔛 γ := (zm_le_qv_self _ hγ hb0).trans hQs
  have hUn : stab 𝔛 γ ≤ Subgroup.normalizer (Uloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hDs : Dloc h.le L γ ≤ stab _ γ := puTrans_le_stab h.le _ γ
  have hUZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h hfull hγ
  have hUs : Uloc h.le L γ ≤ stab 𝔛 γ := hUZ.trans hZs
  have hVab : ⁅Vv 𝔛 γ, Vv 𝔛 γ⁆ = ⊥ := vv_comm_eq_bot h hb hγ
  have hCW : C ≤ W := hWC.2.1
  set NW := NatSec.ofIsSum hWC with hNW
  have hCn : stab 𝔛 γ ≤ Subgroup.normalizer (C : Set 𝔘) := by
    have key : ∀ g ∈ stab 𝔛 γ, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      have hcW := hCW hc
      have hgc := NW.conj_mem ⟨g, hg⟩ hcW
      rw [← NW.coord_eq_zero_iff hgc, NW.coord_conj ⟨g, hg⟩ hcW,
        (NW.coord_eq_zero_iff hcW).mpr hc, Matrix.mulVec_zero]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key g hg c, fun hc => ?_⟩
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
    simpa [mul_assoc] using this
  obtain ⟨s₀, hs₀⟩ := exists_conjSL_levi hWC hxW hxC
  set ψ' := conjSL s₀ ψ with hψ'def
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hψ' := isSumOfNaturalModulesVia_conjSL hψ s₀
  have hWC' := isSumOfNaturalModulesVia_conjSL hWC s₀
  have hF1 : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : 𝔘) * x * (k : 𝔘)⁻¹) ∈ K := fun k hk => hCK x hxW k k.2 (hs₀ k hk)
  have hβH : ¬ IsMVtx 𝔛 β := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hRfin : Finite ↥(Usup 𝔛 α β) := by
    have := finite_qv _ h20 hβH
    have hle : Usup 𝔛 α β ≤ Qv _ β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact commutator_le_of_le ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hxR : ∀ y ∈ Qv 𝔛 γ, ⁅x, y⁆ ∈ Usup 𝔛 α β := by
    intro y hy
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator hxα (qv_le_qv _ h20 hγ hβγ.symm hy)
  have hRq : Nat.card ↥(Usup 𝔛 α β) < Fintype.card F ^ 3 := by
    have h1 := card_usup_le_sq h hfull hφ hα hαβ
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hxUD : ∀ y ∈ Qv 𝔛 γ, ⁅x, y⁆ ∈ Uloc h.le L γ ⊔ Dloc h.le L γ := fun y hy =>
    hWQ (Subgroup.commutator_mem_commutator hxW hy)
  obtain ⟨S₀, hS₀U, hS₀card, hS₀stab, hxS₀⟩ := commutator_le_line_of_levi_dloc h hfull hφ hγ
    hψ's hψ' (hWs hxW) hKQ hF1 hxR hRq hxUD
  set X : Subgroup 𝔘 :=
    Subgroup.closure {u | ∃ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (ptStab : Subgroup (SL3 F)) ∧
      (k : 𝔘) * x * (k : 𝔘)⁻¹ = u} with hXdef
  set U' : Subgroup 𝔘 :=
    Subgroup.closure {u | ∃ k : ↥(stab 𝔛 γ), ∃ y ∈ X, (k : 𝔘) * y * (k : 𝔘)⁻¹ = u}
    with hU'def
  have hXW : X ≤ W := by
    rw [hXdef, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWn k.2) x).mp hxW
  have hxX : x ∈ X := Subgroup.subset_closure ⟨1, by simp, by simp⟩
  have hXstab : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ y ∈ X, (k : 𝔘) * y * (k : 𝔘)⁻¹ ∈ X := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k', hk', rfl⟩ := hy
      refine Subgroup.subset_closure ⟨k * k', ?_, ?_⟩
      · rw [map_mul]
        exact Subgroup.mul_mem _ hk hk'
      · simp only [Subgroup.coe_mul, mul_inv_rev]
        group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : (k : 𝔘) * (a * b) * (k : 𝔘)⁻¹ =
          ((k : 𝔘) * a * (k : 𝔘)⁻¹) * ((k : 𝔘) * b * (k : 𝔘)⁻¹) := by group
      rw [e]
      exact X.mul_mem ha hb
    | inv a _ ha =>
      have e : (k : 𝔘) * a⁻¹ * (k : 𝔘)⁻¹ = ((k : 𝔘) * a * (k : 𝔘)⁻¹)⁻¹ := by group
      rw [e]
      exact X.inv_mem ha
  have hXU' : X ≤ U' := fun y hy => Subgroup.subset_closure ⟨1, y, hy, by simp⟩
  have hxU' : x ∈ U' := hXU' hxX
  have hU'W : U' ≤ W := by
    rw [hU'def, Subgroup.closure_le]
    rintro _ ⟨k, y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWn k.2) y).mp (hXW hy)
  have hU'n : stab 𝔛 γ ≤ Subgroup.normalizer (U' : Set 𝔘) := by
    have key : ∀ g ∈ stab 𝔛 γ, ∀ u ∈ U', g * u * g⁻¹ ∈ U' := by
      intro g hg u hu
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        obtain ⟨k, y, hy, rfl⟩ := hu
        refine Subgroup.subset_closure ⟨⟨g, hg⟩ * k, y, hy, ?_⟩
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      | one => simp
      | mul a b _ _ ha hb =>
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]
        exact U'.mul_mem ha hb
      | inv a _ ha =>
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]
        exact U'.inv_mem ha
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact key g hg u
    · intro hu
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hu
      simpa [mul_assoc] using this
  set NW' := NatSec.ofIsSum hWC' with hNW'
  have hU'C : U' ⊔ C = W := by
    apply le_antisymm (sup_le hU'W hCW)
    intro v hv
    obtain ⟨u, huU, -, huv⟩ := NW'.exists_inv_mul_mem_of_invariant hψ's
      (fun l y hy => (Subgroup.mem_normalizer_iff.mp (hU'n l.2) y).mp hy) hxU' hxW hxC hv
    have : v = u * (u⁻¹ * v) := by group
    rw [this]
    exact Subgroup.mul_mem_sup huU huv
  let SZ : Subgroup 𝔘 :=
    { carrier := {y | y ∈ W ∧ ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
        y⁻¹ * ((k : 𝔘) * y * (k : 𝔘)⁻¹) ∈ C}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun k hk => ?_⟩
        have e : (a * b)⁻¹ * ((k : 𝔘) * (a * b) * (k : 𝔘)⁻¹) =
            b⁻¹ * (a⁻¹ * ((k : 𝔘) * a * (k : 𝔘)⁻¹)) * b *
            (b⁻¹ * ((k : 𝔘) * b * (k : 𝔘)⁻¹)) := by group
        rw [e]
        refine Subgroup.mul_mem _ ?_ (hb' k hk)
        have := (Subgroup.mem_normalizer_iff.mp (hCn (hWs (Subgroup.inv_mem _ hb))) _).mp
          (ha' k hk)
        simpa [mul_assoc] using this
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun k hk => ?_⟩
        have e : a⁻¹⁻¹ * ((k : 𝔘) * a⁻¹ * (k : 𝔘)⁻¹) =
            a * (a⁻¹ * ((k : 𝔘) * a * (k : 𝔘)⁻¹))⁻¹ * a⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCn (hWs ha)) _).mp
          (Subgroup.inv_mem _ (ha' k hk)) }
  have hXSZ : X ≤ SZ := by
    rw [hXdef, Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hWn k'.2) x).mp hxW, fun k hk => ?_⟩
    have hl : toSL3 ψ' (k'⁻¹ * k * k') ∈ (ptLevi : Subgroup (SL3 F)) := by
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_ptLevi hk' hk
    have h1 := hs₀ _ hl
    have e : ((k' : 𝔘) * x * (k' : 𝔘)⁻¹)⁻¹ *
        ((k : 𝔘) * ((k' : 𝔘) * x * (k' : 𝔘)⁻¹) * (k : 𝔘)⁻¹) =
        (k' : 𝔘) * (x⁻¹ * (((k'⁻¹ * k * k' : ↥(stab _ γ)) : 𝔘) * x *
          ((k'⁻¹ * k * k' : ↥(stab _ γ)) : 𝔘)⁻¹)) * (k' : 𝔘)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hCn k'.2) _).mp h1
  have hlevi : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ y ∈ X, y⁻¹ * ((k : 𝔘) * y * (k : 𝔘)⁻¹) ∈ U' ⊓ C ⊔ Dloc h.le L γ := by
    intro k hk y hy
    refine Subgroup.mem_sup_left ⟨?_, (hXSZ hy).2 k hk⟩
    exact Subgroup.mul_mem _ (U'.inv_mem (hXU' hy))
      ((Subgroup.mem_normalizer_iff.mp (hU'n k.2) _).mp (hXU' hy))
  have hS₀D : X ≤ Subgroup.normalizer ((S₀ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) := by
    have hXc : X ≤ Subgroup.centralizer (S₀ : Set 𝔘) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : ⁅y, u⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator (hWV (hXW hy))
          (zm_le_vv h hγ (hUZ (hS₀U hu)))
        rw [hVab] at this
        exact this
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    exact (le_inf (le_normalizer_of_le_centralizer hXc) ((hXW.trans hWs).trans hDn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hXQ : ⁅X, Qv 𝔛 γ⁆ ≤ S₀ ⊔ Dloc h.le L γ := by
    rw [hXdef]
    refine commutator_closure_le_of ?_ (by rw [← hXdef]; exact hS₀D)
    rintro _ ⟨k, hk, rfl⟩ y hy
    have hy' : (k : 𝔘)⁻¹ * y * (k : 𝔘) ∈ Qv 𝔛 γ := by
      have := (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_qv _ γ (Subgroup.inv_mem _ k.2)) y).mp hy
      simpa using this
    have e : ⁅(k : 𝔘) * x * (k : 𝔘)⁻¹, y⁆ =
        (k : 𝔘) * ⁅x, (k : 𝔘)⁻¹ * y * (k : 𝔘)⁆ * (k : 𝔘)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hm := hxS₀ _ hy'
    have hSD : ((S₀ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) =
        (S₀ : Set 𝔘) * (Dloc h.le L γ : Set 𝔘) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hS₀U.trans hUs).trans hDn)
    have hm' : ⁅x, (k : 𝔘)⁻¹ * y * (k : 𝔘)⁆ ∈
        ((S₀ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) := hm
    rw [hSD] at hm'
    obtain ⟨u, hu, w, hw, huw⟩ := hm'
    rw [← huw]
    have e2 : (k : 𝔘) * (u * w) * (k : 𝔘)⁻¹ =
        ((k : 𝔘) * u * (k : 𝔘)⁻¹) * ((k : 𝔘) * w * (k : 𝔘)⁻¹) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup (hS₀stab k hk u hu)
      ((Subgroup.mem_normalizer_iff.mp (hDn k.2) w).mp hw)
  have hne : ¬ ⁅X, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ := fun hle =>
    hxy₀ (hle (Subgroup.commutator_mem_commutator hxX hy₀))
  have hUD : Uloc h.le L γ ⊓ Dloc h.le L γ = ⊥ := by
    have hUD' : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hφ.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD', puTrans, Subgroup.bot_subgroupOf, transN_bot]
  have hU'D : ((U' ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) =
      (U' : Set 𝔘) * (Dloc h.le L γ : Set 𝔘) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hU'W.trans hWs).trans hDn)
  have hUDset : ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) =
      (Uloc h.le L γ : Set 𝔘) * (Dloc h.le L γ : Set 𝔘) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)
  have hUU' : Uloc h.le L γ ≤ U' ⊔ Dloc h.le L γ := by
    set N₁ := Uloc h.le L γ ⊓ (U' ⊔ Dloc h.le L γ) with hN₁
    have hN₁n : stab 𝔛 γ ≤ Subgroup.normalizer (N₁ : Set 𝔘) :=
      le_normalizer_inf hUn ((le_inf hU'n hDn).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _))
    have hxy₀U' : ⁅x, y₀⁆ ∈ U' := by
      have e : ⁅x, y₀⁆ = x * (y₀ * x⁻¹ * y₀⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact U'.mul_mem hxU' ((Subgroup.mem_normalizer_iff.mp (hU'n (hQs hy₀)) _).mp
        (U'.inv_mem hxU'))
    have hm : ⁅x, y₀⁆ ∈ ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) := hxUD y₀ hy₀
    rw [hUDset] at hm
    obtain ⟨u, hu, d, hd, hud⟩ := hm
    have huN : u ∈ N₁ := by
      refine ⟨hu, ?_⟩
      have : u = ⁅x, y₀⁆ * d⁻¹ := by rw [← hud]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxy₀U')
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd))
    have hu1 : u ≠ 1 := by
      rintro rfl
      apply hxy₀
      rw [← hud]
      simpa using hd
    have hNZ : ¬ N₁ ≤ Zloc h.le L γ := by
      intro hle
      apply hu1
      have : u ∈ Uloc h.le L γ ⊓ Zloc h.le L γ := ⟨hu, hle huN⟩
      rw [uloc_inf_zloc h hfull γ] at this
      exact this
    have hle := uloc_le_of_normal h hfull hφ hγ (inf_le_left.trans hUZ) hN₁n hNZ
    exact hle.trans inf_le_right
  have hZC : Uloc h.le L γ ≤ U' ⊓ C ⊔ Dloc h.le L γ := by
    intro u hu
    have hm : u ∈ ((U' ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) := hUU' hu
    rw [hU'D] at hm
    obtain ⟨u', hu', d, hd, hud⟩ := hm
    have hdW : d ∈ W := by
      have : d = u'⁻¹ * u := by rw [← hud]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU'W hu')) (hCW (hUC hu))
    have hu'C : u' ∈ C := by
      have : u' = u * d⁻¹ := by rw [← hud]; group
      rw [this]
      exact Subgroup.mul_mem _ (hUC hu) (Subgroup.inv_mem _ (hDWC ⟨hd, hdW⟩))
    rw [← hud]
    exact Subgroup.mul_mem_sup ⟨hu', hu'C⟩ hd
  have hUN : U' ⊓ Dloc h.le L γ ≤ U' ⊓ C := fun v hv => ⟨hv.1, hDWC ⟨hv.2, hU'W hv.1⟩⟩
  have hCK' : ⁅U' ⊓ C, stab 𝔛 γ⁆ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans hCG
  have hZU : ⁅Uloc h.le L γ, U'⁆ ≤ Dloc h.le L γ := by
    have : ⁅Uloc h.le L γ, U'⁆ ≤ ⁅Vv 𝔛 γ, Vv 𝔛 γ⁆ :=
      Subgroup.commutator_mono (hUZ.trans (zm_le_vv h hγ)) (hU'W.trans hWV)
    rw [hVab] at this
    exact this.trans bot_le
  have hZW : ⁅Uloc h.le L γ, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ := by
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (hUZ.trans (zm_le_centralizer_qv _ h20 hγ))]
    exact bot_le
  have hUW : ⁅U', Qv 𝔛 γ⁆ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ :=
    (Subgroup.commutator_mono hU'W le_rfl).trans hWQ
  have hUC' : IsSumOfNaturalModulesVia (stab 𝔛 γ) U' (U' ⊓ C) ψ' false 1 :=
    isSumOfNaturalModulesVia_transfer hWC' (sup_eq_left.mpr hCW) (inf_eq_right.mpr hCW) hU'W
      hU'C hU'n hCn (hWs.trans hCn)
  have hNψ : ∀ k : ↥(stab 𝔛 γ), (k : 𝔘) ∈ Dloc h.le L γ → ψ' k = 1 := by
    intro k hk
    have hkQ : (k : 𝔘) ∈ Qv 𝔛 γ := by
      rw [Dloc, h.puTrans_Dq hγ] at hk
      exact hk.1
    have h1 := (S46.toSL3_eq_one_iff_mem_qv h hφ hγ hψ k).mpr hkQ
    have h2 : ψ k = 1 := by
      have := congrArg (specialLinearGroupEquivStatedSL 3 F) h1
      simpa [toSL3] using this
    rw [hψ'def, conjSL, MonoidHom.comp_apply, h2, map_one]
  have : ((Dloc h.le L γ).subgroupOf (stab 𝔛 γ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hDn
  have : Finite ↥(stab 𝔛 γ) := finite_stab h hγ
  have : Finite ↥S₀ := Finite.of_injective _ (Subgroup.inclusion_injective (hS₀U.trans hUs))
  have hcard : Nat.card ↥S₀ ≤ Nat.card F ^ 2 := by
    rw [hS₀card, Nat.card_eq_fintype_card]
    exact Nat.le_self_pow (by norm_num) _
  obtain ⟨-, c2, -, c4⟩ := ms17i_bar h17 hDs hn hψ's hNψ hUs (hU'W.trans hWs) hQs
    hψ' hUD hUC' hUN hZC hCK' (stab_le_normalizer_qv _ γ) hZU hZW hUW hXU' rfl
    (fun k hk y hy => Subgroup.mem_sup_left (hXstab k hk y hy)) hlevi hne
    (hS₀U.trans hUs) hXQ hcard
  exact ⟨U', hxU', hU'W, hU'n, c2, c4⟩

theorem commutator_uloc_sup_dloc_qv_le {γ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) :
    ⁅Uloc h.le L γ ⊔ Dloc h.le L γ, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hUZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h hfull hγ
  have hUs : Uloc h.le L γ ≤ stab 𝔛 γ := hUZ.trans ((zm_le_qv_self _ hγ hb0).trans hQs)
  rw [Subgroup.commutator_le]
  intro a ha y hy
  have hset : ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) =
      (Uloc h.le L γ : Set 𝔘) * (Dloc h.le L γ : Set 𝔘) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUs.trans hDn)
  have ha' : a ∈ ((Uloc h.le L γ ⊔ Dloc h.le L γ : Subgroup _) : Set 𝔘) := ha
  rw [hset, Set.mem_mul] at ha'
  obtain ⟨u, hu, d, hd, rfl⟩ := ha'
  have huy : u * y = y * u :=
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hγ (hUZ hu)) y hy).symm
  have h1 : u⁻¹ * y⁻¹ = y⁻¹ * u⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, huy]
  have e : ⁅u * d, y⁆ = u * (d * (y * d⁻¹ * y⁻¹)) * u⁻¹ := by
    calc ⁅u * d, y⁆ = u * d * y * d⁻¹ * (u⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = u * d * y * d⁻¹ * (y⁻¹ * u⁻¹) := by rw [h1]
      _ = u * (d * (y * d⁻¹ * y⁻¹)) * u⁻¹ := by group
  rw [e]
  refine (Subgroup.mem_normalizer_iff.mp (hDn (hUs hu)) _).mp ?_
  exact Subgroup.mul_mem _ hd ((Subgroup.mem_normalizer_iff.mp (hDn (hQs hy)) _).mp
    (Subgroup.inv_mem _ hd))

theorem dloc_inf_le_of_isSum {γ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) {F : Type} [Field F]
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {dual : Bool}
    {W C : Subgroup 𝔘} (hWC : IsSumOfNaturalModulesVia (stab 𝔛 γ) W C ψ dual 1) :
    Dloc h.le L γ ⊓ W ≤ C := by
  have hDc : Dloc h.le L γ ≤ Subgroup.centralizer (Ltil h.le L γ : Set 𝔘) := by
    rw [Dloc, h.puTrans_Dq hγ]
    exact inf_le_right
  rintro v ⟨hvD, hvW⟩
  set NW := NatSec.ofIsSum hWC with hNW
  rw [← NW.coord_eq_zero_iff hvW]
  refine S4A.eq_zero_of_forall_mulVec_eq fun s => ?_
  have hfix : ∀ l : ↥(stab 𝔛 γ), (l : 𝔘) ∈ Ltil h.le L γ →
      NW.coord v = natAct dual (toSL3 ψ l) *ᵥ NW.coord v := by
    intro l hl
    have hlv : (l : 𝔘) * v * (l : 𝔘)⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.mp (hDc hvD) _ hl, mul_inv_cancel_right]
    have := NW.coord_conj l hvW
    rwa [hlv] at this
  cases dual
  · obtain ⟨l, hl, hls⟩ := exists_ltil_toSL3_eq h hfull hγ hψs hψ s
    have := hfix l hl
    rw [natAct_false, hls] at this
    exact this.symm
  · obtain ⟨l, hl, hls⟩ := exists_ltil_toSL3_eq h hfull hγ hψs hψ (transposeInv s)
    have := hfix l hl
    rw [natAct_true, hls, ← coe_transposeInv, transposeInv_transposeInv] at this
    exact this.symm

omit hfull in
theorem exists_dual_of_isC1' {γ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {W : Subgroup 𝔘}
    (hWn : stab 𝔛 γ ≤ Subgroup.normalizer (W : Set 𝔘))
    (hc : IsC1 h.le L (Fintype.card F) γ W (ZM 𝔛 γ))
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) :
    ∃ dual : Bool, IsSumOfNaturalModulesVia (stab 𝔛 γ) (⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ)
      (⁅W, Qv 𝔛 γ⁆ ⊔ ZM 𝔛 γ) ψ dual 1 := by
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  obtain ⟨-, C, hKC, hCW, -, -, -, F', _, _, ψ', hcard', hsurj, hnat⟩ := hc
  have hF'n : Nat.card F' = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard', hn]
  have : CharP F' 2 := FFC.charP_two_of_card_pow hF'n
  refine isSumOfNaturalModulesVia_of_surj hψs hsurj ?_ hnat
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have h1 : toSL3 ψ x = 1 := by simp [toSL3, hx]
  have hxQ := (S46.toSL3_eq_one_iff_mem_qv h hφ hγ hψ x).mp h1
  have hPn : stab 𝔛 γ ≤ Subgroup.normalizer
      ((⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf (le_normalizer_commutator hWn Subgroup.le_normalizer)
      (stab_le_normalizer_zm _ γ)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPW : ⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ ≤ W :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hWn)
      (le_sup_right.trans (hKC.trans hCW))
  have hfix : ∀ v : Fin 3 → F',
      ((toSL3 ψ' x : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ v = v := by
    intro v
    obtain ⟨p, rfl⟩ := secVec_surjective hnat v
    have hsp : (x : 𝔘) * p * (x : 𝔘)⁻¹ ∈ ⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ :=
      (Subgroup.mem_normalizer_iff.mp (hPn x.2) _).mp p.2
    rw [← secVec_conj hnat x p ⟨_, hsp⟩ rfl]
    have hK : (⟨_, hsp⟩ * p⁻¹ : ↥(⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ)) ∈
        (⁅W, Qv 𝔛 γ⁆ ⊔ ZM 𝔛 γ).subgroupOf _ := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_sup_left ?_
      have : ((⟨_, hsp⟩ * p⁻¹ : ↥(⁅W, stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ)) : 𝔘) =
          ⁅(p : 𝔘), (x : 𝔘)⁆⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator (hPW p.2) hxQ)
    have h0 := (secVec_eq_zero_iff hnat _).mpr (Subgroup.mem_subgroupOf.mp hK)
    rw [secVec_mul, secVec_inv, add_neg_eq_zero] at h0
    exact h0
  have h2 : toSL3 ψ' x = 1 := eq_one_of_mulVec_eq_self hfix
  have := congrArg (specialLinearGroupEquivStatedSL 3 F') h2
  simpa [toSL3] using this

theorem exists_isSecD_of_isC1 (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {dual : Bool}
    (hc : IsC1 h.le L (Fintype.card F) γ (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) (ZM 𝔛 γ))
    (hPK : IsSumOfNaturalModulesVia (stab 𝔛 γ)
      (⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ)
      (⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), Qv 𝔛 γ⁆ ⊔ ZM 𝔛 γ) ψ dual 1) :
    ∃ C : Subgroup 𝔘, IsSecD h.le L γ ψ dual (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C := by
  have hb0 := h.critDist_pos
  obtain ⟨hWQL, C, hKC, hCW, hCG, hPC, hPiC, -⟩ := hc
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h (by omega) hγ).trans hQs
  have hWn : stab 𝔛 γ ≤ Subgroup.normalizer (conjCl (stab 𝔛 γ) (ZM 𝔛 α) : Set 𝔘) :=
    le_normalizer_conjCl _ _
  have hWs : conjCl (stab 𝔛 γ) (ZM 𝔛 α) ≤ stab 𝔛 γ :=
    (conjCl_le_of_le_normalizer' hZαV (stab_le_normalizer_vv h γ)).trans hVs
  have hUZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h hfull hγ
  have hZUD : ZM 𝔛 γ ≤ Uloc h.le L γ ⊔ Dloc h.le L γ := by
    rw [zm_eq_uloc_sup_zloc h hfull hγ]
    exact sup_le_sup_left (zloc_le_dloc h γ) _
  have hWQ := commutator_conjCl_qv_le h hfull hb hφ hα hγ hαβ hβγ hH hψs hψ hWQL
  have hK₀ : ⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), Qv 𝔛 γ⁆ ⊔ ZM 𝔛 γ ≤
      Uloc h.le L γ ⊔ Dloc h.le L γ := sup_le hWQ hZUD
  have hCn : stab 𝔛 γ ≤ Subgroup.normalizer (C : Set 𝔘) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hCG.trans hKC)
  have hPW : ⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ ≤
      conjCl (stab 𝔛 γ) (ZM 𝔛 α) :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hWn)
      (le_sup_right.trans (hKC.trans hCW))
  have hWC : IsSumOfNaturalModulesVia (stab 𝔛 γ) (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C ψ dual 1 := by
    have := isSumOfNaturalModulesVia_transfer hPK hPC hPiC le_rfl (sup_eq_left.mpr hCW) hWn hCn
      ((hPW.trans hWs).trans hCn)
    rwa [inf_eq_right.mpr hCW] at this
  refine ⟨C, hUZ.trans (le_sup_right.trans hKC), hCG.trans hK₀, hWQ, hWC, ?_⟩
  intro w hw g hg hwC
  have hP : w⁻¹ * (g * w * g⁻¹) ∈ ⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ := by
    refine Subgroup.mem_sup_left ?_
    have e : w⁻¹ * (g * w * g⁻¹) = ⁅w⁻¹, g⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hw) hg
  have hPC' : w⁻¹ * (g * w * g⁻¹) ∈
      (⁅conjCl (stab 𝔛 γ) (ZM 𝔛 α), stab 𝔛 γ⁆ ⊔ ZM 𝔛 γ) ⊓ C := ⟨hP, hwC⟩
  rw [hPiC] at hPC'
  exact hK₀ hPC'

theorem mem_of_commutator_mem_dloc (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ) {dual : Bool}
    {C : Subgroup 𝔘} (hs : IsSecD h.le L γ ψ dual (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C)
    {w : 𝔘} (hwW : w ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α))
    (hwQ : ∀ y ∈ Qv 𝔛 γ, ⁅w, y⁆ ∈ Dloc h.le L γ) : w ∈ C := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨-, hCG, hWQ, hWC, -⟩ := hs
  by_contra hwC
  apply hH
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h (by omega) hγ).trans hQs
  have hWV : conjCl (stab 𝔛 γ) (ZM 𝔛 α) ≤ Vv 𝔛 γ :=
    conjCl_le_of_le_normalizer' hZαV (stab_le_normalizer_vv h γ)
  have hWs := hWV.trans hVs
  have hZαs : ZM 𝔛 α ≤ stab 𝔛 γ := hZαV.trans hVs
  have hVab : ⁅Vv 𝔛 γ, Vv 𝔛 γ⁆ = ⊥ := vv_comm_eq_bot h hb hγ
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hUDQ := commutator_uloc_sup_dloc_qv_le h hfull hγ
  have hβH : ¬ IsMVtx 𝔛 β := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hRfin : Finite ↥(Usup 𝔛 α β) := by
    have := finite_qv _ h20 hβH
    have hle : Usup 𝔛 α β ≤ Qv _ β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact commutator_le_of_le ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hRq : Nat.card ↥(Usup 𝔛 α β) < Fintype.card F ^ 3 := by
    have h1 := card_usup_le_sq h hfull hφ hα hαβ
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hRZ : Usup 𝔛 α β ≤ ZM 𝔛 α := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))
  have hRs : Usup 𝔛 α β ≤ stab 𝔛 γ := hRZ.trans hZαs
  let K : Subgroup 𝔘 :=
    { carrier := {v | v ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) ∧ ∀ y ∈ Qv 𝔛 γ, ⁅v, y⁆ ∈ Dloc h.le L γ}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hDn (hWs ha)) _).mp (hb' y hy))
          (ha' y hy)
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hDn (hWs (Subgroup.inv_mem _ ha))) _).mp
          (Subgroup.inv_mem _ (ha' y hy)) }
  have hKn : ∀ l : ↥(stab 𝔛 γ), ∀ v ∈ K, (l : 𝔘) * v * (l : 𝔘)⁻¹ ∈ K := by
    rintro l v ⟨hv, hv'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjCl _ _ l.2) v).mp hv,
      fun y hy => ?_⟩
    have hy' : (l : 𝔘)⁻¹ * y * (l : 𝔘) ∈ Qv 𝔛 γ := by
      have := (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_qv _ γ (Subgroup.inv_mem _ l.2)) y).mp hy
      simpa using this
    have e : ⁅(l : 𝔘) * v * (l : 𝔘)⁻¹, y⁆ = (l : 𝔘) * ⁅v, (l : 𝔘)⁻¹ * y * (l : 𝔘)⁆ * (l : 𝔘)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hDn l.2) _).mp (hv' _ hy')
  set NW := NatSec.ofIsSum hWC with hNW
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨u, ⟨huW, huQ⟩, -, huc⟩ :=
    NW.exists_inv_mul_mem_of_invariant hψs hKn ⟨hwW, hwQ⟩ hwW hwC (le_conjCl _ _ hx)
  have hcs : u⁻¹ * x ∈ stab 𝔛 γ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWs huW)) (hZαs hx)
  have hcW : u⁻¹ * x ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ huW) (le_conjCl _ _ hx)
  have hcR : ∀ y' ∈ Qv 𝔛 γ, ⁅u⁻¹ * x, y'⁆ ∈ Usup 𝔛 α β ⊔ Dloc h.le L γ := by
    intro y' hy'
    have hxy : ⁅x, y'⁆ ∈ Usup 𝔛 α β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact Subgroup.commutator_mem_commutator hx (qv_le_qv _ h20 hγ hβγ.symm hy')
    have hcomm : u⁻¹ * ⁅x, y'⁆ * u = ⁅x, y'⁆ := by
      have h1 : ⁅u⁻¹, ⁅x, y'⁆⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator (hWV (Subgroup.inv_mem _ huW))
          (hZαV (hRZ hxy))
        rw [hVab] at this
        exact this
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      rw [h1]
      group
    have hd : ⁅u⁻¹, y'⁆ ∈ Dloc h.le L γ := by
      have e : ⁅u⁻¹, y'⁆ = u⁻¹ * ⁅u, y'⁆⁻¹ * u⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hDn (Subgroup.inv_mem _ (hWs huW))) _).mp
        (Subgroup.inv_mem _ (huQ y' hy'))
    have e : ⁅u⁻¹ * x, y'⁆ = (u⁻¹ * ⁅x, y'⁆ * u) * ⁅u⁻¹, y'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hcomm]
    exact Subgroup.mul_mem_sup hxy hd
  have hcQ := commutator_mem_dloc_of_conj h hfull hφ hγ hcs hUDQ (fun k hk => by
      have e : (u⁻¹ * x)⁻¹ * (k * (u⁻¹ * x) * k⁻¹) = ⁅(u⁻¹ * x)⁻¹, k⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hCG (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ huc) hk))
    hRs hcR hRq (fun y' hy' => hWQ (Subgroup.commutator_mem_commutator hcW hy'))
  have e : ⁅x, y⁆ = u * ⁅u⁻¹ * x, y⁆ * u⁻¹ * ⁅u, y⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hDn (hWs huW)) _).mp (hcQ y hy))
    (huQ y hy)

theorem concl441_of_secD (h17 : MS17i) (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : IsSecD h.le L γ ψ false (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C) :
    Concl441 h.le L α γ := by
  intro _
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hUC, hCG, hWQ, hWC, hCK⟩ := hs
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h (by omega) hγ).trans hQs
  have hWV : conjCl (stab 𝔛 γ) (ZM 𝔛 α) ≤ Vv 𝔛 γ :=
    conjCl_le_of_le_normalizer' hZαV (stab_le_normalizer_vv h γ)
  have hWn : stab 𝔛 γ ≤ Subgroup.normalizer (conjCl (stab 𝔛 γ) (ZM 𝔛 α) : Set 𝔘) :=
    le_normalizer_conjCl _ _
  have hZαs : ZM 𝔛 α ≤ stab 𝔛 γ := hZαV.trans hVs
  have hDn : stab 𝔛 γ ≤ Subgroup.normalizer (Dloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) γ
  have hUDQ := commutator_uloc_sup_dloc_qv_le h hfull hγ
  have hDWC := dloc_inf_le_of_isSum h hfull hγ hψs hψ hWC
  have hβH : ¬ IsMVtx 𝔛 β := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hRfin : Finite ↥(Usup 𝔛 α β) := by
    have := finite_qv _ h20 hβH
    have hle : Usup 𝔛 α β ≤ Qv _ β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact commutator_le_of_le ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hxR : ∀ z ∈ ZM 𝔛 α, ∀ y ∈ Qv 𝔛 γ, ⁅z, y⁆ ∈ Usup 𝔛 α β := by
    intro z hz y hy
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator hz (qv_le_qv _ h20 hγ hβγ.symm hy)
  have hRq : Nat.card ↥(Usup 𝔛 α β) < Fintype.card F ^ 3 := by
    have h1 := card_usup_le_sq h hfull hφ hα hαβ
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hRs : Usup 𝔛 α β ≤ stab 𝔛 γ := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact commutator_le_of_le hZαs (qv_le_stab_of_adj _ hβγ)
  have hcases : ∀ z ∈ ZM 𝔛 α, (∀ y ∈ Qv 𝔛 γ, ⁅z, y⁆ ∈ Dloc h.le L γ) ∨
      ∃ U' : Subgroup 𝔘, z ∈ U' ∧ U' ≤ conjCl (stab 𝔛 γ) (ZM 𝔛 α) ∧
        stab 𝔛 γ ≤ Subgroup.normalizer (U' : Set 𝔘) ∧
        ⁅⁅Qv 𝔛 γ, stab 𝔛 γ⁆, U'⁆ ≤ Dloc h.le L γ ∧
        ∀ w ∈ Qv 𝔛 γ, (∃ u ∈ U', ⁅u, w⁆ ∉ Dloc h.le L γ) →
          Uloc h.le L γ ≤ ⁅U', Subgroup.zpowers w⁆ ⊔ Dloc h.le L γ := by
    intro z hz
    by_cases hzt : ∀ y ∈ Qv 𝔛 γ, ⁅z, y⁆ ∈ Dloc h.le L γ
    · exact Or.inl hzt
    right
    push Not at hzt
    obtain ⟨y₀, hy₀, hzy₀⟩ := hzt
    have hzW : z ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) := le_conjCl _ _ hz
    have hzC : z ∉ C := by
      intro hzC
      refine hzy₀ (commutator_mem_dloc_of_conj h hfull hφ hγ (hZαs hz) hUDQ (fun k hk => ?_)
        hRs (fun y hy => Subgroup.mem_sup_left (hxR z hz y hy)) hRq
        (fun y hy => hWQ (Subgroup.commutator_mem_commutator hzW hy)) y₀ hy₀)
      have e : z⁻¹ * (k * z * k⁻¹) = ⁅z⁻¹, k⁆ := by simp only [commutatorElement_def]; group
      rw [e]
      exact hCG (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hzC) hk)
    exact exists_ms17i_of_same h hfull h17 hb hφ hα hγ hαβ hβγ hWV hWn hψs hψ hWC hUC hDWC hCG
      hWQ hCK hUDQ hz hzW hzC hy₀ hzy₀
  have hgen : ∀ w ∈ Qv 𝔛 γ, ∀ g ∈ stab 𝔛 γ, ∀ z ∈ ZM 𝔛 α,
      ⁅z, g⁻¹ * w * g⁆ ∈ Dloc h.le L γ → ⁅g * z * g⁻¹, w⁆ ∈ Dloc h.le L γ := by
    intro w hw g hg z hz hzw
    have e : ⁅g * z * g⁻¹, w⁆ = g * ⁅z, g⁻¹ * w * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hDn hg) _).mp hzw
  have hconjQ : ∀ w ∈ Qv 𝔛 γ, ∀ g ∈ stab 𝔛 γ, g⁻¹ * w * g ∈ Qv 𝔛 γ := by
    intro w hw g hg
    have := (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_qv _ γ (Subgroup.inv_mem _ hg)) w).mp hw
    simpa using this
  refine ⟨?_, fun w hw hne => ?_⟩
  ·
    rw [Subgroup.commutator_le]
    intro v hv w hw
    refine commutator_conjCl_zpowers_le hDn hZαs (hQs hw.2) (fun g hg z hz => ?_)
      (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers w))
    refine hgen w hw.2 g hg z hz ?_
    rcases hcases z hz with hzt | ⟨U', hzU', -, -, c2, -⟩
    · exact hzt _ (hconjQ w hw.2 g hg)
    · have hzw : ⁅z, w⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hz) w hw.1).symm
      have hq : ⁅w⁻¹, g⁻¹⁆ ∈ ⁅Qv 𝔛 γ, stab 𝔛 γ⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hw.2) (Subgroup.inv_mem _ hg)
      have hzq : ⁅z, ⁅w⁻¹, g⁻¹⁆⁆ ∈ Dloc h.le L γ := by
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ (c2 (Subgroup.commutator_mem_commutator hq hzU'))
      have e : ⁅z, g⁻¹ * w * g⁆ = ⁅z, w⁆ * (w * ⁅z, ⁅w⁻¹, g⁻¹⁆⁆ * w⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e, hzw, one_mul]
      exact (Subgroup.mem_normalizer_iff.mp (hDn (hQs hw.2)) _).mp hzq
  ·
    obtain ⟨g, hg, z, hz, hgz⟩ : ∃ g ∈ stab 𝔛 γ, ∃ z ∈ ZM 𝔛 α,
        ⁅g * z * g⁻¹, w⁆ ∉ Dloc h.le L γ := by
      by_contra hall
      push Not at hall
      exact hne (commutator_conjCl_zpowers_le hDn hZαs (hQs hw) hall)
    rcases hcases z hz with hzt | ⟨U', hzU', hU'W, hU'n, -, c4⟩
    · exact absurd (hgen w hw g hg z hz (hzt _ (hconjQ w hw g hg))) hgz
    · have hu : g * z * g⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp (hU'n hg) z).mp hzU'
      have h1 := c4 w hw ⟨_, hu, hgz⟩
      rw [zm_eq_uloc_sup_zloc h hfull hγ]
      refine sup_le (h1.trans (sup_le_sup_right ?_ _)) ((zloc_le_dloc h γ).trans le_sup_right)
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl hU'W

end Vertex

end CFSG.Quasithin.MS93.S4A.L441
