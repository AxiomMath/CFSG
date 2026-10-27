module

public import CFSG.Quasithin.MS93.S46I469B0
public import CFSG.Quasithin.MS93.S46I468
public import CFSG.Quasithin.MS93.S46Stmt9

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464 CFSG.Quasithin.MS93.S46.I466b
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hb4 : critDist (puAmalgam h.le) = 4)
  (h43 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
    ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
  (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h465 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
  (h466b : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ¬ ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ stabCenter _ x)
  (h467 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    Bloc h.le L x = centerOf (Vv (puAmalgam h.le) x))
  (h468 : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
    ∀ g : GoldAmalgam.Universal (puAmalgam h.le), IsOddL1 (puAmalgam h.le) α β g →
      ∀ x ∈ Vv (puAmalgam h.le) β, ∀ v ∈ Vv (puAmalgam h.le) α, ⁅⁅x, g⁆, v⁆ ∈ stabCenter _ α)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

omit [Fintype F] in
theorem mem_normalizer_zh_of_mem_normalizer_qv {β : Vtx (puAmalgam h.le)} {n : 𝔘}
    (hn : n ∈ Subgroup.normalizer (Qv (puAmalgam h.le) β : Set 𝔘)) :
    n ∈ Subgroup.normalizer (ZH (puAmalgam h.le) β : Set 𝔘) := by
  have key : ∀ m ∈ Subgroup.normalizer (Qv 𝔛 β : Set 𝔘),
      (ZH 𝔛 β).map (MulAut.conj m).toMonoidHom ≤ ZH 𝔛 β := fun m hm => by
    rw [← zh_smul _ m β, zh_smul_eq_of_mem_normalizer h hm]
  exact mem_normalizer_of_map_conj_le (key n hn) (key n⁻¹ (Subgroup.inv_mem _ hn))

include hφ hb4 h43 h463 h464 hsq h465 h466 h466b h467 h468 in
theorem commutator_mem_zh_of_isOddL1 {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {g : 𝔘} (hg : IsOddL1 (puAmalgam h.le) α β g) :
    ∀ x ∈ Vv (puAmalgam h.le) β, ⁅x, g⁆ ∈ ZH (puAmalgam h.le) β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist 𝔛 := by omega
  have hβH : ¬ IsMVtx 𝔛 β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hgV := normalizer_qv_le_normalizer_vv h hβH hg.2.1
  have hgZ := mem_normalizer_zh_of_mem_normalizer_qv h hg.2.1
  have hZV : ZH 𝔛 β ≤ Vv 𝔛 β := by
    have : Zv 𝔛 β ≤ Vv 𝔛 β := le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx 𝔛 |
      (puAmalgam h.le).treeGraph.dist β ρ ≤ 2}) => Zv 𝔛 ρ) β (by simp) le_rfl
    rwa [zv_of_not_isMVtx _ hβH] at this
  have hcV : ∀ y ∈ Vv 𝔛 β, ⁅y, g⁆ ∈ Vv 𝔛 β := fun y hy => by
    have h1 : g * y⁻¹ * g⁻¹ ∈ Vv 𝔛 β :=
      (Subgroup.mem_normalizer_iff.mp hgV _).mp (Subgroup.inv_mem _ hy)
    have e : ⁅y, g⁆ = y * (g * y⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hy h1
  have h461 : ∀ x : Vtx 𝔛, IsMVtx 𝔛 x → centerOf (Vv 𝔛 x) ≤ Bloc h.le L x := fun x hx =>
    (h467 x hx).ge
  refine commutator_mem_of_odd (fun a ha => vv_mul_self_eq_one h hb hβH ha) hZV hgV hgZ
    hg.2.2.2 fun x hx => ?_
  have hx₁ := hcV x hx
  have hx₁α : ⁅x, g⁆ ∈ Vv 𝔛 α := vv_le_vv_of_adj h hα hαβ hx₁
  have hx₁c : ⁅x, g⁆ ∈ centerOf (Vv 𝔛 α) :=
    mem_centerOf_of_commutator_mem_zloc h hφ h464 hsq h466 h463 hb4 h43 h465 h466b h467 h468
      hα hx₁α fun w hw => mem_zloc_of_mem_stabCenter h hφ hα
        (h463 α hα (Subgroup.commutator_mem_commutator hx₁α hw)) (h468 α β hα hαβ g hg x hx w hw)
  have hx₂ : ⁅⁅x, g⁆, g⁆ ∈ ZM 𝔛 α := by
    rw [← commutatorElement_inv]
    refine Subgroup.inv_mem _ ?_
    have := commutator_centerOf_stab_le h h461 h465 hfull hb hα hx₁c hg.1
    rwa [commutatorElement_def]
  exact hg.2.2.1 _ hx₂

include hφ hb4 h43 h463 h464 hsq h465 h466 h466b h467 h468 in
theorem vv_sup_qv_eq_and_usup_eq {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hγ : IsMVtx _ γ) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hβγ : (puAmalgam h.le).treeGraph.Adj β γ) (hZ : ¬ ZM (puAmalgam h.le) γ ≤ Bloc h.le L α) :
    Vv (puAmalgam h.le) α ⊔ Qv _ γ = Qv _ β ∧
      Usup (puAmalgam h.le) γ β = Usup _ α β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hβH : ¬ IsMVtx 𝔛 β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hαγ : α ≠ γ := by
    rintro rfl
    exact hZ (zm_le_bloc h hb hα)
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  have hZV : ZM 𝔛 γ ≤ Vv 𝔛 α := zm_le_vv_of_dist_le_two hγ hd.le
  rw [h467 α hα] at hZ
  obtain ⟨x, hx, hxc⟩ := Set.not_subset.mp hZ
  have hxV : x ∈ Vv 𝔛 α := hZV hx
  have hxVβ : x ∈ Vv 𝔛 β := zm_le_vv_of_adj hβγ hγ hx
  obtain ⟨w₀, hw₀, hxw₀⟩ : ∃ w₀ ∈ Vv 𝔛 α, ⁅x, w₀⁆ ∉ Zloc h.le L α := by
    by_contra! hall
    exact hxc (mem_centerOf_of_commutator_mem_zloc h hφ h464 hsq h466 h463 hb4 h43 h465 h466b
      h467 h468 hα hxV hall)
  have hc : ∀ w ∈ Vv 𝔛 α, ∀ w' ∈ Vv 𝔛 α, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w := fun w hw w' hw' =>
    commute_commutator_vv h h463 hb hα hxV hw' hw
  set R := (commHomOf (Vv 𝔛 α) x hc).range with hRdef
  have hinv' : ∀ g : 𝔘, IsOddL1 𝔛 α β g → ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
    intro g hg y hy
    obtain ⟨w, hw, rfl⟩ := mem_range_commHomOf.mp hy
    have hgV : g * w * g⁻¹ ∈ Vv 𝔛 α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α hg.1) w).mp hw
    have hgVβ := normalizer_qv_le_normalizer_vv h hβH hg.2.1
    have hcβ : ⁅x, g⁆ ∈ Vv 𝔛 β := by
      have h1 : g * x⁻¹ * g⁻¹ ∈ Vv 𝔛 β :=
        (Subgroup.mem_normalizer_iff.mp hgVβ _).mp (Subgroup.inv_mem _ hxVβ)
      have e : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hxVβ h1
    have hcV : ⁅x, g⁆ ∈ Vv 𝔛 α := vv_le_vv_of_adj h hα hαβ hcβ
    have hcc : ⁅x, g⁆ ∈ centerOf (Vv 𝔛 α) :=
      mem_centerOf_of_commutator_mem_zloc h hφ h464 hsq h466 h463 hb4 h43 h465 h466b h467 h468
        hα hcV fun v hv => mem_zloc_of_mem_stabCenter h hφ hα
          (h463 α hα (Subgroup.commutator_mem_commutator hcV hv))
          (h468 α β hα hαβ g hg x hxVβ v hv)
    have hcomm : ⁅x, g⁆⁻¹ * ⁅x, g * w * g⁻¹⁆ = ⁅x, g * w * g⁻¹⁆ * ⁅x, g⁆⁻¹ :=
      commute_commutator_vv h h463 hb hα hxV hgV (Subgroup.inv_mem _ hcV)
    rw [conj_commutatorElement_eq hcomm]
    have h1 : ⁅⁅x, g⁆⁻¹, g * w * g⁻¹⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hcc).2 _ hgV).symm
    rw [h1, mul_one]
    exact mem_range_commHomOf.mpr ⟨_, hgV, rfl⟩
  have hnot : ¬ R ≤ Zloc h.le L α := fun hle =>
    hxw₀ (hle (mem_range_commHomOf.mpr ⟨w₀, hw₀, rfl⟩))
  obtain ⟨hReq₀, hHZ⟩ := range_eq_usup h hφ h464 hsq h466 hb hα hγ hαβ hβγ hx hc hnot
    fun g hg y hy => Subgroup.mem_sup_left (hinv' g hg y hy)
  have hReq : R = Usup 𝔛 γ β := hReq₀
  have : Finite ↥(stab 𝔛 α) := finite_stab h hα
  have : Finite ↥(Vv 𝔛 α) := finite_of_le_stab h hα ((vv_le_qv h hb hα).trans (qv_le_stab _ α))
  refine ⟨?_, ?_⟩
  ·
    have hVβ : Vv 𝔛 α ≤ Qv 𝔛 β := (vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)
    have hQγβ : Qv 𝔛 γ ≤ Qv 𝔛 β := qv_le_qv _ h20 hγ hβγ.symm
    have hle : Vv 𝔛 α ⊔ Qv 𝔛 γ ≤ Qv 𝔛 β := sup_le hVβ hQγβ
    have hVn : Vv 𝔛 α ≤ Subgroup.normalizer (Qv 𝔛 γ : Set 𝔘) :=
      hVβ.trans ((qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_qv _ γ))
    have hcard := card_range_commHomOf_le (hc := hc) (K := Qv 𝔛 γ) fun w _ hwQ =>
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hγ hx) w hwQ).symm
    rw [hReq₀, hsq γ β hγ hβγ.symm, ← relIndex_sup_of_le_normalizer hVn] at hcard
    have h1 := Subgroup.relIndex_mul_relIndex (Qv 𝔛 γ) (Vv 𝔛 α ⊔ Qv 𝔛 γ) (Qv 𝔛 β) le_sup_right
      hle
    rw [h466 γ β hγ hβγ.symm] at h1
    have h2 : (Vv 𝔛 α ⊔ Qv 𝔛 γ).relIndex (Qv 𝔛 β) = 1 := by
      have h3 : (Qv 𝔛 γ).relIndex (Vv 𝔛 α ⊔ Qv 𝔛 γ) ≤ Fintype.card F ^ 2 := by
        rw [← h466 γ β hγ hβγ.symm]
        exact Subgroup.relIndex_le_of_le_right hle (by rw [h466 γ β hγ hβγ.symm]; positivity)
      have h4 : (Qv 𝔛 γ).relIndex (Vv 𝔛 α ⊔ Qv 𝔛 γ) = Fintype.card F ^ 2 := le_antisymm h3 hcard
      rw [h4] at h1
      have hq : 0 < Fintype.card F ^ 2 := by positivity
      exact Nat.eq_of_mul_eq_mul_left hq (h1.trans (mul_one _).symm)
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
  ·
    have hHn : ∀ g : 𝔘, IsOddL1 𝔛 α β g → ∀ y ∈ Usup 𝔛 α β, g * y * g⁻¹ ∈ Usup 𝔛 α β := by
      intro g hg y hy
      have e : (Usup 𝔛 α β).map (MulAut.conj g).toMonoidHom = Usup 𝔛 α β := by
        rw [show Usup 𝔛 α β = ⁅ZM 𝔛 α, Qv 𝔛 β⁆ by rw [Usup, zv_of_isMVtx _ hα],
          Subgroup.map_commutator,
          map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ α hg.1),
          map_conj_eq_of_mem_normalizer hg.2.1]
      rw [← e]
      exact ⟨y, hy, rfl⟩
    have hYinv : ∀ g : 𝔘, IsOddL1 𝔛 α β g → ∀ y ∈ Usup 𝔛 γ β ⊓ Usup 𝔛 α β,
        g * y * g⁻¹ ∈ Usup 𝔛 γ β ⊓ Usup 𝔛 α β :=
      fun g hg y hy => ⟨by rw [← hReq]; exact hinv' g hg y (by rw [hReq]; exact hy.1),
        hHn g hg y hy.2⟩
    have : Finite ↥(Usup 𝔛 γ β) := finite_of_le_stab h hα ((h464 γ β hγ hβγ.symm).trans
      ((zh_le_zm _ hαβ).trans ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α))))
    rcases eq_bot_or_eq_usup h hφ h464 hsq h466 hα hαβ
      (inf_le_right : Usup 𝔛 γ β ⊓ Usup 𝔛 α β ≤ Usup 𝔛 α β) hYinv with hY | hY
    · exfalso
      obtain ⟨h₀, hh₀, hh₀1⟩ : ∃ h₀ ∈ Usup 𝔛 γ β, h₀ ≠ 1 := by
        by_contra! hall
        have hbot : Usup 𝔛 γ β = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
        have := hsq γ β hγ hβγ.symm
        rw [hbot, Subgroup.card_bot] at this
        have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
        nlinarith
      have hh₀Z : h₀ ∈ Usup 𝔛 α β ⊔ Zloc h.le L α := by
        rw [← zh_eq_usup_sup_zloc h hφ h464 hsq hα hαβ]
        exact h464 γ β hγ hβγ.symm hh₀
      obtain ⟨a, ha, ζ, hζ, rfl⟩ := exists_mul_of_mem_sup_of_commute
        (fun a ha b hb' => commute_zh h (h464 α β hα hαβ ha) (zloc_le_zh h hfull hα hαβ hb'))
        hh₀Z
      have ha1 : a ≠ 1 := by
        rintro rfl
        rw [one_mul] at hh₀ hh₀1
        have : ζ ∈ Usup 𝔛 γ β ⊓ Zloc h.le L α := ⟨hh₀, hζ⟩
        rw [hHZ, Subgroup.mem_bot] at this
        exact hh₀1 this
      obtain ⟨g, hg, hgaH, hgane⟩ := exists_isOddL1_conj_ne h hφ h464 hsq h466 hα hαβ ha ha1
      have hζc : g * ζ * g⁻¹ = ζ := by
        rw [Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hα hζ) g hg.1,
          mul_inv_cancel_right]
      have hconj : g * (a * ζ) * g⁻¹ = (g * a * g⁻¹) * ζ := by
        calc g * (a * ζ) * g⁻¹ = (g * a * g⁻¹) * (g * ζ * g⁻¹) := by group
          _ = (g * a * g⁻¹) * ζ := by rw [hζc]
      have hmem : g * (a * ζ) * g⁻¹ ∈ Usup 𝔛 γ β := by
        rw [← hReq]
        exact hinv' g hg _ (by rw [hReq]; exact hh₀)
      rw [hconj] at hmem
      have hprod : a * ζ * ((g * a * g⁻¹) * ζ)⁻¹ = a * (g * a * g⁻¹)⁻¹ := by group
      have hY' : a * (g * a * g⁻¹)⁻¹ ∈ Usup 𝔛 γ β ⊓ Usup 𝔛 α β := by
        refine ⟨?_, Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hgaH)⟩
        rw [← hprod]
        exact Subgroup.mul_mem _ hh₀ (Subgroup.inv_mem _ hmem)
      rw [hY, Subgroup.mem_bot, mul_inv_eq_one] at hY'
      exact hgane hY'.symm
    · have hle : Usup 𝔛 α β ≤ Usup 𝔛 γ β := by rw [← hY]; exact inf_le_left
      exact (Subgroup.eq_of_le_of_card_ge hle (by
        rw [hsq α β hα hαβ, hsq γ β hγ hβγ.symm])).symm

omit [Fintype F] in
include hb4 h43 h467 in
theorem not_zm_le_bloc_of_not_zm_le_bloc (hfull : IsSL3Full M T L) {α β γ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hγ : IsMVtx _ γ) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hβγ : (puAmalgam h.le).treeGraph.Adj β γ) (hZ : ¬ ZM (puAmalgam h.le) γ ≤ Bloc h.le L α) :
    ¬ ZM (puAmalgam h.le) α ≤ Bloc h.le L γ := by
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hC := centHyp_of_gen23 h hfull
  have hαγ : α ≠ γ := by
    rintro rfl
    exact hZ (zm_le_bloc h hb hα)
  have hd : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  rw [h467 α hα] at hZ
  obtain ⟨x, hx, hxc⟩ := Set.not_subset.mp hZ
  have hxV : x ∈ Vv 𝔛 α := zm_le_vv_of_dist_le_two hγ hd.le hx
  obtain ⟨w, hw, hxw⟩ : ∃ w ∈ Vv 𝔛 α, x * w ≠ w * x := by
    by_contra! hall
    exact hxc ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun w hw => (hall w hw).symm⟩
  have hVQ := not_vv_le_qv_of_not_commute h20 hb4 h43 hγ hd hx hw hxw
  intro hle
  rw [h467 γ hγ] at hle
  apply hVQ
  intro v hv
  rw [← hC α β hα hαβ]
  refine ⟨qv_le_qv _ h20 hγ hβγ.symm (vv_le_qv h hb hγ hv),
    Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hle hz).2 v hv).symm

include hφ hb4 h43 h463 h464 hsq h465 h466 h466b h467 h468 in
theorem commutator_qv_ltil_le_vv {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    ⁅Qv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ Vv _ α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hb0 : 0 < critDist 𝔛 := by omega
  have hC := centHyp_of_gen23 h hfull
  obtain ⟨α', hc', hgeo1⟩ := exists_isCritical_geo _ h20 hb0 hα hαβ
  have hγ : IsMVtx 𝔛 (geo 𝔛 α α' 2) := isMVtx_geo_two' hb4 hc'
  have hβγ : (puAmalgam h.le).treeGraph.Adj β (geo 𝔛 α α' 2) := by
    have := adj_geo_crit hb4 hc' (i := 1) (by omega)
    rwa [hgeo1] at this
  have hd : (puAmalgam h.le).treeGraph.dist α (geo 𝔛 α α' 2) = 2 := dist_geo_crit hb4 hc' (by omega)
  have hVQ : ¬ Vv 𝔛 α ≤ Qv 𝔛 (geo 𝔛 α α' 2) := by
    have := h43 α α' hc'
    rwa [geo_rev_two hb4 hc'] at this
  have hZ : ¬ ZM 𝔛 (geo 𝔛 α α' 2) ≤ Bloc h.le L α := by
    rw [h467 α hα]
    intro hle
    apply hVQ
    intro v hv
    rw [← hC _ β hγ hβγ.symm]
    refine ⟨qv_le_qv _ h20 hα hαβ (vv_le_qv h hb hα hv),
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hle hz).2 v hv).symm
  obtain ⟨hT, -⟩ := vv_sup_qv_eq_and_usup_eq h hφ hb4 h43 h463 h464 hsq h465 h466 h466b h467
    h468 hα hγ hαβ hβγ hZ
  have hVn : Vv 𝔛 α ≤ Subgroup.normalizer (Qv 𝔛 (geo 𝔛 α α' 2) : Set 𝔘) :=
    ((vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)).trans
      ((qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_qv _ _))
  have hα' : IsMVtx 𝔛 α' := hc'.isMVtx_right _ h20
  have hK : ⁅Qv 𝔛 α, ZM 𝔛 α'⁆ ≤ Vv 𝔛 α := by
    rw [Subgroup.commutator_le]
    intro q hq z hz
    have hqT : q ∈ ((Vv 𝔛 α ⊔ Qv 𝔛 (geo 𝔛 α α' 2) : Subgroup 𝔘) : Set 𝔘) := by
      rw [SetLike.mem_coe, hT]
      exact qv_le_qv _ h20 hα hαβ hq
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVn] at hqT
    obtain ⟨v, hv, t, ht, rfl⟩ := hqT
    have hzs : z ∈ stab 𝔛 α := zm_le_stab_of_isCritical _ h20 hb0 hc' hz
    have hzVγ : z ∈ Vv 𝔛 (geo 𝔛 α α' 2) := zm_le_vv_of_dist_le_two hα'
      (by rw [dist_geo_crit_right hb4 hc' (by omega)]) hz
    have h1 : ⁅t, z⁆ ∈ Vv 𝔛 α := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (zm_le_vv_of_dist_le_two hγ hd.le
        (h465 _ hγ (Subgroup.commutator_mem_commutator hzVγ ht)))
    have h2 : ⁅v, z⁆ ∈ Vv 𝔛 α := by
      have h3 : z * v⁻¹ * z⁻¹ ∈ Vv 𝔛 α :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α hzs) _).mp
          (Subgroup.inv_mem _ hv)
      have e : ⁅v, z⁆ = v * (z * v⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hv h3
    rw [commutatorElement_mul_left_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hv h1)
      (Subgroup.inv_mem _ hv)) h2
  have hKρ : ZM 𝔛 α' ≤ Qv 𝔛 β := by
    have := zm_right_le_qv_geo h20 hb4 hc' (i := 1) le_rfl (by omega)
    rwa [hgeo1] at this
  exact commutator_ltil_le_of_commutator_le h hfull hα hαβ (stab_le_normalizer_qv _ α)
    (stab_le_normalizer_vv h α) hK hKρ (ms22_iii _ h20 hb0 hC hc').2.2

include hφ hb4 h43 h463 h464 hsq h465 h466 h466b h467 h468 in
theorem commutator_vv_eq_uloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ = Uloc h.le L α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist 𝔛 := by omega
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  have hle : ⁅Vv 𝔛 α, Vv 𝔛 α⁆ ≤ Uloc h.le L α := by
    refine commutator_iSup₂_le_of (fun ρ hρ => ?_) (fun ρ hρ => ?_)
    · have hρ' : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 := hρ
      by_cases h1 : (puAmalgam h.le).treeGraph.dist α ρ ≤ 1
      · rw [Subgroup.commutator_le]
        intro x hx w hw
        have hxZ := zv_le_zm_of_dist_le_one h hα h1 hx
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv h hb hα hxZ hw)]
        exact one_mem _
      · have h2 : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by omega
        have hρM : IsMVtx 𝔛 ρ := ((even_dist_iff _ α ρ).mp (by rw [h2]; decide)).mp hα
        rw [zv_of_isMVtx _ hρM]
        have ha1 : (puAmalgam h.le).treeGraph.Adj α (geo 𝔛 α ρ 1) := by
          have := adj_geo 𝔛 (u := α) (w := ρ) (i := 0) (by omega)
          rwa [geo_zero] at this
        have ha2 : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 α ρ 1) ρ := by
          have := adj_geo 𝔛 (u := α) (w := ρ) (i := 1) (by omega)
          rwa [show geo 𝔛 α ρ (1 + 1) = ρ from geo_of_le _ (by omega)] at this
        by_cases hZ : ZM 𝔛 ρ ≤ Bloc h.le L α
        · rw [h467 α hα] at hZ
          rw [Subgroup.commutator_le]
          intro x hx w hw
          rw [commutatorElement_eq_one_iff_mul_comm.mpr
            (Subgroup.mem_centralizer_iff.mp (hZ hx).2 w hw).symm]
          exact one_mem _
        · obtain ⟨-, hUU⟩ := vv_sup_qv_eq_and_usup_eq h hφ hb4 h43 h463 h464 hsq h465 h466 h466b
            h467 h468 hα hρM ha1 ha2 hZ
          have hVT : Vv 𝔛 α ≤ Qv 𝔛 (geo 𝔛 α ρ 1) :=
            (vv_le_qv h hb hα).trans (qv_le_qv _ h.hyp20 hα ha1)
          calc ⁅ZM 𝔛 ρ, Vv 𝔛 α⁆ ≤ ⁅ZM 𝔛 ρ, Qv 𝔛 (geo 𝔛 α ρ 1)⁆ :=
                Subgroup.commutator_mono le_rfl hVT
            _ = Usup 𝔛 ρ (geo 𝔛 α ρ 1) := by rw [Usup, zv_of_isMVtx _ hρM]
            _ = Usup 𝔛 α (geo 𝔛 α ρ 1) := hUU
            _ ≤ Uloc h.le L α := usup_le_uloc' h hfull hα ha1
    · have hρ' : (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 := hρ
      have : Zv 𝔛 ρ ≤ Vv 𝔛 α := le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx 𝔛 |
        (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}) => Zv 𝔛 ρ) ρ hρ' le_rfl
      exact this.trans ((vv_le_qv h hb hα).trans ((qv_le_stab _ α).trans hUn))
  have hn : stab 𝔛 α ≤ Subgroup.normalizer ((⁅Vv 𝔛 α, Vv 𝔛 α⁆ : Subgroup 𝔘) : Set 𝔘) :=
    le_normalizer_of_map_conj_le fun g hg => by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h α hg)]
  rcases eq_bot_or_eq_uloc_of_le h hφ hα hle hn with hbot | heq
  · exfalso
    apply h466b α hα
    rw [hbot]
    exact bot_le
  · exact heq

end Main

theorem i469Cfg_of_s468Cfg (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h466b : I466b) (h467 : I467) {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (h468 : S468Cfg M T L φ) : I469Cfg M T L φ := by
  intro c α β hα hαβ
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have c : Hyp46 M T L φ := ⟨h, hmin, hb4, hφ⟩
  have h43' : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2) :=
    fun δ δ' hc => h43 G M T L h hmin hb hfull δ δ' hc
  have h463' : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x := fun x hx => (h463 G M T L F φ c x hx).2
  have h465' : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x := fun x hx => by
    obtain ⟨ρ, hρ⟩ := exists_adj (puAmalgam h.le) x
    exact (h465 G M T L F φ c x ρ hx hρ).2.2
  have h468' : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
      ∀ g, IsOddL1 (puAmalgam h.le) α β g → ∀ x ∈ Vv (puAmalgam h.le) β,
        ∀ v ∈ Vv (puAmalgam h.le) α, ⁅⁅x, g⁆, v⁆ ∈ stabCenter _ α :=
    fun α β hα hαβ g hg x hx v hv =>
      h468 c α β hα hαβ g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 x hx v hv
  have hh464 := fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ
  have hhsq := fun δ ρ hδ hδρ => (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hh466 := fun δ ρ hδ hδρ => h466a G M T L F φ c δ ρ hδ hδρ
  have hh466b := fun x hx => h466b G M T L F φ c x hx
  have hh467 := fun x hx => h467 G M T L F φ c x hx
  refine ⟨commutator_qv_ltil_le_vv h hφ hb4 h43' h463' hh464 hhsq h465' hh466 hh466b hh467 h468'
      hα hαβ,
    commutator_vv_eq_uloc h hφ hb4 h43' h463' hh464 hhsq h465' hh466 hh466b hh467 h468' hα,
    fun g hg hgN hgZ hodd x hx => commutator_mem_zh_of_isOddL1 h hφ hb4 h43' h463' hh464 hhsq
      h465' hh466 hh466b hh467 h468' hα hαβ ⟨hg, hgN, hgZ, hodd⟩ x hx,
    fun γ hβγ hZ => ?_⟩
  have hγ : IsMVtx (puAmalgam h.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβγ
    tauto
  obtain ⟨hT, hU⟩ := vv_sup_qv_eq_and_usup_eq h hφ hb4 h43' h463' hh464 hhsq h465' hh466 hh466b
    hh467 h468' hα hγ hαβ hβγ hZ
  exact ⟨hT, hU, not_zm_le_bloc_of_not_zm_le_bloc h hb4 h43' hh467 hfull hα hγ hαβ hβγ hZ⟩

theorem i469_of_s468 (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h466b : I466b) (h467 : I467) (h468 : S468) : I469 :=
  fun G _ _ M T L F _ _ φ => i469Cfg_of_s468Cfg h43 h463 h464 h465 h466a h466b h467
    (h468 G M T L F φ)

end CFSG.Quasithin.MS93.S46
