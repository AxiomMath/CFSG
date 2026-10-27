module

public import CFSG.Quasithin.MS93.S4A432I
public import CFSG.LieType.Universal.SpecialLinear
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section SL3

variable {F : Type} [Field F]

theorem eq_top_of_normal_of_not_mem_center {N : Subgroup (SL3 F)} (hN : N.Normal) {g : SL3 F}
    (hg : g ∈ N) (hgc : g ∉ Subgroup.center (SL3 F)) : N = ⊤ := by
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  have hq' : CFSG.Open.IsQuasisimple (SL3 F) := ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  rcases @CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top _ _ hq' N hN with
    h1 | h1
  · exact absurd (h1 hg) hgc
  · exact h1

theorem not_mem_center_of_mulVec_eq {g : SL3 F} (hg : g ≠ 1) {w : Fin 3 → F} (hw : w ≠ 0)
    (hgw : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w) :
    g ∉ Subgroup.center (SL3 F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext hcon)
  have h1 := congrFun hgw i
  rw [← hr] at h1
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal] at h1
  have hr1 : r = 1 := by
    have : (r - 1) * w i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hi)
  apply hg
  apply Subtype.ext
  rw [← hr, hr1, map_one, coe_one_SL3]

theorem eq_top_of_stabilizer_le' {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {A : Subgroup (SL3 F)}
    (hA : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer P ≤ A)
    (hne : ¬ A ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer P) : A = ⊤ := by
  obtain ⟨g₀, hg₀⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq P
  rw [hP] at hg₀
  have hconj := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer_map_conj g₀
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagSpace 3 F 2)
  rw [hg₀] at hconj
  set A' := A.map (MulAut.conj g₀⁻¹ : SL3 F →* SL3 F) with hA'
  have hle : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagSpace 3 F 2) ≤ A' := by
    intro x hx
    refine ⟨g₀ * x * g₀⁻¹, hA ?_, ?_⟩
    · rw [← hconj]
      exact ⟨x, hx, rfl⟩
    · simp [mul_assoc]
  rcases CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_of_stabilizer_flagSpace_le A' hle with
    h1 | h1
  · exfalso
    apply hne
    intro a ha
    have : g₀⁻¹ * a * g₀ ∈ A' := ⟨a, ha, by simp⟩
    rw [h1] at this
    rw [← hconj]
    exact ⟨_, this, by simp [mul_assoc]⟩
  · rw [eq_top_iff]
    intro a _
    have : g₀⁻¹ * a * g₀ ∈ A' := by rw [h1]; exact Subgroup.mem_top _
    obtain ⟨b, hb, hbe⟩ := this
    have : b = a := by
      have := congrArg (fun y => g₀ * y * g₀⁻¹) hbe
      simpa [mul_assoc] using this
    rw [← this]
    exact hb

theorem mulVec_mem_of_mem_stabilizer' {P : Submodule F (Fin 3 → F)} {s : SL3 F}
    (hs : s ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer P) {v : Fin 3 → F}
    (hv : v ∈ P) : ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ P := by
  have hs' : P.map (Matrix.mulVecLin ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = P := hs
  rw [← hs']
  exact ⟨v, hv, rfl⟩

theorem le_of_finrank_eq_one' {r H : Submodule F (Fin 3 → F)} (hr : Module.finrank F r = 1)
    {x : Fin 3 → F} (hx : x ∈ r) (hx0 : x ≠ 0) (hxH : x ∈ H) : r ≤ H := by
  have hspan : Submodule.span F {x} = r :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)
      (by rw [finrank_span_singleton hx0, hr])
  rw [← hspan]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxH

end SL3

section Conj

variable {Γ : Type*} [Group Γ]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_le {H : Subgroup Γ} {g : Γ}
    (h1 : H.map (MulAut.conj g).toMonoidHom ≤ H) (h2 : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ H) :
    g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 ⟨x, hx, rfl⟩
  · intro hx
    have := h2 ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

@[expose] def centMod (K W Z : Subgroup Γ) (hKZ : K ≤ Subgroup.normalizer (Z : Set Γ)) :
    Subgroup Γ where
  carrier := {g | g ∈ K ∧ ∀ w ∈ W, ⁅w, g⁆ ∈ Z}
  one_mem' := ⟨K.one_mem, fun w _ => by rw [commutatorElement_one_right]; exact Z.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun w hw => by
    have e : ⁅w, g * g'⁆ = ⁅w, g⁆ * (g * ⁅w, g'⁆ * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hg.2 w hw) ((Subgroup.mem_normalizer_iff.mp (hKZ hg.1) _).mp (hg'.2 w hw))⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun w hw => by
    have e : ⁅w, g⁻¹⁆ = g⁻¹ * ⁅w, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ (K.inv_mem hg.1)) _).mp (Z.inv_mem (hg.2 w hw))⟩

end Conj

section Wnu

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] def Snu (α ν₁ : Vtx (puAmalgam hTM)) : Set (Vtx (puAmalgam hTM)) :=
  {μ | ∃ ν, (puAmalgam hTM).treeGraph.Adj α ν ∧ (puAmalgam hTM).treeGraph.Adj ν μ ∧
    μ ∈ nablaSet hTM L α ∧ Usup (puAmalgam hTM) α ν = Usup (puAmalgam hTM) α ν₁}

@[expose] noncomputable def Wnu (α ν₁ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  Vv (puAmalgam hTM) α ⊔ ⨆ μ ∈ Snu hTM L α ν₁, Vv (puAmalgam hTM) μ

theorem vv_le_wnu (α ν₁ : Vtx (puAmalgam hTM)) : Vv (puAmalgam hTM) α ≤ Wnu hTM L α ν₁ :=
  le_sup_left

theorem vv_le_wnu_of_mem {α ν₁ μ : Vtx (puAmalgam hTM)} (hμ : μ ∈ Snu hTM L α ν₁) :
    Vv (puAmalgam hTM) μ ≤ Wnu hTM L α ν₁ :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun μ (_ : μ ∈ Snu hTM L α ν₁) =>
    Vv (puAmalgam hTM) μ) μ hμ le_rfl)

end Wnu

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

omit [Fintype F] c in
theorem critR0_le_vv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : critR0 𝔛 α α' ≤ Vv 𝔛 α :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs.1).trans (stab_le_normalizer_vv h α))

theorem not_zm_le_qv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : ¬ ZM 𝔛 α' ≤ Qv 𝔛 α := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  exact (isCritical_of_not_le h c.hyp.2.2 (hs.1.isMVtx_right _ h.hyp20) hs.1.1 hd'
    hs.1.2.2).2.2

theorem mem_nablaSet_geo_two' {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    α' ∈ nablaSet h.le L (geo 𝔛 α' α 2) := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  exact mem_nablaSet_geo_two h c.full c.cent c.b2
    (isCritical_of_not_le h c.hyp.2.2 (hs.1.isMVtx_right _ h.hyp20) hs.1.1 hd' hs.1.2.2)

theorem critR0_eq {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' = Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ∧
      ⁅ZM 𝔛 α', Qv 𝔛 (geo 𝔛 α' α 2)⁆ = critR0 𝔛 α α' := by
  have hb := c.b4
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  have hγ : IsMVtx 𝔛 (geo 𝔛 α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hα'ρ : 𝔄 α' (geo 𝔛 α' α 1) := adj_geo_one _ (by omega)
  have hργ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  obtain ⟨h3a, h3b⟩ := c.three hγ hργ.symm hα'ρ.symm (c.mem_nablaSet_geo_two' hs)
  have h0 := (c.s431A G M T L h F inferInstance inferInstance φ c.hyp α α' hs).1
  refine ⟨h0.trans h3b, ?_⟩
  rw [h3a, h0, h3b]

theorem uloc_le_usup_sup {γ ρ τ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγρ : 𝔄 γ ρ) (hγτ : 𝔄 γ τ)
    (hne : Usup 𝔛 γ ρ ≠ Usup 𝔛 γ τ) : Uloc h.le L γ ≤ Usup 𝔛 γ ρ ⊔ Usup 𝔛 γ τ := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.hyp.2.2 hγ
  have hTρ : Qv 𝔛 ρ ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγρ.symm
  have hTτ : Qv 𝔛 τ ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγτ.symm
  have hfin : ∀ {x : Vtx 𝔛}, 𝔄 γ x → Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 x))) = 2 := by
    intro x hγx
    have := (c.edge hγ hγx).2.1
    rw [usup_eq_commutator_uloc h c.full hγ hγx,
      card_commutator_eq hψ (qv_le_stab_of_adj _ hγx.symm),
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hmem : ∀ {x : Vtx 𝔛} (hγx : 𝔄 γ x) (u : ↥(Uloc h.le L γ)),
      (u : 𝔘) ∈ Usup 𝔛 γ x ↔ natVec hψ u ∈ commN (natImage ψ (Qv 𝔛 x)) := by
    intro x hγx u
    rw [usup_eq_commutator_uloc h c.full hγ hγx]
    exact mem_commutator_iff_natVec hψ (qv_le_stab_of_adj _ hγx.symm) u
  have hneP : commN (natImage ψ (Qv 𝔛 ρ)) ≠ commN (natImage ψ (Qv 𝔛 τ)) := by
    intro heq
    apply hne
    have hUρ := c.usup_le_uloc hγ hγρ
    have hUτ := c.usup_le_uloc hγ hγτ
    ext u
    constructor
    · intro hu
      have := (hmem hγρ ⟨u, hUρ hu⟩).mp hu
      rw [heq] at this
      exact (hmem hγτ ⟨u, hUρ hu⟩).mpr this
    · intro hu
      have := (hmem hγτ ⟨u, hUτ hu⟩).mp hu
      rw [← heq] at this
      exact (hmem hγρ ⟨u, hUτ hu⟩).mpr this
  have htop : commN (natImage ψ (Qv 𝔛 ρ)) ⊔ commN (natImage ψ (Qv 𝔛 τ)) = ⊤ := by
    have h1 := finrank_inf_planes_eq_one (hfin hγρ) (hfin hγτ) hneP
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commN (natImage ψ (Qv 𝔛 ρ)))
      (commN (natImage ψ (Qv 𝔛 τ)))
    rw [hfin hγρ, hfin hγτ, h1] at h2
    exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
  intro u hu
  have hv : natVec hψ ⟨u, hu⟩ ∈ commN (natImage ψ (Qv 𝔛 ρ)) ⊔ commN (natImage ψ (Qv 𝔛 τ)) :=
    htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  obtain ⟨ua, rfl⟩ := natVec_surjective hψ a
  obtain ⟨ub, rfl⟩ := natVec_surjective hψ b
  have he : (⟨u, hu⟩ : ↥(Uloc h.le L γ)) = ua * ub := by
    apply natVec_injective hψ
    rw [natVec_mul, hab]
  have hu' : u = (ua : 𝔘) * ub := congrArg Subtype.val he
  rw [hu']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hmem hγρ ua).mpr ha))
    (Subgroup.mem_sup_right ((hmem hγτ ub).mpr hb))

theorem le_qv_of_le_qv_three {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    {X : Subgroup 𝔘} (hXT : X ≤ Qv 𝔛 (geo 𝔛 α' α 3))
    (hXR : X ≤ Subgroup.centralizer (critR0 𝔛 α α' : Set 𝔘)) : X ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
  have hb := c.b4
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  have hγ : IsMVtx 𝔛 (geo 𝔛 α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hργ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hγτ : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := adj_geo _ (i := 2) (by omega)
  have hXs : X ≤ stab 𝔛 (geo 𝔛 α' α 2) := hXT.trans (qv_le_stab_of_adj _ hγτ.symm)
  have hcτ : X ≤ Subgroup.centralizer (Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) : Set 𝔘) :=
    Subgroup.le_centralizer_iff.mpr (((c.edge hγ hγτ).1.trans (zh_le_centralizer _ _)).trans
      (Subgroup.centralizer_le hXT))
  have hcρ : X ≤ Subgroup.centralizer (Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) : Set 𝔘) := by
    rw [← (c.critR0_eq hs).1]
    exact hXR
  have hcU : X ≤ Subgroup.centralizer (Uloc h.le L (geo 𝔛 α' α 2) : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine (c.uloc_le_usup_sup hγ hργ.symm hγτ h4).trans (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.mp hcρ
    · exact Subgroup.le_centralizer_iff.mp hcτ
  intro x hx
  exact S46.stab_inf_centralizer_uloc_le_qv h c.hyp.2.2 hγ ⟨hXs hx, hcU hx⟩

theorem wnu_le_qv (hb6 : 6 < critDist 𝔛) {α α' ν₁ : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) : Wnu h.le L α ν₁ ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
  have hb := hb6
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  refine sup_le hs.2 (iSup₂_le fun μ hμ => ?_)
  obtain ⟨ν, hαν, hνμ, hμn, hUeq⟩ := hμ
  have hR' : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν := by rw [hUeq]; exact hR
  have h6 := vv_le_qv_of_dual h c.full c.hyp c.cent c.s42 c.s431A c.s431B c.b4 c.star c.kind c.ch
    hb6 hs hαν hνμ hμn hR'
  have h4M : IsMVtx 𝔛 (geo 𝔛 α' α 4) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_iff_two_dvd.mpr (by norm_num), fun _ => hα'⟩
  have h43 : Qv 𝔛 (geo 𝔛 α' α 4) ≤ Qv 𝔛 (geo 𝔛 α' α 3) :=
    qv_le_qv _ h.hyp20 h4M (adj_geo _ (i := 3) (by omega)).symm
  refine c.le_qv_of_le_qv_three hs h4 (h6.trans h43) ?_
  have hdμ : (puAmalgam h.le).treeGraph.dist μ α = 2 := by rw [tdist_comm]; exact hμn.1
  have hcomm : Vv 𝔛 μ ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) :=
    S45.vi_le_centralizer_vi _ h.hyp20 h.critDist_pos (by omega)
  exact hcomm.trans (Subgroup.centralizer_le (critR0_le_vv (h := h) hs))

omit [Fintype F] c in
theorem qv_le_normalizer_usup {α ν : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hαν : 𝔄 α ν) :
    Qv 𝔛 α ≤ Subgroup.normalizer (Usup 𝔛 α ν : Set 𝔘) := by
  rw [Usup, zv_of_isMVtx _ hα]
  exact le_normalizer_commutator ((qv_le_stab _ α).trans (stab_le_normalizer_zm _ α))
    ((qv_le_qv _ h.hyp20 hα hαν).trans Subgroup.le_normalizer)

omit [Fintype F] c in
theorem map_wnu_le {α ν₁ : Vtx 𝔛} {g : 𝔘} (hg : g ∈ stab 𝔛 α)
    (hgU : (Usup 𝔛 α ν₁).map (MulAut.conj g).toMonoidHom = Usup 𝔛 α ν₁) :
    (Wnu h.le L α ν₁).map (MulAut.conj g).toMonoidHom ≤ Wnu h.le L α ν₁ := by
  have hgα : g • α = α := (mem_stab _).mp hg
  rw [Wnu, Subgroup.map_sup, Subgroup.map_iSup]
  refine sup_le ?_ (iSup_le fun μ => ?_)
  · have hV : (Vv 𝔛 α).map (MulAut.conj g).toMonoidHom = Vv 𝔛 (g • α) := (vi_smul _ g α 2).symm
    rw [hV, hgα]
    exact le_sup_left
  · rw [Subgroup.map_iSup]
    refine iSup_le fun hμ => ?_
    obtain ⟨ν, hαν, hνμ, hμn, hUeq⟩ := hμ
    have hV : (Vv 𝔛 μ).map (MulAut.conj g).toMonoidHom = Vv 𝔛 (g • μ) := (vi_smul _ g μ 2).symm
    rw [hV]
    refine vv_le_wnu_of_mem h.le L ⟨g • ν, ?_, ?_, ?_, ?_⟩
    · have := (adj_smul _ g α ν).mpr hαν
      rwa [hgα] at this
    · exact (adj_smul _ g ν μ).mpr hνμ
    · have := (mem_nablaSet_smul h g α μ).mpr hμn
      rwa [hgα] at this
    · have := usup_smul _ g α ν
      rw [hgα] at this
      rw [this, hUeq, hgU]

theorem mem_normalizer_usup_of_stab {α ν : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hαν : 𝔄 α ν)
    {ψ : ↥(stab 𝔛 α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 α) (Uloc h.le L α) ⊥ ψ false 1) {g : ↥(stab 𝔛 α)}
    (hg : toSL3 ψ g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
      (commN (natImage ψ (Qv 𝔛 ν)))) :
    (g : 𝔘) ∈ Subgroup.normalizer (Usup 𝔛 α ν : Set 𝔘) := by
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαν.symm
  have hUU := c.usup_le_uloc hα hαν
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  have key : ∀ k : ↥(stab 𝔛 α),
      toSL3 ψ k ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
        (commN (natImage ψ (Qv 𝔛 ν))) →
      (Usup 𝔛 α ν).map (MulAut.conj (k : 𝔘)).toMonoidHom ≤ Usup 𝔛 α ν := by
    rintro k hk _ ⟨u, hu, rfl⟩
    have hu' := hUU hu
    have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Uloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (hUn k.2) u).mp hu'
    rw [usup_eq_commutator_uloc h c.full hα hαν] at hu ⊢
    have h1 := (mem_commutator_iff_natVec hψ hTs ⟨u, hu'⟩).mp hu
    show (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ ⁅Uloc h.le L α, Qv 𝔛 ν⁆
    refine (mem_commutator_iff_natVec hψ hTs ⟨_, hku⟩).mpr ?_
    rw [natVec_conj hψ k ⟨u, hu'⟩ ⟨_, hku⟩ rfl]
    exact mulVec_mem_of_mem_stabilizer' hk h1
  refine mem_normalizer_of_map_le (key g hg) ?_
  have := key g⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hg)
  simpa using this

theorem stab_le_normalizer_wnu (hb6 : 6 < critDist 𝔛) {α α' ν₁ : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) :
    stab 𝔛 α ≤ Subgroup.normalizer (Wnu h.le L α ν₁ : Set 𝔘) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hα := hs.1.1
  set W := Wnu h.le L α ν₁ with hWdef
  set K := stab 𝔛 α ⊓ Subgroup.normalizer (W : Set 𝔘) with hKdef
  have hKa : ∀ g ∈ stab 𝔛 α, g ∈ Subgroup.normalizer (Usup 𝔛 α ν₁ : Set 𝔘) → g ∈ K := by
    intro g hg hgU
    exact ⟨hg, mem_normalizer_of_map_le (map_wnu_le (h := h) hg (map_conj_eq_of_mem_normalizer hgU))
      (map_wnu_le (h := h) (inv_mem hg) (map_conj_eq_of_mem_normalizer (inv_mem hgU)))⟩
  have hWQ := c.wnu_le_qv hb6 hs h4 hR
  have hZs : ZM 𝔛 α' ≤ stab 𝔛 α := zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs.1
  have hzW : ∀ z ∈ ZM 𝔛 α', W.map (MulAut.conj z).toMonoidHom ≤ W := by
    rintro z hz _ ⟨x, hx, rfl⟩
    have hc : ⁅z, x⁆ ∈ critR0 𝔛 α α' := by
      rw [← (c.critR0_eq hs).2]
      exact Subgroup.commutator_mem_commutator hz (hWQ hx)
    have e : (MulAut.conj z).toMonoidHom x = ⁅z, x⁆ * x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (vv_le_wnu h.le L α ν₁ (critR0_le_vv (h := h) hs hc)) hx
  have hZK : ZM 𝔛 α' ≤ K := fun z hz =>
    ⟨hZs hz, mem_normalizer_of_map_le (hzW z hz) (hzW z⁻¹ (inv_mem hz))⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.hyp.2.2 hα
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZβ : ZM 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α α' 1) := zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hs.1
  have hTs : Qv 𝔛 ν₁ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαν₁.symm
  have hfin : ∀ {x : Vtx 𝔛}, 𝔄 α x → Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 x))) = 2 := by
    intro x hαx
    have := (c.edge hα hαx).2.1
    rw [usup_eq_commutator_uloc h c.full hα hαx,
      card_commutator_eq hψ (qv_le_stab_of_adj _ hαx.symm),
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hr1 : Module.finrank F ↥(commN (natImage ψ (ZM 𝔛 α'))) = 1 := by
    have hcR := (c.s431A G M T L h F inferInstance inferInstance φ c.hyp α α' hs).2.2.1
    rw [critR, commutator_zm_eq_uloc h c.full hα hZs, card_commutator_eq hψ hZs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at hcR
    exact Nat.pow_right_injective hq (hcR.trans (pow_one _).symm)
  have hrβ : commN (natImage ψ (ZM 𝔛 α')) ≤ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) :=
    commN_mono (natImage_mono hZβ)
  have hrP : ¬ commN (natImage ψ (ZM 𝔛 α')) ≤ commN (natImage ψ (Qv 𝔛 ν₁)) := by
    intro hle
    apply hR
    rw [critR, commutator_zm_eq_uloc h c.full hα hZs, usup_eq_commutator_uloc h c.full hα hαν₁]
    intro u hu
    have hu' : u ∈ Uloc h.le L α := Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α)) hu
    exact (mem_commutator_iff_natVec hψ hTs ⟨u, hu'⟩).mpr
      (hle ((mem_commutator_iff_natVec hψ hZs ⟨u, hu'⟩).mp hu))
  have hne : commN (natImage ψ (Qv 𝔛 ν₁)) ≠ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) :=
    fun he => hrP (he ▸ hrβ)
  obtain ⟨w, hwP, hwβ⟩ : ∃ w ∈ commN (natImage ψ (Qv 𝔛 ν₁)),
      w ∉ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) := by
    by_contra hcon
    push Not at hcon
    exact hne (Submodule.eq_of_le_of_finrank_eq hcon (by rw [hfin hαν₁, hfin hαβ]))
  have hfix : fixN (natImage ψ (ZM 𝔛 α')) = commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) :=
    fixN_eq_commN_of_le_qv h c.full c.hyp.2.2 hα hαβ (c.edge hα hαβ).1 (c.edge hα hαβ).2.1 hψ hZβ
      (c.not_zm_le_qv hs)
  obtain ⟨g, hg, hgw⟩ : ∃ g ∈ natImage ψ (ZM 𝔛 α'),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hwβ (hfix ▸ mem_fixN.mpr hcon)
  obtain ⟨z, hzZ, rfl⟩ := mem_natImage.mp hg
  have hzst : toSL3 ψ z ∉ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
      (commN (natImage ψ (Qv 𝔛 ν₁))) := by
    intro hst
    have h3 := Submodule.sub_mem _ (mulVec_mem_of_mem_stabilizer' hst hwP) hwP
    exact hrP (le_of_finrank_eq_one' hr1 (sub_mem_commN hg w) (sub_ne_zero.mpr hgw) h3)
  have hA : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
      (commN (natImage ψ (Qv 𝔛 ν₁))) ≤ natImage ψ K := by
    intro s hs'
    obtain ⟨g, rfl⟩ := toSL3_surjective hψs s
    exact mem_natImage.mpr ⟨g, hKa g g.2 (c.mem_normalizer_usup_of_stab hα hαν₁ hψ hs'), rfl⟩
  have hnot : ¬ natImage ψ K ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
      (commN (natImage ψ (Qv 𝔛 ν₁))) :=
    fun hle => hzst (hle (mem_natImage.mpr ⟨z, hZK hzZ, rfl⟩))
  have htop := eq_top_of_stabilizer_le' (hfin hαν₁) hA hnot
  intro g hg
  have hmem : toSL3 ψ ⟨g, hg⟩ ∈ natImage ψ K := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hkK, hke⟩ := mem_natImage.mp hmem
  have h1 : toSL3 ψ (k⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hke, inv_mul_cancel]
  have h2 := (S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hψ _).mp h1
  have h3 : ((k⁻¹ * ⟨g, hg⟩ : ↥(stab 𝔛 α)) : 𝔘) ∈ K :=
    hKa _ (k⁻¹ * ⟨g, hg⟩).2 (qv_le_normalizer_usup (h := h) hα hαν₁ h2)
  have h4' := K.mul_mem hkK h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h4'
  exact h4'.2

theorem exists_inv_mul_mem_qv (hb6 : 6 < critDist 𝔛) {α α' ν₁ : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) {g : 𝔘} (hg : g ∈ stab 𝔛 α) :
    ∃ n ∈ stab 𝔛 α, (∀ x ∈ Wnu h.le L α ν₁, ⁅x, n⁆ ∈ Vv 𝔛 α) ∧ n⁻¹ * g ∈ Qv 𝔛 α := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hα := hs.1.1
  set W := Wnu h.le L α ν₁ with hWdef
  set N := centMod (stab 𝔛 α) W (Vv 𝔛 α) (stab_le_normalizer_vv h α) with hNdef
  have hWn := c.stab_le_normalizer_wnu hb6 hs h4 hαν₁ hR
  have hWQ := c.wnu_le_qv hb6 hs h4 hR
  have hZs : ZM 𝔛 α' ≤ stab 𝔛 α := zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs.1
  have hNn : ∀ k ∈ stab 𝔛 α, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    rintro k hk n ⟨hn, hnW⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hn) (Subgroup.inv_mem _ hk), fun x hx => ?_⟩
    have hx' : k⁻¹ * x * k⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWn (Subgroup.inv_mem _ hk)) x).mp hx
    have e : ⁅x, k * n * k⁻¹⁆ = k * ⁅k⁻¹ * x * k⁻¹⁻¹, n⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α hk) _).mp (hnW _ hx')
  have hZN : ZM 𝔛 α' ≤ N := fun z hz => ⟨hZs hz, fun x hx => by
    have hc : ⁅z, x⁆ ∈ critR0 𝔛 α α' := by
      rw [← (c.critR0_eq hs).2]
      exact Subgroup.commutator_mem_commutator hz (hWQ hx)
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (critR0_le_vv (h := h) hs hc)⟩
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.hyp.2.2 hα
  have hNimg : (natImage ψ N).Normal := by
    constructor
    intro t ht s
    obtain ⟨n, hnN, rfl⟩ := mem_natImage.mp ht
    obtain ⟨k, rfl⟩ := toSL3_surjective hψs s
    exact mem_natImage.mpr ⟨k * n * k⁻¹, hNn k k.2 n hnN, by simp [map_mul, map_inv]⟩
  obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp (c.not_zm_le_qv hs)
  have hzs : z ∈ stab 𝔛 α := hZs hzZ
  have hz1 : toSL3 ψ ⟨z, hzs⟩ ≠ 1 := fun h1 =>
    hzQ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hψ _).mp h1)
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZβ : ZM 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α α' 1) := zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hs.1
  have hfix : fixN (natImage ψ (ZM 𝔛 α')) = commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) :=
    fixN_eq_commN_of_le_qv h c.full c.hyp.2.2 hα hαβ (c.edge hα hαβ).1 (c.edge hα hαβ).2.1 hψ hZβ
      (c.not_zm_le_qv hs)
  obtain ⟨w, hwβ, hw0⟩ : ∃ w ∈ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))), w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) = ⊥ :=
      eq_bot_iff.mpr fun v hv => (Submodule.mem_bot F).mpr (hcon v hv)
    have := (c.edge hα hαβ).2.1
    rw [usup_eq_commutator_uloc h c.full hα hαβ,
      card_commutator_eq hψ (qv_le_stab_of_adj _ hαβ.symm), hbot] at this
    have h1 : Nat.card ↥(⊥ : Submodule F (Fin 3 → F)) = 1 := by simp
    rw [h1] at this
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hzw : ((toSL3 ψ ⟨z, hzs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
    mem_fixN.mp (hfix ▸ hwβ) _ (mem_natImage.mpr ⟨⟨z, hzs⟩, hzZ, rfl⟩)
  have htop := eq_top_of_normal_of_not_mem_center hNimg
    (mem_natImage.mpr ⟨⟨z, hzs⟩, hZN hzZ, rfl⟩) (not_mem_center_of_mulVec_eq hz1 hw0 hzw)
  obtain ⟨n, hnN, hne⟩ := mem_natImage.mp (htop ▸ Subgroup.mem_top (toSL3 ψ ⟨g, hg⟩))
  refine ⟨n, hnN.1, hnN.2, ?_⟩
  have h1 : toSL3 ψ (n⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hne, inv_mul_cancel]
  exact (S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hψ _).mp h1

theorem stab_le_normalizer_pv_sup (hb6 : 6 < critDist 𝔛) {α α' ν₁ μ : Vtx 𝔛}
    (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) (hμ : μ ∈ Snu h.le L α ν₁) :
    stab 𝔛 α ≤ Subgroup.normalizer ((Pv 𝔛 μ ⊔ Vv 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
  have hα := hs.1.1
  obtain ⟨ν, hαν, hνμ, hμn, -⟩ := id hμ
  have hμM := (zm_le_vv_of_mem_nablaSet h hα hμn).1
  have hQμ : Qv 𝔛 α ≤ stab 𝔛 μ := (qv_le_qv _ h.hyp20 hα hαν).trans (qv_le_stab_of_adj _ hνμ)
  set A := Pv 𝔛 μ ⊔ Vv 𝔛 α with hA
  have hPW : Pv 𝔛 μ ≤ Wnu h.le L α ν₁ := (pv_le_vv h hμM).trans (vv_le_wnu_of_mem h.le L hμ)
  have hconjA : ∀ k ∈ Qv 𝔛 α, ∀ x ∈ A, k * x * k⁻¹ ∈ A := by
    intro k hk x hx
    have hkA : A.map (MulAut.conj k).toMonoidHom ≤ A := by
      rw [hA, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_pv _ μ (hQμ hk)) y).mp hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α (qv_le_stab _ α hk)) y).mp
          hy
    exact hkA ⟨x, hx, rfl⟩
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  obtain ⟨n, hn, hnW, hng⟩ := c.exists_inv_mul_mem_qv hb6 hs h4 hαν₁ hR hg
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := by
    have hle : A.map (MulAut.conj n).toMonoidHom ≤ A := by
      rw [hA, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        have e : (MulAut.conj n).toMonoidHom x = x * ⁅x⁻¹, n⁆ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (hnW _ (hPW (Subgroup.inv_mem _ hx))))
      · rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv h α hn) x).mp hx)
    exact fun x hx => hle ⟨x, hx, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hconjA _ hng x hx
  have h2 := hnA _ h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  convert h2 using 1
  group

end Ctx

end CFSG.Quasithin.MS93.S4A.D432
