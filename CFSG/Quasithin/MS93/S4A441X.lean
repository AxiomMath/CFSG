module

public import CFSG.Quasithin.MS93.S4A441Main
import CFSG.Quasithin.MS93.S4A441XA
import CFSG.Quasithin.MS93.S4A441XT
import CFSG.Quasithin.MS93.S4A44Nabla
import CFSG.Quasithin.MS93.S45Vtx

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S441C1Good : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      ∀ ψ : ↥(stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)) →* ↥(StatedSL 3 F),
        Function.Surjective ψ →
        IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2))
          (Uloc h.le L (geo (puAmalgam h.le) α α' 2)) ⊥ ψ false 1 →
        ∀ C : Subgroup (puAmalgam h.le).Universal,
          L441.IsSecD h.le L (geo (puAmalgam h.le) α α' 2) ψ true
            (conjCl (stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2))
              (ZM (puAmalgam h.le) α)) C →
          ∃ k ∈ stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2),
            ¬ ZM (puAmalgam h.le) (k • α) ≤ Qv (puAmalgam h.le) α' ∧
            Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 3) ⊓
                Subgroup.centralizer
                  (Usup (puAmalgam h.le) (k • α) (k • geo (puAmalgam h.le) α α' 1) :
                    Set (puAmalgam h.le).Universal) ≤
              Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)

namespace X441

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem false_of_dual (hgood : S441C1Good) (hmin : PUMin M T L) (hb : 4 < critDist 𝔛)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    {α α' : Vtx 𝔛} (hc : IsCritical 𝔛 α α')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • α) (g • geo 𝔛 α α' 2))
    {ψ : ↥(stab 𝔛 (geo 𝔛 α α' 2)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 (geo 𝔛 α α' 2)) (Uloc h.le L (geo 𝔛 α α' 2)) ⊥ ψ
      false 1) {C : Subgroup 𝔘}
    (hs : L441.IsSecD h.le L (geo 𝔛 α α' 2) ψ true
      (conjCl (stab 𝔛 (geo 𝔛 α α' 2)) (ZM 𝔛 α)) C) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hc.2.1
  have hα : IsMVtx 𝔛 α := hc.1
  obtain ⟨k, hk, hkZ, hkgood⟩ := hgood G M T L h F inferInstance inferInstance φ
    ⟨hmin, by omega, hφ⟩ hb α α' hc hfail ψ hψs hψ C hs
  have hγM : IsMVtx 𝔛 (geo 𝔛 α α' 2) := isMVtx_geo_two _ h20 hb0 hc
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : 𝔄 (geo 𝔛 α α' 1) (geo 𝔛 α α' 2) := adj_geo _ (i := 1) (by omega)
  have hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 2)⁆ ≤ Dloc h.le L (geo 𝔛 α α' 2) := by
    intro hle
    apply hfail 1
    rw [one_smul, one_smul]
    intro hn
    exact absurd hle hn
  have hex₁ := commutator_zm_qv_eq_usup h hb hφ hα hγM hαβ hβγ hH hψs hψ hs
  have hex₂ := usup_eq_of_isSecD h hb hφ hα hγM hαβ hβγ hH hψs hψ hs
  have hex : ∀ g : 𝔘, ⁅ZM 𝔛 (g • α), Qv 𝔛 (g • geo 𝔛 α α' 2)⁆ =
        Usup 𝔛 (g • α) (g • geo 𝔛 α α' 1) ∧
      Usup 𝔛 (g • α) (g • geo 𝔛 α α' 1) = Usup 𝔛 (g • geo 𝔛 α α' 2) (g • geo 𝔛 α α' 1) := by
    intro g
    rw [zm_smul, qv_smul, usup_smul, usup_smul, ← Subgroup.map_commutator, hex₁, hex₂]
    exact ⟨rfl, rfl⟩
  obtain ⟨hcμ, hg1, hg2, hg3⟩ := isCritical_smul_of_mem_stab _ (by omega) hc hk hkZ
  have hkγ : k • geo 𝔛 α α' 2 = geo 𝔛 α α' 2 := (mem_stab _).mp hk
  have hexk := (hex k).1
  have hμkβ : 𝔄 (k • α) (k • geo 𝔛 α α' 1) := (adj_smul _ k α _).mpr hαβ
  obtain ⟨μ, hμdef⟩ : ∃ μ, k • α = μ := ⟨_, rfl⟩
  rw [hμdef] at hcμ hg1 hg2 hg3 hkZ hkgood hμkβ hexk
  rw [hkγ] at hexk
  have hgoodμ : Qv 𝔛 (geo 𝔛 μ α' 3) ⊓
      Subgroup.centralizer (Usup 𝔛 μ (geo 𝔛 μ α' 1) : Set 𝔘) ≤ Qv 𝔛 (geo 𝔛 μ α' 2) := by
    rw [hg1, hg2, hg3]
    exact hkgood
  have hμM : IsMVtx 𝔛 μ := hcμ.1
  have hcμ' := ms22_iii _ h20 hb0 hC hcμ
  have hα'M : IsMVtx 𝔛 α' := hcμ'.1
  have hdμα' : (puAmalgam h.le).treeGraph.dist μ α' = critDist 𝔛 := hcμ.2.1
  have hdα'μ : (puAmalgam h.le).treeGraph.dist α' μ = critDist 𝔛 := hcμ'.2.1
  have hT := exists_isSecD_smul h hψs hψ hs k
  have hWk : (conjCl (stab 𝔛 (geo 𝔛 α α' 2)) (ZM 𝔛 α)).map (MulAut.conj k).toMonoidHom =
      conjCl (stab 𝔛 (geo 𝔛 α α' 2)) (ZM 𝔛 μ) := by
    rw [conjCl_map_conj, ← stab_smul, ← zm_smul, hkγ, hμdef]
  rw [hWk, hkγ] at hT
  obtain ⟨ψk, hψks, hψk, hsk⟩ := hT
  have hA7 := vcirc_le_of_good h hφ hb hV hα hγM hαβ hβγ hex hcμ hgoodμ hg2 hψks hψk hsk
  obtain ⟨g₀, hg₀γ, -⟩ := exists_smul_edge_of_isMVtx _ hγM hβγ.symm hμM
    (adj_geo_one_of_isCritical _ hb0 hcμ)
  have hA7μ : Vcirc h.le L μ ≤ conjCl (stab 𝔛 μ) (ZM 𝔛 (g₀ • μ)) := by
    have := Subgroup.map_mono (f := (MulAut.conj g₀).toMonoidHom) hA7
    rw [← vcirc_smul h g₀, conjCl_map_conj, ← stab_smul, ← zm_smul, hg₀γ] at this
    exact this
  have hD7 := not_vcirc_le_qv_of_isCritical h hfull (by omega) hV hcμ
  obtain ⟨l, hl, hlZ⟩ : ∃ l ∈ stab 𝔛 μ, ¬ ZM 𝔛 (l • g₀ • μ) ≤ Qv 𝔛 (geo 𝔛 α' μ 2) := by
    by_contra hall
    push Not at hall
    apply hD7
    refine hA7μ.trans (iSup₂_le fun l hl => ?_)
    rw [← zm_smul]
    exact hall l hl
  obtain ⟨g₁, hg₁def⟩ : ∃ g, l * g₀ * k = g := ⟨_, rfl⟩
  have hg₁γ : g₁ • geo 𝔛 α α' 2 = μ := by
    rw [← hg₁def, mul_smul, mul_smul, hkγ, hg₀γ, (mem_stab _).mp hl]
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, l • g₀ • μ = δ₀ := ⟨_, rfl⟩
  have hg₁α : g₁ • α = δ₀ := by
    rw [← hg₁def, mul_smul, mul_smul, hμdef, hδ₀]
  rw [hδ₀] at hlZ
  have hδ₀M : IsMVtx 𝔛 δ₀ := by
    rw [← hg₁α]
    exact (isMVtx_smul _ _ _).mpr hα
  have hdμδ₀ : (puAmalgam h.le).treeGraph.dist μ δ₀ = 2 := by
    rw [← hg₁γ, ← hg₁α, dist_smul, tdist_comm, dist_geo _ (by omega)]
  obtain ⟨hc₂, hgeo₂, -⟩ := isCritical_move _ (by omega) hcμ hδ₀M hdμδ₀ hlZ
  obtain ⟨α'', hα''⟩ : ∃ x, geo 𝔛 α' μ 2 = x := ⟨_, rfl⟩
  rw [hα''] at hc₂ hgeo₂
  have hgeo2 : geo 𝔛 δ₀ α'' 2 = μ := by
    have := hgeo₂ 0 (by omega)
    rwa [zero_add, geo_zero] at this
  have hfail₂ : ∀ g : 𝔘, ¬ Concl441 h.le L (g • δ₀) (g • μ) := by
    intro g
    have := hfail (g * g₁)
    rwa [mul_smul, mul_smul, hg₁α, hg₁γ] at this
  have hT₁ := exists_isSecD_smul h hψs hψ hs g₁
  have hW₁ : (conjCl (stab 𝔛 (geo 𝔛 α α' 2)) (ZM 𝔛 α)).map (MulAut.conj g₁).toMonoidHom =
      conjCl (stab 𝔛 μ) (ZM 𝔛 δ₀) := by
    rw [conjCl_map_conj, ← stab_smul, ← zm_smul, hg₁γ, hg₁α]
  rw [hW₁, hg₁γ] at hT₁
  obtain ⟨ψ₁, hψ₁s, hψ₁, hs₁⟩ := hT₁
  have key : ∀ γ' : Vtx 𝔛, geo 𝔛 δ₀ α'' 2 = γ' →
      (∀ g : 𝔘, ¬ Concl441 h.le L (g • δ₀) (g • γ')) →
      ∀ ψ' : ↥(stab 𝔛 γ') →* ↥(StatedSL 3 F), Function.Surjective ψ' →
        IsSumOfNaturalModulesVia (stab 𝔛 γ') (Uloc h.le L γ') ⊥ ψ' false 1 →
        ∀ C' : Subgroup 𝔘, L441.IsSecD h.le L γ' ψ' true (conjCl (stab 𝔛 γ') (ZM 𝔛 δ₀)) C' →
          ∃ k ∈ stab 𝔛 γ', ¬ ZM 𝔛 (k • δ₀) ≤ Qv 𝔛 α'' ∧
            Qv 𝔛 (geo 𝔛 δ₀ α'' 3) ⊓
                Subgroup.centralizer (Usup 𝔛 (k • δ₀) (k • geo 𝔛 δ₀ α'' 1) : Set 𝔘) ≤
              Qv 𝔛 γ' := by
    intro γ' hγ'
    subst hγ'
    exact hgood G M T L h F inferInstance inferInstance φ ⟨hmin, by omega, hφ⟩ hb δ₀ α'' hc₂
  obtain ⟨k₂, hk₂, hk₂Z, hk₂good⟩ := key μ hgeo2 hfail₂ ψ₁ hψ₁s hψ₁ _ hs₁
  obtain ⟨hcδ, h1', h2', h3'⟩ := isCritical_smul_of_mem_stab _ (by omega) hc₂
    (by rw [hgeo2]; exact hk₂) hk₂Z
  have hgoodδ : Qv 𝔛 (geo 𝔛 (k₂ • δ₀) α'' 3) ⊓
      Subgroup.centralizer (Usup 𝔛 (k₂ • δ₀) (geo 𝔛 (k₂ • δ₀) α'' 1) : Set 𝔘) ≤
        Qv 𝔛 (geo 𝔛 (k₂ • δ₀) α'' 2) := by
    rw [h1', h2', h3', hgeo2]
    exact hk₂good
  obtain ⟨hR3, g'₁, g'₂, hg'₁, hg'₂, -, -, hR3le⟩ :=
    card_inf_centralizer_of_good h hφ hb hV hα hγM hαβ hβγ hex hcδ hgoodδ
  rw [h2', hgeo2] at hR3le
  have hα''M : IsMVtx 𝔛 α'' := (ms22_iii _ h20 hb0 hC hc₂).1
  have hsym : geo 𝔛 α' μ 2 = geo 𝔛 μ α' (critDist 𝔛 - 2) := by
    have := geo_symm 𝔛 (u := μ) (w := α') (i := critDist 𝔛 - 2) (by omega)
    rwa [hdμα', show critDist 𝔛 - (critDist 𝔛 - 2) = 2 by omega] at this
  have hdα''γ : (puAmalgam h.le).treeGraph.dist α'' (geo 𝔛 μ α' 2) = critDist 𝔛 - 4 := by
    rw [← hα'', hsym, tdist_comm, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hVγ : Vv 𝔛 α'' ≤ Qv 𝔛 (geo 𝔛 α α' 2) :=
    S45.vi_le_qv _ (by rw [← hg2, hdα''γ]; omega)
  have hZV : ∀ g : 𝔘, g • geo 𝔛 α α' 2 = α'' → ZM 𝔛 (g • α) ≤ Vv 𝔛 α'' := by
    intro g hg
    have hdist : (puAmalgam h.le).treeGraph.dist α'' (g • α) ≤ 2 := by
      rw [← hg, dist_smul, tdist_comm, dist_geo _ (by omega)]
    have := zv_le_vv h (α := α'') (ρ := g • α) hdist
    rwa [zv_of_isMVtx _ ((isMVtx_smul _ g α).mpr hα)] at this
  have hRi : ∀ g : 𝔘, g • geo 𝔛 α α' 2 = α'' →
      ⁅ZM 𝔛 μ, ZM 𝔛 (g • α)⁆ ≤ Usup 𝔛 μ (k • geo 𝔛 α α' 1) := fun g hg =>
    (Subgroup.commutator_mono le_rfl ((hZV g hg).trans hVγ)).trans hexk.le
  have hRle := hR3le.trans (sup_le (hRi g'₁ hg'₁) (hRi g'₂ hg'₂))
  have hUcard := card_usup_eq_sq h hφ hC hb hμM hμkβ
  have hfinU : Finite ↥(Usup 𝔛 μ (k • geo 𝔛 α α' 1)) := Nat.finite_of_card_ne_zero (by
    rw [hUcard]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  have hReq := Subgroup.eq_of_le_of_card_ge hRle (hUcard.trans hR3.symm).le
  have hUle : Usup 𝔛 μ (k • geo 𝔛 α α' 1) ≤ Uloc h.le L α'' := by
    rw [← hReq]
    exact inf_le_left
  have hdα'α'' : (puAmalgam h.le).treeGraph.dist α' α'' ≤ 2 := by
    rw [← hα'', dist_geo _ (by omega)]
  have hZα''V : ZM 𝔛 α'' ≤ Vv 𝔛 α' := by
    have := zv_le_vv h (α := α') (ρ := α'') hdα'α''
    rwa [zv_of_isMVtx _ hα''M] at this
  have hVab := vv_comm_eq_bot h hb hα'M
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hVab
  have hVc : Vv 𝔛 α' ≤ Subgroup.centralizer (Usup 𝔛 μ (k • geo 𝔛 α α' 1) : Set 𝔘) :=
    hVab.trans (Subgroup.centralizer_le (hUle.trans ((uloc_le_zm h hfull hα''M).trans hZα''V)))
  have hVε : Vv 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 μ α' 3) := by
    refine S45.vi_le_qv _ ?_
    rw [tdist_comm, dist_geo_right _ (by omega), hdμα']
    omega
  rw [← hg1] at hVc
  exact hV α' μ hcμ' ((le_inf hVε hVc).trans hgoodμ)

end Vertex

end X441

theorem s441C1Dual_of (h43 : S43) (hgood : S441C1Good) : S441C1Dual := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail ψ hψs hψ C hs
  obtain ⟨hmin, hb2, hφ⟩ := hH
  exact X441.false_of_dual h hφ hgood hmin hb
    (h43 G M T L h hmin hb2 (isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩)) hc hfail hψs hψ hs

end CFSG.Quasithin.MS93.S4A
