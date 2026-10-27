module

public import CFSG.Quasithin.MS93.S4A441EB5
public import CFSG.Quasithin.MS93.S4A441E
import CFSG.Quasithin.MS93.S4A441XG
import CFSG.Quasithin.MS93.S4A441NoSec

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace X441

section Grp

variable {Γ : Type*} [Group Γ]

theorem map_conj_le_centralizer_map {H X : Subgroup Γ} (hX : X ≤ Subgroup.centralizer (H : Set Γ))
    (g : Γ) : X.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_mul, Subgroup.mem_centralizer_iff.mp (hX hx) k hk, map_mul]

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem uloc_inf_centralizer_ne_bot (hφ : IsSL3FullVia M T L φ) {α β : Vtx 𝔛} (hα : IsMVtx 𝔛 α)
    (hαβ : 𝔄 α β) : Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) ≠ ⊥ := by
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hTs : Qv 𝔛 β ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαβ.symm
  have hβH : ¬ IsMVtx 𝔛 β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hP : IsPGroup 2 ↥(natImage ψ (Qv 𝔛 β)) :=
    ((isPGroup_qv _ h.hyp20 hβH).of_equiv (Subgroup.subgroupOfEquivOfLe hTs).symm).map (toSL3 ψ)
  have hne : fixN (natImage ψ (Qv 𝔛 β)) ≠ ⊥ := by
    rw [Ne, ← Submodule.finrank_eq_zero]
    have := S46.finrank_fixN_pos hP
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, rfl⟩ := natVec_surjective hψ v
  intro hbot
  apply hv0
  have hu : (u : 𝔘) ∈ Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) :=
    ⟨u.2, (mem_centralizer_iff_natVec hψ hTs u).mpr hv⟩
  rw [hbot, Subgroup.mem_bot] at hu
  rw [show u = 1 from Subtype.ext hu, natVec_one]

theorem false_of_le_dloc (hG6 : S441EndB6) (hH : Hyp40 h φ) (hb : 4 < critDist 𝔛)
    (hdual : S441C1Dual)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    {α α' : Vtx 𝔛} (hc : IsCritical 𝔛 α α')
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • α) (g • geo 𝔛 α α' 2))
    (hc1 : ∀ g : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g • geo 𝔛 α α' 2)
      (conjCl (stab 𝔛 (g • geo 𝔛 α α' 2)) (ZM 𝔛 (g • α))) (ZM 𝔛 (g • geo 𝔛 α α' 2)))
    (hB : ¬ ⁅Vv 𝔛 α, Qv 𝔛 α⁆ ≤ Bloc h.le L α) {μ lam : Vtx 𝔛}
    (hconj : ∃ g : 𝔘, g • μ = α ∧ g • α = geo 𝔛 α α' 2)
    (hcμ : IsCritical 𝔛 μ (geo 𝔛 α' α 2)) (hgeoμ : geo 𝔛 μ (geo 𝔛 α' α 2) 2 = α)
    (h2 : ⁅⁅ZM 𝔛 μ, Qv 𝔛 α⁆, ZM 𝔛 α'⁆ ≠ ⊥) (hlam : IsMVtx 𝔛 lam)
    (hdl : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) lam = 2)
    (hN : ¬ ZM 𝔛 μ ≤ Subgroup.normalizer
      ((⁅ZM 𝔛 lam, Qv 𝔛 (geo 𝔛 α' α 2)⁆ ⊔ ZM 𝔛 (geo 𝔛 α' α 2) : Subgroup 𝔘) : Set 𝔘))
    (hcl : IsCritical 𝔛 lam α) (hgeol : geo 𝔛 lam α 2 = geo 𝔛 α' α 2)
    (h3l : ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 α' α 2)⁆ ≤ ZM 𝔛 α)
    (hX : Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 μ α 1) : Set 𝔘) ≤
      Dloc h.le L α) : False := by
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx 𝔛 α := hc.1
  have hμ : IsMVtx 𝔛 μ := hcμ.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hcl' := ms22_iii _ h20 hb0 hC hcl
  have h3l' : ⁅ZM 𝔛 lam, Vv 𝔛 α ⊓ Qv 𝔛 (geo 𝔛 lam α 2)⁆ ≤ ZM 𝔛 α := by
    rw [hgeol]
    exact h3l
  have hdα'ν : (puAmalgam h.le).treeGraph.dist α' (geo 𝔛 α' α 2) = 2 :=
    dist_geo _ (by rw [hc'.2.1]; omega)
  set ν := geo 𝔛 α' α 2 with hνdef
  have hdαν : (puAmalgam h.le).treeGraph.dist α ν = critDist 𝔛 - 2 := by
    rw [hνdef, tdist_comm, dist_geo_right _ (by rw [hc'.2.1]; omega), hc'.2.1]
  have hdνα : (puAmalgam h.le).treeGraph.dist ν α = critDist 𝔛 - 2 := by
    rw [tdist_comm]
    exact hdαν
  have hgen := stab_eq_conjCl_sup_qv h hfull hcl
  have hαβ : 𝔄 α (geo 𝔛 α lam 1) := adj_geo_one_of_isCritical _ hb0 hcl'
  have hZlβ : ZM 𝔛 lam ≤ Qv 𝔛 (geo 𝔛 α lam 1) := zm_le_qv_geo_one _ h20 hb0 hcl'
  obtain ⟨β, hβdef⟩ : ∃ x : Vtx 𝔛, x = geo 𝔛 α lam 1 := ⟨_, rfl⟩
  rw [← hβdef] at hgen hαβ hZlβ
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 2 := by
    rw [← hgeoμ, dist_geo _ (by rw [hcμ.2.1]; omega)]
  have hμσ : 𝔄 μ (geo 𝔛 μ α 1) := adj_geo_one _ (by omega)
  have hσα : 𝔄 (geo 𝔛 μ α 1) α := by
    have := adj_geo _ (u := μ) (w := α) (i := 1) (by omega)
    rwa [show geo 𝔛 μ α (1 + 1) = α from geo_of_le _ (by omega)] at this
  obtain ⟨t, htμ, htσ⟩ := exists_smul_edge_of_isMVtx _ hμ hμσ hα hαβ
  have hδ₀β : 𝔄 (t • α) β := by
    rw [← htσ]
    exact (adj_smul _ t α _).mpr hσα.symm
  have hdαδ₀ : (puAmalgam h.le).treeGraph.dist α (t • α) = 2 := by
    have := dist_smul _ t μ α
    rwa [htμ, hdμα] at this
  have hctν : IsCritical 𝔛 α (t • ν) := by
    rw [← htμ]
    exact (isCritical_smul _ t μ ν).mpr hcμ
  have hgeotν : geo 𝔛 α (t • ν) 2 = t • α := by
    have := geo_smul _ t μ ν 2
    rwa [htμ, hgeoμ] at this
  have hX₁Z : Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) ≤ ZH 𝔛 β := by
    rw [← zh_inf_uloc h hfull hα hαβ]
    exact inf_le_left
  have hX₁Q : Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) ≤ Qv 𝔛 α :=
    inf_le_left.trans ((uloc_le_zm h hfull hα).trans (zm_le_qv_self _ hα hb0))
  have hX₁₁ : Qv 𝔛 β ≤ Subgroup.normalizer
      ((Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) := by
    rw [← zh_inf_uloc h hfull hα hαβ]
    exact (le_inf ((qv_le_stab _ β).trans (stab_le_normalizer_zh _ β))
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_uloc h α))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hX₁₂ : ¬ stab 𝔛 α ≤ Subgroup.normalizer
      ((Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 β : Set 𝔘) : Subgroup 𝔘) : Set 𝔘) := by
    intro hn
    apply uloc_inf_centralizer_ne_bot h hφ hα hαβ
    rw [eq_bot_iff, ← uloc_inf_dloc h hφ α]
    exact le_inf inf_le_left (le_dloc_of_le_normalizer h hfull hα hαβ hX₁Q hX₁Z hn hZlβ hcl.2.2)
  have h₂ : Qv 𝔛 β ≤ Subgroup.normalizer ((ZM 𝔛 (t • α) ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) :=
    (le_inf ((qv_le_stab_of_adj _ hδ₀β.symm).trans (stab_le_normalizer_zm _ _))
      ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_zm _ α))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h₂' : ¬ stab 𝔛 α ≤
      Subgroup.normalizer ((ZM 𝔛 (t • α) ⊔ ZM 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
    have := ms22_v _ h20 hb0 hC hV hctν
    rwa [hgeotν, xm_eq_zm h hfull hα] at this
  obtain ⟨g, hg, hn1, hn2⟩ := ms21_vii _ hgen hX₁₁ hX₁₂ h₂ h₂'
  have hgα : g • α = α := (mem_stab _).mp hg
  rw [map_conj_uloc_inf_centralizer h hfull hα hαβ g, hgα] at hn1
  rw [Subgroup.map_sup, ← zm_smul, ← zm_smul, hgα] at hn2
  obtain ⟨γ, hγdef⟩ : ∃ x : Vtx 𝔛, x = g • β := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ x : Vtx 𝔛, x = g • t • α := ⟨_, rfl⟩
  rw [← hγdef] at hn1
  rw [← hδdef] at hn2
  obtain ⟨s, hsdef⟩ : ∃ x : 𝔘, x = g * t := ⟨_, rfl⟩
  have hsμ : s • μ = α := by rw [hsdef, mul_smul, htμ, hgα]
  have hsσ : s • geo 𝔛 μ α 1 = γ := by rw [hsdef, mul_smul, htσ, hγdef]
  have hsα : s • α = δ := by rw [hsdef, mul_smul, hδdef]
  have hαγ : 𝔄 α γ := by
    have := (adj_smul _ g α β).mpr hαβ
    rwa [hgα, ← hγdef] at this
  have hγδ : 𝔄 γ δ := by
    have := (adj_smul _ g β (t • α)).mpr hδ₀β.symm
    rwa [← hγdef, ← hδdef] at this
  have hδ : IsMVtx 𝔛 δ := by
    rw [hδdef]
    exact (isMVtx_smul _ g _).mpr ((isMVtx_smul _ t α).mpr hα)
  have hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2 := by
    have := dist_smul _ g α (t • α)
    rwa [hgα, hdαδ₀, ← hδdef] at this
  have hcδ := isCritical_of_not_le_normalizer_sup h hb hcl h3l' hδ hdαδ hn2
  rw [hgeol] at hcδ
  have hgeoδ2 := (geo_eq_of_dist_eq h hb hdαδ hdαν hcδ.2.1).1
  have hXZ : Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 μ α 1) : Set 𝔘) ≤ ZM 𝔛 α := by
    rw [← zh_inf_uloc h hfull hμ hμσ]
    exact inf_le_left.trans (zh_le_zm _ hσα.symm)
  have hXc : Uloc h.le L μ ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 μ α 1) : Set 𝔘) ≤
      Subgroup.centralizer (stab 𝔛 α : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff, stab_eq_ltil_sup_qv h hfull hα]
    exact sup_le (Subgroup.le_centralizer_iff.mp (hX.trans (dloc_le_centralizer_ltil h hα)))
      (Subgroup.le_centralizer_iff.mp (hXZ.trans (zm_le_centralizer_qv _ h20 hα)))
  have hYc : Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) ≤
      Subgroup.centralizer (stab 𝔛 δ : Set 𝔘) := by
    have := map_conj_le_centralizer_map hXc s
    rwa [map_conj_uloc_inf_centralizer h hfull hμ hμσ s, hsμ, hsσ, ← stab_smul, hsα] at this
  have hfail' : ∀ g' : 𝔘, ¬ Concl441 h.le L (g' • α) (g' • δ) := by
    obtain ⟨g₁, hg₁μ, hg₁α⟩ := id hconj
    have e0 : g₁⁻¹ • α = μ := by rw [← hg₁μ, inv_smul_smul]
    intro g' hcon
    apply hfail (g' * s * g₁⁻¹)
    have e1 : (g' * s * g₁⁻¹) • α = g' • α := by simp only [mul_smul, e0, hsμ]
    have e2 : (g' * s * g₁⁻¹) • geo 𝔛 α α' 2 = g' • δ := by
      rw [← hg₁α]
      simp only [mul_smul, inv_smul_smul, hsα]
    rw [e1, e2]
    exact hcon
  have hcy : IsCritical 𝔛 α (s • ν) := by
    rw [← hsμ]
    exact (isCritical_smul _ s μ ν).mpr hcμ
  have hy : geo 𝔛 α (s • ν) 2 = δ := by
    have := geo_smul _ s μ ν 2
    rwa [hsμ, hgeoμ, hsα] at this
  obtain ⟨k, hk, hkZ⟩ : ∃ k ∈ stab 𝔛 δ, ¬ ZM 𝔛 (k • geo 𝔛 δ ν 2) ≤ Qv 𝔛 (geo 𝔛 ν δ 2) := by
    refine exists_smul_not_le_qv_of_fail h hφ hH hb hdual hV hcδ ?_ (y := s • ν) ?_ ?_
    · rw [hgeoδ2]
      exact hfail'
    · rw [hgeoδ2]
      exact hcy
    · rw [hgeoδ2]
      exact hy
  rw [hgeoδ2] at hkZ
  have hdνδ : (puAmalgam h.le).treeGraph.dist ν δ = critDist 𝔛 :=
    (ms22_iii _ h20 hb0 hC hcδ).2.1
  obtain ⟨ε, hεdef⟩ : ∃ x : Vtx 𝔛, x = geo 𝔛 ν δ 2 := ⟨_, rfl⟩
  rw [← hεdef] at hkZ
  have hdνε : (puAmalgam h.le).treeGraph.dist ν ε = 2 := by
    rw [hεdef]
    exact dist_geo _ (by omega)
  have hdδε : (puAmalgam h.le).treeGraph.dist δ ε = critDist 𝔛 - 2 := by
    rw [tdist_comm, hεdef, dist_geo_right _ (by omega), hdνδ]
  have hkα : IsMVtx 𝔛 (k • α) := (isMVtx_smul _ k α).mpr hα
  have hkδ : k • δ = δ := (mem_stab _).mp hk
  have hdkα : (puAmalgam h.le).treeGraph.dist (k • α) δ = 2 := by
    have := dist_smul _ k α δ
    rwa [hkδ, hdαδ] at this
  have hcrit : IsCritical 𝔛 (k • α) ε := by
    refine ⟨hkα, ?_, hkZ⟩
    have t := dist_triangle 𝔛 (k • α) δ ε
    by_contra hne
    exact hkZ (zm_le_qv_of_dist_lt _ hkα (by omega))
  have hkγ : geo 𝔛 (k • α) ε 1 = k • γ := by
    have hadd : (puAmalgam h.le).treeGraph.dist (k • α) ε =
        (puAmalgam h.le).treeGraph.dist (k • α) δ + (puAmalgam h.le).treeGraph.dist δ ε := by
      have := hcrit.2.1
      omega
    rw [geo_eq_of_dist_eq_add _ hadd (by omega)]
    symm
    refine eq_geo_one _ ((adj_smul _ k α γ).mpr hαγ) ?_
    have := dist_eq_one_of_adj _ ((adj_smul _ k γ δ).mpr hγδ)
    rw [hkδ] at this
    omega
  have hYk : Uloc h.le L (k • α) ⊓ Subgroup.centralizer (Qv 𝔛 (k • γ) : Set 𝔘) =
      Uloc h.le L α ⊓ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) := by
    rw [← map_conj_uloc_inf_centralizer h hfull hα hαγ k]
    exact map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.le_centralizer_iff.mp hYc hk))
  have hZε : ZM 𝔛 lam ≤ Subgroup.centralizer (ZM 𝔛 ε : Set 𝔘) := by
    refine zm_le_centralizer_zm h hlam (ms22_iii _ h20 hb0 hC hcrit).1 ?_
    have t := dist_triangle 𝔛 lam ν ε
    have hdlν : (puAmalgam h.le).treeGraph.dist lam ν = 2 := by
      rw [tdist_comm]
      exact hdl
    omega
  have hε4 : ε = geo 𝔛 α' α 4 := by
    have hadd1 : (puAmalgam h.le).treeGraph.dist ν δ =
        (puAmalgam h.le).treeGraph.dist ν α + (puAmalgam h.le).treeGraph.dist α δ := by
      omega
    have hadd2 : (puAmalgam h.le).treeGraph.dist α' α =
        (puAmalgam h.le).treeGraph.dist α' ν + (puAmalgam h.le).treeGraph.dist ν α := by
      have := hc'.2.1
      omega
    have e2 : geo 𝔛 α' α 4 = geo 𝔛 ν α 2 := by
      have := geo_of_dist_eq_add _ hadd2 (k := 2) (by omega)
      rwa [hdα'ν] at this
    rw [hεdef, geo_eq_of_dist_eq_add _ hadd1 (by omega), e2]
  apply hn1
  refine (hZε.trans (Subgroup.centralizer_le ?_)).trans (Subgroup.centralizer_le_normalizer _)
  rcases uloc_inf_centralizer_le_or h hφ hb hcrit with hle | ⟨hcen, hcard⟩
  · rw [hkγ, hYk] at hle
    exact hle.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((zm_le_stab_right _ h20 hb0 hC hcrit).trans (stab_le_normalizer_zm _ ε)))
  · rw [hkγ] at hcen
    subst hε4
    exact hG6 G M T L h F inferInstance inferInstance φ hH hb α α' hc hfail hc1 hB μ lam γ δ
      hconj hcμ hgeoμ h2 hdl hN hcl hX hαγ hγδ ⟨s, hsα, hsσ, hsμ⟩ hn1 hn2 hcδ k hk hkZ hcen hcard

end Vertex

end X441

theorem s441EndB_of (h32 : S32) (h43 : S43) (hG5 : S441EndB5) (hG6 : S441EndB6) :
    S441EndB := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail hc1
  have hdual := s441C1Dual_of_s43 h43
  have h2c := C441.s441C2Cent_of_dual h32 h43 hdual
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) δ' δ 2) :=
    fun δ δ' hcδ => h43 G M T L h hH.1 hH.2.1 hfull δ δ' hcδ
  by_contra hB
  obtain ⟨μ, lam, hconj, hcμ, hgeoμ, h2, hlam, hdl, hN, hcl, hgeol, h3l⟩ :=
    X441.exists_lam_of_not_le_bloc h hH h2c hb hc hfail hc1 hB
  by_cases hX : Uloc h.le L μ ⊓ Subgroup.centralizer
      (Qv (puAmalgam h.le) (geo (puAmalgam h.le) μ α 1) : Set (puAmalgam h.le).Universal) ≤
      Dloc h.le L α
  · exact X441.false_of_le_dloc h hG6 hH hb hdual hV hc hfail hc1 hB hconj hcμ hgeoμ h2 hlam hdl
      hN hcl hgeol h3l hX
  · exact X441.false_of_not_le_dloc h hG5 hH hb hc hfail hc1 hB hconj hcμ hgeoμ h2 hlam hdl hN
      hcl hgeol h3l hX

end CFSG.Quasithin.MS93.S4A
