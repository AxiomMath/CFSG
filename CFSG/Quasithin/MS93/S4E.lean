module

public import CFSG.Quasithin.MS93.S4A441EB6
import CFSG.Quasithin.MS93.S4A441XG
import CFSG.Quasithin.MS93.S4A441NoSec
import CFSG.Quasithin.MS93.S46TypeLin

public section

namespace CFSG.Quasithin.MS93.S4E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem commN_le_fixN_of_commute {E E' : Subgroup (SL3 F)}
    (hc : ∀ g ∈ E', ∀ k ∈ E, g * k = k * g) (hE : commN E ≤ fixN E') :
    commN E' ≤ fixN E := by
  rw [commN, Submodule.span_le]
  rintro _ ⟨g, hg, v, rfl⟩ k hk
  have e : ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (k : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_mul_SL3, ← coe_mul_SL3, hc g hg k hk]
  have h1 := hE (sub_mem_commN hk v) g hg
  rw [Matrix.mulVec_sub] at h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  abel

end Lin

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem uloc_inf_centralizer_le_of_fail (h2c : C441.S441C2Cent) (hH : Hyp40 h φ)
    (hb : 4 < critDist 𝔛) {x z : Vtx 𝔛} (hc : IsCritical 𝔛 x z)
    (hfail : ∀ g : 𝔘, ¬ Concl441 h.le L (g • x) (g • geo 𝔛 x z 2))
    (hc1 : ∀ g : 𝔘, ¬ IsC1 h.le L (Fintype.card F) (g • geo 𝔛 x z 2)
      (conjCl (stab 𝔛 (g • geo 𝔛 x z 2)) (ZM 𝔛 (g • x))) (ZM 𝔛 (g • geo 𝔛 x z 2)))
    (hB : ¬ ⁅Vv 𝔛 x, Qv 𝔛 x⁆ ≤ Bloc h.le L x) :
    Uloc h.le L x ⊓ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 x z 1) : Set 𝔘) ≤ ⁅ZM 𝔛 x, ZM 𝔛 z⁆ := by
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  have hx : IsMVtx 𝔛 x := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hz : IsMVtx 𝔛 z := hc'.1
  have hd : (puAmalgam h.le).treeGraph.dist x z = critDist 𝔛 := hc.2.1
  obtain ⟨μ, lam, -, hcμ, hgeoμ, h2, hlam, hdl, hN, hcl, -, -⟩ :=
    X441.exists_lam_of_not_le_bloc h hH h2c hb hc hfail hc1 hB
  set y := geo 𝔛 z x 2 with hy
  have hdzy : (puAmalgam h.le).treeGraph.dist z y = 2 := dist_geo _ (by rw [hc'.2.1]; omega)
  have hdyz : (puAmalgam h.le).treeGraph.dist y z = 2 := by rw [tdist_comm]; exact hdzy
  have hdyx : (puAmalgam h.le).treeGraph.dist y x = critDist 𝔛 - 2 := by
    rw [hy, dist_geo_right _ (by rw [hc'.2.1]; omega), hc'.2.1]
  have hdxy : (puAmalgam h.le).treeGraph.dist x y = critDist 𝔛 - 2 := by
    rw [tdist_comm]; exact hdyx
  have h3 : ⁅ZM 𝔛 μ, Vv 𝔛 y ⊓ Qv 𝔛 (geo 𝔛 μ y 2)⁆ ≤ ZM 𝔛 y := by
    have := C441.commutator_zm_vv_inf_qv_eq h hφ hC hb hcμ hdyz (by rw [hgeoμ]; exact h2)
    rw [this]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((zm_le_stab_right _ h20 hb0 hC hcμ).trans (stab_le_normalizer_zm _ y))
  obtain ⟨-, -, hrel, -⟩ := X441.isCritical_relIndex_of_not_normalizer h hφ hb hcμ hlam hdl hN h3
  rw [hgeoμ] at hrel
  have hcl' := ms22_iii _ h20 hb0 hC hcl
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hx
  obtain ⟨ψl, -, hψl⟩ := exists_natural_Uloc h hφ hlam
  obtain ⟨ψz, -, hψz⟩ := exists_natural_Uloc h hφ hz
  obtain ⟨hf, -, hrel', -, -, -⟩ := s35_core h hC hφ hcl hψl hψ
  obtain ⟨-, -, -, -, -, hE0⟩ := s35_core h hC hφ hc hψ hψz
  have hq : 2 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]; exact Finite.one_lt_card
  have hf1 : Module.finrank F (fixN (natImage ψ (ZM 𝔛 lam))) = 1 := by
    have e1 := hrel.symm.trans hrel'
    rw [Nat.card_eq_fintype_card] at e1
    have e2 := Nat.pow_right_injective hq e1
    have hle := Submodule.finrank_le (fixN (natImage ψl (ZM 𝔛 x)))
    rw [Module.finrank_fin_fun] at hle
    rw [hf]
    omega
  set τ := geo 𝔛 x z 1 with hτ
  have hadd1 : (puAmalgam h.le).treeGraph.dist x lam =
      (puAmalgam h.le).treeGraph.dist x y + (puAmalgam h.le).treeGraph.dist y lam := by
    rw [tdist_comm, hcl.2.1, hdxy, hdl]; omega
  have hadd2 : (puAmalgam h.le).treeGraph.dist x z =
      (puAmalgam h.le).treeGraph.dist x y + (puAmalgam h.le).treeGraph.dist y z := by
    rw [hd, hdxy, hdyz]; omega
  have hτl : geo 𝔛 x lam 1 = τ := by
    rw [hτ, geo_eq_of_dist_eq_add _ hadd1 (by omega), geo_eq_of_dist_eq_add _ hadd2 (by omega)]
  have hZlτ : ZM 𝔛 lam ≤ Qv 𝔛 τ := hτl ▸ zm_le_qv_geo_one _ h20 hb0 hcl'
  have hZzτ : ZM 𝔛 z ≤ Qv 𝔛 τ := zm_le_qv_geo_one _ h20 hb0 hc
  have hxτ : 𝔄 x τ := adj_geo_one_of_isCritical _ hb0 hc
  have hτH : ¬ IsMVtx 𝔛 τ := by
    rw [← isMVtx_iff_of_adj _ hxτ]
    exact hx
  have hTs : Qv 𝔛 τ ≤ stab 𝔛 x := qv_le_stab_of_adj _ hxτ.symm
  have hZzs : ZM 𝔛 z ≤ stab 𝔛 x := hZzτ.trans hTs
  have hP2 : IsPGroup 2 ↥(natImage ψ (Qv 𝔛 τ)) :=
    ((isPGroup_qv _ h20 hτH).of_equiv (Subgroup.subgroupOfEquivOfLe hTs).symm).map (toSL3 ψ)
  have hfix : fixN (natImage ψ (Qv 𝔛 τ)) = fixN (natImage ψ (ZM 𝔛 lam)) := by
    refine Submodule.eq_of_le_of_finrank_le (fixN_anti (natImage_mono hZlτ)) ?_
    rw [hf1]
    exact S46.finrank_fixN_pos hP2
  have hdlz : (puAmalgam h.le).treeGraph.dist lam z < critDist 𝔛 := by
    have t := dist_triangle 𝔛 lam y z
    rw [tdist_comm _ lam y, hdl, hdyz] at t
    omega
  have hZc : ZM 𝔛 lam ≤ Subgroup.centralizer (ZM 𝔛 z : Set 𝔘) :=
    zm_le_centralizer_zm h hlam hz hdlz
  have hcomm : ∀ g ∈ natImage ψ (ZM 𝔛 z), ∀ k ∈ natImage ψ (ZM 𝔛 lam), g * k = k * g := by
    intro g hg k hk
    obtain ⟨a, haZ, rfl⟩ := mem_natImage.mp hg
    obtain ⟨c, hcZ, rfl⟩ := mem_natImage.mp hk
    have hac : a * c = c * a :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZc hcZ) a haZ)
    rw [← map_mul, hac, map_mul]
  have hCE : commN (natImage ψ (ZM 𝔛 lam)) ≤ fixN (natImage ψ (ZM 𝔛 z)) :=
    (commN_le_fixN_of_elemAb (natImage_zm_sq h hlam) (natImage_zm_comm h hlam)).trans
      (hfix ▸ fixN_anti (natImage_mono hZzτ))
  have hkey := commN_le_fixN_of_commute hcomm hCE
  have heq : commN (natImage ψ (ZM 𝔛 z)) = fixN (natImage ψ (ZM 𝔛 lam)) := by
    refine Submodule.eq_of_le_of_finrank_le hkey ?_
    rw [hf1, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hE0
  rintro u ⟨huU, huc⟩
  have h1 := (mem_centralizer_iff_natVec hψ hTs ⟨u, huU⟩).mp huc
  rw [commutator_zm_eq_uloc h hfull hx hZzs]
  refine (mem_commutator_iff_natVec hψ hZzs ⟨u, huU⟩).mpr ?_
  rw [heq, ← hfix]
  exact h1

end Vertex

section Grp

private theorem forall_smul_of_smul {Γ V : Type*} [Group Γ] [MulAction Γ V] {P : V → V → Prop}
    {a b a' b' : V} {e : Γ} (ha : e • a = a') (hb : e • b = b')
    (hP : ∀ g : Γ, P (g • a) (g • b)) (g : Γ) : P (g • a') (g • b') := by
  have := hP (g * e)
  rwa [mul_smul, mul_smul, ha, hb] at this

end Grp

theorem s441EndB5_of (h32 : S32) (h43 : S43) : S4A.S441EndB5 := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail hc1 hB μ lam δ hconj hcμ hgeoμ h2 hdl hN hcl
    hX hδ hn1 hn2 hcδ hY hcen hcard
  have h2c := C441.s441C2Cent_of_dual h32 h43 (s441C1Dual_of_s43 h43)
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx _ α := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  obtain ⟨g, hgμ, hgα⟩ := hconj
  obtain ⟨l, hl, hlμ⟩ := hδ
  have hlα : l • α = α := (mem_stab _).mp hl
  have hgμ' : g⁻¹ • α = μ := by rw [← hgμ, inv_smul_smul]
  have hgα' : g⁻¹ • geo (puAmalgam h.le) α α' 2 = α := by rw [← hgα, inv_smul_smul]
  have he1 : (l * g⁻¹) • α = δ := by rw [mul_smul, hgμ', hlμ]
  have he2 : (l * g⁻¹) • geo (puAmalgam h.le) α α' 2 = α := by rw [mul_smul, hgα', hlα]
  have hdαν : (puAmalgam h.le).treeGraph.dist α (geo (puAmalgam h.le) α' α 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, dist_geo_right _ (by rw [hc'.2.1]; omega), hc'.2.1]
  have hdαμ : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    rw [tdist_comm, ← hgeoμ, dist_geo _ (by rw [hcμ.2.1]; omega)]
  have hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2 := by
    have := dist_smul _ l α μ
    rwa [hlα, hlμ, hdαμ] at this
  obtain ⟨hgeo2, hgeo1⟩ := X441.geo_eq_of_dist_eq h hb hdαδ hdαν hcδ.2.1
  have hfail' : ∀ g' : (puAmalgam h.le).Universal,
      ¬ Concl441 h.le L (g' • δ) (g' • geo (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) 2) := by
    rw [hgeo2]
    exact forall_smul_of_smul (P := fun u v => ¬ Concl441 h.le L u v) he1 he2 hfail
  have hc1' : ∀ g' : (puAmalgam h.le).Universal,
      ¬ IsC1 h.le L (Fintype.card F)
        (g' • geo (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) 2)
        (conjCl (stab (puAmalgam h.le)
          (g' • geo (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) 2))
          (ZM (puAmalgam h.le) (g' • δ)))
        (ZM (puAmalgam h.le) (g' • geo (puAmalgam h.le) δ (geo (puAmalgam h.le) α' α 2) 2)) := by
    rw [hgeo2]
    exact forall_smul_of_smul (P := fun u v => ¬ IsC1 h.le L (Fintype.card F) v
      (conjCl (stab (puAmalgam h.le) v) (ZM (puAmalgam h.le) u)) (ZM (puAmalgam h.le) v))
      he1 he2 hc1
  have hB' := X441.not_commutator_vv_qv_le_bloc h hα hcδ.1 hB
  have key := uloc_inf_centralizer_le_of_fail h h2c hH hb hcδ hfail' hc1' hB'
  rw [hgeo1] at key
  exact key.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((zm_le_stab_right _ h20 hb0 hC hcδ).trans (stab_le_normalizer_zm _ _)))

theorem s441EndB6_of (h32 : S32) (h43 : S43) : S4A.S441EndB6 := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail hc1 hB μ lam γ δ hconj hcμ hgeoμ h2 hdl hN hcl
    hX hαγ hγδ hs hn1 hn2 hcδ k hk hkZ hcen hcard
  have h2c := C441.s441C2Cent_of_dual h32 h43 (s441C1Dual_of_s43 h43)
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx _ α := hc.1
  have hμ : IsMVtx _ μ := hcμ.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  obtain ⟨g₁, hg₁μ, hg₁α⟩ := hconj
  obtain ⟨s, hsα, hsσ, hsμ⟩ := hs
  have hdα'ν : (puAmalgam h.le).treeGraph.dist α' (geo (puAmalgam h.le) α' α 2) = 2 :=
    dist_geo _ (by rw [hc'.2.1]; omega)
  set ν := geo (puAmalgam h.le) α' α 2 with hνdef
  have hdαν : (puAmalgam h.le).treeGraph.dist α ν = critDist (puAmalgam h.le) - 2 := by
    rw [hνdef, tdist_comm, dist_geo_right _ (by rw [hc'.2.1]; omega), hc'.2.1]
  have hdνα : (puAmalgam h.le).treeGraph.dist ν α = critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm]
    exact hdαν
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 2 := by
    rw [← hgeoμ, dist_geo _ (by rw [hcμ.2.1]; omega)]
  have hμσ : (puAmalgam h.le).treeGraph.Adj μ (geo (puAmalgam h.le) μ α 1) :=
    adj_geo_one _ (by omega)
  have hσα : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) μ α 1) α := by
    have := adj_geo _ (u := μ) (w := α) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) μ α (1 + 1) = α from geo_of_le _ (by omega)] at this
  have hdαδ : (puAmalgam h.le).treeGraph.dist α δ = 2 := by
    have := dist_smul _ s μ α
    rwa [hsμ, hsα, hdμα] at this
  have hXZ : Uloc h.le L μ ⊓ Subgroup.centralizer
      (Qv (puAmalgam h.le) (geo (puAmalgam h.le) μ α 1) : Set (puAmalgam h.le).Universal) ≤
      ZM (puAmalgam h.le) α := by
    rw [← zh_inf_uloc h hfull hμ hμσ]
    exact inf_le_left.trans (zh_le_zm _ hσα.symm)
  have hXc : Uloc h.le L μ ⊓ Subgroup.centralizer
      (Qv (puAmalgam h.le) (geo (puAmalgam h.le) μ α 1) : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (stab (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff, stab_eq_ltil_sup_qv h hfull hα]
    exact sup_le (Subgroup.le_centralizer_iff.mp (hX.trans (dloc_le_centralizer_ltil h hα)))
      (Subgroup.le_centralizer_iff.mp (hXZ.trans (zm_le_centralizer_qv _ h20 hα)))
  have hYc : Uloc h.le L α ⊓ Subgroup.centralizer
      (Qv (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (stab (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
    have := X441.map_conj_le_centralizer_map hXc s
    rwa [X441.map_conj_uloc_inf_centralizer h hfull hμ hμσ s, hsμ, hsσ, ← stab_smul,
      hsα] at this
  have hdνδ : (puAmalgam h.le).treeGraph.dist ν δ = critDist (puAmalgam h.le) :=
    (ms22_iii _ h20 hb0 hC hcδ).2.1
  obtain ⟨ε, hεdef⟩ : ∃ x : Vtx (puAmalgam h.le), x = geo (puAmalgam h.le) ν δ 2 := ⟨_, rfl⟩
  have hε4 : ε = geo (puAmalgam h.le) α' α 4 := by
    have hadd1 : (puAmalgam h.le).treeGraph.dist ν δ =
        (puAmalgam h.le).treeGraph.dist ν α + (puAmalgam h.le).treeGraph.dist α δ := by
      omega
    have hadd2 : (puAmalgam h.le).treeGraph.dist α' α =
        (puAmalgam h.le).treeGraph.dist α' ν + (puAmalgam h.le).treeGraph.dist ν α := by
      have := hc'.2.1
      omega
    have e2 : geo (puAmalgam h.le) α' α 4 = geo (puAmalgam h.le) ν α 2 := by
      have := geo_of_dist_eq_add _ hadd2 (k := 2) (by omega)
      rwa [hdα'ν] at this
    rw [hεdef, geo_eq_of_dist_eq_add _ hadd1 (by omega), e2]
  rw [← hε4] at hkZ ⊢
  have hdδε : (puAmalgam h.le).treeGraph.dist δ ε = critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, hεdef, dist_geo_right _ (by omega), hdνδ]
  have hkα : IsMVtx (puAmalgam h.le) (k • α) := (isMVtx_smul _ k α).mpr hα
  have hkδ : k • δ = δ := (mem_stab _).mp hk
  have hdkα : (puAmalgam h.le).treeGraph.dist (k • α) δ = 2 := by
    have := dist_smul _ k α δ
    rwa [hkδ, hdαδ] at this
  have hcrit : IsCritical (puAmalgam h.le) (k • α) ε := by
    refine ⟨hkα, ?_, hkZ⟩
    have t := dist_triangle (puAmalgam h.le) (k • α) δ ε
    by_contra hne
    exact hkZ (zm_le_qv_of_dist_lt _ hkα (by omega))
  have hadd : (puAmalgam h.le).treeGraph.dist (k • α) ε =
      (puAmalgam h.le).treeGraph.dist (k • α) δ + (puAmalgam h.le).treeGraph.dist δ ε := by
    have := hcrit.2.1
    omega
  have hkγ : geo (puAmalgam h.le) (k • α) ε 1 = k • γ := by
    rw [geo_eq_of_dist_eq_add _ hadd (by omega)]
    symm
    refine eq_geo_one _ ((adj_smul _ k α γ).mpr hαγ) ?_
    have := dist_eq_one_of_adj _ ((adj_smul _ k γ δ).mpr hγδ)
    rw [hkδ] at this
    omega
  have hkδ2 : geo (puAmalgam h.le) (k • α) ε 2 = δ := by
    rw [geo_eq_of_dist_eq_add _ hadd (by omega)]
    exact geo_of_le _ (by omega)
  have hYk : Uloc h.le L (k • α) ⊓ Subgroup.centralizer
      (Qv (puAmalgam h.le) (k • γ) : Set (puAmalgam h.le).Universal) =
      Uloc h.le L α ⊓ Subgroup.centralizer
        (Qv (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal) := by
    rw [← X441.map_conj_uloc_inf_centralizer h hfull hα hαγ k]
    exact map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.le_centralizer_iff.mp hYc hk))
  have hg₁μ' : g₁⁻¹ • α = μ := by rw [← hg₁μ, inv_smul_smul]
  have hg₁α' : g₁⁻¹ • geo (puAmalgam h.le) α α' 2 = α := by rw [← hg₁α, inv_smul_smul]
  have he1 : (k * s * g₁⁻¹) • α = k • α := by rw [mul_smul, mul_smul, hg₁μ', hsμ]
  have he2 : (k * s * g₁⁻¹) • geo (puAmalgam h.le) α α' 2 =
      geo (puAmalgam h.le) (k • α) ε 2 := by
    rw [mul_smul, mul_smul, hg₁α', hsα, hkδ, hkδ2]
  have hfail' := forall_smul_of_smul (P := fun u v => ¬ Concl441 h.le L u v) he1 he2 hfail
  have hc1' := forall_smul_of_smul (P := fun u v => ¬ IsC1 h.le L (Fintype.card F) v
    (conjCl (stab (puAmalgam h.le) v) (ZM (puAmalgam h.le) u)) (ZM (puAmalgam h.le) v))
    he1 he2 hc1
  have hB' := X441.not_commutator_vv_qv_le_bloc h hα hkα hB
  have key := uloc_inf_centralizer_le_of_fail h h2c hH hb hcrit hfail' hc1' hB'
  rw [hkγ, hYk] at key
  exact key.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((zm_le_stab_right _ h20 hb0 hC hcrit).trans (stab_le_normalizer_zm _ _)))

theorem s441EndB_holds (h32 : S32) (h43 : S43) : S4A.S441EndB :=
  S4A.s441EndB_of h32 h43 (s441EndB5_of h32 h43) (s441EndB6_of h32 h43)

end CFSG.Quasithin.MS93.S4E
