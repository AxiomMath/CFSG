module

public import CFSG.Quasithin.MS93.S46I466aQTyp
public import CFSG.Quasithin.MS93.S46I466aQCnt
public import CFSG.Quasithin.MS93.S46I466aQOrb
public import CFSG.Quasithin.MS93.S46I469Loc
public import CFSG.Quasithin.MS93.S46I469B0
public import CFSG.Quasithin.MS93.S46I469Crit
public import CFSG.Quasithin.MS93.S4A44Lin
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Quasithin.MS93.S4A44Stmt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S46.I466b
open CFSG.Quasithin.MS93.S4A
open scoped Matrix commutatorElement

section Grp

variable {𝔾 : Type*} [Group 𝔾]

theorem not_map_conj_le_radModSub {V 𝔷 W : Subgroup 𝔾}
    {h𝔷 : V ≤ Subgroup.normalizer (𝔷 : Set 𝔾)} {k : 𝔾}
    (hkV : k ∈ Subgroup.normalizer (V : Set 𝔾)) (hk𝔷 : k ∈ Subgroup.normalizer (𝔷 : Set 𝔾))
    (hWV : W ≤ V) (hW : ¬ W ≤ radModSub V 𝔷 h𝔷) :
    ¬ W.map (MulAut.conj k).toMonoidHom ≤ radModSub V 𝔷 h𝔷 := by
  obtain ⟨a, haW, haR⟩ := Set.not_subset.mp hW
  obtain ⟨w, hwV, haw⟩ : ∃ w ∈ V, ⁅a, w⁆ ∉ 𝔷 := by
    by_contra hno
    push Not at hno
    exact haR ⟨hWV haW, hno⟩
  intro hle
  have hka : k * a * k⁻¹ ∈ radModSub V 𝔷 h𝔷 :=
    hle ⟨a, haW, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hkw : k * w * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkV w).mp hwV
  have h1 := hka.2 _ hkw
  have e : ⁅k * a * k⁻¹, k * w * k⁻¹⁆ = k * ⁅a, w⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← Subgroup.mem_normalizer_iff.mp hk𝔷] at h1
  exact haw h1

end Grp

section Gen

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hb4 : critDist (puAmalgam h.le) = 4)

theorem zv_le_vv_of_dist {z τ : Vtx (puAmalgam h.le)}
    (hτ : (puAmalgam h.le).treeGraph.dist z τ ≤ 2) :
    Zv (puAmalgam h.le) τ ≤ Vv _ z :=
  le_iSup₂_of_le (f := fun τ (_ : τ ∈ {τ : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.dist z τ ≤ 2}) => Zv (puAmalgam h.le) τ) τ hτ le_rfl

include h hb4 in
theorem isCritical_of_not_commute {z ρ ρ' : Vtx (puAmalgam h.le)} (hz : IsMVtx _ z)
    (hρ : (puAmalgam h.le).treeGraph.dist z ρ ≤ 2)
    (hρ' : (puAmalgam h.le).treeGraph.dist z ρ' ≤ 2) {a b : (puAmalgam h.le).Universal}
    (ha : a ∈ Zv (puAmalgam h.le) ρ) (hb : b ∈ Zv (puAmalgam h.le) ρ') (hab : a * b ≠ b * a) :
    IsCritical (puAmalgam h.le) ρ ρ' ∧ geo (puAmalgam h.le) ρ ρ' 2 = z ∧
      (puAmalgam h.le).treeGraph.dist z ρ = 2 ∧ (puAmalgam h.le).treeGraph.dist z ρ' = 2 := by
  have h20 := h.hyp20
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hVQ := vv_le_qv h hb2 hz
  have hd : ∀ {τ τ' : Vtx (puAmalgam h.le)} {c d : (puAmalgam h.le).Universal},
      (puAmalgam h.le).treeGraph.dist z τ ≤ 1 → (puAmalgam h.le).treeGraph.dist z τ' ≤ 2 →
      c ∈ Zv (puAmalgam h.le) τ → d ∈ Zv (puAmalgam h.le) τ' → d * c = c * d := by
    intro τ τ' c d hτ hτ' hc hd
    exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hz
      (zv_le_zm_of_dist_le_one h hz hτ hc)) d (hVQ (zv_le_vv_of_dist h hτ' hd))
  have h2 : (puAmalgam h.le).treeGraph.dist z ρ = 2 := by
    by_contra hne
    exact hab (hd (by omega) hρ' ha hb).symm
  have h2' : (puAmalgam h.le).treeGraph.dist z ρ' = 2 := by
    by_contra hne
    exact hab (hd (by omega) hρ hb ha)
  have hM : ∀ {τ : Vtx (puAmalgam h.le)}, (puAmalgam h.le).treeGraph.dist z τ = 2 →
      IsMVtx _ τ := by
    intro τ hτ
    rcases isMVtx_of_dist_le_two h hz (le_of_eq hτ) with hτM | hadj
    · exact hτM
    · have := dist_eq_one_of_adj _ hadj
      omega
  have hρM := hM h2
  have hρ'M := hM h2'
  have haZ : a ∈ ZM (puAmalgam h.le) ρ := by rwa [zv_of_isMVtx _ hρM] at ha
  have hbZ : b ∈ ZM (puAmalgam h.le) ρ' := by rwa [zv_of_isMVtx _ hρ'M] at hb
  have hdist : (puAmalgam h.le).treeGraph.dist ρ ρ' = 4 := by
    have htri := dist_triangle _ ρ z ρ'
    rw [tdist_comm _ ρ z, h2, h2'] at htri
    by_contra hne
    exact hab (commute_of_dist_le_three h20 hb4 hρM (by omega) haZ hb)
  have hcr : IsCritical (puAmalgam h.le) ρ ρ' := by
    refine ⟨hρM, hdist.trans hb4.symm, fun hle => hab ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hρ'M hbZ) a (hle haZ)
  refine ⟨hcr, ?_, h2, h2'⟩
  exact (eq_geo_of_dist _ (by rw [tdist_comm]; exact h2)
    (by rw [tdist_comm _ ρ z, h2, h2', hdist])).symm

include hb4 in
theorem geo_one_eq_of_geo_two_eq {μ ν τ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ ν) (hcτ : IsCritical (puAmalgam h.le) μ τ)
    (he : geo (puAmalgam h.le) μ τ 2 = geo _ μ ν 2) :
    geo (puAmalgam h.le) μ τ 1 = geo _ μ ν 1 := by
  rw [← geo_geo _ (show 1 ≤ 2 by norm_num)
      (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ τ by rw [dist_eq_four hb4 hcτ]; norm_num), he,
    geo_geo _ (show 1 ≤ 2 by norm_num)
      (show 2 ≤ (puAmalgam h.le).treeGraph.dist μ ν by rw [dist_eq_four hb4 hc]; norm_num)]

end Gen

section Lab

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le)) (hb4 : critDist (puAmalgam h.le) = 4)
  (hS : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
    (Qv (puAmalgam h.le) α).relIndex (Qv _ β) < Fintype.card F ^ 2)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)

include h hφ hC hS in
theorem card_critR_eq_or {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F ∨
      Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F ^ 2 := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨-, hR, h1, h2⟩ := card_natImage_zm_of_lt h hφ hC hc
    (hS α _ hc.1 (adj_geo_one_of_isCritical _ h.critDist_pos hc)) hψ
  rcases (by omega : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 1 ∨
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) = 2) with hw | hw
  · left
    rw [hR, hw, pow_one]
  · right
    rw [hR, hw]

include h hφ hC hb4 hS h464 hsq in
theorem commutator_zm_vv_le {μ ν z : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) μ ν)
    (hz : geo (puAmalgam h.le) μ ν 2 = z) (hR : ¬ critR (puAmalgam h.le) μ ν ≤ Zloc h.le L z) :
    ⁅ZM (puAmalgam h.le) μ, Vv _ z⁆ ≤ critR (puAmalgam h.le) μ ν ⊔ Zloc h.le L z := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hμr : (puAmalgam h.le).treeGraph.Adj μ (geo _ μ ν 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hrz : (puAmalgam h.le).treeGraph.Adj (geo _ μ ν 1) z :=
    hz ▸ adj_geo_crit hb4 hc (i := 1) (by norm_num)
  have hzM : IsMVtx _ z := hz ▸ isMVtx_geo_two' hb4 hc
  have hVr : Vv (puAmalgam h.le) z ≤ Qv _ (geo _ μ ν 1) :=
    (vv_le_qv h hb2 hzM).trans (qv_le_qv _ h20 hzM hrz.symm)
  rcases card_critR_eq_or h hφ hC hS hc with h2 | h3
  ·
    have hdμ : (puAmalgam h.le).treeGraph.dist z μ = 2 := by
      rw [← hz, tdist_comm]
      exact dist_geo_crit hb4 hc (by norm_num)
    have hXZ : critR (puAmalgam h.le) μ ν ⊔ Zloc h.le L z ≤ ZM _ z :=
      sup_le ((critR_le_usup_one h hc).trans ((h464 μ _ hc.1 hμr).trans (zh_le_zm _ hrz.symm)))
        (zloc_le_zm h hfull hzM)
    have hVn : Vv (puAmalgam h.le) z ≤ Subgroup.normalizer
        ((critR (puAmalgam h.le) μ ν ⊔ Zloc h.le L z : Subgroup _) : Set _) :=
      ((vv_le_qv h hb2 hzM).trans ((Subgroup.le_centralizer_iff.mp
        (zm_le_centralizer_qv _ h20 hzM)).trans (Subgroup.centralizer_le hXZ))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.commutator_le]
    intro a ha w hw
    have hle : Vv (puAmalgam h.le) z ≤ commModRight (Vv _ z) _ hVn a := by
      refine iSup₂_le fun τ hτ => ?_
      intro b hb
      refine ⟨zv_le_vv_of_dist h hτ hb, ?_⟩
      by_contra hnot
      have hnz : ⁅a, b⁆ ∉ Zloc h.le L z := fun hm => hnot (Subgroup.mem_sup_right hm)
      have hne : a * b ≠ b * a := fun he =>
        hnz (by rw [commutatorElement_eq_one_iff_mul_comm.mpr he]; exact one_mem _)
      obtain ⟨hcτ, hgτ, -, -⟩ := isCritical_of_not_commute h hb4 hzM (le_of_eq hdμ) hτ
        (by rwa [zv_of_isMVtx _ hc.1]) hb hne
      have hgeo : geo (puAmalgam h.le) μ τ 1 = geo _ μ ν 1 :=
        geo_one_eq_of_geo_two_eq h hb4 hc hcτ (hgτ.trans hz.symm)
      have hbZ : b ∈ ZM (puAmalgam h.le) τ := by
        rwa [zv_of_isMVtx _ (hcτ.isMVtx_right _ h20)] at hb
      rcases card_critR_eq_or h hφ hC hS hcτ with h2τ | h3τ
      · apply hnot
        refine Subgroup.mem_sup_left ?_
        rw [critR_eq_critR_of_card h hφ hC hc hcτ hgeo (hS μ _ hc.1 hμr) h2 h2τ]
        exact Subgroup.commutator_mem_commutator ha hbZ
      · apply hR
        have := critR_le_zloc_of_card_sq h hφ hC hb4 h464 hsq hcτ h3τ hc hgeo.symm
          (by rw [hgeo]; exact hS μ _ hc.1 hμr) h2
        rwa [hgτ] at this
    exact (hle hw).2
  ·
    refine le_sup_of_le_left ?_
    rw [critR_eq_usup_of_card_sq h hc (hsq μ _ hc.1 hμr) h3, Usup, zv_of_isMVtx _ hc.1]
    exact Subgroup.commutator_mono le_rfl hVr

include h hφ hC hb4 hS h464 hsq in
theorem sup_zloc_eq {μ ν z : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) μ ν)
    (hz : geo (puAmalgam h.le) μ ν 2 = z) (hR : ¬ critR (puAmalgam h.le) μ ν ≤ Zloc h.le L z) :
    ⁅ZM (puAmalgam h.le) μ, Vv _ z⁆ ⊔ Zloc h.le L z =
      critR (puAmalgam h.le) μ ν ⊔ Zloc h.le L z := by
  refine le_antisymm (sup_le (commutator_zm_vv_le h hφ hC hb4 hS h464 hsq hc hz hR) le_sup_right)
    (sup_le_sup_right (Subgroup.commutator_mono le_rfl ?_) _)
  have hdν : (puAmalgam h.le).treeGraph.dist z ν = 2 := by
    rw [← hz]
    exact dist_geo_crit_right hb4 hc (by norm_num)
  have := zv_le_vv_of_dist h (le_of_eq hdν)
  rwa [zv_of_isMVtx _ (hc.isMVtx_right _ h.hyp20)] at this

include h hφ hC hb4 hS h464 hsq in
theorem lab_eq_of_commutator_not_mem {z ρ ρ' : Vtx (puAmalgam h.le)} (hz : IsMVtx _ z)
    (hρ : (puAmalgam h.le).treeGraph.dist z ρ ≤ 2)
    (hρ' : (puAmalgam h.le).treeGraph.dist z ρ' ≤ 2) {a b : (puAmalgam h.le).Universal}
    (ha : a ∈ Zv (puAmalgam h.le) ρ) (hb : b ∈ Zv (puAmalgam h.le) ρ')
    (hab : ⁅a, b⁆ ∉ Zloc h.le L z) :
    ⁅Zv (puAmalgam h.le) ρ, Vv _ z⁆ ⊔ Zloc h.le L z =
      ⁅Zv (puAmalgam h.le) ρ', Vv _ z⁆ ⊔ Zloc h.le L z := by
  have hne : a * b ≠ b * a := fun he =>
    hab (by rw [commutatorElement_eq_one_iff_mul_comm.mpr he]; exact one_mem _)
  obtain ⟨hc, hgz, -, -⟩ := isCritical_of_not_commute h hb4 hz hρ hρ' ha hb hne
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  have haZ : a ∈ ZM (puAmalgam h.le) ρ := by rwa [zv_of_isMVtx _ hc.1] at ha
  have hbZ : b ∈ ZM (puAmalgam h.le) ρ' := by rwa [zv_of_isMVtx _ hc'.1] at hb
  have hR : ¬ critR (puAmalgam h.le) ρ ρ' ≤ Zloc h.le L z :=
    fun hle => hab (hle (Subgroup.commutator_mem_commutator haZ hbZ))
  have hR' : ¬ critR (puAmalgam h.le) ρ' ρ ≤ Zloc h.le L z := by
    rwa [critR, Subgroup.commutator_comm]
  rw [zv_of_isMVtx _ hc.1, zv_of_isMVtx _ hc'.1,
    sup_zloc_eq h hφ hC hb4 hS h464 hsq hc hgz hR,
    sup_zloc_eq h hφ hC hb4 hS h464 hsq hc' (by rw [geo_rev_two hb4 hc, hgz]) hR', critR, critR,
    Subgroup.commutator_comm]

include h in
theorem commutator_vv_sup_zloc_smul {z : Vtx (puAmalgam h.le)} {k : (puAmalgam h.le).Universal}
    (hk : k ∈ stab (puAmalgam h.le) z) (ρ : Vtx (puAmalgam h.le)) :
    ⁅Zv (puAmalgam h.le) (k • ρ), Vv _ z⁆ ⊔ Zloc h.le L z =
      (⁅Zv (puAmalgam h.le) ρ, Vv _ z⁆ ⊔ Zloc h.le L z).map (MulAut.conj k).toMonoidHom := by
  have hkz : k • z = z := (mem_stab _).mp hk
  have hV : (Vv (puAmalgam h.le) z).map (MulAut.conj k).toMonoidHom = Vv _ z := by
    rw [show Vv (puAmalgam h.le) z = Vi _ z 2 from rfl, ← vi_smul, hkz]
  have hZ : (Zloc h.le L z).map (MulAut.conj k).toMonoidHom = Zloc h.le L z := by
    rw [← zloc_smul h, hkz]
  rw [Subgroup.map_sup, Subgroup.map_commutator, hV, hZ, ← zv_smul]

end Lab

section Count

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le)) (hb4 : critDist (puAmalgam h.le) = 4)
  (hS : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
    (Qv (puAmalgam h.le) α).relIndex (Qv _ β) < Fintype.card F ^ 2)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)

include h hφ hC hS h464 hsq in
theorem exists_conj_natImage_zm_eq_rootGroup {z μ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) z μ')
    (h2 : Nat.card ↥(critR (puAmalgam h.le) z μ') = Fintype.card F)
    {ψ : ↥(stab (puAmalgam h.le) z) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ z) (Uloc h.le L z) ⊥ ψ false 1) :
    ∃ y : SL3 F, (natImage ψ (ZM (puAmalgam h.le) μ')).map (MulAut.conj y).toMonoidHom =
      rootGroup 0 1 := by
  have hb0 := h.critDist_pos
  have hzr : (puAmalgam h.le).treeGraph.Adj z (geo _ z μ' 1) := adj_geo_one_of_isCritical _ hb0 hc
  obtain ⟨hE, hR, -, -⟩ := card_natImage_zm_of_lt h hφ hC hc (hS z _ hc.1 hzr) hψ
  have hq2 := two_le_card_field (F := F)
  have hw1 : Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) μ'))) = 1 := by
    rw [h2] at hR
    exact Nat.pow_right_injective hq2 (hR.symm.trans (pow_one _).symm)
  obtain ⟨hP2, hPc⟩ := fixN_natImage_qv h hφ h464 hsq hc.1 hzr hψ
  have hne : commN (natImage ψ (ZM (puAmalgam h.le) μ')) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hw1
    omega
  obtain ⟨r₀, hr₀, hr₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hline : commN (natImage ψ (ZM (puAmalgam h.le) μ')) = F ∙ r₀ :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hr₀)
      (by rw [finrank_span_singleton hr₀0, hw1])).symm
  have hEle : natImage ψ (ZM (puAmalgam h.le) μ') ≤ natImage ψ (Qv _ (geo _ z μ' 1)) :=
    natImage_mono (zm_le_qv_geo_one _ h.hyp20 hb0 hc)
  refine exists_conj_eq_rootGroup hP2 ?_ hr₀0 (fun g hg p hp => hp g (hEle hg)) ?_ ?_
  · rw [← hPc]
    exact commN_mono hEle hr₀
  · intro g hg v
    rw [← hline]
    exact sub_mem_commN hg v
  · rw [hE, Nat.card_eq_fintype_card]

omit [Field F] in
include h hb4 hS in
theorem relIndex_centralizer_zm_lt {z μ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) z μ') :
    (Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set (puAmalgam h.le).Universal)).relIndex
      (Vv (puAmalgam h.le) z) < Fintype.card F ^ 4 := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hz := hc.1
  have hμ' : IsMVtx _ μ' := hc.isMVtx_right _ h20
  have hr1 : (puAmalgam h.le).treeGraph.Adj z (geo _ z μ' 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hxr : (puAmalgam h.le).treeGraph.Adj (geo _ z μ' 1) (geo _ z μ' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by norm_num)
  have hxs : (puAmalgam h.le).treeGraph.Adj (geo _ z μ' 2) (geo _ z μ' 3) :=
    adj_geo_crit hb4 hc (i := 2) (by norm_num)
  have hsμ : (puAmalgam h.le).treeGraph.Adj (geo _ z μ' 3) μ' := by
    have := adj_geo_crit hb4 hc (i := 3) (by norm_num)
    rwa [geo_four hb4 hc] at this
  have hx : IsMVtx _ (geo (puAmalgam h.le) z μ' 2) := isMVtx_geo_two' hb4 hc
  have hVr : Vv (puAmalgam h.le) z ≤ Qv _ (geo _ z μ' 1) :=
    (vv_le_qv h hb2 hz).trans (qv_le_qv _ h20 hz hr1)
  have hxs' : Qv (puAmalgam h.le) (geo _ z μ' 2) ≤ Qv _ (geo _ z μ' 3) := qv_le_qv _ h20 hx hxs
  have hμC : Qv (puAmalgam h.le) μ' ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) μ' : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hμ')
  have := finite_stab h hz
  have hVs : Vv (puAmalgam h.le) z ≤ stab _ z := (vv_le_qv h hb2 hz).trans (qv_le_stab _ z)
  have hrs : Qv (puAmalgam h.le) (geo _ z μ' 1) ≤ stab _ z := qv_le_stab_of_adj _ hr1.symm
  have : Finite ↥(stab (puAmalgam h.le) μ') := finite_stab h hμ'
  have hss : Qv (puAmalgam h.le) (geo _ z μ' 3) ≤ stab _ μ' := qv_le_stab_of_adj _ hsμ
  have e := Subgroup.relIndex_inf_mul_relIndex (Qv (puAmalgam h.le) μ') (Qv _ (geo _ z μ' 2))
    (Vv (puAmalgam h.le) z)
  have h1 : (Subgroup.centralizer (ZM (puAmalgam h.le) μ' :
      Set (puAmalgam h.le).Universal)).relIndex (Vv (puAmalgam h.le) z) ≤
        (Qv (puAmalgam h.le) μ' ⊓ Qv _ (geo _ z μ' 2)).relIndex (Vv (puAmalgam h.le) z) :=
    Subgroup.relIndex_le_of_le_left (inf_le_left.trans hμC) (relIndex_ne_zero_of_le_finite hVs)
  have h2 : (Qv (puAmalgam h.le) (geo _ z μ' 2)).relIndex (Vv (puAmalgam h.le) z) <
      Fintype.card F ^ 2 :=
    lt_of_le_of_lt (Subgroup.relIndex_le_of_le_right hVr (relIndex_ne_zero_of_le_finite hrs))
      (hS _ _ hx hxr.symm)
  have h3 : (Qv (puAmalgam h.le) μ').relIndex (Qv _ (geo _ z μ' 2) ⊓ Vv (puAmalgam h.le) z) <
      Fintype.card F ^ 2 :=
    lt_of_le_of_lt (Subgroup.relIndex_le_of_le_right (inf_le_left.trans hxs')
      (relIndex_ne_zero_of_le_finite hss)) (hS _ _ hμ' hsμ.symm)
  calc _ ≤ _ := h1
    _ = _ := e.symm
    _ < Fintype.card F ^ 2 * Fintype.card F ^ 2 :=
        mul_lt_mul'' h3 h2 (Nat.zero_le _) (Nat.zero_le _)
    _ = Fintype.card F ^ 4 := by ring

theorem pow_four_le_two_pow_mul {q : ℕ} (hq : 4 ≤ q) : q ^ 4 ≤ 2 ^ (q * (q - 1)) := by
  have h1 : q ≤ 2 ^ (q - 1) := by
    have := Nat.lt_two_pow_self (n := q - 1)
    have : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
    omega
  calc q ^ 4 ≤ (2 ^ (q - 1)) ^ 4 := Nat.pow_le_pow_left h1 4
    _ = 2 ^ ((q - 1) * 4) := by rw [← pow_mul]
    _ ≤ 2 ^ (q * (q - 1)) := Nat.pow_le_pow_right (by norm_num)
        (by rw [mul_comm q]; exact Nat.mul_le_mul_left _ hq)

include h hφ hC hb4 hS h464 hsq in
theorem commutator_vv_le_zloc (hq : 4 ≤ Fintype.card F)
    (hII : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
      ∃ α', IsCritical (puAmalgam h.le) α α' ∧ geo _ α α' 1 = β ∧
        Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F)
    {z : Vtx (puAmalgam h.le)} (hz : IsMVtx _ z) :
    ⁅Vv (puAmalgam h.le) z, Vv _ z⁆ ≤ Zloc h.le L z := by
  by_contra hn
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hVQ := vv_le_qv h hb2 hz
  have hVs : Vv (puAmalgam h.le) z ≤ stab _ z := hVQ.trans (qv_le_stab _ z)
  have := finite_stab h hz
  have : Finite ↥(Vv (puAmalgam h.le) z) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVs)
  have hZn : stab (puAmalgam h.le) z ≤ Subgroup.normalizer (Zloc h.le L z : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) z
  have h𝔷 : Vv (puAmalgam h.le) z ≤ Subgroup.normalizer (Zloc h.le L z : Set _) := hVs.trans hZn
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hz
  obtain ⟨r', hzr'⟩ := exists_adj _ z
  obtain ⟨μ', hc', -, h2'⟩ := hII z r' hz hzr'
  obtain ⟨y, hy⟩ := exists_conj_natImage_zm_eq_rootGroup h hφ hC hS h464 hsq hc' h2' hψ
  obtain ⟨ρs, hρs⟩ : ∃ ρs : ↥(stab (puAmalgam h.le) z) →* SL3 F,
      ∀ k, ρs k = y * toSL3 ψ k * y⁻¹ := ⟨(MulAut.conj y).toMonoidHom.comp (toSL3 ψ), fun _ => rfl⟩
  have hρsurj : Function.Surjective ρs := by
    intro g
    obtain ⟨k, hk⟩ := toSL3_surjective hψs (y⁻¹ * g * y)
    exact ⟨k, by rw [hρs, hk]; group⟩
  have hX : ∀ c : F, ∃ x : ↥(stab (puAmalgam h.le) z), (x : (puAmalgam h.le).Universal) ∈
      ZM (puAmalgam h.le) μ' ∧ ρs x = rootElt 0 1 c := by
    intro c
    have hmem : rootElt 0 1 c ∈ (natImage ψ (ZM (puAmalgam h.le) μ')).map
        (MulAut.conj y).toMonoidHom := by
      rw [hy]
      exact rootElt_mem_rootGroup 0 1 c
    obtain ⟨g, hg, hgc⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨a, haZ, hag⟩ := mem_natImage.mp hg
    exact ⟨a, haZ, by rw [hρs, hag, ← hgc]; rfl⟩
  have hκ : ∀ (k : ↥(stab (puAmalgam h.le) z)) (s : Subgroup (puAmalgam h.le).Universal),
      natSpan hψ y (s.map (MulAut.conj (k : (puAmalgam h.le).Universal)).toMonoidHom) =
        (natSpan hψ y s).map ((ρs k : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin := by
    intro k s
    rw [hρs]
    exact natSpan_map_conj hψ y k s
  obtain ⟨ρ₁, hρ₁, hρ₁R⟩ : ∃ ρ₁ : Vtx (puAmalgam h.le),
      (puAmalgam h.le).treeGraph.dist z ρ₁ ≤ 2 ∧
        ¬ Zv (puAmalgam h.le) ρ₁ ≤ radModSub (Vv (puAmalgam h.le) z) (Zloc h.le L z) h𝔷 := by
    by_contra hall
    push Not at hall
    apply hn
    have hVR : Vv (puAmalgam h.le) z ≤ radModSub (Vv (puAmalgam h.le) z) (Zloc h.le L z) h𝔷 :=
      iSup₂_le fun τ hτ => hall τ hτ
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact (hVR hg₁).2 g₂ hg₂
  obtain ⟨a, haW, haR⟩ := Set.not_subset.mp hρ₁R
  obtain ⟨w, hwV, haw⟩ : ∃ w ∈ Vv (puAmalgam h.le) z, ⁅a, w⁆ ∉ Zloc h.le L z := by
    by_contra hno
    push Not at hno
    exact haR ⟨zv_le_vv_of_dist h hρ₁ haW, hno⟩
  have hd₁ : (puAmalgam h.le).treeGraph.dist z ρ₁ = 2 := by
    by_contra hne
    apply haw
    have hc : w * a = a * w := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hz
      (zv_le_zm_of_dist_le_one h hz (by omega) haW)) w (hVQ hwV)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.symm]
    exact one_mem _
  have hρ₁M : IsMVtx _ ρ₁ := by
    rcases isMVtx_of_dist_le_two h hz hρ₁ with hM | hadj
    · exact hM
    · have := dist_eq_one_of_adj _ hadj
      omega
  have hzr₁ : (puAmalgam h.le).treeGraph.Adj z (geo _ z ρ₁ 1) := adj_geo_one _ (by omega)
  have hr₁ρ₁ : (puAmalgam h.le).treeGraph.Adj (geo _ z ρ₁ 1) ρ₁ := by
    have := adj_geo (puAmalgam h.le) (u := z) (w := ρ₁) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist z ρ₁ ≤ 1 + 1)] at this
  have hlab₁ : ⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z ≤
      Usup (puAmalgam h.le) z (geo _ z ρ₁ 1) ⊔ Zloc h.le L z := by
    rw [← zh_eq_usup_sup_zloc h hφ h464 hsq hz hzr₁]
    refine sup_le ?_ (zloc_le_zh h hfull hz hzr₁)
    calc ⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ≤ ⁅Zv (puAmalgam h.le) ρ₁, Qv _ (geo _ z ρ₁ 1)⁆ :=
          Subgroup.commutator_mono le_rfl (hVQ.trans (qv_le_qv _ h20 hz hzr₁))
      _ ≤ ZH _ (geo _ z ρ₁ 1) := h464 ρ₁ _ hρ₁M hr₁ρ₁.symm
  have hU : ∀ u : ↥(Uloc h.le L z),
      (u : (puAmalgam h.le).Universal) ∈ ⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z →
        natVec hψ u ∈ commN (natImage ψ (Qv (puAmalgam h.le) (geo _ z ρ₁ 1))) := by
    intro u hu
    refine (mem_usup_iff_natVec h hφ hz hzr₁ hψ u).mp ?_
    have hc : ∀ v ∈ Usup (puAmalgam h.le) z (geo _ z ρ₁ 1), ∀ ζ ∈ Zloc h.le L z,
        v * ζ = ζ * v := fun v hv ζ hζ =>
      Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hz hζ) v
        (puTrans_le_stab h.le _ z (usup_le_uloc h hfull hz hzr₁ hv))
    obtain ⟨v, hv, ζ, hζ, he⟩ := exists_mul_of_mem_sup_of_commute hc (hlab₁ hu)
    have hζU : ζ ∈ Uloc h.le L z := by
      have e : ζ = v⁻¹ * u := by rw [he]; group
      rw [e]
      exact (Uloc h.le L z).mul_mem ((Uloc h.le L z).inv_mem (usup_le_uloc h hfull hz hzr₁ hv))
        u.2
    have hζ1 : ζ = 1 := by
      have : ζ ∈ Uloc h.le L z ⊓ Zloc h.le L z := ⟨hζU, hζ⟩
      rwa [uloc_inf_zloc h hfull z, Subgroup.mem_bot] at this
    rw [he, hζ1, mul_one]
    exact hv
  have hκ1 : Module.finrank F
        (natSpan hψ y (⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z)) = 1 ∨
      Module.finrank F
        (natSpan hψ y (⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z)) = 2 := by
    have hup : Module.finrank F
        (natSpan hψ y (⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z)) ≤ 2 := by
      have h1 := Submodule.finrank_mono (natSpan_le_map hψ y hU)
      have h2 := Submodule.finrank_map_le (((y : SL3 F) : Matrix (Fin 3) (Fin 3) F).mulVecLin)
        (commN (natImage ψ (Qv (puAmalgam h.le) (geo _ z ρ₁ 1))))
      have h3 : Module.finrank F
          (commN (natImage ψ (Qv (puAmalgam h.le) (geo _ z ρ₁ 1)))) = 2 := by
        obtain ⟨hf, hcf⟩ := fixN_natImage_qv h hφ h464 hsq hz hzr₁ hψ
        rw [hcf, hf]
      omega
    have hpZ : ⁅a, w⁆ ∈ ZM (puAmalgam h.le) z :=
      (sup_le ((usup_le_uloc h hfull hz hzr₁).trans (uloc_le_zm h hfull hz))
        (zloc_le_zm h hfull hz)) (hlab₁ (Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator haW hwV)))
    obtain ⟨u, hu, ζ, hζ, he⟩ := exists_uloc_mul_zloc h hfull hz hpZ
    have hulab : u ∈ ⁅Zv (puAmalgam h.le) ρ₁, Vv _ z⁆ ⊔ Zloc h.le L z := by
      have e : u = ⁅a, w⁆ * ζ⁻¹ := by rw [he]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator haW hwV))
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hζ))
    have hu1 : (⟨u, hu⟩ : ↥(Uloc h.le L z)) ≠ 1 := by
      intro h1
      apply haw
      have h1' : u = 1 := congrArg Subtype.val h1
      rw [he, h1', one_mul]
      exact hζ
    have hlow := Submodule.one_le_finrank_iff.mpr (natSpan_ne_bot hψ y (u := ⟨u, hu⟩) hulab hu1)
    omega
  have hgen : Vv (puAmalgam h.le) z = ⨆ i : ↥{τ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist z τ ≤ 2}, Zv (puAmalgam h.le) i.1 := by
    rw [show Vv (puAmalgam h.le) z = Vi _ z 2 from rfl, Vi, iSup_subtype']
  have hKP : ∀ i j : ↥{τ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist z τ ≤ 2},
      ∀ a ∈ Zv (puAmalgam h.le) i.1, ∀ b ∈ Zv (puAmalgam h.le) j.1, ⁅a, b⁆ ∉ Zloc h.le L z →
        ⁅Zv (puAmalgam h.le) i.1, Vv _ z⁆ ⊔ Zloc h.le L z =
          ⁅Zv (puAmalgam h.le) j.1, Vv _ z⁆ ⊔ Zloc h.le L z :=
    fun i j a ha b hb hab =>
      lab_eq_of_commutator_not_mem h hφ hC hb4 hS h464 hsq hz i.2 j.2 ha hb hab
  have hZs : ZM (puAmalgam h.le) μ' ≤ stab _ z := zm_le_stab_of_isCritical _ h20 hb0 hc'
  have hX𝔷 : ZM (puAmalgam h.le) μ' ≤ Subgroup.normalizer (Zloc h.le L z : Set _) :=
    hZs.trans hZn
  have hdk : ∀ {k : (puAmalgam h.le).Universal}, k ∈ stab (puAmalgam h.le) z →
      ∀ {τ : Vtx (puAmalgam h.le)}, (puAmalgam h.le).treeGraph.dist z τ ≤ 2 →
        (puAmalgam h.le).treeGraph.dist z (k • τ) ≤ 2 := by
    intro k hk τ hτ
    rw [tdist_comm, dist_smul_of_smul_eq _ ((mem_stab _).mp hk), tdist_comm]
    exact hτ
  have hperm : ∀ x ∈ ZM (puAmalgam h.le) μ',
      ∀ i : ↥{τ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist z τ ≤ 2},
        ∃ j : ↥{τ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist z τ ≤ 2},
          (Zv (puAmalgam h.le) i.1).map (MulAut.conj x).toMonoidHom = Zv (puAmalgam h.le) j.1 ∧
            ⁅Zv (puAmalgam h.le) j.1, Vv _ z⁆ ⊔ Zloc h.le L z =
              (⁅Zv (puAmalgam h.le) i.1, Vv _ z⁆ ⊔ Zloc h.le L z).map
                (MulAut.conj x).toMonoidHom :=
    fun x hx i => ⟨⟨x • i.1, hdk (hZs hx) i.2⟩, (zv_smul _ x i.1).symm,
      commutator_vv_sup_zloc_smul h (hZs hx) i.1⟩
  obtain ⟨𝒪, hO, hO1', hO2⟩ := exists_regular_labels ρs hρsurj hX (natSpan hψ y) hκ hκ1
  have hO1 : ∀ s ∈ 𝒪, ∃ i : ↥{τ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist z τ ≤ 2},
      ⁅Zv (puAmalgam h.le) i.1, Vv _ z⁆ ⊔ Zloc h.le L z = s ∧
        ¬ Zv (puAmalgam h.le) i.1 ≤ radModSub (Vv (puAmalgam h.le) z) (Zloc h.le L z) h𝔷 := by
    intro s hs
    obtain ⟨k, rfl⟩ := hO1' s hs
    refine ⟨⟨(k : (puAmalgam h.le).Universal) • ρ₁, hdk k.2 hρ₁⟩,
      commutator_vv_sup_zloc_smul h k.2 ρ₁, ?_⟩
    show ¬ Zv (puAmalgam h.le) ((k : (puAmalgam h.le).Universal) • ρ₁) ≤ _
    rw [zv_smul]
    exact not_map_conj_le_radModSub (stab_le_normalizer_vv h z k.2) (hZn k.2)
      (zv_le_vv_of_dist h hρ₁) hρ₁R
  have hcount := two_pow_card_le_relIndex_centralizer h𝔷
    (fun i : ↥{τ : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist z τ ≤ 2} =>
      Zv (puAmalgam h.le) i.1) (fun i => zv_le_vv_of_dist h i.2) hgen
    (fun i => ⁅Zv (puAmalgam h.le) i.1, Vv _ z⁆ ⊔ Zloc h.le L z) hKP hX𝔷 hperm 𝒪 hO1 hO2
  have hup := relIndex_centralizer_zm_lt h hb4 hS hc'
  have h2O : 2 ^ (Fintype.card F * (Fintype.card F - 1)) ≤ 2 ^ 𝒪.card :=
    Nat.pow_le_pow_right (by norm_num) hO
  exact absurd ((pow_four_le_two_pow_mul hq).trans (h2O.trans hcount)) (not_le.mpr hup)

end Count

end CFSG.Quasithin.MS93.S46
