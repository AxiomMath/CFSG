module

public import CFSG.Quasithin.MS93.S4A445
public import CFSG.Quasithin.MS93.S4A44Q

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Geo

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem geo_of_dist_eq_add {u v w : Vtx X}
    (h : X.treeGraph.dist u w = X.treeGraph.dist u v + X.treeGraph.dist v w) {k : ℕ}
    (hk : k ≤ X.treeGraph.dist v w) :
    geo X u w (X.treeGraph.dist u v + k) = geo X v w k := by
  have h1 := dist_geo X hk
  have h2 := dist_geo_right X hk
  have t1 := dist_triangle X u v (geo X v w k)
  have t2 := dist_triangle X u (geo X v w k) w
  symm
  apply eq_geo_of_dist X (by omega)
  omega

theorem geo_eq_of_dist_eq_add {u v w : Vtx X}
    (h : X.treeGraph.dist u w = X.treeGraph.dist u v + X.treeGraph.dist v w) {k : ℕ}
    (hk : k ≤ X.treeGraph.dist u v) : geo X u w k = geo X u v k := by
  have hv : v = geo X u w (X.treeGraph.dist u v) := eq_geo X (by omega)
  rw [hv, geo_geo X hk (by omega)]

end Geo

section Plane

open Module

variable {F : Type} [Field F]

theorem finrank_ker_eq_two {f : (Fin 3 → F) →ₗ[F] F} (hf : f ≠ 0) :
    finrank F (LinearMap.ker f) = 2 := by
  have hsurj : LinearMap.range f = ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf (LinearMap.ext hcon)
    rw [eq_top_iff]
    intro x _
    refine ⟨(x / f v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  omega

theorem exists_plane_not_mem {r : Fin 3 → F} (hr : r ≠ 0) :
    ∃ K : Submodule F (Fin 3 → F), finrank F K = 2 ∧ r ∉ K := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hr (funext hcon)
  refine ⟨LinearMap.ker (LinearMap.proj i), finrank_ker_eq_two ?_, ?_⟩
  · intro h0
    exact hi (by simpa using LinearMap.congr_fun h0 r)
  · simpa using hi

theorem exists_plane_not_mem_two {r c : Fin 3 → F} (hr : r ≠ 0) (hc : c ≠ 0) :
    ∃ K : Submodule F (Fin 3 → F), finrank F K = 2 ∧ r ∉ K ∧ c ∉ K := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hr (funext hcon)
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hc (funext hcon)
  by_cases hci : c i ≠ 0
  · refine ⟨LinearMap.ker (LinearMap.proj i), finrank_ker_eq_two ?_, by simpa using hi,
      by simpa using hci⟩
    intro h0
    exact hi (by simpa using LinearMap.congr_fun h0 r)
  push Not at hci
  by_cases hrj : r j ≠ 0
  · refine ⟨LinearMap.ker (LinearMap.proj j), finrank_ker_eq_two ?_, by simpa using hrj,
      by simpa using hj⟩
    intro h0
    exact hj (by simpa using LinearMap.congr_fun h0 c)
  push Not at hrj
  refine ⟨LinearMap.ker ((LinearMap.proj i : (Fin 3 → F) →ₗ[F] F) + LinearMap.proj j),
    finrank_ker_eq_two ?_, ?_, ?_⟩
  · intro h0
    have := LinearMap.congr_fun h0 r
    simp [hrj] at this
    exact hi this
  · simp [hrj, hi]
  · simp [hci, hj]

end Plane

section Conj

variable {G : Type*} [Group G]

theorem conjCl_map_conj_of_mem {H K : Subgroup G} {t : G} (ht : t ∈ H) :
    conjCl H (K.map (MulAut.conj t).toMonoidHom) = conjCl H K := by
  refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup₂_le fun g hg => ?_)
  · rw [Subgroup.map_map, show (MulAut.conj g).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (g * t)).toMonoidHom by ext x; simp [mul_assoc]]
    exact S4A.map_conj_le_conjCl (H.mul_mem hg ht)
  · have : K.map (MulAut.conj g).toMonoidHom =
        (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (g * t⁻¹)).toMonoidHom := by
      rw [Subgroup.map_map, show (MulAut.conj (g * t⁻¹)).toMonoidHom.comp
        (MulAut.conj t).toMonoidHom = (MulAut.conj g).toMonoidHom by ext x; simp [mul_assoc]]
    rw [this]
    exact S4A.map_conj_le_conjCl (H.mul_mem hg (H.inv_mem ht))

end Conj

section NatConj

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]

namespace E44

theorem natImage_map_conj (ψ : ↥K →* ↥(StatedSL 3 F)) (t : ↥K) (A : Subgroup G) :
    natImage ψ (A.map (MulAut.conj (t : G)).toMonoidHom) =
      (natImage ψ A).map (MulAut.conj (toSL3 ψ t)).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_natImage]
  constructor
  · rintro ⟨a, ⟨b, hb, hba⟩, rfl⟩
    have hbK : b ∈ K := by
      have : b = (t : G)⁻¹ * a * t := by rw [← hba]; group
      rw [this]
      exact K.mul_mem (K.mul_mem (K.inv_mem t.2) a.2) t.2
    refine ⟨toSL3 ψ ⟨b, hbK⟩, ⟨⟨b, hbK⟩, hb, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hba]
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨t * c * t⁻¹, ⟨c, hc, by simp⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]

end E44

end NatConj

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem exists_adj_commN_eq (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {K' : Submodule F (Fin 3 → F)} (hK' : Module.finrank F K' = 2) :
    ∃ γ, (puAmalgam h.le).treeGraph.Adj α γ ∧ commN (natImage ψ (Qv (puAmalgam h.le) γ)) = K' := by
  obtain ⟨β, hαβ⟩ := exists_adj _ α
  have hW := finrank_commN_qv h hφ hC hb hα hαβ hψ
  obtain ⟨g₀, hg₀⟩ :=
    LinearFlag.exists_map_flagSpace_eq (commN (natImage ψ (Qv (puAmalgam h.le) β)))
  obtain ⟨g₁, hg₁⟩ := LinearFlag.exists_map_flagSpace_eq K'
  rw [hW] at hg₀
  rw [hK'] at hg₁
  obtain ⟨t, ht⟩ := toSL3_surjective hψs (g₁ * g₀⁻¹)
  refine ⟨(t : (puAmalgam h.le).Universal) • β, ?_, ?_⟩
  · have := (adj_smul _ (t : (puAmalgam h.le).Universal) _ _).mpr hαβ
    rwa [(mem_stab _).mp t.2] at this
  · rw [qv_smul, E44.natImage_map_conj, commN_map_conj, ht, ← hg₁, ← hg₀, ← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro v
    change ((g₁ * g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g₀ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((g₁ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end Coord

section Commutator

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem exists_commutator_conjCl_le (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') {γ : Vtx (puAmalgam h.le)}
    (hαγ : (puAmalgam h.le).treeGraph.Adj α γ)
    (hγN : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α γ : Set (puAmalgam h.le).Universal)) :
    ∃ (W : Subgroup (puAmalgam h.le).Universal) (x : Vtx (puAmalgam h.le)),
      IsCritical (puAmalgam h.le) x (geo _ α' α 4) ∧ ZM (puAmalgam h.le) x ≤ W ∧
      W ≤ Qv (puAmalgam h.le) (geo _ α' α 5) ∧
      ⁅W, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≤ Usup (puAmalgam h.le) α γ ∧
      ⁅W, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≤ Dloc h.le L (geo _ α' α 6) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hd
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hdα : ∀ j, j ≤ critDist (puAmalgam h.le) →
      (puAmalgam h.le).treeGraph.dist α (geo _ α' α j) = critDist (puAmalgam h.le) - j :=
    fun j hj => by rw [tdist_comm, dist_geo_right _ (by omega), hd']
  have hdgg : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) →
      (puAmalgam h.le).treeGraph.dist (geo _ α' α i) (geo _ α' α j) = j - i :=
    fun i j hij hj => dist_geo_geo _ hij (by omega)
  have hMp : ∀ j, j ≤ critDist (puAmalgam h.le) → Even j →
      IsMVtx (puAmalgam h.le) (geo _ α' α j) :=
    fun j hj he => (isMVtx_geo _ (by omega)).mpr ⟨fun _ => he, fun _ => hα'⟩
  obtain ⟨t, ht, htU, htZ⟩ := h444 α α' hc hs γ hαγ hγN
  have htα : t • α = α := (mem_stab _).mp ht
  have hδ : IsMVtx (puAmalgam h.le) (t • geo _ α α' 2) :=
    (isMVtx_smul _ _ _).mpr (isMVtx_geo_two _ h.hyp20 hb0 hc)
  have hδα : (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) α = 2 := by
    have h2 : (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) (t • α) = 2 := by
      rw [dist_smul, tdist_comm, dist_geo _ (by omega)]
    rwa [htα] at h2
  have hβ'δ : (puAmalgam h.le).treeGraph.Adj (t • geo _ α α' 1) (t • geo _ α α' 2) :=
    (adj_smul _ t _ _).mpr (adj_geo _ (i := 1) (by omega))
  have hαβ' : (puAmalgam h.le).treeGraph.Adj α (t • geo _ α α' 1) := by
    have := (adj_smul _ t _ _).mpr (adj_geo_one_of_isCritical _ hb0 hc)
    rwa [htα] at this
  have hZδ : ¬ ZM (puAmalgam h.le) (t • geo _ α α' 2) ≤ Qv _ (geo _ α' α 2) := by
    rw [zm_smul]; exact htZ
  have hdδ : ∀ j, 2 ≤ j → j ≤ critDist (puAmalgam h.le) →
      (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) (geo _ α' α j) =
        critDist (puAmalgam h.le) - j + 2 := by
    intro j hj2 hjb
    have hy : (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) (geo _ α' α 2) =
        critDist (puAmalgam h.le) := by
      have t1 := dist_triangle _ (t • geo _ α α' 2) α (geo _ α' α 2)
      rw [hδα, hdα 2 (by omega)] at t1
      by_contra hne
      exact hZδ (zm_le_qv_of_dist_lt _ hδ (by omega))
    have t1 := dist_triangle _ (t • geo _ α α' 2) α (geo _ α' α j)
    have t2 := dist_triangle _ (t • geo _ α α' 2) (geo _ α' α j) (geo _ α' α 2)
    rw [hδα, hdα j hjb] at t1
    rw [hy, tdist_comm _ (geo _ α' α j), hdgg 2 j hj2 hjb] at t2
    omega
  have hcδ : IsCritical (puAmalgam h.le) (t • geo _ α α' 2) (geo _ α' α 2) :=
    ⟨hδ, by rw [hdδ 2 le_rfl (by omega)]; omega, hZδ⟩
  have hsplit : (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) (geo _ α' α 2) =
      (puAmalgam h.le).treeGraph.dist (t • geo _ α α' 2) α +
        (puAmalgam h.le).treeGraph.dist α (geo _ α' α 2) := by
    rw [hdδ 2 le_rfl (by omega), hδα, hdα 2 (by omega)]
    omega
  have hgeoδ : ∀ j, j ≤ critDist (puAmalgam h.le) - 2 →
      geo (puAmalgam h.le) (t • geo _ α α' 2) (geo _ α' α 2) (2 + j) = geo _ α α' j := by
    intro j hj
    have h1 := geo_of_dist_eq_add _ hsplit (k := j) (by rw [hdα 2 (by omega)]; omega)
    rw [hδα] at h1
    rw [h1]
    have hy : geo (puAmalgam h.le) α' α 2 = geo _ α α' (critDist (puAmalgam h.le) - 2) := by
      have := geo_symm (puAmalgam h.le) (u := α) (w := α') (i := critDist (puAmalgam h.le) - 2)
        (by omega)
      rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
        at this
    rw [hy, geo_geo _ hj (by omega)]
  have hgeoδ2 : geo (puAmalgam h.le) (t • geo _ α α' 2) (geo _ α' α 2) 2 = α := by
    have := hgeoδ 0 (by omega)
    rwa [add_zero, geo_zero] at this
  have hsδ : IsStraight (puAmalgam h.le) (t • geo _ α α' 2) (geo _ α' α 2) := by
    intro i hi0 hib
    rw [hdδ 2 le_rfl (by omega)] at hib
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi2
    · refine ⟨t, ?_, ?_⟩
      · rw [show 2 * 1 = 2 from rfl, hgeoδ2]; exact ht
      · rw [show 2 * 1 + 2 = 2 + 2 from rfl, hgeoδ 2 (by omega), show 2 * 1 - 2 = 0 from rfl,
          geo_zero]
    · obtain ⟨g, hg, hge⟩ := hs (i - 1) (by omega) (by rw [hd]; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [show 2 * i = 2 + 2 * (i - 1) by omega, hgeoδ _ (by omega)]; exact hg
      · rw [show 2 * i + 2 = 2 + (2 * (i - 1) + 2) by omega, hgeoδ _ (by omega),
          show 2 * i - 2 = 2 + (2 * (i - 1) - 2) by omega, hgeoδ _ (by omega)]
        exact hge
  obtain ⟨γ', hγ'a, hγ'N⟩ := exists_adj_not_le_normalizer_usup h hφ hC hb hcδ
  obtain ⟨t', ht', -, ht'Z⟩ := h444 _ _ hcδ hsδ γ' hγ'a hγ'N
  rw [hgeoδ2] at ht'Z
  have hgy : geo (puAmalgam h.le) (geo _ α' α 2) (t • geo _ α α' 2) 2 = geo _ α' α 4 := by
    have hsplit' : (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) (t • geo _ α α' 2) =
        (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) α +
          (puAmalgam h.le).treeGraph.dist α (t • geo _ α α' 2) := by
      rw [tdist_comm, hsplit, tdist_comm _ α (geo _ α' α 2), tdist_comm _ α]
      omega
    rw [geo_eq_of_dist_eq_add _ hsplit' (by rw [tdist_comm, hdα 2 (by omega)]; omega)]
    have hsplit'' : (puAmalgam h.le).treeGraph.dist α' α =
        (puAmalgam h.le).treeGraph.dist α' (geo _ α' α 2) +
          (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) α := (dist_geo_add _ (by omega)).symm
    have := geo_of_dist_eq_add _ hsplit'' (k := 2)
      (by rw [tdist_comm, hdα 2 (by omega)]; omega)
    rw [dist_geo _ (by omega)] at this
    exact this.symm
  rw [hgy] at ht'Z
  have hx : IsMVtx (puAmalgam h.le) (t' • α) := (isMVtx_smul _ _ _).mpr hα
  have hZx : ¬ ZM (puAmalgam h.le) (t' • α) ≤ Qv _ (geo _ α' α 4) := by
    rw [zm_smul]; exact ht'Z
  have hxδ : (puAmalgam h.le).treeGraph.dist (t' • α) (t • geo _ α α' 2) = 2 := by
    have h2 : (puAmalgam h.le).treeGraph.dist (t' • α) (t' • (t • geo _ α α' 2)) = 2 := by
      rw [dist_smul, tdist_comm, hδα]
    rwa [(mem_stab _).mp ht'] at h2
  have hdδ4 := hdδ 4 (by omega) (by omega)
  have hdxz : (puAmalgam h.le).treeGraph.dist (t' • α) (geo _ α' α 4) =
      critDist (puAmalgam h.le) := by
    have t1 := dist_triangle _ (t' • α) (t • geo _ α α' 2) (geo _ α' α 4)
    rw [hxδ, hdδ4] at t1
    by_contra hne
    exact hZx (zm_le_qv_of_dist_lt _ hx (by omega))
  have hcx : IsCritical (puAmalgam h.le) (t' • α) (geo _ α' α 4) := ⟨hx, hdxz, hZx⟩
  have hz := hMp 4 (by omega) ⟨2, rfl⟩
  have hxW : ZM (puAmalgam h.le) (t' • α) ≤
      conjCl (stab (puAmalgam h.le) (t • geo _ α α' 2)) (ZM (puAmalgam h.le) α) := by
    rw [zm_smul]; exact map_conj_le_conjCl ht'
  have hWV : conjCl (stab (puAmalgam h.le) (t • geo _ α α' 2)) (ZM (puAmalgam h.le) α) ≤
      Vv _ (t • geo _ α α' 2) := by
    refine conjCl_le_of_le_normalizer ?_ (stab_le_normalizer_vv h _)
    rw [← zv_of_isMVtx _ hα]
    exact zv_le_vv h hδα.le
  have hWQ : conjCl (stab (puAmalgam h.le) (t • geo _ α α' 2)) (ZM (puAmalgam h.le) α) ≤
      Qv _ (geo _ α' α 5) :=
    hWV.trans (vv_le_qv_of_dist h hδ (by rw [hdδ 5 (by omega) (by omega)]; omega))
  have hgx : geo (puAmalgam h.le) (t' • α) (geo _ α' α 4) 2 = t • geo _ α α' 2 := by
    symm
    apply eq_geo_of_dist _ hxδ
    rw [hxδ, hdδ4, hdxz]
    omega
  have hZzδ : ZM (puAmalgam h.le) (geo _ α' α 4) ≤ Qv _ (t • geo _ α α' 2) :=
    zm_le_qv_of_dist_lt _ hz (by rw [tdist_comm, hdδ4]; omega)
  have hLX := commutator_conjCl_le_dloc_of_le h hφ hC hb hV (ms22_iii _ h.hyp20 hb0 hC hcx)
    (h441 _ _ hcx) (zm_le_vv h hz) (by rw [hgx]; exact hZzδ)
  rw [hgx, zm_smul, conjCl_map_conj_of_mem ht'] at hLX
  have hLQ := commutator_conjCl_le_of_le_dloc h hfull hb hδ hδα hZzδ hLX
  refine ⟨_, _, hcx, hxW, hWQ, ?_, ?_⟩
  · refine hLQ.trans (inf_le_left.trans ?_)
    have hUβ' : Usup (puAmalgam h.le) α (t • geo _ α α' 1) = Usup (puAmalgam h.le) α γ := by
      have := usup_smul (puAmalgam h.le) t α (geo _ α α' 1)
      rw [htα] at this
      rw [this, htU]
    rw [← hUβ', Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h.hyp20 hδ hβ'δ.symm)
  · have hY := commutator_zm_vv_le_dloc_geo h hφ hC hb hV h441 hz hδ
      (by rw [tdist_comm, hdδ4]; omega)
    have hg6 : geo (puAmalgam h.le) (geo _ α' α 4) (t • geo _ α α' 2) 2 = geo _ α' α 6 := by
      have hsplit4 : (puAmalgam h.le).treeGraph.dist (geo _ α' α 4) (t • geo _ α α' 2) =
          (puAmalgam h.le).treeGraph.dist (geo _ α' α 4) (geo _ α' α 6) +
            (puAmalgam h.le).treeGraph.dist (geo _ α' α 6) (t • geo _ α α' 2) := by
        rw [tdist_comm _ (geo _ α' α 4), hdδ4, hdgg 4 6 (by omega) (by omega), tdist_comm,
          hdδ 6 (by omega) (by omega)]
        omega
      rw [geo_eq_of_dist_eq_add _ hsplit4 (by rw [hdgg 4 6 (by omega) (by omega)])]
      have h46 := geo_dist (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 6)
      rw [hdgg 4 6 (by omega) (by omega)] at h46
      exact h46
    rw [hg6] at hY
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hWV).trans hY

end Commutator

section Card

variable {G : Type*} [Group G]

theorem card_mul_card_le_card_sup {A B : Subgroup G} [Finite ↥(A ⊔ B)] (hAB : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ heq
  have heq' : (a : G) * b = a' * b' := congrArg Subtype.val heq
  have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [heq']
      _ = b' * (b : G)⁻¹ := by group
  have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have ha : (a : G) = a' := by
    calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one]
  have hb : (b : G) = b' := by
    have := heq'
    rw [ha] at this
    exact mul_left_cancel this
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

end Card

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem exists_rgamma (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') {γ : Vtx (puAmalgam h.le)}
    (hαγ : (puAmalgam h.le).treeGraph.Adj α γ)
    (hRγ : ¬ ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Usup (puAmalgam h.le) α γ) :
    ∃ (Rγ : Subgroup (puAmalgam h.le).Universal) (x : Vtx (puAmalgam h.le)),
      IsCritical (puAmalgam h.le) x (geo _ α' α 4) ∧
      ZM (puAmalgam h.le) x ≤ Qv (puAmalgam h.le) (geo _ α' α 5) ∧
      ⁅ZM (puAmalgam h.le) x, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≤ Rγ ∧
      ⁅ZM (puAmalgam h.le) x, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≠ ⊥ ∧
      Fintype.card F ≤ Nat.card ↥⁅ZM (puAmalgam h.le) x, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ∧
      Rγ ≤ Usup (puAmalgam h.le) α γ ⊓ (Uloc h.le L α ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal)) ∧
      Rγ ≤ Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5) ∧
      Rγ ≤ Dloc h.le L (geo _ α' α 6) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hc.2.1
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZ2 : IsPGroup 2 ↥(ZM (puAmalgam h.le) α') :=
    (S46.isPGroup_qv_of_isMVtx h hα').to_le (zm_le_qv_self _ hα' hb0)
  have hγN : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α γ : Set (puAmalgam h.le).Universal) :=
    fun hN => hRγ (commutator_uloc_le_usup_of_le_normalizer h hφ hC hb hα hαγ hZs hZ2 hN)
  obtain ⟨W, x, hcx, hxW, hWQ, hWU, hWD⟩ :=
    exists_commutator_conjCl_le h hφ hC hb6 hV h441 h444 hc hs hαγ hγN
  have hz : IsMVtx (puAmalgam h.le) (geo _ α' α 4) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => ⟨2, rfl⟩, fun _ => hα'⟩
  have hz5 : (puAmalgam h.le).treeGraph.Adj (geo _ α' α 4) (geo _ α' α 5) :=
    adj_geo _ (by omega)
  have hRZ : ⁅W, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≤ ZM (puAmalgam h.le) (geo _ α' α 4) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hWQ.trans ((qv_le_stab_of_adj _ hz5.symm).trans (stab_le_normalizer_zm _ _)))
  have hZC : ZM (puAmalgam h.le) (geo _ α' α 4) ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
    (zm_le_qv_of_dist_lt _ hz (by rw [tdist_comm, dist_geo _ (by omega)]; omega)).trans
      (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hα'))
  have hZxs : ZM (puAmalgam h.le) (geo _ α' α 4) ≤ stab _ x :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hcx
  have hne : ⁅ZM (puAmalgam h.le) x, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ≠ ⊥ :=
    ms22_ii _ h.hyp20 hb0 hC hcx
  have hcard := le_card_commutator_uloc h hφ hcx.1 (adj_geo_one_of_isCritical _ hb0 hcx)
    (zm_le_qv_geo_one _ h.hyp20 hb0 hcx)
    (by rwa [← commutator_zm_eq_uloc h hfull hcx.1 hZxs])
  rw [← commutator_zm_eq_uloc h hfull hcx.1 hZxs] at hcard
  refine ⟨_, x, hcx, hxW.trans hWQ, Subgroup.commutator_mono hxW le_rfl, hne, hcard,
    le_inf hWU (le_inf (hWU.trans (usup_le_uloc h hφ hα hαγ)) (hRZ.trans hZC)), ?_, hWD⟩
  rw [Subgroup.commutator_comm, Usup, zv_of_isMVtx _ hz]
  exact Subgroup.commutator_mono le_rfl hWQ

theorem inf_centralizer_eq_usup (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    (h444 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      IsStraight (puAmalgam h.le) δ δ' → Concl444 h.le δ δ')
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') :
    Uloc h.le L α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) =
        Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5) ∧
      Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5) ≤ Dloc h.le L (geo _ α' α 6) ∧
      ∃ x₁ x₂ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) x₁ (geo _ α' α 4) ∧
        IsCritical (puAmalgam h.le) x₂ (geo _ α' α 4) ∧
        ZM (puAmalgam h.le) x₁ ≤ Qv (puAmalgam h.le) (geo _ α' α 5) ∧
        ZM (puAmalgam h.le) x₂ ≤ Qv (puAmalgam h.le) (geo _ α' α 5) ∧
        ⁅ZM (puAmalgam h.le) x₁, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ ⊓
          ⁅ZM (puAmalgam h.le) x₂, ZM (puAmalgam h.le) (geo _ α' α 4)⁆ = ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  set C := Uloc h.le L α ⊓
    Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) with hCdef
  have hRU : ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Uloc h.le L α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans (stab_le_normalizer_uloc h α))
  have hRZ : ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ ZM (puAmalgam h.le) α' := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((uloc_le_zm h hfull hα).trans
      ((zm_le_stab_right _ h.hyp20 hb0 hC hc).trans (stab_le_normalizer_zm _ _)))
  have hZab : ZM (puAmalgam h.le) α' ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
    (zm_le_centralizer_qv _ h.hyp20 hα').trans (Subgroup.centralizer_le (zm_le_qv_self _ hα' hb0))
  have hRC : ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ C := le_inf hRU (hRZ.trans hZab)
  have hRne : ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hα hZs]
    exact ms22_ii _ h.hyp20 hb0 hC hc
  obtain ⟨u₀, hu₀, hu₀1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hRne
  set r := natVec hψ ⟨u₀, hRU hu₀⟩ with hrdef
  have hr0 : r ≠ 0 := by
    intro h0
    apply hu₀1
    have : (⟨u₀, hRU hu₀⟩ : ↥(Uloc h.le L α)) = 1 :=
      natVec_injective hψ (by rw [← hrdef, h0, natVec_one])
    exact congrArg Subtype.val this
  have hrC : r ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')) :=
    (mem_centralizer_iff_natVec hψ hZs _).mp (hRC hu₀).2
  have hC2 : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤ 2 := by
    have h3 := Submodule.finrank_le (fixN (natImage ψ (ZM (puAmalgam h.le) α')))
    rw [Module.finrank_fin_fun] at h3
    by_contra hcon
    have htop : fixN (natImage ψ (ZM (puAmalgam h.le) α')) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    exact (ms22_iii _ h.hyp20 hb0 hC hc).2.2 (le_qv_of_fixN_eq_top h hφ hα hψ hZs htop)
  have hgam : ∀ K' : Submodule F (Fin 3 → F), Module.finrank F K' = 2 → r ∉ K' →
      ∃ γ, (puAmalgam h.le).treeGraph.Adj α γ ∧
        commN (natImage ψ (Qv (puAmalgam h.le) γ)) = K' ∧
        ¬ ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Usup (puAmalgam h.le) α γ := by
    intro K' hK' hrK'
    obtain ⟨γ, hαγ, hγK⟩ := exists_adj_commN_eq h hφ hC hb hα hψs hψ hK'
    refine ⟨γ, hαγ, hγK, fun hle => hrK' ?_⟩
    rw [← hγK]
    exact (mem_usup_iff_natVec h hφ hα hαγ hψ _).mp (hle hu₀)
  obtain ⟨K₁, hK₁, hrK₁⟩ := exists_plane_not_mem hr0
  obtain ⟨γ₁, hαγ₁, hγ₁K, hRγ₁⟩ := hgam K₁ hK₁ hrK₁
  obtain ⟨R₁, x₁, hcx₁, hx₁Q, hx₁R, hx₁ne, hx₁q, hR₁C, hR₁U, hR₁D⟩ :=
    exists_rgamma h hφ hC hb6 hV h441 h444 hc hs hαγ₁ hRγ₁
  obtain ⟨u₁, hu₁, hu₁1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (ne_bot_of_le_ne_bot hx₁ne hx₁R)
  have hu₁U : u₁ ∈ Uloc h.le L α := (hR₁C hu₁).2.1
  set c := natVec hψ ⟨u₁, hu₁U⟩ with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu₁1
    have : (⟨u₁, hu₁U⟩ : ↥(Uloc h.le L α)) = 1 :=
      natVec_injective hψ (by rw [← hcdef, h0, natVec_one])
    exact congrArg Subtype.val this
  have hcK₁ : c ∈ K₁ := by
    rw [← hγ₁K]
    exact (mem_usup_iff_natVec h hφ hα hαγ₁ hψ _).mp (hR₁C hu₁).1
  have hcC : c ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')) :=
    (mem_centralizer_iff_natVec hψ hZs _).mp (hR₁C hu₁).2.2
  obtain ⟨K₂, hK₂, hrK₂, hcK₂⟩ := exists_plane_not_mem_two hr0 hc0
  obtain ⟨γ₂, hαγ₂, hγ₂K, hRγ₂⟩ := hgam K₂ hK₂ hrK₂
  obtain ⟨R₂, x₂, hcx₂, hx₂Q, hx₂R, hx₂ne, hx₂q, hR₂C, hR₂U, hR₂D⟩ :=
    exists_rgamma h hφ hC hb6 hV h441 h444 hc hs hαγ₂ hRγ₂
  have hline : K₁ ⊓ fixN (natImage ψ (ZM (puAmalgam h.le) α')) = Submodule.span F {c} := by
    symm
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨hcK₁, hcC⟩
    · have hlt : K₁ ⊓ fixN (natImage ψ (ZM (puAmalgam h.le) α')) <
          fixN (natImage ψ (ZM (puAmalgam h.le) α')) :=
        lt_of_le_of_ne inf_le_right fun heq => hrK₁ (heq ▸ hrC).1
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [finrank_span_singleton hc0]
      omega
  have hdisj : ∀ u ∈ Usup (puAmalgam h.le) α γ₁ ⊓ C, u ∈ Usup (puAmalgam h.le) α γ₂ → u = 1 := by
    intro u hu1 hu2
    have huU : u ∈ Uloc h.le L α := hu1.2.1
    have hv1 : natVec hψ ⟨u, huU⟩ ∈ K₁ := by
      rw [← hγ₁K]; exact (mem_usup_iff_natVec h hφ hα hαγ₁ hψ _).mp hu1.1
    have hv2 : natVec hψ ⟨u, huU⟩ ∈ K₂ := by
      rw [← hγ₂K]; exact (mem_usup_iff_natVec h hφ hα hαγ₂ hψ _).mp hu2
    have hvC := (mem_centralizer_iff_natVec hψ hZs ⟨u, huU⟩).mp hu1.2.2
    have hvl : natVec hψ ⟨u, huU⟩ ∈ Submodule.span F {c} := hline ▸ ⟨hv1, hvC⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvl
    have ha0 : a = 0 := by
      by_contra ha0
      apply hcK₂
      have : c = a⁻¹ • natVec hψ ⟨u, huU⟩ := by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [this]
      exact K₂.smul_mem _ hv2
    have hv0 : natVec hψ ⟨u, huU⟩ = 0 := by rw [← ha, ha0, zero_smul]
    have : (⟨u, huU⟩ : ↥(Uloc h.le L α)) = 1 := natVec_injective hψ (by rw [hv0, natVec_one])
    exact congrArg Subtype.val this
  have hR₁₂ : R₁ ⊓ R₂ = ⊥ := by
    rw [eq_bot_iff]
    intro u ⟨hu1, hu2⟩
    exact (Subgroup.mem_bot).mpr (hdisj u ⟨(hR₁C hu1).1, (hR₁C hu1).2⟩ (hR₂C hu2).1)
  have hfinU : Finite ↥(Uloc h.le L α) := Nat.finite_of_card_ne_zero (by
    rw [card_eq_of_natural hψ]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hR₁₂C : R₁ ⊔ R₂ ≤ C := sup_le (hR₁C.trans inf_le_right) (hR₂C.trans inf_le_right)
  have hfin12 : Finite ↥(R₁ ⊔ R₂) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hR₁₂C.trans inf_le_left))
  have hfin1 : Finite ↥R₁ := Finite.of_injective _ (Subgroup.inclusion_injective
    (le_sup_left.trans (hR₁₂C.trans inf_le_left)))
  have hfin2 : Finite ↥R₂ := Finite.of_injective _ (Subgroup.inclusion_injective
    (le_sup_right.trans (hR₁₂C.trans inf_le_left)))
  have hq1 : Fintype.card F ≤ Nat.card ↥R₁ := hx₁q.trans (Subgroup.card_le_of_le hx₁R)
  have hq2 : Fintype.card F ≤ Nat.card ↥R₂ := hx₂q.trans (Subgroup.card_le_of_le hx₂R)
  have hlow : Fintype.card F ^ 2 ≤ Nat.card ↥(R₁ ⊔ R₂) := by
    rw [sq]
    exact (Nat.mul_le_mul hq1 hq2).trans (card_mul_card_le_card_sup hR₁₂)
  have hCq : Nat.card ↥C ≤ Fintype.card F ^ 2 := by
    rw [hCdef, S46.I464.card_inf_centralizer_eq_pow hψ hZs, Nat.card_eq_fintype_card]
    exact Nat.pow_le_pow_right (by omega) hC2
  have hfinC : Finite ↥C := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left : C ≤ Uloc h.le L α))
  have hR₁₂eq : R₁ ⊔ R₂ = C := Subgroup.eq_of_le_of_card_ge hR₁₂C (hCq.trans hlow)
  have hz : IsMVtx (puAmalgam h.le) (geo _ α' α 4) :=
    (isMVtx_geo _ (by rw [tdist_comm, hc.2.1]; omega)).mpr ⟨fun _ => ⟨2, rfl⟩, fun _ => hα'⟩
  have hz5 : (puAmalgam h.le).treeGraph.Adj (geo _ α' α 4) (geo _ α' α 5) :=
    adj_geo _ (by rw [tdist_comm, hc.2.1]; omega)
  have hUz : Nat.card ↥(Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5)) =
      Fintype.card F ^ 2 := card_usup_eq_sq h hφ hC hb hz hz5
  have hfinUz : Finite ↥(Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5)) :=
    Nat.finite_of_card_ne_zero (by rw [hUz]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hR₁₂Uz : R₁ ⊔ R₂ = Usup (puAmalgam h.le) (geo _ α' α 4) (geo _ α' α 5) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hR₁U hR₂U) (by rw [hUz]; exact hlow)
  refine ⟨hR₁₂eq.symm.trans hR₁₂Uz, hR₁₂Uz ▸ sup_le hR₁D hR₂D, x₁, x₂, hcx₁, hcx₂, hx₁Q, hx₂Q,
    ?_⟩
  rw [eq_bot_iff, ← hR₁₂]
  exact inf_le_inf hx₁R hx₂R

end Main

end CFSG.Quasithin.MS93.S4A
