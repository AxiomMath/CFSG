module

public import CFSG.Quasithin.MS93.S4A44U
public import CFSG.Quasithin.MS93.S46I464Lin
public import CFSG.Quasithin.MS93.S46Ker

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Plane

open Matrix LinearFlag

variable {F : Type} [Field F]

theorem single_zero_mem_flagSpace_one : (Pi.single 0 (1 : F) : Fin 3 → F) ∈ flagSpace 3 F 1 := by
  rw [mem_flagSpace]
  intro j hj
  rw [Pi.single_apply, ite_eq_right_iff]
  rintro rfl
  simp at hj

theorem isCoatom_stabilizer_of_finrank_eq_two {k : Submodule F (Fin 3 → F)}
    (hk : Module.finrank F k = 2) : IsCoatom (stabilizer k) := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq k
  rw [hk] at hg
  have h0 : IsCoatom (stabilizer (flagSpace 3 F 2)) :=
    ⟨stabilizer_flagSpace_ne_top (by norm_num) (by norm_num), fun Q hQ =>
      (eq_of_stabilizer_flagSpace_le Q hQ.le).resolve_left hQ.ne'⟩
  rw [← hg, ← stabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) _).mpr h0

@[expose] def diagSL (c : Fˣ) : SL3 F :=
  ⟨diagonal ![(c : F), ((c⁻¹ : Fˣ) : F), 1], by
    simp [det_diagonal, Fin.prod_univ_three]⟩

theorem diagSL_mulVec_single_zero (c : Fˣ) :
    ((diagSL c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 (1 : F) : Fin 3 → F) =
      (c : F) • (Pi.single 0 (1 : F) : Fin 3 → F) := by
  ext i
  fin_cases i <;> simp [diagSL, mulVec_diagonal]

theorem diagSL_mem_stabilizer (c : Fˣ) : diagSL c ∈ stabilizer (flagSpace 3 F 2) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_flagSpace] at hx
  rw [mem_flagSpace]
  intro j hj
  have hj2 : j = 2 := by
    fin_cases j
    · simp at hj
    · simp at hj
    · rfl
  subst hj2
  have hx2 := hx 2 le_rfl
  simp [diagSL, mulVec_diagonal, hx2]

theorem map_inv_eq_of_map_eq {g : SL3 F} {W W' : Submodule F (Fin 3 → F)}
    (hg : W.map (mulVecLin ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = W') :
    W'.map (mulVecLin ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = W := by
  rw [← hg, ← Submodule.map_comp, ← mulVecLin_mul, coe_inv_mul_coe, mulVecLin_one,
    Submodule.map_id]

theorem exists_mem_stabilizer_mulVec_eq {k : Submodule F (Fin 3 → F)}
    (hk : Module.finrank F k = 2) {v w : Fin 3 → F} (hv : v ∈ k) (hw : w ∈ k) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) :
    ∃ s ∈ stabilizer k, ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w := by
  have hk' : Module.finrank F k = 3 - 1 := by rw [hk]
  obtain ⟨g, hg1, hg2⟩ := exists_map_flagSpace_eq_of_le (n := 3) (by norm_num)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) (finrank_span_singleton hv0) hk'
  obtain ⟨g', hg1', hg2'⟩ := exists_map_flagSpace_eq_of_le (n := 3) (by norm_num)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hw) (finrank_span_singleton hw0) hk'
  set e₀ : Fin 3 → F := Pi.single 0 1 with he₀
  have he0 : e₀ ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [he₀] at this
  have hge : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ ∈ F ∙ v := by
    rw [← hg1]
    exact ⟨e₀, single_zero_mem_flagSpace_one, rfl⟩
  have hge' : ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ ∈ F ∙ w := by
    rw [← hg1']
    exact ⟨e₀, single_zero_mem_flagSpace_one, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hge
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hge'
  have hinj : ∀ (x : SL3 F) (y : Fin 3 → F),
      ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = 0 → y = 0 := by
    intro x y hy
    have := congrArg (fun z => ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) hy
    simp only [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact he0 (hinj g e₀ ha.symm)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact he0 (hinj g' e₀ hb.symm)
  set c : Fˣ := Units.mk0 (a * b⁻¹) (mul_ne_zero ha0 (inv_ne_zero hb0)) with hc
  have hginv : ∀ x ∈ k, ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ flagSpace 3 F 2 := by
    intro x hx
    rw [← map_inv_eq_of_map_eq hg2]
    exact ⟨x, hx, rfl⟩
  have hmat : ((g' * diagSL c * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((diagSL c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  refine ⟨g' * diagSL c * g⁻¹, ?_, ?_⟩
  · refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨x, hx, rfl⟩
    show ((g' * diagSL c * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ k
    rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hg2']
    refine ⟨_, ?_, rfl⟩
    rw [← mem_stabilizer.mp (diagSL_mem_stabilizer c)]
    exact ⟨_, hginv x hx, rfl⟩
  ·
    have hgi : ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = a⁻¹ • e₀ := by
      have h1 : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (a⁻¹ • e₀) = v := by
        rw [Matrix.mulVec_smul, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [← h1, Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
    rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgi, Matrix.mulVec_smul,
      diagSL_mulVec_single_zero, smul_smul, Matrix.mulVec_smul, ← hb, smul_smul]
    rw [hc, Units.val_mk0]
    field_simp
    simp

end Plane

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem mem_usup_iff_natVec {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    (u : ↥(Uloc h.le L μ)) :
    (u : (puAmalgam h.le).Universal) ∈ Usup (puAmalgam h.le) μ ρ ↔
      natVec hψ u ∈ commN (natImage ψ (Qv (puAmalgam h.le) ρ)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rw [usup_eq_commutator_uloc h hfull hμ hμρ]
  exact mem_commutator_iff_natVec hψ (qv_le_stab_of_adj _ hμρ.symm) u

theorem finrank_commN_qv (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1) :
    Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hcard := card_usup_eq_sq h hφ hC hb hμ hμρ
  rw [usup_eq_commutator_uloc h hfull hμ hμρ,
    card_commutator_eq hψ (qv_le_stab_of_adj _ hμρ.symm),
    Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at hcard
  exact Nat.pow_right_injective hq hcard

theorem usup_le_uloc {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ) :
    Usup (puAmalgam h.le) μ ρ ≤ Uloc h.le L μ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rw [usup_eq_commutator_uloc h hfull hμ hμρ]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((qv_le_stab_of_adj _ hμρ.symm).trans (stab_le_normalizer_uloc h μ))

theorem mem_qv_of_forall_mulVec {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    (x : ↥(stab (puAmalgam h.le) μ))
    (hx : ∀ v, ((toSL3 ψ x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    (x : (puAmalgam h.le).Universal) ∈ Qv _ μ :=
  (S46.toSL3_eq_one_iff_mem_qv h hφ hμ hψ x).mp (eq_one_of_mulVec_eq_self hx)


theorem commN_le_fixN_of_le_centralizer {μ σ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμσ : (puAmalgam h.le).treeGraph.Adj μ σ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    {X : Subgroup (puAmalgam h.le).Universal} (hXs : X ≤ stab _ μ)
    (hle : Usup (puAmalgam h.le) μ σ ≤ Subgroup.centralizer (X : Set (puAmalgam h.le).Universal)) :
    commN (natImage ψ (Qv (puAmalgam h.le) σ)) ≤ fixN (natImage ψ X) := by
  intro v hv
  obtain ⟨u, rfl⟩ := natVec_surjective hψ v
  have hu : (u : (puAmalgam h.le).Universal) ∈ Usup _ μ σ :=
    (mem_usup_iff_natVec h hφ hμ hμσ hψ u).mpr hv
  exact (mem_centralizer_iff_natVec hψ hXs u).mp (hle hu)

theorem le_qv_of_fixN_eq_top {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    {X : Subgroup (puAmalgam h.le).Universal} (hXs : X ≤ stab _ μ)
    (htop : fixN (natImage ψ X) = ⊤) : X ≤ Qv _ μ := by
  intro x hx
  refine mem_qv_of_forall_mulVec h hφ hμ hψ ⟨x, hXs hx⟩ fun v => ?_
  have hv : v ∈ fixN (natImage ψ X) := htop ▸ Submodule.mem_top
  exact (mem_fixN.mp hv) _ (mem_natImage.mpr ⟨⟨x, hXs hx⟩, hx, rfl⟩)

omit h hφ [Fintype F] in
theorem sup_eq_top_of_finrank_eq_two {k k' : Submodule F (Fin 3 → F)}
    (hk : Module.finrank F k = 2) (hk' : Module.finrank F k' = 2) (hne : k ≠ k') :
    k ⊔ k' = ⊤ := by
  have hlt : k < k ⊔ k' := by
    refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
    have : k' ≤ k := heq ▸ le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq this (by rw [hk, hk'])).symm
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 := Submodule.finrank_le (k ⊔ k')
  rw [Module.finrank_fin_fun] at h4
  exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)

omit h hφ [Fintype F] in
theorem sup_eq_top_of_not_le {k c : Submodule F (Fin 3 → F)} (hk : Module.finrank F k = 2)
    (hc : ¬ c ≤ k) : k ⊔ c = ⊤ := by
  have hlt : k < k ⊔ c := lt_of_le_of_ne le_sup_left fun heq => hc (heq ▸ le_sup_right)
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 := Submodule.finrank_le (k ⊔ c)
  rw [Module.finrank_fin_fun] at h4
  exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)

theorem usup_eq_of_le_centralizer (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {μ ρ ρ' : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ) (hμρ' : (puAmalgam h.le).treeGraph.Adj μ ρ')
    {X : Subgroup (puAmalgam h.le).Universal} (hXs : X ≤ stab _ μ) (hXQ : ¬ X ≤ Qv _ μ)
    (h1 : Usup (puAmalgam h.le) μ ρ ≤ Subgroup.centralizer (X : Set (puAmalgam h.le).Universal))
    (h2 : Usup (puAmalgam h.le) μ ρ' ≤ Subgroup.centralizer (X : Set (puAmalgam h.le).Universal)) :
    Usup (puAmalgam h.le) μ ρ = Usup (puAmalgam h.le) μ ρ' := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  have hkk : commN (natImage ψ (Qv (puAmalgam h.le) ρ)) =
      commN (natImage ψ (Qv (puAmalgam h.le) ρ')) := by
    by_contra hne
    apply hXQ
    refine le_qv_of_fixN_eq_top h hφ hμ hψ hXs (eq_top_iff.mpr ?_)
    rw [← sup_eq_top_of_finrank_eq_two (finrank_commN_qv h hφ hC hb hμ hμρ hψ)
      (finrank_commN_qv h hφ hC hb hμ hμρ' hψ) hne]
    exact sup_le (commN_le_fixN_of_le_centralizer h hφ hμ hμρ hψ hXs h1)
      (commN_le_fixN_of_le_centralizer h hφ hμ hμρ' hψ hXs h2)
  apply le_antisymm
  · intro x hx
    have hxU := usup_le_uloc h hφ hμ hμρ hx
    have := (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨x, hxU⟩).mp hx
    rw [hkk] at this
    exact (mem_usup_iff_natVec h hφ hμ hμρ' hψ ⟨x, hxU⟩).mpr this
  · intro x hx
    have hxU := usup_le_uloc h hφ hμ hμρ' hx
    have := (mem_usup_iff_natVec h hφ hμ hμρ' hψ ⟨x, hxU⟩).mp hx
    rw [← hkk] at this
    exact (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨x, hxU⟩).mpr this

theorem commutator_uloc_le_usup (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {μ σ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμσ : (puAmalgam h.le).treeGraph.Adj μ σ) {X : Subgroup (puAmalgam h.le).Universal}
    (hXs : X ≤ stab _ μ) (hX2 : IsPGroup 2 ↥X)
    (hle : Usup (puAmalgam h.le) μ σ ≤ Subgroup.centralizer (X : Set (puAmalgam h.le).Universal)) :
    ⁅Uloc h.le L μ, X⁆ ≤ Usup (puAmalgam h.le) μ σ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hk2 := finrank_commN_qv h hφ hC hb hμ hμσ hψ
  have hkfix := commN_le_fixN_of_le_centralizer h hφ hμ hμσ hψ hXs hle
  have hP : IsPGroup 2 ↥(natImage ψ X) := by
    have hX2' : IsPGroup 2 ↥(X.subgroupOf (stab (puAmalgam h.le) μ)) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXs).symm
    exact hX2'.map _
  have hfr : 2 ≤ Module.finrank F (fixN (natImage ψ X)) :=
    hk2 ▸ Submodule.finrank_mono hkfix
  have hcf := S46.I464.commN_le_fixN_of_two_le_finrank hP hfr
  have h3 := Submodule.finrank_le (fixN (natImage ψ X))
  rw [Module.finrank_fin_fun] at h3
  have hXU : X ≤ Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    hXs.trans (stab_le_normalizer_uloc h μ)
  rcases (show Module.finrank F (fixN (natImage ψ X)) = 2 ∨
      Module.finrank F (fixN (natImage ψ X)) = 3 by omega) with h2 | h3'
  · have heq : commN (natImage ψ (Qv (puAmalgam h.le) σ)) = fixN (natImage ψ X) :=
      Submodule.eq_of_le_of_finrank_eq hkfix (by rw [hk2, h2])
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hcU : ⁅u, x⁆ ∈ Uloc h.le L μ :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hXU
        (Subgroup.commutator_mem_commutator hu hx)
    refine (mem_usup_iff_natVec h hφ hμ hμσ hψ ⟨_, hcU⟩).mpr ?_
    rw [heq]
    apply hcf
    rw [natVec_commutator hψ ⟨x, hXs hx⟩ ⟨u, hu⟩ ⟨_, hcU⟩ rfl]
    have hm := sub_mem_commN (A := natImage ψ X) (mem_natImage.mpr ⟨⟨x, hXs hx⟩, hx, rfl⟩)
      (natVec hψ ⟨u, hu⟩)
    have : natVec hψ ⟨u, hu⟩ - ((toSL3 ψ ⟨x, hXs hx⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        natVec hψ ⟨u, hu⟩ = -(((toSL3 ψ ⟨x, hXs hx⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        natVec hψ ⟨u, hu⟩ - natVec hψ ⟨u, hu⟩) := by abel
    rw [this]
    exact Submodule.neg_mem _ hm
  · have htop : fixN (natImage ψ X) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3', Module.finrank_fin_fun])
    have hXQ := le_qv_of_fixN_eq_top h hφ hμ hψ hXs htop
    have hbot : ⁅Uloc h.le L μ, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (uloc_le_zm h (isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩) hμ).trans
        ((zm_le_centralizer_qv _ h.hyp20 hμ).trans (Subgroup.centralizer_le hXQ))
    rw [hbot]
    exact bot_le


theorem mem_normalizer_usup_iff {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    (g : ↥(stab (puAmalgam h.le) μ)) :
    (g : (puAmalgam h.le).Universal) ∈
        Subgroup.normalizer (Usup (puAmalgam h.le) μ ρ : Set (puAmalgam h.le).Universal) ↔
      toSL3 ψ g ∈ LinearFlag.stabilizer (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) := by
  have hUn := stab_le_normalizer_uloc h μ
  have key : ∀ a : ↥(stab (puAmalgam h.le) μ),
      toSL3 ψ a ∈ LinearFlag.stabilizer (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) →
      ∀ u ∈ Usup (puAmalgam h.le) μ ρ,
        (a : (puAmalgam h.le).Universal) * u * (a : (puAmalgam h.le).Universal)⁻¹ ∈
          Usup (puAmalgam h.le) μ ρ := by
    intro a ha u hu
    have huU := usup_le_uloc h hφ hμ hμρ hu
    have haU : (a : (puAmalgam h.le).Universal) * u * (a : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn a.2) u).mp huU
    refine (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨_, haU⟩).mpr ?_
    rw [natVec_conj hψ a ⟨u, huU⟩ ⟨_, haU⟩ rfl, ← LinearFlag.mem_stabilizer.mp ha]
    exact ⟨_, (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨u, huU⟩).mp hu, rfl⟩
  constructor
  · intro hg
    refine LinearFlag.mem_stabilizer_of_map_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, rfl⟩ := natVec_surjective hψ x
    have hu : (u : (puAmalgam h.le).Universal) ∈ Usup (puAmalgam h.le) μ ρ :=
      (mem_usup_iff_natVec h hφ hμ hμρ hψ u).mpr hx
    have hgu := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
    have hgU : (g : (puAmalgam h.le).Universal) * u * (g : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn g.2) u).mp u.2
    show ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u ∈ _
    rw [← natVec_conj hψ g u ⟨_, hgU⟩ rfl]
    exact (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨_, hgU⟩).mp hgu
  · intro hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key g hs u, fun hu => ?_⟩
    have := key g⁻¹ (by rw [map_inv]; exact inv_mem hs) _ hu
    simpa [mul_assoc] using this

theorem eq_stab_of_le (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    {H : Subgroup (puAmalgam h.le).Universal} (hHs : H ≤ stab _ μ)
    (hPH : stab (puAmalgam h.le) μ ⊓
      Subgroup.normalizer (Usup (puAmalgam h.le) μ ρ : Set (puAmalgam h.le).Universal) ≤ H)
    (hHN : ¬ H ≤ Subgroup.normalizer (Usup (puAmalgam h.le) μ ρ : Set (puAmalgam h.le).Universal)) :
    H = stab (puAmalgam h.le) μ := by
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hμ
  have hS := isCoatom_stabilizer_of_finrank_eq_two (finrank_commN_qv h hφ hC hb hμ hμρ hψ)
  have hSH : LinearFlag.stabilizer (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) ≤
      natImage ψ H := by
    intro s hs
    obtain ⟨p, rfl⟩ := toSL3_surjective hψs s
    have hpN := (mem_normalizer_usup_iff h hφ hμ hμρ hψ p).mpr hs
    exact mem_natImage.mpr ⟨p, hPH ⟨p.2, hpN⟩, rfl⟩
  have hne : LinearFlag.stabilizer (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) ≠
      natImage ψ H := by
    intro heq
    apply hHN
    intro x hx
    have hmem : toSL3 ψ ⟨x, hHs hx⟩ ∈
        LinearFlag.stabilizer (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) :=
      heq ▸ mem_natImage.mpr ⟨⟨x, hHs hx⟩, hx, rfl⟩
    exact (mem_normalizer_usup_iff h hφ hμ hμρ hψ ⟨x, hHs hx⟩).mpr hmem
  have htop : natImage ψ H = ⊤ := hS.2 _ (lt_of_le_of_ne hSH hne)
  refine le_antisymm hHs fun g hg => ?_
  have hmem : toSL3 ψ ⟨g, hg⟩ ∈ natImage ψ H := htop ▸ Subgroup.mem_top _
  obtain ⟨p, hpH, hpg⟩ := mem_natImage.mp hmem
  have hk1 : toSL3 ψ (p⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hpg, inv_mul_cancel]
  have hQ := (S46.toSL3_eq_one_iff_mem_qv h hφ hμ hψ _).mp hk1
  have hQH : ((p⁻¹ * ⟨g, hg⟩ : ↥(stab (puAmalgam h.le) μ)) : (puAmalgam h.le).Universal) ∈ H :=
    hPH ⟨(p⁻¹ * ⟨g, hg⟩).2,
      qv_le_normalizer_usup h hμρ (qv_le_qv _ h.hyp20 hμ hμρ hQ)⟩
  have e : g = (p : (puAmalgam h.le).Universal) *
      ((p⁻¹ * ⟨g, hg⟩ : ↥(stab (puAmalgam h.le) μ)) : (puAmalgam h.le).Universal) := by
    simp
  rw [e]
  exact H.mul_mem hpH hQH

theorem usup_le_of_inf_ne_bot (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ) {N : Subgroup (puAmalgam h.le).Universal}
    (hNU : N ≤ Uloc h.le L μ)
    (hNn : stab (puAmalgam h.le) μ ⊓
      Subgroup.normalizer (Usup (puAmalgam h.le) μ ρ : Set (puAmalgam h.le).Universal) ≤
        Subgroup.normalizer (N : Set (puAmalgam h.le).Universal))
    (hne : N ⊓ Usup (puAmalgam h.le) μ ρ ≠ ⊥) : Usup (puAmalgam h.le) μ ρ ≤ N := by
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hμ
  obtain ⟨n₀, ⟨hn₀N, hn₀U⟩, hn₀1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  have hn₀L : n₀ ∈ Uloc h.le L μ := hNU hn₀N
  have hv₀ := (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨n₀, hn₀L⟩).mp hn₀U
  have hv₀0 : natVec hψ ⟨n₀, hn₀L⟩ ≠ 0 := by
    intro h0
    apply hn₀1
    have := natVec_injective hψ (h0.trans (natVec_one hψ).symm)
    exact congrArg Subtype.val this
  intro u hu
  have huL := usup_le_uloc h hφ hμ hμρ hu
  by_cases hu1 : u = 1
  · rw [hu1]
    exact N.one_mem
  have hw := (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨u, huL⟩).mp hu
  have hw0 : natVec hψ ⟨u, huL⟩ ≠ 0 := by
    intro h0
    apply hu1
    have := natVec_injective hψ (h0.trans (natVec_one hψ).symm)
    exact congrArg Subtype.val this
  obtain ⟨s, hsS, hsv⟩ := exists_mem_stabilizer_mulVec_eq
    (finrank_commN_qv h hφ hC hb hμ hμρ hψ) hv₀ hw hv₀0 hw0
  obtain ⟨p, rfl⟩ := toSL3_surjective hψs s
  have hpN : (p : (puAmalgam h.le).Universal) ∈ Subgroup.normalizer (N : Set _) :=
    hNn ⟨p.2, (mem_normalizer_usup_iff h hφ hμ hμρ hψ p).mpr hsS⟩
  have hpn := (Subgroup.mem_normalizer_iff.mp hpN n₀).mp hn₀N
  have hcoord := natVec_conj hψ p ⟨n₀, hn₀L⟩ ⟨_, hNU hpn⟩ rfl
  have heq : (⟨_, hNU hpn⟩ : ↥(Uloc h.le L μ)) = ⟨u, huL⟩ :=
    natVec_injective hψ (hcoord.trans hsv)
  have : (p : (puAmalgam h.le).Universal) * n₀ * (p : (puAmalgam h.le).Universal)⁻¹ = u :=
    congrArg Subtype.val heq
  rw [← this]
  exact hpn

theorem uloc_le_usup_sup (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    {A : Subgroup (puAmalgam h.le).Universal} (hAs : A ≤ stab _ μ)
    (hnot : ¬ Uloc h.le L μ ⊓ Subgroup.centralizer (A : Set (puAmalgam h.le).Universal) ≤
      Usup (puAmalgam h.le) μ ρ) :
    Uloc h.le L μ ≤ Usup (puAmalgam h.le) μ ρ ⊔
      (Uloc h.le L μ ⊓ Subgroup.centralizer (A : Set (puAmalgam h.le).Universal)) := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  have hc : ¬ fixN (natImage ψ A) ≤ commN (natImage ψ (Qv (puAmalgam h.le) ρ)) := by
    intro hle
    apply hnot
    rintro x ⟨hxU, hxC⟩
    exact (mem_usup_iff_natVec h hφ hμ hμρ hψ ⟨x, hxU⟩).mpr
      (hle ((mem_centralizer_iff_natVec hψ hAs ⟨x, hxU⟩).mp hxC))
  have htop := sup_eq_top_of_not_le (finrank_commN_qv h hφ hC hb hμ hμρ hψ) hc
  intro u hu
  have hmem : natVec hψ ⟨u, hu⟩ ∈
      commN (natImage ψ (Qv (puAmalgam h.le) ρ)) ⊔ fixN (natImage ψ A) :=
    htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨u₁, rfl⟩ := natVec_surjective hψ y
  obtain ⟨u₂, rfl⟩ := natVec_surjective hψ z
  have h1 := (mem_usup_iff_natVec h hφ hμ hμρ hψ u₁).mpr hy
  have h2 := (mem_centralizer_iff_natVec hψ hAs u₂).mpr hz
  have heq : u₁ * u₂ = ⟨u, hu⟩ := natVec_injective hψ (by rw [natVec_mul, hyz])
  have : u = (u₁ : (puAmalgam h.le).Universal) * u₂ := (congrArg Subtype.val heq).symm
  rw [this]
  exact Subgroup.mul_mem_sup h1 ⟨u₂.2, h2⟩

theorem zh_inf_usup_ne_bot (hC : CentHyp (puAmalgam h.le)) {μ ρ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ) :
    ZH (puAmalgam h.le) ρ ⊓ Usup (puAmalgam h.le) μ ρ ≠ ⊥ := by
  have hb0 := h.critDist_pos
  have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
    rw [← isMVtx_iff_of_adj _ hμρ]
    exact hμ
  have hUZ : Usup (puAmalgam h.le) μ ρ ≤ ZM (puAmalgam h.le) μ := by
    rw [Usup, zv_of_isMVtx _ hμ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hμρ.symm).trans (stab_le_normalizer_zm _ μ))
  have hUQ : Usup (puAmalgam h.le) μ ρ ≤ Qv _ ρ :=
    hUZ.trans ((zm_le_qv_self _ hμ hb0).trans (qv_le_qv _ h.hyp20 hμ hμρ))
  have := isNilpotent_qv _ h.hyp20 hρH
  have : ((Usup (puAmalgam h.le) μ ρ).subgroupOf (Qv (puAmalgam h.le) ρ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (qv_le_normalizer_usup h hμρ)
  have hne : (Usup (puAmalgam h.le) μ ρ).subgroupOf (Qv (puAmalgam h.le) ρ) ≠ ⊥ := by
    intro h0
    apply usup_ne_bot h hφ hC hμ hμρ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hUQ hx⟩ : ↥(Qv (puAmalgam h.le) ρ)) ∈
        (Usup (puAmalgam h.le) μ ρ).subgroupOf (Qv (puAmalgam h.le) ρ) := hx
    rw [h0, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  obtain ⟨x, ⟨hxU, hxZ⟩, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro hbot
  apply hx1
  have hxc : (x : (puAmalgam h.le).Universal) ∈
      Subgroup.centralizer (Qv (puAmalgam h.le) ρ : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩)
  have hx2 : (x : (puAmalgam h.le).Universal) ^ 2 = 1 :=
    (isElemAbelian_zm _ h.hyp20 hb0 hμ).2 _ (hUZ hxU)
  have hxZH : (x : (puAmalgam h.le).Universal) ∈ ZH (puAmalgam h.le) ρ :=
    Subgroup.subset_closure ⟨⟨x.2, hxc⟩, hx2⟩
  have hmem : (x : (puAmalgam h.le).Universal) ∈
      ZH (puAmalgam h.le) ρ ⊓ Usup (puAmalgam h.le) μ ρ := ⟨hxZH, hxU⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Coord

end CFSG.Quasithin.MS93.S4A
