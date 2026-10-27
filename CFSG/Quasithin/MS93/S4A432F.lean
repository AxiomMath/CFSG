module

public import CFSG.Quasithin.MS93.S4A432E

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Plane

variable {F : Type} [Field F]

theorem eq_of_le_of_finrank_eq_two {W S : Submodule F (Fin 3 → F)} (hWS : W ≤ S)
    (hW : Module.finrank F W = 2) (hS : S ≠ ⊤) : S = W := by
  by_contra hne
  have hlt : W < S := lt_of_le_of_ne hWS (Ne.symm hne)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_le S
  rw [Module.finrank_fin_fun] at h2
  exact hS (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega))

@[expose] def orthN (v : Fin 3 → F) : Submodule F (Fin 3 → F) where
  carrier := {x | v ⬝ᵥ x = 0}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, dotProduct_add] at hx hy ⊢
    rw [hx, hy, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, dotProduct_smul] at hx ⊢
    rw [hx, smul_zero]

theorem orthN_ne_top {v : Fin 3 → F} (hv : v ≠ 0) : orthN v ≠ ⊤ := by
  intro htop
  apply hv
  funext i
  have : (Pi.single i 1 : Fin 3 → F) ∈ orthN v := htop ▸ Submodule.mem_top
  simpa [orthN, dotProduct_single] using this

theorem commN_le_orthN {A : Subgroup (SL3 F)} {v : Fin 3 → F}
    (hA : ∀ g ∈ A, dualMat g *ᵥ v = v) : commN A ≤ orthN v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, x, rfl⟩
  show v ⬝ᵥ (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x) = 0
  have := dualMat_mulVec_dotProduct g v x
  rw [hA g hg] at this
  rw [dotProduct_sub, this, sub_self]

theorem finrank_inf_planes_eq_one {W W' : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 2) (hW' : Module.finrank F W' = 2) (hne : W ≠ W') :
    Module.finrank F ↥(W ⊓ W') = 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W W'
  have hle : Module.finrank F ↥(W ⊔ W') ≤ 3 := by
    have := Submodule.finrank_le (W ⊔ W')
    rwa [Module.finrank_fin_fun] at this
  have hlt : 2 < Module.finrank F ↥(W ⊔ W') := by
    by_contra hge
    have h1 : W = W ⊔ W' := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have h2 : W' = W ⊔ W' := Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    exact hne (h1.trans h2.symm)
  omega

end Plane

section Dist

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem dist_eq_add_one_of_adj_of_ne {u x w : Vtx X} (hux : X.treeGraph.Adj u x)
    (hne : x ≠ geo X u w 1) (huw : u ≠ w) :
    X.treeGraph.dist x w = X.treeGraph.dist u w + 1 := by
  have h1 := dist_triangle X x u w
  have h2 := dist_triangle X u x w
  rw [tdist_comm X x u, dist_eq_one_of_adj X hux] at h1
  rw [dist_eq_one_of_adj X hux] at h2
  have hpos : 0 < X.treeGraph.dist u w := by
    rcases Nat.eq_zero_or_pos (X.treeGraph.dist u w) with h0 | h0
    · exact absurd ((dist_eq_zero_iff X).mp h0) huw
    · exact h0
  have hpar : X.treeGraph.dist x w ≠ X.treeGraph.dist u w := by
    intro heq
    have e1 := even_dist_iff X u w
    have e2 := even_dist_iff X x w
    rw [heq] at e2
    have := isMVtx_iff_of_adj X hux
    tauto
  have hne' : X.treeGraph.dist x w + 1 ≠ X.treeGraph.dist u w := fun h' =>
    hne (eq_geo_one X hux h')
  omega

end Dist

section Perp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_uloc_le_usup_of_dual {F : Type} [Field F] [Fintype F]
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hc : IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    (hk : KindAt h.le L F true μ) {ν δ : Vtx (puAmalgam h.le)}
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν) (hνδ : (puAmalgam h.le).treeGraph.Adj ν δ)
    (hUμq : Nat.card ↥(Usup (puAmalgam h.le) μ ν) = Fintype.card F ^ 2)
    (hUδ : Usup (puAmalgam h.le) δ ν ≤ ZH (puAmalgam h.le) ν)
    {v : (puAmalgam h.le).Universal} (hv : v ∈ ZM (puAmalgam h.le) δ)
    (hvB : v ∉ Bloc h.le L μ) {X : Subgroup (puAmalgam h.le).Universal}
    (hXs : X ≤ stab (puAmalgam h.le) μ) (hvX : ∀ c ∈ X, ⁅v, c⁆ ∈ Bloc h.le L μ) :
    ⁅Uloc h.le L μ, X⁆ ≤ Usup (puAmalgam h.le) μ ν := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hνH : ¬ IsMVtx (puAmalgam h.le) ν := by
    rw [← isMVtx_iff_of_adj _ hμν]
    exact hμ
  have hδ : IsMVtx (puAmalgam h.le) δ := by
    by_contra hδ
    exact hνH ((isMVtx_iff_of_adj _ hνδ).mpr hδ)
  have hQs : Qv (puAmalgam h.le) μ ≤ stab _ μ := qv_le_stab _ μ
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb hμ).trans hQs
  have hTs : Qv (puAmalgam h.le) ν ≤ stab _ μ := qv_le_stab_of_adj _ hμν.symm
  have hVn := stab_le_normalizer_vv h μ
  have hBn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hBV : Bloc h.le L μ ≤ Vv _ μ := bloc_le_vv h μ
  have hZB : ZM (puAmalgam h.le) μ ≤ Bloc h.le L μ := zm_le_bloc h hb hμ
  have hdμδ : (puAmalgam h.le).treeGraph.dist μ δ ≤ 2 := by
    have := dist_triangle (puAmalgam h.le) μ ν δ
    rw [dist_eq_one_of_adj _ hμν, dist_eq_one_of_adj _ hνδ] at this
    exact this
  have hvV : v ∈ Vv (puAmalgam h.le) μ := by
    have : Zv (puAmalgam h.le) δ ≤ Vv _ μ := zv_le_vv h hdμδ
    rw [zv_of_isMVtx _ hδ] at this
    exact this hv
  obtain ⟨ψ, -, hψ, hP⟩ := hk
  obtain ⟨-, -, -, -, -, -, -, hPiB, hPB, -, -⟩ := isC1_normal h hfull hb hμ hc
  have hPV : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Vv _ μ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hμ)
  have hVB := isSumOfNaturalModulesVia_transfer hP hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn
    ((hPV.trans hVs).trans hBn)
  set N := NatSec.ofIsSum hVB with hNdef
  set v₀ := N.coord v with hv₀
  have hv0 : v₀ ≠ 0 := by
    rw [hv₀, Ne, N.coord_eq_zero_iff hvV]
    exact fun h' => hvB h'.2
  have hfix : ∀ k : ↥(stab (puAmalgam h.le) μ), ⁅v, (k : (puAmalgam h.le).Universal)⁆ ∈
      Bloc h.le L μ → dualMat (toSL3 ψ k) *ᵥ v₀ = v₀ := by
    intro k hk
    have hkv : (k : (puAmalgam h.le).Universal) * v * (k : (puAmalgam h.le).Universal)⁻¹ ∈
        Vv (puAmalgam h.le) μ := N.conj_mem k hvV
    have hmem : v⁻¹ * ((k : (puAmalgam h.le).Universal) * v *
        (k : (puAmalgam h.le).Universal)⁻¹) ∈ Vv (puAmalgam h.le) μ ⊓ Bloc h.le L μ := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hvV) hkv, ?_⟩
      have e : v⁻¹ * ((k : (puAmalgam h.le).Universal) * v *
          (k : (puAmalgam h.le).Universal)⁻¹) =
          v⁻¹ * ⁅v, (k : (puAmalgam h.le).Universal)⁆⁻¹ * v := by
        simp only [commutatorElement_def]
        group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hBn (hVs (Subgroup.inv_mem _ hvV))) _).mp
        (Subgroup.inv_mem _ hk)
      simpa [mul_assoc] using this
    have h0 := (N.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvV) hkv)).mpr hmem
    rw [N.coord_mul (Subgroup.inv_mem _ hvV) hkv, N.coord_inv hvV, N.coord_conj k hvV,
      natAct_true, neg_add_eq_zero] at h0
    exact h0.symm
  have hTperp : commN (natImage ψ (Qv (puAmalgam h.le) ν)) ≤ orthN v₀ := by
    refine commN_le_orthN fun g hg => ?_
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    refine hfix t ?_
    have e : ⁅v, (t : (puAmalgam h.le).Universal)⁆ = ⁅(t : (puAmalgam h.le).Universal), v⁆⁻¹ := by
      rw [commutatorElement_inv]
    rw [e]
    refine Subgroup.inv_mem _ (hZB (zh_le_zm _ hμν (hUδ ?_)))
    rw [Usup, zv_of_isMVtx _ hδ, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv htT)
  have hXperp : commN (natImage ψ X) ≤ orthN v₀ := by
    refine commN_le_orthN fun g hg => ?_
    obtain ⟨c, hcX, rfl⟩ := mem_natImage.mp hg
    exact hfix c (hvX _ hcX)
  have hcardC : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ν))) = 2 := by
    have := hUμq
    rw [usup_eq_commutator_uloc h hfull hμ hμν, card_commutator_eq hψ hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have horth : orthN v₀ = commN (natImage ψ (Qv (puAmalgam h.le) ν)) :=
    eq_of_le_of_finrank_eq_two hTperp hcardC (orthN_ne_top hv0)
  intro u hu
  have hUX : ⁅Uloc h.le L μ, X⁆ ≤ Uloc h.le L μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hXs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ))
  have h1 := (mem_commutator_iff_natVec hψ hXs ⟨u, hUX hu⟩).mp hu
  have h2 : natVec hψ ⟨u, hUX hu⟩ ∈ commN (natImage ψ (Qv (puAmalgam h.le) ν)) :=
    horth ▸ hXperp h1
  rw [usup_eq_commutator_uloc h hfull hμ hμν]
  exact (mem_commutator_iff_natVec hψ hTs ⟨u, hUX hu⟩).mpr h2

theorem fixN_eq_commN_of_le_qv {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {μ ν : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν)
    (hUZ : Usup (puAmalgam h.le) μ ν ≤ ZH (puAmalgam h.le) ν)
    (hUq : Nat.card ↥(Usup (puAmalgam h.le) μ ν) = Fintype.card F ^ 2)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    {X : Subgroup (puAmalgam h.le).Universal} (hXT : X ≤ Qv (puAmalgam h.le) ν)
    (hXQ : ¬ X ≤ Qv (puAmalgam h.le) μ) :
    fixN (natImage ψ X) = commN (natImage ψ (Qv (puAmalgam h.le) ν)) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hTs : Qv (puAmalgam h.le) ν ≤ stab _ μ := qv_le_stab_of_adj _ hμν.symm
  have hXs : X ≤ stab (puAmalgam h.le) μ := hXT.trans hTs
  have hW : commN (natImage ψ (Qv (puAmalgam h.le) ν)) ≤ fixN (natImage ψ (Qv _ ν)) := by
    intro x hx
    obtain ⟨w, rfl⟩ := natVec_surjective hψ x
    have hw : (w : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L μ, Qv (puAmalgam h.le) ν⁆ :=
      (mem_commutator_iff_natVec hψ hTs w).mpr hx
    rw [← usup_eq_commutator_uloc h hfull hμ hμν] at hw
    have hwC : (w : (puAmalgam h.le).Universal) ∈
        Subgroup.centralizer (Qv (puAmalgam h.le) ν : Set _) :=
      ((zh_inf_uloc h hfull hμ hμν).le ⟨hUZ hw, w.2⟩).2
    exact (mem_centralizer_iff_natVec hψ hTs w).mp hwC
  have hcardC : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ν))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h hfull hμ hμν, card_commutator_eq hψ hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  refine eq_of_le_of_finrank_eq_two (hW.trans (fixN_anti (natImage_mono hXT))) hcardC ?_
  intro htop
  apply hXQ
  intro x hx
  refine S46.stab_inf_centralizer_uloc_le_qv h hφ hμ ⟨hXs hx, ?_⟩
  show x ∈ Subgroup.centralizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have := (mem_centralizer_iff_natVec hψ hXs ⟨u, hu⟩).mpr
    (htop ▸ Submodule.mem_top : natVec hψ ⟨u, hu⟩ ∈ fixN (natImage ψ X))
  exact (Subgroup.mem_centralizer_iff.mp this x hx).symm

omit hfull in
theorem le_card_commutator_uloc_of_not_le {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) {X : Subgroup (puAmalgam h.le).Universal}
    (hXs : X ≤ stab (puAmalgam h.le) μ) (hXQ : ¬ X ≤ Qv (puAmalgam h.le) μ) :
    Fintype.card F ≤ Nat.card ↥⁅Uloc h.le L μ, X⁆ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  rw [card_commutator_eq hψ hXs, ← Nat.card_eq_fintype_card]
  refine card_le_of_ne_bot (commN_ne_bot ?_)
  intro hbot
  apply hXQ
  intro x hx
  have hmem : toSL3 ψ ⟨x, hXs hx⟩ ∈ natImage ψ X := mem_natImage.mpr ⟨_, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (S46.toSL3_eq_one_iff_mem_qv h hφ hμ hψ ⟨x, hXs hx⟩).mp hmem

end Perp

section Dual

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le)) (h42 : S42) (h431A : S431A)
  (h431B : S431B) (hb : 4 < critDist (puAmalgam h.le)) {α₀ α₀' : Vtx (puAmalgam h.le)}
  (hs : Star (puAmalgam h.le) α₀ α₀')
  (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F true μ)
  (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
    ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
include h hfull hH hC h42 h431A h431B hb hs hk hCH

theorem uloc_inf_bloc_eq_usup_of_dual {μ ν δ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμν : (puAmalgam h.le).treeGraph.Adj μ ν) (hνδ : (puAmalgam h.le).treeGraph.Adj ν δ)
    (hδ : δ ∈ nablaSet h.le L μ) :
    Uloc h.le L δ ⊓ Bloc h.le L μ = Usup (puAmalgam h.le) μ ν := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hδM, hZδV⟩ := zm_le_vv_of_mem_nablaSet h hμ hδ
  obtain ⟨hcomm, hUeq⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
    hk hCH hμ hμν hνδ hδ
  obtain ⟨hUμZ, hUμq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμ hμν
  obtain ⟨hUδZ, hUδq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hδM hνδ.symm
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hUμU : Usup (puAmalgam h.le) μ ν ≤ Uloc h.le L μ := by
    rw [usup_eq_commutator_uloc h hfull hμ hμν]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hμν.symm).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ))
  have hUδU : Usup (puAmalgam h.le) δ ν ≤ Uloc h.le L δ := by
    rw [usup_eq_commutator_uloc h hfull hδM hνδ.symm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hνδ).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) δ))
  apply le_antisymm
  · rintro u ⟨hu, huB⟩
    have hcμ := isC1_of_star h hH h431A hs hμ
    obtain ⟨-, -, -, -, -, -, -, -, -, hBG, -⟩ := isC1_normal h hfull hb2 hμ hcμ
    have hVQμ := commutator_vv_qv_le_zm_of_star h hfull hH hC h42 h431A h431B hs hμ
    have hBG' : ⁅Bloc h.le L μ, stab (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) μ :=
      hBG.trans (sup_le hVQμ le_rfl)
    have hZcQ := zm_le_centralizer_qv _ h20 hμ
    have huZδ : u ∈ ZM (puAmalgam h.le) δ := uloc_le_zm h hfull hδM hu
    set N := Subgroup.closure {r | ∃ y ∈ Qv (puAmalgam h.le) μ, ⁅u, y⁆ = r} with hNdef
    have hNU : N ≤ Usup (puAmalgam h.le) μ ν := by
      rw [hNdef, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator huZδ hy
    have hNn : stab (puAmalgam h.le) μ ≤
        Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
      have key : ∀ g ∈ stab (puAmalgam h.le) μ, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
        intro g hg n hn
        induction hn using Subgroup.closure_induction with
        | mem n hn =>
          obtain ⟨y, hy, rfl⟩ := hn
          have hc : ⁅u⁻¹, g⁆ ∈ ZM (puAmalgam h.le) μ :=
            hBG' (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ huB) hg)
          have hy' : g * y * g⁻¹ ∈ Qv (puAmalgam h.le) μ :=
            (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ hg) y).mp hy
          have hcy : ⁅u⁻¹, g⁆ * (g * y * g⁻¹) = (g * y * g⁻¹) * ⁅u⁻¹, g⁆ :=
            (Subgroup.mem_centralizer_iff.mp (hZcQ hc) _ hy').symm
          have e : g * ⁅u, y⁆ * g⁻¹ = ⁅u, g * y * g⁻¹⁆ := by
            have e1 : g * ⁅u, y⁆ * g⁻¹ = ⁅u * ⁅u⁻¹, g⁆, g * y * g⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
            rw [e1]
            simp only [commutatorElement_def] at hcy ⊢
            calc u * (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹) *
                  (u * (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹))⁻¹ * (g * y * g⁻¹)⁻¹
                = u * ((u⁻¹ * g * u⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹)) *
                  (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹)⁻¹ * u⁻¹ * (g * y * g⁻¹)⁻¹ := by group
              _ = u * ((g * y * g⁻¹) * (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹)) *
                  (u⁻¹ * g * u⁻¹⁻¹ * g⁻¹)⁻¹ * u⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hcy]
              _ = u * (g * y * g⁻¹) * u⁻¹ * (g * y * g⁻¹)⁻¹ := by group
          rw [e]
          exact Subgroup.subset_closure ⟨_, hy', rfl⟩
        | one => simp
        | mul a b _ _ ha hb =>
          have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [this]
          exact N.mul_mem ha hb
        | inv a _ ha =>
          have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [this]
          exact N.inv_mem ha
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · exact key g hg n
      · intro hn
        have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hn
        simpa [mul_assoc] using this
    have hNZ : N ≤ Zloc h.le L μ := by
      by_contra hNZ
      have hUN := uloc_le_of_normal h hfull hH.2.2 hμ
        ((hNU.trans hUμU).trans (uloc_le_zm h hfull hμ)) hNn hNZ
      have := finite_stab h hμ
      have hfinU : Finite ↥(Uloc h.le L μ) := Finite.of_injective _
        (Subgroup.inclusion_injective ((uloc_le_zm h hfull hμ).trans
          ((zm_le_qv_self _ hμ hb0).trans (qv_le_stab _ μ))))
      have hfinS : Finite ↥(Usup (puAmalgam h.le) μ ν) :=
        Finite.of_injective _ (Subgroup.inclusion_injective hUμU)
      have h1 := Subgroup.card_le_of_le (hUN.trans hNU)
      obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hH.2.2 hμ
      rw [card_eq_of_natural hψ, hUμq, Nat.card_eq_fintype_card (α := F)] at h1
      have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
        Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    have hu1 : ∀ y ∈ Qv (puAmalgam h.le) μ, ⁅u, y⁆ = 1 := by
      intro y hy
      have hmem : ⁅u, y⁆ ∈ Uloc h.le L μ ⊓ Zloc h.le L μ :=
        ⟨hUμU (hNU (Subgroup.subset_closure ⟨y, hy, rfl⟩)),
          hNZ (Subgroup.subset_closure ⟨y, hy, rfl⟩)⟩
      rw [uloc_inf_zloc h hfull μ] at hmem
      exact hmem
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hH.2.2 hδM
    have hTs : Qv (puAmalgam h.le) ν ≤ stab _ δ := qv_le_stab_of_adj _ hνδ
    have hQs : Qv (puAmalgam h.le) μ ≤ stab _ δ := (qv_le_qv _ h20 hμ hμν).trans hTs
    have hcardC : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ν))) = 2 := by
      have := hUδq
      rw [usup_eq_commutator_uloc h hfull hδM hνδ.symm, card_commutator_eq hψ hTs,
        Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
      exact Nat.pow_right_injective hq this
    have hW : commN (natImage ψ (Qv (puAmalgam h.le) ν)) ≤ fixN (natImage ψ (Qv _ ν)) := by
      intro x hx
      obtain ⟨w, rfl⟩ := natVec_surjective hψ x
      have hw : (w : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L δ, Qv (puAmalgam h.le) ν⁆ :=
        (mem_commutator_iff_natVec hψ hTs w).mpr hx
      rw [← usup_eq_commutator_uloc h hfull hδM hνδ.symm] at hw
      have hwC : (w : (puAmalgam h.le).Universal) ∈
          Subgroup.centralizer (Qv (puAmalgam h.le) ν : Set _) :=
        ((zh_inf_uloc h hfull hδM hνδ.symm).le ⟨hUδZ hw, w.2⟩).2
      exact (mem_centralizer_iff_natVec hψ hTs w).mp hwC
    have hQne : fixN (natImage ψ (Qv (puAmalgam h.le) μ)) ≠ ⊤ := by
      intro htop
      have hcen : ⁅Uloc h.le L δ, Qv (puAmalgam h.le) μ⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := (mem_centralizer_iff_natVec hψ hQs ⟨w, hw⟩).mpr
          (htop ▸ Submodule.mem_top : natVec hψ ⟨w, hw⟩ ∈ fixN (natImage ψ (Qv _ μ)))
        exact Subgroup.mem_centralizer_iff.mp this y hy
      have h1 : ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) μ⁆ = ⊥ := by
        rw [commutator_zm_eq_uloc h hfull hδM hQs, hcen]
      rw [hcomm] at h1
      rw [h1, Subgroup.card_bot] at hUμq
      have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have hfixT : fixN (natImage ψ (Qv (puAmalgam h.le) ν)) =
        commN (natImage ψ (Qv (puAmalgam h.le) ν)) := by
      refine eq_of_le_of_finrank_eq_two hW hcardC fun htop => hQne ?_
      exact eq_top_iff.mpr (htop ▸ fixN_anti (natImage_mono (qv_le_qv _ h20 hμ hμν)))
    have hfixQ : fixN (natImage ψ (Qv (puAmalgam h.le) μ)) =
        commN (natImage ψ (Qv (puAmalgam h.le) ν)) :=
      eq_of_le_of_finrank_eq_two
        (hfixT ▸ fixN_anti (natImage_mono (qv_le_qv _ h20 hμ hμν))) hcardC hQne
    have huC : (u : (puAmalgam h.le).Universal) ∈
        Subgroup.centralizer (Qv (puAmalgam h.le) μ : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hu1 y hy
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    have hcoord := (mem_centralizer_iff_natVec hψ hQs ⟨u, hu⟩).mp huC
    rw [hfixQ] at hcoord
    have := (mem_commutator_iff_natVec hψ hTs ⟨u, hu⟩).mpr hcoord
    rw [← usup_eq_commutator_uloc h hfull hδM hνδ.symm, hUeq] at this
    exact this
  · exact le_inf (hUeq ▸ hUδU) (hUμZ.trans ((zh_le_zm _ hμν).trans (zm_le_bloc h hb2 hμ)))

end Dual

end CFSG.Quasithin.MS93.S4A
