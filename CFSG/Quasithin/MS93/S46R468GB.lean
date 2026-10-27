module

public import CFSG.Quasithin.MS93.S46R468B3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commutator_zm_trichotomy (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ρ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) {A : Subgroup (puAmalgam c.pu.le).Universal}
    (hA : A ≤ Qv (puAmalgam c.pu.le) ρ) :
    ⁅ZM (puAmalgam c.pu.le) x, A⁆ = ⊥ ∨
      (∃ P, IsPtOn (puAmalgam c.pu.le) x ρ P ∧ ⁅ZM (puAmalgam c.pu.le) x, A⁆ = P) ∨
      ⁅ZM (puAmalgam c.pu.le) x, A⁆ = Usup (puAmalgam c.pu.le) x ρ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hAs : A ≤ stab (puAmalgam c.pu.le) x := hA.trans (qv_le_stab_of_adj _ hxρ.symm)
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨hW2, hcW⟩ := I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxρ hψ
  set W := fixN (natImage ψ (Qv (puAmalgam c.pu.le) ρ)) with hWdef
  set C := commN (natImage ψ A) with hCdef
  have hCW : C ≤ W := by
    rw [← hcW]
    refine commN_mono fun B hB => ?_
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hB
    exact mem_natImage.mpr ⟨a, hA ha, rfl⟩
  have hUC : ⁅Uloc c.pu.le L x, A⁆ ≤ Uloc c.pu.le L x :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hAs.trans hψ.1)
  rw [commutator_zm_eq_uloc c.pu hfull hx hAs]
  have heq : ∀ {S : Subgroup (puAmalgam c.pu.le).Universal} {s : Submodule F (Fin 3 → F)},
      S ≤ Uloc c.pu.le L x →
      (∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ S ↔ natVec hψ u ∈ s) →
      C = s → ⁅Uloc c.pu.le L x, A⁆ = S := by
    intro S s hSU hS hCs
    ext y
    constructor
    · intro hy
      have h1 := (mem_commutator_iff_natVec hψ hAs ⟨y, hUC hy⟩).mp hy
      rw [← hCdef, hCs] at h1
      exact (hS ⟨y, hUC hy⟩).mpr h1
    · intro hy
      have h1 := (hS ⟨y, hSU hy⟩).mp hy
      rw [← hCs, hCdef] at h1
      exact (mem_commutator_iff_natVec hψ hAs ⟨y, hSU hy⟩).mpr h1
  have hle2 : Module.finrank F C ≤ 2 := hW2 ▸ Submodule.finrank_mono hCW
  rcases Nat.lt_or_ge (Module.finrank F C) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Module.finrank F C) 1 with hlt' | hge'
    ·
      left
      have hC0 : C = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      refine heq bot_le (fun u => ?_) hC0
      rw [Submodule.mem_bot, Subgroup.mem_bot]
      constructor
      · intro hu
        have : u = 1 := Subtype.ext hu
        rw [this, natVec_one]
      · intro hu
        have : u = 1 := natVec_injective hψ (by rw [hu, natVec_one])
        rw [this]
        rfl
    ·
      right; left
      have hC1 : Module.finrank F C = 1 := by omega
      have hCne : C ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hC1; omega
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
      obtain ⟨P, hP, hPU, hPc⟩ := exists_isPtOn_span h464 h465 c hx hxρ hψs hψ (hCW hv) hv0
      exact ⟨P, hP, heq hPU hPc (eq_span_singleton_of_mem_of_finrank_eq_one hC1 hv hv0)⟩
  ·
    right; right
    have hCW' : C = W :=
      Submodule.eq_of_le_of_finrank_eq hCW (by rw [hW2]; omega)
    exact heq (usup_le_uloc' c.pu hfull hx hxρ)
      (mem_usup_iff c.pu c.via h464' hsq hx hxρ hψ) hCW'

theorem exists_root_crit (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α')
    {p : Subgroup (puAmalgam c.pu.le).Universal}
    (hp : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) p)
    (hZp : ZM (puAmalgam c.pu.le) α' ≤ ptQ _ α p) {x ℓ : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P) :
    ∃ α'', IsCritical (puAmalgam c.pu.le) x α'' ∧
      Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) = Usup _ x ℓ ∧
      ZM (puAmalgam c.pu.le) α'' ≤ ptQ _ x P ∧
      (Qv (puAmalgam c.pu.le) x).relIndex (ZM _ α'') = Fintype.card F := by
  have hb4 := c.b4
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ hc.1 hαβ hx hxℓ
  have hc₁ : IsCritical (puAmalgam c.pu.le) x (g • α') := by
    rw [← hg1]; exact (isCritical_smul _ g α α').mpr hc
  have hgeo : geo (puAmalgam c.pu.le) x (g • α') 1 = ℓ := by
    rw [← hg1, geo_smul, hg2]
  have hp₁ : IsPtOn (puAmalgam c.pu.le) x ℓ (p.map (MulAut.conj g).toMonoidHom) := by
    rw [← hg1, ← hg2]; exact (isPtOn_smul g α _ p).mpr hp
  have hZp₁ : ZM (puAmalgam c.pu.le) (g • α') ≤
      ptQ (puAmalgam c.pu.le) x (p.map (MulAut.conj g).toMonoidHom) := by
    rw [zm_smul, ← hg1, ptQ_smul]
    exact Subgroup.map_mono hZp
  obtain ⟨k, hk, hkN, hkp⟩ := exists_conj_pt h464 h465 h466a c hx hxℓ hp₁ hP
  have hkx : k • x = x := MulAction.mem_stabilizer_iff.mp hk
  have hc'' : IsCritical (puAmalgam c.pu.le) x (k • g • α') := by
    have := (isCritical_smul _ k x (g • α')).mpr hc₁
    rwa [hkx] at this
  have e1 : geo (puAmalgam c.pu.le) x (k • g • α') 1 = k • ℓ := by
    rw [← hkx, geo_smul, hgeo]
  have e2 : Usup (puAmalgam c.pu.le) x (k • ℓ) =
      (Usup (puAmalgam c.pu.le) x ℓ).map (MulAut.conj k).toMonoidHom := by
    rw [← usup_smul, hkx]
  have hU'' : Usup (puAmalgam c.pu.le) x (geo _ x (k • g • α') 1) = Usup _ x ℓ := by
    rw [e1, e2, Usup, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (stab_le_normalizer_of_smul _ (fun g' δ => zv_smul _ g' δ) x hk),
      map_conj_eq_of_mem_normalizer hkN]
  have hZQ : ZM (puAmalgam c.pu.le) (k • g • α') ≤ ptQ _ x P := by
    have e3 : ptQ (puAmalgam c.pu.le) x ((p.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj k).toMonoidHom) = (ptQ (puAmalgam c.pu.le) x
          (p.map (MulAut.conj g).toMonoidHom)).map (MulAut.conj k).toMonoidHom := by
      rw [← ptQ_smul, hkx]
    rw [zm_smul, ← hkp, e3]
    exact Subgroup.map_mono hZp₁
  refine ⟨k • g • α', hc'', hU'', hZQ, le_antisymm ?_ ?_⟩
  ·
    have hx1 : (puAmalgam c.pu.le).treeGraph.Adj x (geo _ x (k • g • α') 1) := by
      have := adj_geo_crit hb4 hc'' (i := 0) (by omega)
      rwa [geo_zero] at this
    have hZT : ZM (puAmalgam c.pu.le) (k • g • α') ≤ Qv _ (geo _ x (k • g • α') 1) :=
      zm_le_qv_of_dist_lt _ (hc''.isMVtx_right _ c.pu.hyp20) (by
        rw [tdist_comm, dist_geo_crit_right hb4 hc'' (by omega)]
        omega)
    have hPc := card_of_isPtOn h464 h465 c hx hxℓ hP
    have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPc]; exact Fintype.card_ne_zero)
    have hle := relIndex_qv_le_of_commutator_mem h464 h465 h466a c hx hx1 (P := P)
      (A := ZM _ (k • g • α')) (fun a ha => hZT ha)
      fun a ha z hz => (mem_ptQ.mp (hZQ ha)).2.2 z hz
    rwa [hPc] at hle
  ·
    rw [← relIndex_zm_comm c.pu c.via c.pu.centHyp hc'']
    rcases crit_type c.pu c.via c.pu.centHyp hc'' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
    · rw [h]
      exact Nat.le_self_pow (by norm_num) _
    · rw [h]
    · rw [h]

theorem commutator_commutator_mem_zm_of_root (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x m ℓ α'' : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    (hneℓ : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x m)
    {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPe : P = Usup (puAmalgam c.pu.le) x m ⊓ Usup _ x ℓ)
    (hc'' : IsCritical (puAmalgam c.pu.le) x α'')
    (hU'' : Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) = Usup _ x ℓ)
    (hZQ : ZM (puAmalgam c.pu.le) α'' ≤ ptQ _ x P)
    (hidx : (Qv (puAmalgam c.pu.le) x).relIndex (ZM _ α'') = Fintype.card F)
    {v t₁ t₂ : (puAmalgam c.pu.le).Universal} (hv : v ∈ Vv (puAmalgam c.pu.le) m)
    (ht₁ : t₁ ∈ ptQ (puAmalgam c.pu.le) x P) (ht₂ : t₂ ∈ ptQ (puAmalgam c.pu.le) x P) :
    ⁅⁅v, t₁⁆, t₂⁆ ∈ ZM (puAmalgam c.pu.le) x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hPm : P ≤ Usup (puAmalgam c.pu.le) x m := by rw [hPe]; exact inf_le_left
  have hPℓ : IsPtOn (puAmalgam c.pu.le) x ℓ P :=
    ⟨m, hxm, Ne.symm hneℓ, by rw [hPe, inf_comm]⟩
  have hx1 : (puAmalgam c.pu.le).treeGraph.Adj x (geo _ x α'' 1) := by
    have := adj_geo_crit c.b4 hc'' (i := 0) (by omega)
    rwa [geo_zero] at this
  have hTeq : Qv (puAmalgam c.pu.le) (geo _ x α'' 1) = Qv _ ℓ :=
    qv_eq_of_usup_eq h464 h465 h466a c hx hx1 hxℓ hU''
  have hZT : ZM (puAmalgam c.pu.le) α'' ≤ Qv _ ℓ := by
    rw [← hTeq]
    exact zm_le_qv_of_dist_lt _ (hc''.isMVtx_right _ c.pu.hyp20) (by
      rw [tdist_comm, dist_geo_crit_right c.b4 hc'' (by omega)]
      have := c.b4
      omega)
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x :=
    (le_uloc_of_isPtOn c hx hPℓ).trans (uloc_le_zm c.pu hfull hx)
  have hQP := qv_le_ptQ c hx hPZ
  have hZs : ZM (puAmalgam c.pu.le) α'' ≤ stab _ x := hZQ.trans fun t ht => (mem_ptQ.mp ht).1
  have hZQn : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) x : Set _) :=
    hZs.trans (stab_le_normalizer_qv _ x)
  have hidx' : (Qv (puAmalgam c.pu.le) x).relIndex (ZM _ α'' ⊔ Qv _ x) = Fintype.card F := by
    rw [S46.relIndex_sup_of_le_normalizer hZQn]
    exact hidx
  have hsub : ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ x ≤ Qv _ ℓ ⊓ ptQ _ x P :=
    sup_le (le_inf hZT hZQ) (le_inf (qv_le_qv _ c.pu.hyp20 hx hxℓ) hQP)
  have hroot : Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P ≤ ZM _ α'' ⊔ Qv _ x := by
    have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) x) (ZM _ α'' ⊔ Qv _ x)
      (Qv _ ℓ ⊓ ptQ _ x P) le_sup_right hsub
    rw [hidx', relIndex_qv_inf_ptQ h464 h465 h466a c hx hxℓ hPℓ] at hmul
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have h1 : (ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ x).relIndex (Qv _ ℓ ⊓ ptQ _ x P) = 1 :=
      Nat.eq_of_mul_eq_mul_left hq (hmul.trans (mul_one _).symm)
    exact Subgroup.relIndex_eq_one.mp h1
  have hTm : Qv (puAmalgam c.pu.le) x ≤ Qv _ m := qv_le_qv _ c.pu.hyp20 hx hxm
  have hQP' : ptQ (puAmalgam c.pu.le) x P ≤ ZM _ α'' ⊔ Qv _ m := by
    refine (ptQ_le_sup_qv_inf h464 h465 h466a c hx hxℓ hxm hneℓ
      (by rw [hPe, inf_comm])).trans
      (sup_le (hroot.trans (sup_le le_sup_left (hTm.trans le_sup_right)))
        (inf_le_left.trans le_sup_right))
  have hZn : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) m : Set _) :=
    hZQ.trans (ptQ_le_normalizer_qv h464 h465 h466a c hx hxm hPm)
  have hZnV : ZM (puAmalgam c.pu.le) α'' ≤ Subgroup.normalizer (Vv (puAmalgam c.pu.le) m : Set _) :=
    hZQ.trans (ptQ_le_normalizer_vv h464 h465 h466a c hx hxm hPm)
  have hdec : ∀ {t}, t ∈ ptQ (puAmalgam c.pu.le) x P →
      ∃ z ∈ ZM (puAmalgam c.pu.le) α'', ∃ s ∈ Qv (puAmalgam c.pu.le) m, z * s = t := by
    intro t ht
    have h1 : t ∈ ((ZM (puAmalgam c.pu.le) α'' ⊔ Qv _ m : Subgroup _) : Set _) := hQP' ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn] at h1
    obtain ⟨z, hz, s, hs, he⟩ := h1
    exact ⟨z, hz, s, hs, he⟩
  have hZxn : stab (puAmalgam c.pu.le) x ≤ Subgroup.normalizer (ZM (puAmalgam c.pu.le) x : Set _) :=
    stab_le_normalizer_zm _ x
  have hVm : Vv (puAmalgam c.pu.le) m ≤ stab _ x :=
    (vv_le_qv_of_dist_le_two c.b4 hm (by rw [SimpleGraph.dist_self]; omega)).trans
      (qv_le_stab_of_adj _ hxm.symm)
  have hVTm : ∀ {w s}, w ∈ Vv (puAmalgam c.pu.le) m → s ∈ Qv (puAmalgam c.pu.le) m →
      ⁅w, s⁆ ∈ ZM (puAmalgam c.pu.le) x := fun hw hs =>
    zh_le_zm _ hxm (commutator_vv_qv_le_zh c.pu h464' hm (Subgroup.commutator_mem_commutator hw hs))
  have hnV : ∀ {z w}, z ∈ ZM (puAmalgam c.pu.le) α'' → w ∈ Vv (puAmalgam c.pu.le) m →
      ⁅w, z⁆ ∈ Vv (puAmalgam c.pu.le) m := fun {z w} hz hw => by
    have e : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hw ((Subgroup.mem_normalizer_iff.mp (hZnV hz) _).mp
      (Subgroup.inv_mem _ hw))
  have hne1 : Usup (puAmalgam c.pu.le) x (geo _ x α'' 1) ≠ Usup _ x m := by
    rw [hU'']
    exact hneℓ
  obtain ⟨z₁, hz₁, s₁, hs₁, rfl⟩ := hdec ht₁
  obtain ⟨z₂, hz₂, s₂, hs₂, rfl⟩ := hdec ht₂
  have e1 : ⁅v, z₁ * s₁⁆ = ⁅v, z₁⁆ * (z₁ * ⁅v, s₁⁆ * z₁⁻¹) := by
    simp only [commutatorElement_def]; group
  set y := ⁅v, z₁⁆ with hydef
  set ζ := z₁ * ⁅v, s₁⁆ * z₁⁻¹ with hζdef
  have hyV : y ∈ Vv (puAmalgam c.pu.le) m := hnV hz₁ hv
  have hζ : ζ ∈ ZM (puAmalgam c.pu.le) x :=
    (Subgroup.mem_normalizer_iff.mp (hZxn (hZs hz₁)) _).mp (hVTm hv hs₁)
  rw [e1]
  have e2 : ⁅y * ζ, z₂ * s₂⁆ = y * ⁅ζ, z₂ * s₂⁆ * y⁻¹ * ⁅y, z₂ * s₂⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  have hζt : ⁅ζ, z₂ * s₂⁆ ∈ ZM (puAmalgam c.pu.le) x := hPZ ((mem_ptQ.mp ht₂).2.2 ζ hζ)
  have e3 : ⁅y, z₂ * s₂⁆ = ⁅y, z₂⁆ * (z₂ * ⁅y, s₂⁆ * z₂⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e3]
  refine Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hZxn (hVm hyV)) _).mp hζt)
    (Subgroup.mul_mem _ (commutator_commutator_mem_zm_of_crit h464 h465 h466a c hc'' hxm hne1
      hZnV hv hz₁ hz₂) ((Subgroup.mem_normalizer_iff.mp (hZxn (hZs hz₂)) _).mp (hVTm hyV hs₂)))

end CFSG.Quasithin.MS93.S46R
