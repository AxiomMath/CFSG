module

public import CFSG.Quasithin.MS93.S46R468N1
public import CFSG.Quasithin.MS93.S46R468C4T
public import CFSG.Quasithin.MS93.S46R468B3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

theorem sup_span_eq_of_finrank_two {F : Type} [Field F] {W : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 2) {u a : Fin 3 → F} (hu : u ∈ W) (ha : a ∈ W) (hu0 : u ≠ 0)
    (hau : a ∉ F ∙ u) : F ∙ u ⊔ F ∙ a = W := by
  have ha0 : a ≠ 0 := fun h => hau (h ▸ Submodule.zero_mem _)
  refine Submodule.eq_of_le_of_finrank_eq (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)) ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F ∙ u) (F ∙ a)
  have h2 : Module.finrank F ↥((F ∙ u) ⊓ (F ∙ a)) = 0 := by
    by_contra hne
    have hle : Module.finrank F ↥((F ∙ u) ⊓ (F ∙ a)) ≤ 1 := by
      rw [← finrank_span_singleton (K := F) hu0]
      exact Submodule.finrank_mono inf_le_left
    have he1 : (F ∙ u) ⊓ (F ∙ a) = F ∙ u := Submodule.eq_of_le_of_finrank_eq inf_le_left
      (by rw [finrank_span_singleton hu0]; omega)
    have he2 : (F ∙ u) ⊓ (F ∙ a) = F ∙ a := Submodule.eq_of_le_of_finrank_eq inf_le_right
      (by rw [finrank_span_singleton ha0]; omega)
    exact hau (he1 ▸ he2.symm ▸ Submodule.mem_span_singleton_self a)
  rw [finrank_span_singleton hu0, finrank_span_singleton ha0, h2] at h1
  rw [hW]
  omega

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_line_of_coord (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {u a w : Fin 3 → F} (hu : u ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)))
    (ha : a ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ))) (hli : LinearIndependent F ![u, a])
    (hli' : LinearIndependent F ![u, w]) :
    ∃ m, (puAmalgam c.pu.le).treeGraph.Adj x m ∧ ∀ y : ↥(Uloc c.pu.le L x),
      (y : (puAmalgam c.pu.le).Universal) ∈ Usup _ x m ↔ natVec hψ y ∈ F ∙ u ⊔ F ∙ w := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hu0 : u ≠ 0 := by simpa using hli.ne_zero 0
  have hau : a ∉ F ∙ u := fun h => by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    exact (LinearIndependent.pair_iff' hu0).mp hli t ht
  have hW : F ∙ u ⊔ F ∙ a = fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) :=
    sup_span_eq_of_finrank_two (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxℓ hψ).1 hu ha hu0
      hau
  obtain ⟨A, hAu, hAw⟩ := exists_sl3_mulVec_pair hli hli'
  obtain ⟨k, hk⟩ := toSL3_surjective hψs A
  have hkx : (k : (puAmalgam c.pu.le).Universal) • x = x := MulAction.mem_stabilizer_iff.mp k.2
  refine ⟨(k : (puAmalgam c.pu.le).Universal) • ℓ, ?_, fun y => ?_⟩
  · have := (adj_smul _ (k : (puAmalgam c.pu.le).Universal) x ℓ).mpr hxℓ
    rwa [hkx] at this
  · have hU : Usup (puAmalgam c.pu.le) x ((k : (puAmalgam c.pu.le).Universal) • ℓ) =
        (Usup (puAmalgam c.pu.le) x ℓ).map
          (MulAut.conj (k : (puAmalgam c.pu.le).Universal)).toMonoidHom := by
      rw [← usup_smul, hkx]
    rw [hU, mem_map_conj_iff_coord hψ (usup_le_uloc' c.pu hfull hx hxℓ)
      (mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψ) k y, hk, ← hW, Submodule.map_sup,
      Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hAu, hAw]

theorem exists_third_line (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β ℓ n : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    (hxn : (puAmalgam c.pu.le).treeGraph.Adj x n) (hPℓ : P ≤ Usup (puAmalgam c.pu.le) x ℓ)
    (hPn : P ≤ Usup (puAmalgam c.pu.le) x n) :
    ∃ m, (puAmalgam c.pu.le).treeGraph.Adj x m ∧ P ≤ Usup (puAmalgam c.pu.le) x m ∧
      Usup (puAmalgam c.pu.le) x m ≠ Usup _ x ℓ ∧ Usup (puAmalgam c.pu.le) x m ≠ Usup _ x n := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, -, hp1, hPU, hPp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP
  obtain ⟨u, hu0, rfl⟩ := exists_span_eq_of_finrank_eq_one hp1
  set Wℓ := fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) with hWℓ
  set Wn := fixN (natImage ψ (Qv (puAmalgam c.pu.le) n)) with hWn
  have hmℓ := mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψ
  have hmn := mem_usup_iff c.pu c.via h464' hsq hx hxn hψ
  obtain ⟨y₀, hy₀⟩ := natVec_surjective hψ u
  have hy₀P : (y₀ : (puAmalgam c.pu.le).Universal) ∈ P :=
    (hPp y₀).mpr (by rw [hy₀]; exact Submodule.mem_span_singleton_self u)
  have huℓ : u ∈ Wℓ := hy₀ ▸ (hmℓ y₀).mp (hPℓ hy₀P)
  have hun : u ∈ Wn := hy₀ ▸ (hmn y₀).mp (hPn hy₀P)
  have hWℓ2 : Module.finrank F Wℓ = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxℓ hψ).1
  have hWn2 : Module.finrank F Wn = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxn hψ).1
  have htop : ∀ {W : Submodule F (Fin 3 → F)}, Module.finrank F W = 2 → ∃ z, z ∉ W := by
    intro W hW2
    have hWt : W < ⊤ := lt_top_iff_ne_top.mpr fun he => by
      have h1 := hW2
      rw [he, finrank_top, Module.finrank_fin_fun] at h1
      omega
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt hWt
    exact ⟨z, hz⟩
  obtain ⟨w, hwℓ, hwn⟩ : ∃ w, w ∉ Wℓ ∧ w ∉ Wn := by
    obtain ⟨z₁, hz₁⟩ := htop hWℓ2
    by_cases h1 : z₁ ∈ Wn
    · obtain ⟨z₂, hz₂⟩ := htop hWn2
      by_cases h2 : z₂ ∈ Wℓ
      · refine ⟨z₁ + z₂, fun h => hz₁ ?_, fun h => hz₂ ?_⟩
        · have := Wℓ.sub_mem h h2
          rwa [add_sub_cancel_right] at this
        · have := Wn.sub_mem h h1
          rwa [add_sub_cancel_left] at this
      · exact ⟨z₂, h2, hz₂⟩
    · exact ⟨z₁, hz₁, h1⟩
  have hlt : F ∙ u < Wℓ := lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr huℓ)
    fun he => by
      have h1 := finrank_span_singleton (K := F) hu0
      rw [he, hWℓ2] at h1
      omega
  obtain ⟨a, haℓ, hau⟩ := IsConcreteLE.exists_of_lt hlt
  have hli : ∀ {b : Fin 3 → F}, b ∉ F ∙ u → LinearIndependent F ![u, b] := fun {b} hb =>
    (LinearIndependent.pair_iff' hu0).mpr fun t ht => hb (ht ▸ Submodule.smul_mem _ t
      (Submodule.mem_span_singleton_self u))
  have hwu : w ∉ F ∙ u := fun h => hwℓ (((Submodule.span_singleton_le_iff_mem _ _).mpr huℓ) h)
  obtain ⟨m, hxm, hm⟩ := exists_line_of_coord h464 h465 c hx hxℓ hψs hψ huℓ haℓ (hli hau) (hli hwu)
  have hUm : Usup (puAmalgam c.pu.le) x m ≤ Uloc c.pu.le L x := usup_le_uloc' c.pu hfull hx hxm
  refine ⟨m, hxm, fun y hy => ?_, fun he => hwℓ ?_, fun he => hwn ?_⟩
  · have hyU := hPU hy
    exact (hm ⟨y, hyU⟩).mpr (Submodule.mem_sup_left ((hPp ⟨y, hyU⟩).mp hy))
  · have h1 := (S45.eq_iff_of_natVec_iff hψ hUm (usup_le_uloc' c.pu hfull hx hxℓ) hm hmℓ).mp he
    rw [hWℓ, ← h1]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
  · have h1 := (S45.eq_iff_of_natVec_iff hψ hUm (usup_le_uloc' c.pu hfull hx hxn) hm hmn).mp he
    rw [hWn, ← h1]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)

theorem commutator_pencil_le_vv_of_key (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x m l : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m) (hxl : (puAmalgam c.pu.le).treeGraph.Adj x l)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPl : P ≤ Usup (puAmalgam c.pu.le) x l)
    (hkey : pencil (puAmalgam c.pu.le) x P ≤ Vv _ m ⊔ Vv _ l ⊔ ptSub _ x P)
    {t : (puAmalgam c.pu.le).Universal} (ht : t ∈ Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P)
    {y : (puAmalgam c.pu.le).Universal} (hy : y ∈ pencil (puAmalgam c.pu.le) x P) :
    ⁅y, t⁆ ∈ Vv (puAmalgam c.pu.le) l := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  have hm : ¬ IsMVtx (puAmalgam c.pu.le) m := (isMVtx_iff_of_adj _ hxm).mp hx
  have hZl : ZM (puAmalgam c.pu.le) x ≤ Vv _ l := zm_le_vv_of_adj hxl.symm hx
  have hQl : Qv (puAmalgam c.pu.le) x ≤ Subgroup.normalizer (Vv (puAmalgam c.pu.le) l : Set _) :=
    (qv_le_stab_of_adj _ hxl).trans (stab_le_normalizer_vv c.pu l)
  have htl : t ∈ Subgroup.normalizer (Vv (puAmalgam c.pu.le) l : Set _) :=
    ptQ_le_normalizer_vv h464 h465 h466a c hx hxl hPl ht.2
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {y | y ∈ Qv (puAmalgam c.pu.le) x ∧ ⁅y, t⁆ ∈ Vv (puAmalgam c.pu.le) l}
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', ?_⟩
        have e : ⁅a * b, t⁆ = a * ⁅b, t⁆ * a⁻¹ * ⁅a, t⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hQl ha) _).mp hb'') ha'
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hQl (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ ha') }
  have hVx : ∀ {n}, (puAmalgam c.pu.le).treeGraph.Adj x n →
      Vv (puAmalgam c.pu.le) n ≤ Qv _ x := fun hxn =>
    (I466b.vv_le_vv_of_adj c.pu hx hxn).trans (vv_le_qv c.pu hb hx)
  have hle : Vv (puAmalgam c.pu.le) m ⊔ Vv _ l ⊔ ptSub _ x P ≤ S := by
    refine sup_le (sup_le (fun v hv => ⟨hVx hxm hv, hZl (zh_le_zm _ hxm
      (commutator_vv_qv_le_zh c.pu h464' hm (Subgroup.commutator_mem_commutator hv ht.1)))⟩)
      (fun v hv => ⟨hVx hxl hv, ?_⟩)) (fun v hv => ⟨(ptSub_le_vv c hx P).trans
        (vv_le_qv c.pu hb hx) hv, hZl (commutator_ptSub_ptQ_le c hx P
          (Subgroup.commutator_mem_commutator hv ht.2))⟩)
    have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp htl _).mp (Subgroup.inv_mem _ hv))
  exact (hle (hkey hy)).2

theorem BadConf.false_of_key (h464 : I464) (h465 : I465) (h466a : I466a) {c : Hyp46 M T L φ}
    {α₀ α₀' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α₀ α₀') {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    (hkey : ∀ ℓ ℓ', (puAmalgam c.pu.le).treeGraph.Adj x ℓ →
      (puAmalgam c.pu.le).treeGraph.Adj x ℓ' → P ≤ Usup (puAmalgam c.pu.le) x ℓ →
      P ≤ Usup (puAmalgam c.pu.le) x ℓ' → Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x ℓ' →
      pencil (puAmalgam c.pu.le) x P ≤ Vv _ ℓ ⊔ Vv _ ℓ' ⊔ ptSub _ x P) : False := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  have hc := hB.crit
  have hα₀β₀ : (puAmalgam c.pu.le).treeGraph.Adj α₀ (geo _ α₀ α₀' 1) := by
    have := adj_geo_crit c.b4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hxβ).mp hx
  have hPβ : P ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  have hPc := card_of_isPtOn h464 h465 c hx hxβ hP
  apply not_commutator_vv_ptQ_le h464 h465 h466a c hB.not_s468At hc.1 hα₀β₀ hx hxβ hP
  rw [Subgroup.commutator_le]
  intro v hv t ht
  refine mem_bzero_of_forall_vv h464 h465 c hx hxβ hP fun l hxl hPl => ?_
  have hnβ : ⁅v, t⁆ ∈ Vv (puAmalgam c.pu.le) β := by
    have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp
      (ptQ_le_normalizer_vv h464 h465 h466a c hx hxβ hPβ ht) _).mp (Subgroup.inv_mem _ hv))
  by_cases hlβ : Usup (puAmalgam c.pu.le) x l = Usup _ x β
  · rw [vv_eq_of_usup_eq h464 h465 h466a c hx hxl hxβ hlβ]
    exact hnβ
  obtain ⟨m, hxm, hPm, hmβ, hml⟩ := exists_third_line h464 h465 c hx hxβ hP hxβ hxl hPβ hPl
  have hcard := card_usup_inf_usup h464 h465 c hx hxβ hxm (Ne.symm hmβ)
  have : Finite ↥(Usup (puAmalgam c.pu.le) x β ⊓ Usup _ x m) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)
  have hPe : P = Usup (puAmalgam c.pu.le) x β ⊓ Usup _ x m :=
    Subgroup.eq_of_le_of_card_ge (le_inf hPβ hPm) (by rw [hcard, hPc])
  have hD1 := ptQ_le_sup_qv_inf h464 h465 h466a c hx hxβ hxm (Ne.symm hmβ) hPe ht
  have hnorm : Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P ≤
      Subgroup.normalizer ((Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P : Subgroup _) : Set _) :=
    fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨ptQ_le_normalizer_qv h464 h465 h466a c hx hxm hPm ha.2, Subgroup.le_normalizer ha.2⟩
  have h1 : t ∈ (((Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P) ⊔
      (Qv (puAmalgam c.pu.le) m ⊓ ptQ _ x P) : Subgroup _) : Set _) := hD1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at h1
  obtain ⟨a, ha, b, hb', rfl⟩ := h1
  have e : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine Subgroup.mul_mem _ (zm_le_vv_of_adj hxl.symm hx (zh_le_zm _ hxβ
    (commutator_vv_qv_le_zh c.pu h464' hβ (Subgroup.commutator_mem_commutator hv ha.1)))) ?_
  exact (Subgroup.mem_normalizer_iff.mp (ptQ_le_normalizer_vv h464 h465 h466a c hx hxl hPl ha.2)
    _).mp (commutator_pencil_le_vv_of_key h464 h465 h466a c hx hxm hxl hPl
      (hkey m l hxm hxl hPm hPl hml) hb' (vv_le_pencil hxβ hPβ hv))

theorem key_of_trivial (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hPc : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    (htriv : ∀ k ∈ ptL (puAmalgam c.pu.le) x ψ, Odd (orderOf k) →
      ∀ v ∈ pencil (puAmalgam c.pu.le) x P, ⁅k, v⁆ ∈ ptSub (puAmalgam c.pu.le) x P) :
    ∀ ℓ ℓ', (puAmalgam c.pu.le).treeGraph.Adj x ℓ → (puAmalgam c.pu.le).treeGraph.Adj x ℓ' →
      P ≤ Usup (puAmalgam c.pu.le) x ℓ → P ≤ Usup (puAmalgam c.pu.le) x ℓ' →
      Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x ℓ' →
      pencil (puAmalgam c.pu.le) x P ≤ Vv _ ℓ ⊔ Vv _ ℓ' ⊔ ptSub _ x P := by
  intro ℓ ℓ' hxℓ _ hPℓ _ _
  have hPU := le_uloc_of_isPtOn c hx hP
  have hKs : ptL (puAmalgam c.pu.le) x ψ ≤ stab _ x := ptL_le_stab ψ
  have hKU : ptL (puAmalgam c.pu.le) x ψ ≤
      Subgroup.normalizer (ptSub (puAmalgam c.pu.le) x P : Set _) :=
    le_normalizer_ptSub hKs (ptL_le_normalizer c hψU hPU hPc)
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ ptL (puAmalgam c.pu.le) x ψ ∧
        ∀ v ∈ pencil (puAmalgam c.pu.le) x P, ⁅k, v⁆ ∈ ptSub (puAmalgam c.pu.le) x P}
      one_mem' := ⟨Subgroup.one_mem _, fun v _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun v hv => ?_⟩
        have e : ⁅a * b, v⁆ = a * ⁅b, v⁆ * a⁻¹ * ⁅a, v⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hKU ha) _).mp (hb' v hv))
          (ha' v hv)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun v hv => ?_⟩
        have hv' : a⁻¹ * v * a⁻¹⁻¹ ∈ pencil (puAmalgam c.pu.le) x P :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pencil hKs
            (ptL_le_normalizer c hψU hPU hPc) (Subgroup.inv_mem _ ha)) v).mp hv
        have e : ⁅a⁻¹, v⁆ = ⁅a, a⁻¹ * v * a⁻¹⁻¹⁆⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.inv_mem _ (ha' _ hv') }
  have hclS : Subgroup.closure {g | g ∈ ptL (puAmalgam c.pu.le) x ψ ∧ Odd (orderOf g)} ≤ S :=
    (Subgroup.closure_le _).mpr fun g hg => ⟨hg.1, htriv g hg.1 hg.2⟩
  refine (pencil_le fun m hxm hPm => ?_).trans (sup_le_sup_right le_sup_left _)
  obtain ⟨k, hk, hkm⟩ := exists_closure_odd_smul h464 h465 c hx hψs hψU hPc hxℓ hxm hPℓ hPm
  have hkS := hclS hk
  have hkx : k • x = x := MulAction.mem_stabilizer_iff.mp (hKs hkS.1)
  have hxkℓ : (puAmalgam c.pu.le).treeGraph.Adj x (k • ℓ) := by
    have := (adj_smul _ k x ℓ).mpr hxℓ
    rwa [hkx] at this
  rw [← vv_eq_of_usup_eq h464 h465 h466a c hx hxkℓ hxm hkm,
    show Vv (puAmalgam c.pu.le) (k • ℓ) = (Vv _ ℓ).map (MulAut.conj k).toMonoidHom from
      vi_smul _ k ℓ 2]
  rintro _ ⟨v, hv, rfl⟩
  have e : (MulAut.conj k).toMonoidHom v = ⁅k, v⁆ * v := by
    simp [commutatorElement_def, mul_assoc]
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup (hkS.2 v (vv_le_pencil hxℓ hPℓ hv)) hv

end CFSG.Quasithin.MS93.S46R
