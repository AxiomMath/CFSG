module

public import CFSG.Quasithin.MS93.S46R468B1
public import CFSG.Quasithin.MS93.S46R468LvA

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem inf_eq_bot_of_finrank_eq_one {p p' : Submodule F (Fin 3 → F)}
    (hp : Module.finrank F p = 1) (hp' : Module.finrank F p' = 1) (hne : p ≠ p') : p ⊓ p' = ⊥ := by
  by_contra h
  have h1 : 1 ≤ Module.finrank F ↥(p ⊓ p') := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact h
  have h2 : Module.finrank F ↥(p ⊓ p') ≤ Module.finrank F p := Submodule.finrank_mono inf_le_left
  have h3 : Module.finrank F ↥(p ⊓ p') ≤ Module.finrank F p' :=
    Submodule.finrank_mono inf_le_right
  have e1 : p ⊓ p' = p := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have e2 : p ⊓ p' = p' := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  exact hne (e1.symm.trans e2)

theorem finrank_span_single (i : Fin 3) :
    Module.finrank F ↥(F ∙ (Pi.single i 1 : Fin 3 → F)) = 1 :=
  finrank_span_singleton (by
    intro h
    have := congrFun h i
    simp at this)

theorem not_mem_span_of_apply {u w : Fin 3 → F} {j : Fin 3} (hu : u j = 0) (hw : w j ≠ 0) :
    w ∉ F ∙ u := by
  intro h
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h
  simp [hu] at hw

theorem map_pt0_of_mem_stabE0 {A : SL3 F} (hA : A ∈ stabE0) :
    (pt0 : Submodule F (Fin 3 → F)).map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) =
      pt0 := by
  have hlin : (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hv1, hv2⟩ := mem_pt0.mp hv
    have h1 := col_zero_of_mem_stabE0 hA 1
    have h2 := col_zero_of_mem_stabE0 hA 2
    simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ite_false] at h1 h2
    refine mem_pt0.mpr ⟨?_, ?_⟩ <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h1, h2]
  · rw [← hlin, LinearEquiv.finrank_map_eq]

theorem span_ne_of_apply {u w : Fin 3 → F} {j : Fin 3} (hu : u j = 0) (hw : w j ≠ 0) :
    (F ∙ u) ≠ (F ∙ w) := fun h =>
  not_mem_span_of_apply hu hw (h ▸ Submodule.mem_span_singleton_self w)

end Lin

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem inf_eq_bot_of_isPtOn (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P P' : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hP' : IsPtOn (puAmalgam c.pu.le) x β P')
    (hne : P ≠ P') : P ⊓ P' = ⊥ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, -, hp1, hPU, hPp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP
  obtain ⟨p', -, hp1', hPU', hPp'⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP'
  have hpp : p ≠ p' := fun e => hne ((S45.eq_iff_of_natVec_iff hψ hPU hPU' hPp hPp').mpr e)
  have hbot := inf_eq_bot_of_finrank_eq_one hp1 hp1' hpp
  refine le_bot_iff.mp fun y hy => ?_
  have hyU := hPU hy.1
  have h0 : natVec hψ ⟨y, hyU⟩ = 0 := by
    have : natVec hψ ⟨y, hyU⟩ ∈ p ⊓ p' := ⟨(hPp ⟨y, hyU⟩).mp hy.1, (hPp' ⟨y, hyU⟩).mp hy.2⟩
    rw [hbot] at this
    exact this
  have h1 : (⟨y, hyU⟩ : ↥(Uloc c.pu.le L x)) = 1 := natVec_injective hψ (by rw [h0, natVec_one])
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

theorem qv_inf_ptQ_inf_ptQ_le (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P P' : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hP' : IsPtOn (puAmalgam c.pu.le) x β P')
    (hne : P ≠ P') :
    Qv (puAmalgam c.pu.le) β ⊓ ptQ _ x P ⊓ ptQ _ x P' ≤ Qv (puAmalgam c.pu.le) x := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨y, hy, hyβ⟩ : ∃ y ∈ ZM (puAmalgam c.pu.le) x, y ∉ ZH (puAmalgam c.pu.le) β := by
    by_contra hno
    have h1 : (ZH (puAmalgam c.pu.le) β).relIndex (ZM _ x) = 1 :=
      Subgroup.relIndex_eq_one.mpr fun y hy => by_contra fun hn => hno ⟨y, hy, hn⟩
    have h2 := (h465 G M T L F φ c x β hx hxβ).2.1
    have : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  rintro g ⟨⟨hgT, hgP⟩, hgP'⟩
  have h1 : ⁅y, g⁆ ∈ P ⊓ P' := ⟨(mem_ptQ.mp hgP).2.2 y hy, (mem_ptQ.mp hgP').2.2 y hy⟩
  rw [inf_eq_bot_of_isPtOn h464 h465 c hx hxβ hP hP' hne] at h1
  have h2 : y * g = g * y := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
  exact mem_qv_of_commute c.pu c.via h464' hsq h466 hx hxβ hy hyβ hgT h2.symm

omit [Fintype F] in
theorem fixN_rootGroup_sup :
    fixN (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) = coordZero 0 := by
  rw [fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide), inf_idem]

theorem exists_coord_qv_pts (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P P' : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hP' : IsPtOn (puAmalgam c.pu.le) x β P')
    (hne : P ≠ P') :
    ∃ ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      ∃ hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1,
        natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0 ∧
        (∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
          natVec hψU u ∈ F ∙ (Pi.single 1 1 : Fin 3 → F)) ∧
        ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P' ↔
          natVec hψU u ∈ F ∙ (Pi.single 2 1 : Fin 3 → F) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨ψ₀, hψ₀s, hψ₀, hψ₀T⟩ := exists_coord_qv h464 h465 h466a c hx hxβ
  have hW : fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) β)) = coordZero 0 := by
    rw [hψ₀T, fixN_rootGroup_sup]
  have hW2 : Module.finrank F ↥(coordZero 0 : Submodule F (Fin 3 → F)) = 2 := by
    rw [← hW]
    exact (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ₀).1
  obtain ⟨β₁, hxβ₁, hne₁, hPe⟩ := hP
  obtain ⟨β₂, hxβ₂, hne₂, hP'e⟩ := hP'
  set p := fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) β)) ⊓ fixN (natImage ψ₀ (Qv _ β₁)) with hpdef
  set p' := fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) β)) ⊓ fixN (natImage ψ₀ (Qv _ β₂))
    with hp'def
  have hneW : ∀ {ρ : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      Usup (puAmalgam c.pu.le) x ρ ≠ Usup _ x β →
      fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) β)) ≠ fixN (natImage ψ₀ (Qv _ ρ)) :=
    fun {ρ} hxρ hne' heq => hne' ((S45.eq_iff_of_natVec_iff hψ₀ (usup_le_uloc' c.pu hfull hx hxρ)
      (usup_le_uloc' c.pu hfull hx hxβ) (mem_usup_iff c.pu c.via h464' hsq hx hxρ hψ₀)
      (mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ₀)).mpr heq.symm)
  have hp1 : Module.finrank F ↥p = 1 := S45.finrank_inf_eq_one
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ₀).1
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ₁ hψ₀).1 (hneW hxβ₁ hne₁)
  have hp1' : Module.finrank F ↥p' = 1 := S45.finrank_inf_eq_one
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ₀).1
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ₂ hψ₀).1 (hneW hxβ₂ hne₂)
  have hPp : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψ₀ u ∈ p := fun u => by
    rw [hPe, Subgroup.mem_inf, mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ₀,
      mem_usup_iff c.pu c.via h464' hsq hx hxβ₁ hψ₀, Submodule.mem_inf]
  have hP'p : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P' ↔
      natVec hψ₀ u ∈ p' := fun u => by
    rw [hP'e, Subgroup.mem_inf, mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ₀,
      mem_usup_iff c.pu c.via h464' hsq hx hxβ₂ hψ₀, Submodule.mem_inf]
  have hPU : P ≤ Uloc c.pu.le L x := hPe ▸ inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxβ)
  have hP'U : P' ≤ Uloc c.pu.le L x := hP'e ▸ inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxβ)
  have hpp : p ≠ p' := fun e => hne ((S45.eq_iff_of_natVec_iff hψ₀ hPU hP'U hPp hP'p).mpr e)
  have hpW : p ≤ coordZero 0 := hW ▸ inf_le_left
  have hp'W : p' ≤ coordZero 0 := hW ▸ inf_le_left
  have he1W : (F ∙ (Pi.single 1 1 : Fin 3 → F)) ≤ coordZero 0 :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (by
      show (Pi.single 1 1 : Fin 3 → F) 0 = 0
      simp)
  have he2W : (F ∙ (Pi.single 2 1 : Fin 3 → F)) ≤ coordZero 0 :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (by
      show (Pi.single 2 1 : Fin 3 → F) 0 = 0
      simp)
  have he12 : (F ∙ (Pi.single 1 1 : Fin 3 → F)) ≠ (F ∙ (Pi.single 2 1 : Fin 3 → F)) :=
    span_ne_of_apply (j := 2) (by simp) (by simp)
  obtain ⟨A, hAW, hAp, hAp'⟩ := exists_sl3_map_pts hW2 hpW hp'W he1W he2W hp1 hp1'
    (finrank_span_single 1) (finrank_span_single 2) hpp he12
  have hψ := isSumOfNaturalModulesVia_conjSL hψ₀ A
  have hlin : (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply]
  have hfix : ∀ δ, fixN (natImage (conjSL A ψ₀) (Qv (puAmalgam c.pu.le) δ)) =
      (fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) δ))).map
        (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) := fun δ => by
    rw [natImage_conjSL, fixN_map_conj, hlin]
  have hAWW : (coordZero 0 : Submodule F (Fin 3 → F)).map
      (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = coordZero 0 := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hAW v hv
    · rw [← hlin, LinearEquiv.finrank_map_eq]
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) := by
    rw [← hlin]
    exact (Matrix.SpecialLinearGroup.toLin' A).injective
  refine ⟨conjSL A ψ₀, conjSL_surjective hψ₀s, hψ, ?_, fun u => ?_, fun u => ?_⟩
  · rw [I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hx hxβ hψ, hfix, hW, hAWW,
      ← hψ₀T, I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hx hxβ hψ₀, hW]
  · rw [hPe, Subgroup.mem_inf, mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ,
      mem_usup_iff c.pu c.via h464' hsq hx hxβ₁ hψ, ← Submodule.mem_inf, hfix, hfix,
      ← Submodule.map_inf _ hinj, ← hpdef, hAp]
  · rw [hP'e, Subgroup.mem_inf, mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ,
      mem_usup_iff c.pu c.via h464' hsq hx hxβ₂ hψ, ← Submodule.mem_inf, hfix, hfix,
      ← Submodule.map_inf _ hinj, ← hp'def, hAp']

theorem lSub_le_of_ptQ_le (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hψT : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {P₁ P₂ : Subgroup (puAmalgam c.pu.le).Universal} (hP₁U : P₁ ≤ Uloc c.pu.le L x)
    (hP₂U : P₂ ≤ Uloc c.pu.le L x)
    (hP₁c : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P₁ ↔
      natVec hψU u ∈ F ∙ (Pi.single 1 1 : Fin 3 → F))
    (hP₂c : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P₂ ↔
      natVec hψU u ∈ F ∙ (Pi.single 2 1 : Fin 3 → F))
    {S : Subgroup (puAmalgam c.pu.le).Universal}
    (hTS : Qv (puAmalgam c.pu.le) β ≤ S) (hQ₁ : ptQ (puAmalgam c.pu.le) x P₁ ≤ S)
    (hQ₂ : ptQ (puAmalgam c.pu.le) x P₂ ≤ S) {k : ↥(stab (puAmalgam c.pu.le) x)}
    (hk : toSL3 ψ k ∈ (S468.stabX0 : Subgroup (SL3 F))) :
    (k : (puAmalgam c.pu.le).Universal) ∈ S := by
  let D : Subgroup (SL3 F) := (S.subgroupOf (stab (puAmalgam c.pu.le) x)).map (toSL3 ψ)
  have hlift : ∀ B : SL3 F, (∀ k : ↥(stab (puAmalgam c.pu.le) x), toSL3 ψ k = B →
      (k : (puAmalgam c.pu.le).Universal) ∈ S) → B ∈ D := by
    intro B hB
    obtain ⟨k, hk⟩ := toSL3_surjective hψs B
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (hB k hk), hk⟩
  have hR : ∀ k : ↥(stab (puAmalgam c.pu.le) x),
      toSL3 ψ k ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) →
        (k : (puAmalgam c.pu.le).Universal) ∈ S := fun k hk =>
    hTS (S468.mem_qv_of_toSL3_mem c.pu c.via hx hxβ hψU hψT hk)
  have h10 : ∀ cc : F, rootElt 1 0 cc ∈ D := fun cc => hlift _ fun k hk => hR k (by
    rw [hk]; exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 cc))
  have h20 : ∀ cc : F, rootElt 2 0 cc ∈ D := fun cc => hlift _ fun k hk => hR k (by
    rw [hk]; exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 cc))
  have h12 : ∀ cc : F, rootElt 1 2 cc ∈ D := fun cc => hlift _ fun k hk =>
    hQ₁ (mem_ptQ_of_toSL3_mem c hx hψU hP₁U (i := 1) (j := 2) (by decide) hP₁c
      (by rw [hk]; exact rootElt_mem_rootGroup 1 2 cc))
  have h21 : ∀ cc : F, rootElt 2 1 cc ∈ D := fun cc => hlift _ fun k hk =>
    hQ₂ (mem_ptQ_of_toSL3_mem c hx hψU hP₂U (i := 2) (j := 1) (by decide) hP₂c
      (by rw [hk]; exact rootElt_mem_rootGroup 2 1 cc))
  have hrow : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
    funext j
    rw [S468.row_zero_of_mem_stabX0 hk j]
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  obtain ⟨s, hs, hse⟩ := KC2.mem_of_row_zero h10 h20 h12 h21 hrow
  have h1 : toSL3 ψ (s⁻¹ * k) = 1 := by rw [map_mul, map_inv, hse, inv_mul_cancel]
  have h2 := (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψU _).mp h1
  have e : (k : (puAmalgam c.pu.le).Universal) = (s : (puAmalgam c.pu.le).Universal) *
      ((s⁻¹ * k : ↥(stab (puAmalgam c.pu.le) x)) : (puAmalgam c.pu.le).Universal) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hs) (hTS (qv_le_qv _ c.pu.hyp20 hx hxβ h2))

theorem isOddL1_mem_of_ptQ_le (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P P' : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hP' : IsPtOn (puAmalgam c.pu.le) x β P')
    (hne : P ≠ P') {S : Subgroup (puAmalgam c.pu.le).Universal}
    (hTS : Qv (puAmalgam c.pu.le) β ≤ S)
    (hQ : ptQ (puAmalgam c.pu.le) x P ≤ S) (hQ' : ptQ (puAmalgam c.pu.le) x P' ≤ S)
    {g : (puAmalgam c.pu.le).Universal} (hg : IsOddL1 (puAmalgam c.pu.le) x β g) : g ∈ S := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, hψs, hψU, hψT, hPc, hP'c⟩ := exists_coord_qv_pts h464 h465 h466a c hx hxβ hP hP' hne
  exact lSub_le_of_ptQ_le c hx hxβ hψs hψU hψT (le_uloc_of_isPtOn c hx hP)
    (le_uloc_of_isPtOn c hx hP') hPc hP'c hTS hQ hQ' (k := ⟨g, hg.1⟩)
    (S468.toSL3_mem_of_commutator_mem_zh c.pu c.via hx hxβ hψU hψT h464' hsq hg.2.2.1)

theorem exists_two_isPtOn_ne (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) (p₀ : Subgroup (puAmalgam c.pu.le).Universal) :
    ∃ δ₁ δ₂, IsPtOn (puAmalgam c.pu.le) x β δ₁ ∧ IsPtOn (puAmalgam c.pu.le) x β δ₂ ∧ δ₁ ≠ δ₂ ∧
      δ₁ ≠ p₀ ∧ δ₂ ≠ p₀ := by
  obtain ⟨ψ, hψs, hψU, hψT⟩ := exists_coord_qv h464 h465 h466a c hx hxβ
  have hW : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) = coordZero 0 := by
    rw [hψT, fixN_rootGroup_sup]
  set v₁ : Fin 3 → F := Pi.single 1 1 with hv₁
  set v₂ : Fin 3 → F := Pi.single 2 1 with hv₂
  set v₃ : Fin 3 → F := Pi.single 1 1 + Pi.single 2 1 with hv₃
  have hmem : ∀ v : Fin 3 → F, v 0 = 0 → v ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) :=
    fun v hv => hW ▸ hv
  have hne0 : ∀ v : Fin 3 → F, ∀ j : Fin 3, v j ≠ 0 → v ≠ 0 := fun v j hv h => hv (by simp [h])
  obtain ⟨P₁, hP₁, hP₁U, hP₁c⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψU
    (hmem v₁ (by simp [hv₁])) (hne0 v₁ 1 (by simp [hv₁]))
  obtain ⟨P₂, hP₂, hP₂U, hP₂c⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψU
    (hmem v₂ (by simp [hv₂])) (hne0 v₂ 2 (by simp [hv₂]))
  obtain ⟨P₃, hP₃, hP₃U, hP₃c⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψU
    (hmem v₃ (by simp [hv₃])) (hne0 v₃ 1 (by simp [hv₃]))
  have hne : ∀ {P P' : Subgroup (puAmalgam c.pu.le).Universal} {v v' : Fin 3 → F} {j : Fin 3},
      P ≤ Uloc c.pu.le L x → P' ≤ Uloc c.pu.le L x →
      (∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔ natVec hψU u ∈ F ∙ v) →
      (∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P' ↔
        natVec hψU u ∈ F ∙ v') → v j = 0 → v' j ≠ 0 → P ≠ P' :=
    fun hPU hP'U hPc hP'c hv hv' e =>
      span_ne_of_apply hv hv' ((S45.eq_iff_of_natVec_iff hψU hPU hP'U hPc hP'c).mp e)
  have h12 : P₁ ≠ P₂ := hne hP₁U hP₂U hP₁c hP₂c (j := 2) (by simp [hv₁]) (by simp [hv₂])
  have h13 : P₁ ≠ P₃ := hne hP₁U hP₃U hP₁c hP₃c (j := 2) (by simp [hv₁]) (by simp [hv₃])
  have h23 : P₂ ≠ P₃ := hne hP₂U hP₃U hP₂c hP₃c (j := 1) (by simp [hv₂]) (by simp [hv₃])
  by_cases e1 : P₁ = p₀
  · exact ⟨P₂, P₃, hP₂, hP₃, h23, fun e => h12 (e1.trans e.symm), fun e => h13 (e1.trans e.symm)⟩
  by_cases e2 : P₂ = p₀
  · exact ⟨P₁, P₃, hP₁, hP₃, h13, e1, fun e => h23 (e2.trans e.symm)⟩
  exact ⟨P₁, P₂, hP₁, hP₂, h12, e1, e2⟩

end CFSG.Quasithin.MS93.S46R
