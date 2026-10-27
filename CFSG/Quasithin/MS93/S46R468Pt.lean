module

public import CFSG.Quasithin.MS93.S46R468P

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def ptQ (x : Vtx X) (P : Subgroup X.Universal) : Subgroup X.Universal where
  carrier := {g | g ∈ stab X x ∧ g ∈ Subgroup.normalizer (P : Set X.Universal) ∧
    ∀ z ∈ ZM X x, ⁅z, g⁆ ∈ P}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun z _ => by
    rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
    refine ⟨Subgroup.mul_mem _ ha hb, Subgroup.mul_mem _ ha' hb', fun z hz => ?_⟩
    have e : ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (ha'' z hz) ((Subgroup.mem_normalizer_iff.mp ha' _).mp (hb'' z hz))
  inv_mem' := by
    rintro a ⟨ha, ha', ha''⟩
    refine ⟨Subgroup.inv_mem _ ha, Subgroup.inv_mem _ ha', fun z hz => ?_⟩
    have e : ⁅z, a⁻¹⁆ = a⁻¹ * ⁅z, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha') _).mp
      (Subgroup.inv_mem _ (ha'' z hz))

@[expose] def ptSub (x : Vtx X) (P : Subgroup X.Universal) : Subgroup X.Universal :=
  Subgroup.closure {v | ∃ β', X.treeGraph.Adj x β' ∧ P ≤ Usup X x β' ∧ v ∈ Vv X β' ∧
    ∀ t ∈ ptQ X x P, ⁅v, t⁆ ∈ ZM X x}

@[expose] def IsPtOn (x β : Vtx X) (P : Subgroup X.Universal) : Prop :=
  ∃ β', X.treeGraph.Adj x β' ∧ Usup X x β' ≠ Usup X x β ∧ P = Usup X x β ⊓ Usup X x β'

@[expose] noncomputable def ptConst (x : Vtx X) (T P R : Subgroup X.Universal) : ℕ :=
  (ZM X x).relIndex (⁅ptSub X x P, T ⊓ ptQ X x R⁆ ⊔ ZM X x)

variable {X}

theorem mem_ptQ {x : Vtx X} {P : Subgroup X.Universal} {g : X.Universal} :
    g ∈ ptQ X x P ↔ g ∈ stab X x ∧ g ∈ Subgroup.normalizer (P : Set X.Universal) ∧
      ∀ z ∈ ZM X x, ⁅z, g⁆ ∈ P :=
  Iff.rfl

theorem ptSub_le_pencil (x : Vtx X) (P : Subgroup X.Universal) : ptSub X x P ≤ pencil X x P :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hxβ', hP, hv, _⟩ => vv_le_pencil hxβ' hP hv

theorem ptQ_smul (g : X.Universal) (x : Vtx X) (P : Subgroup X.Universal) :
    ptQ X (g • x) (P.map (MulAut.conj g).toMonoidHom) =
      (ptQ X x P).map (MulAut.conj g).toMonoidHom := by
  ext a
  rw [mem_map_conj, mem_ptQ, mem_ptQ, mem_stab_smul, normalizer_map_conj, mem_map_conj, zm_smul]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h z hz
    have h1 := h (g * z * g⁻¹) (conj_mem_map_conj hz)
    rw [mem_map_conj] at h1
    have e : g⁻¹ * ⁅g * z * g⁻¹, a⁆ * g = ⁅z, g⁻¹ * a * g⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h1
  · intro h z hz
    rw [mem_map_conj] at hz ⊢
    have e : g⁻¹ * ⁅z, a⁆ * g = ⁅g⁻¹ * z * g, g⁻¹ * a * g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h _ hz

theorem ptSub_smul_le (g : X.Universal) (x : Vtx X) (P : Subgroup X.Universal) :
    ptSub X (g • x) (P.map (MulAut.conj g).toMonoidHom) ≤
      (ptSub X x P).map (MulAut.conj g).toMonoidHom := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro v ⟨β', hxβ', hP, hv, ht⟩
  obtain ⟨β, rfl⟩ : ∃ β, β' = g • β := ⟨g⁻¹ • β', (smul_inv_smul g β').symm⟩
  rw [adj_smul] at hxβ'
  rw [usup_smul, map_conj_le_map_conj_iff] at hP
  rw [show Vv X (g • β) = (Vv X β).map (MulAut.conj g).toMonoidHom from vi_smul X g β 2,
    mem_map_conj] at hv
  refine mem_map_conj.mpr (Subgroup.subset_closure ⟨β, hxβ', hP, hv, fun t htQ => ?_⟩)
  have h1 := ht (g * t * g⁻¹) (by rw [ptQ_smul]; exact conj_mem_map_conj htQ)
  rw [zm_smul, mem_map_conj] at h1
  have e : g⁻¹ * ⁅v, g * t * g⁻¹⁆ * g = ⁅g⁻¹ * v * g, t⁆ := by
    simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem ptSub_smul (g : X.Universal) (x : Vtx X) (P : Subgroup X.Universal) :
    ptSub X (g • x) (P.map (MulAut.conj g).toMonoidHom) =
      (ptSub X x P).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm (ptSub_smul_le g x P) ?_
  have h := ptSub_smul_le g⁻¹ (g • x) (P.map (MulAut.conj g).toMonoidHom)
  rw [inv_smul_smul, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  rwa [map_conj_le_iff]

theorem pencil_smul_le (g : X.Universal) (γ : Vtx X) (P : Subgroup X.Universal) :
    pencil X (g • γ) (P.map (MulAut.conj g).toMonoidHom) ≤
      (pencil X γ P).map (MulAut.conj g).toMonoidHom := by
  refine pencil_le fun β' hγβ' hP => ?_
  obtain ⟨β, rfl⟩ : ∃ β, β' = g • β := ⟨g⁻¹ • β', (smul_inv_smul g β').symm⟩
  rw [adj_smul] at hγβ'
  rw [usup_smul, map_conj_le_map_conj_iff] at hP
  rw [show Vv X (g • β) = (Vv X β).map (MulAut.conj g).toMonoidHom from vi_smul X g β 2]
  exact Subgroup.map_mono (vv_le_pencil hγβ' hP)

theorem pencil_smul (g : X.Universal) (γ : Vtx X) (P : Subgroup X.Universal) :
    pencil X (g • γ) (P.map (MulAut.conj g).toMonoidHom) =
      (pencil X γ P).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm (pencil_smul_le g γ P) ?_
  have h := pencil_smul_le g⁻¹ (g • γ) (P.map (MulAut.conj g).toMonoidHom)
  rw [inv_smul_smul, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  rwa [map_conj_le_iff]

theorem isPtOn_smul (g : X.Universal) (x β : Vtx X) (P : Subgroup X.Universal) :
    IsPtOn X (g • x) (g • β) (P.map (MulAut.conj g).toMonoidHom) ↔ IsPtOn X x β P := by
  constructor
  · rintro ⟨β', hxβ', hne, he⟩
    obtain ⟨β'', rfl⟩ : ∃ β'', β' = g • β'' := ⟨g⁻¹ • β', (smul_inv_smul g β').symm⟩
    rw [adj_smul] at hxβ'
    rw [usup_smul, usup_smul] at hne he
    rw [← Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at he
    exact ⟨β'', hxβ', fun h => hne (by rw [h]),
      Subgroup.map_injective (MulAut.conj g).injective he⟩
  · rintro ⟨β', hxβ', hne, rfl⟩
    refine ⟨g • β', (adj_smul X g x β').mpr hxβ', ?_, ?_⟩
    · rw [usup_smul, usup_smul]
      exact fun h => hne (Subgroup.map_injective (MulAut.conj g).injective h)
    · rw [usup_smul, usup_smul, Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem ptConst_smul (g : X.Universal) (x : Vtx X) (K P R : Subgroup X.Universal) :
    ptConst X (g • x) (K.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom)
      (R.map (MulAut.conj g).toMonoidHom) = ptConst X x K P R := by
  rw [ptConst, ptConst, ptSub_smul, ptQ_smul, zm_smul,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← Subgroup.map_commutator,
    ← Subgroup.map_sup, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

end Def

section Lin

variable {F : Type} [Field F]

theorem exists_span_eq_of_finrank_eq_one {p : Submodule F (Fin 3 → F)}
    (hp : Module.finrank F p = 1) : ∃ u : Fin 3 → F, u ≠ 0 ∧ p = F ∙ u := by
  have hne : p ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hp
    exact zero_ne_one hp
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨u, hu0, eq_span_singleton_of_mem_of_finrank_eq_one hp hu hu0⟩

theorem exists_sl3_mulVec_pair {u w u' w' : Fin 3 → F} (h : LinearIndependent F ![u, w])
    (h' : LinearIndependent F ![u', w']) :
    ∃ A : SL3 F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u' ∧
      (A : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w' := by
  classical
  have hext : ∀ {a b : Fin 3 → F}, LinearIndependent F ![a, b] →
      ∃ z : Fin 3 → F, LinearIndependent F ![a, b, z] := by
    intro a b hab
    have hlt : Submodule.span F (Set.range ![a, b]) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => ?_
      have h1 := finrank_span_eq_card hab
      rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
      omega
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨z, ?_⟩
    have := linearIndependent_finSnoc.mpr ⟨hab, hz⟩
    convert this using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨z, hz⟩ := hext h
  obtain ⟨z', hz'⟩ := hext h'
  have hc : Fintype.card (Fin 3) = Module.finrank F (Fin 3 → F) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hz hc with hbdef
  set b' := basisOfLinearIndependentOfCardEqFinrank hz' hc with hb'def
  have hb : ⇑b = ![u, w, z] := coe_basisOfLinearIndependentOfCardEqFinrank hz hc
  have hb' : ⇑b' = ![u', w', z'] := coe_basisOfLinearIndependentOfCardEqFinrank hz' hc
  set d := b.det ![u', w', z'] with hd
  have hd0 : d ≠ 0 := by
    have := b.isUnit_det b'
    rw [hb'] at this
    exact this.ne_zero
  set f := b.constr F ![u', w', d⁻¹ • z'] with hf
  have hfb : ∀ i, f (b i) = ![u', w', d⁻¹ • z'] i := fun i => b.constr_basis F _ i
  have hdet : LinearMap.det f = 1 := by
    have h1 := b.det_comp f b
    rw [b.det_self, mul_one] at h1
    rw [← h1]
    have e : (f ∘ ⇑b) = Function.update ![u', w', z'] 2 (d⁻¹ • z') := by
      funext i
      rw [Function.comp_apply, hfb]
      fin_cases i <;> simp [Function.update]
    have e2 : Function.update ![u', w', z'] 2 z' = ![u', w', z'] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [e, AlternatingMap.map_update_smul, e2, ← hd, smul_eq_mul, inv_mul_cancel₀ hd0]
  refine ⟨⟨LinearMap.toMatrix' f, by rw [LinearMap.det_toMatrix']; exact hdet⟩, ?_, ?_⟩
  · show LinearMap.toMatrix' f *ᵥ u = u'
    rw [LinearMap.toMatrix'_mulVec]
    have := hfb 0
    rw [hb] at this
    simpa using this
  · show LinearMap.toMatrix' f *ᵥ w = w'
    rw [LinearMap.toMatrix'_mulVec]
    have := hfb 1
    rw [hb] at this
    simpa using this

theorem exists_sl3_map_pts {W p r p' r' : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 2) (hp : p ≤ W) (hr : r ≤ W) (hp' : p' ≤ W) (hr' : r' ≤ W)
    (hp1 : Module.finrank F p = 1) (hr1 : Module.finrank F r = 1)
    (hp1' : Module.finrank F p' = 1) (hr1' : Module.finrank F r' = 1) (hpr : p ≠ r)
    (hpr' : p' ≠ r') :
    ∃ A : SL3 F, (∀ v ∈ W, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) ∧
      p.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = p' ∧
      r.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = r' := by
  obtain ⟨u, hu0, rfl⟩ := exists_span_eq_of_finrank_eq_one hp1
  obtain ⟨w, hw0, rfl⟩ := exists_span_eq_of_finrank_eq_one hr1
  obtain ⟨u', hu0', rfl⟩ := exists_span_eq_of_finrank_eq_one hp1'
  obtain ⟨w', hw0', rfl⟩ := exists_span_eq_of_finrank_eq_one hr1'
  have hli : ∀ {a b : Fin 3 → F}, a ≠ 0 → b ≠ 0 → (F ∙ a) ≠ (F ∙ b) →
      LinearIndependent F ![a, b] := by
    intro a b ha hb hab
    refine (LinearIndependent.pair_iff' ha).mpr fun t ht => hab ?_
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hb ht.symm
    rw [← ht, Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht0)]
  obtain ⟨A, hAu, hAw⟩ := exists_sl3_mulVec_pair (hli hu0 hw0 hpr) (hli hu0' hw0' hpr')
  have hmap : ∀ v : Fin 3 → F, (F ∙ v).map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) =
      F ∙ ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := fun v => by
    rw [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply]
  refine ⟨A, fun v hv => ?_, by rw [hmap, hAu], by rw [hmap, hAw]⟩
  have hWeq : (F ∙ u) ⊔ (F ∙ w) = W := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hp hr) ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F ∙ u) (F ∙ w)
    have h2 : Module.finrank F ↥((F ∙ u) ⊓ (F ∙ w)) = 0 := by
      by_contra hne
      have hle : Module.finrank F ↥((F ∙ u) ⊓ (F ∙ w)) ≤ 1 := by
        rw [← hp1]
        exact Submodule.finrank_mono inf_le_left
      have he1 : (F ∙ u) ⊓ (F ∙ w) = F ∙ u :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hp1]; omega)
      have he2 : (F ∙ u) ⊓ (F ∙ w) = F ∙ w :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hr1]; omega)
      exact hpr (he1.symm.trans he2)
    rw [hp1, hr1, h2] at h1
    rw [hW]
    omega
  have hv' : v ∈ (F ∙ u) ⊔ (F ∙ w) := hWeq ▸ hv
  have := Submodule.mem_map_of_mem (f := Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) hv'
  rw [Submodule.map_sup, hmap, hmap, hAu, hAw, Matrix.mulVecLin_apply] at this
  exact sup_le hp' hr' this

end Lin

section Natural

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem map_conj_eq_of_coord (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1)
    {S S' : Subgroup G} {s s' : Submodule F (Fin 3 → F)} (hS : S ≤ V) (hS' : S' ≤ V)
    (hs : ∀ v : ↥V, (v : G) ∈ S ↔ natVec hψ v ∈ s)
    (hs' : ∀ v : ↥V, (v : G) ∈ S' ↔ natVec hψ v ∈ s') (g : ↥K)
    (hg : s.map (Matrix.mulVecLin ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = s') :
    S.map (MulAut.conj (g : G)).toMonoidHom = S' := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huV := hS hu
    have hmem : (g : G) * u * (g : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hψ.1 g.2) u).mp huV
    show (g : G) * u * (g : G)⁻¹ ∈ S'
    refine (hs' ⟨_, hmem⟩).mpr ?_
    rw [natVec_conj hψ g ⟨u, huV⟩ ⟨_, hmem⟩ rfl, ← hg]
    exact Submodule.mem_map_of_mem ((hs ⟨u, huV⟩).mp hu)
  · intro hv
    have hvV := hS' hv
    have hmem : (g : G)⁻¹ * v * (g : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hψ.1 (g⁻¹).2) v).mp hvV
      simpa using this
    refine ⟨_, (hs ⟨_, hmem⟩).mpr ?_, by simp [mul_assoc]⟩
    have e := natVec_conj hψ g ⟨_, hmem⟩ ⟨v, hvV⟩ (by simp [mul_assoc])
    have h1 := (hs' ⟨v, hvV⟩).mp hv
    rw [e, ← hg] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [Matrix.mulVecLin_apply] at hye
    have hy' : y = natVec hψ ⟨_, hmem⟩ := by
      have := congrArg (fun z => (((toSL3 ψ g)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) hye
      simpa only [inv_mulVec_mulVec_SL3] using this
    rwa [← hy']

end Natural

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem zm_le_ptSub (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) : ZM (puAmalgam c.pu.le) x ≤ ptSub _ x P := by
  obtain ⟨β', hxβ', -, rfl⟩ := hP
  intro z hz
  refine Subgroup.subset_closure ⟨β', hxβ', inf_le_right, zm_le_vv_of_adj hxβ'.symm hx hz,
    fun t ht => ?_⟩
  exact I464.usup_le_zm c.pu hx hxβ' (Subgroup.mem_inf.mp ((mem_ptQ.mp ht).2.2 z hz)).2

theorem ptSub_le_vv (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (P : Subgroup (puAmalgam c.pu.le).Universal) :
    ptSub (puAmalgam c.pu.le) x P ≤ Vv _ x :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hxβ', _, hv, _⟩ => I466b.vv_le_vv_of_adj c.pu hx hxβ' hv

theorem commutator_ptSub_ptQ_le (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (P : Subgroup (puAmalgam c.pu.le).Universal) :
    ⁅ptSub (puAmalgam c.pu.le) x P, ptQ _ x P⁆ ≤ ZM _ x := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {a | a ∈ stab (puAmalgam c.pu.le) x ∧
        ∀ t ∈ ptQ (puAmalgam c.pu.le) x P, ⁅a, t⁆ ∈ ZM (puAmalgam c.pu.le) x}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun t ht => ?_⟩
        have e : ⁅a * b, t⁆ = a * ⁅b, t⁆ * a⁻¹ * ⁅a, t⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_zm _ x ha) _).mp (hb' t ht)) (ha' t ht)
      one_mem' := ⟨Subgroup.one_mem _, fun t _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun t ht => ?_⟩
        have e : ⁅a⁻¹, t⁆ = a⁻¹ * ⁅a, t⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ x
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ (ha' t ht)) }
  have hle : ptSub (puAmalgam c.pu.le) x P ≤ S :=
    (Subgroup.closure_le _).mpr fun _ ⟨_, hxβ', _, hv, hvt⟩ =>
      ⟨qv_le_stab _ x (vv_le_qv c.pu hb hx (I466b.vv_le_vv_of_adj c.pu hx hxβ' hv)), hvt⟩
  rw [Subgroup.commutator_le]
  exact fun a ha t ht => (hle ha).2 t ht

theorem ptConst_self (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (K P : Subgroup (puAmalgam c.pu.le).Universal) :
    ptConst (puAmalgam c.pu.le) x K P P = 1 :=
  Subgroup.relIndex_eq_one.mpr (sup_le ((Subgroup.commutator_mono le_rfl inf_le_right).trans
    (commutator_ptSub_ptQ_le c hx P)) le_rfl)

theorem exists_coord_of_isPtOn (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P) :
    ∃ p : Submodule F (Fin 3 → F), p ≤ fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) ∧
      Module.finrank F p = 1 ∧ P ≤ Uloc c.pu.le L x ∧
      ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔ natVec hψ u ∈ p := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨β', hxβ', hne, rfl⟩ := hP
  have hm := mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ
  have hm' := mem_usup_iff c.pu c.via h464' hsq hx hxβ' hψ
  have hne' : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) ≠ fixN (natImage ψ (Qv _ β')) :=
    fun heq => hne ((S45.eq_iff_of_natVec_iff hψ (usup_le_uloc' c.pu hfull hx hxβ')
      (usup_le_uloc' c.pu hfull hx hxβ) hm' hm).mpr heq.symm)
  refine ⟨_ ⊓ _, inf_le_left, S45.finrank_inf_eq_one
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ).1
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ' hψ).1 hne',
    inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxβ), fun u => ?_⟩
  rw [Subgroup.mem_inf, hm, hm', Submodule.mem_inf]

theorem exists_conj_pts (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P R P' R' : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    (hR : IsPtOn (puAmalgam c.pu.le) x β R) (hP' : IsPtOn (puAmalgam c.pu.le) x β P')
    (hR' : IsPtOn (puAmalgam c.pu.le) x β R') (hPR : P ≠ R) (hPR' : P' ≠ R') :
    ∃ g ∈ stab (puAmalgam c.pu.le) x,
      g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) ∧
      P.map (MulAut.conj g).toMonoidHom = P' ∧ R.map (MulAut.conj g).toMonoidHom = R' := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, hpW, hp1, hPU, hPp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP
  obtain ⟨r, hrW, hr1, hRU, hRr⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hR
  obtain ⟨p', hpW', hp1', hPU', hPp'⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP'
  obtain ⟨r', hrW', hr1', hRU', hRr'⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hR'
  have hpr : p ≠ r := fun e => hPR ((S45.eq_iff_of_natVec_iff hψ hPU hRU hPp hRr).mpr e)
  have hpr' : p' ≠ r' := fun e => hPR' ((S45.eq_iff_of_natVec_iff hψ hPU' hRU' hPp' hRr').mpr e)
  obtain ⟨A, hAW, hAp, hAr⟩ := exists_sl3_map_pts
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ).1 hpW hrW hpW' hrW' hp1 hr1 hp1' hr1'
    hpr hpr'
  obtain ⟨s, hs⟩ := toSL3_surjective hψs A
  refine ⟨s, s.2, I466b.mem_normalizer_qv_of_toSL3 c.pu c.via h464' hsq h466 hx hxβ hψ
    (by rw [hs]; exact hAW), map_conj_eq_of_coord hψ hPU hPU' hPp hPp' s (by rw [hs]; exact hAp),
    map_conj_eq_of_coord hψ hRU hRU' hRr hRr' s (by rw [hs]; exact hAr)⟩

theorem ptConst_eq (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β y ρ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) (hy : IsMVtx (puAmalgam c.pu.le) y)
    (hyρ : (puAmalgam c.pu.le).treeGraph.Adj y ρ)
    {P R P' R' : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    (hR : IsPtOn (puAmalgam c.pu.le) x β R) (hPR : P ≠ R)
    (hP' : IsPtOn (puAmalgam c.pu.le) y ρ P') (hR' : IsPtOn (puAmalgam c.pu.le) y ρ R')
    (hPR' : P' ≠ R') :
    ptConst (puAmalgam c.pu.le) x (Qv _ β) P R = ptConst (puAmalgam c.pu.le) y (Qv _ ρ) P' R' := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hx hxβ hy hyρ
  have hP₁ := (isPtOn_smul g x β P).mpr hP
  have hR₁ := (isPtOn_smul g x β R).mpr hR
  have hPR₁ : P.map (MulAut.conj g).toMonoidHom ≠ R.map (MulAut.conj g).toMonoidHom :=
    fun h => hPR (Subgroup.map_injective (MulAut.conj g).injective h)
  obtain ⟨k, hk, hkn, hkP, hkR⟩ :=
    exists_conj_pts h464 h465 h466a c hy hyρ hP₁ hR₁ hP' hR' hPR₁ hPR'
  have hkx : k • (g • x) = g • x := MulAction.mem_stabilizer_iff.mp hk
  have hkT : (Qv (puAmalgam c.pu.le) (g • β)).map (MulAut.conj k).toMonoidHom = Qv _ (g • β) :=
    map_conj_eq_of_mem_normalizer hkn
  have h1 := ptConst_smul k (g • x) (Qv (puAmalgam c.pu.le) (g • β))
    (P.map (MulAut.conj g).toMonoidHom) (R.map (MulAut.conj g).toMonoidHom)
  rw [hkx, hkT, hkP, hkR] at h1
  rw [h1, qv_smul]
  exact (ptConst_smul g x (Qv _ β) P R).symm

end CFSG.Quasithin.MS93.S46R
