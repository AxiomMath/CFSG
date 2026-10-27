module

public import CFSG.Quasithin.MS93.S46R468Lv
public import CFSG.Quasithin.MS93.S46R468Pt
public import CFSG.Quasithin.MS93.S4AL3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

section Lin

variable {F : Type} [Field F]

theorem axisGroup_ln01 : I466b.axisGroup (ln01 : Submodule F (Fin 3 → F)) = qLn := by
  ext B
  constructor
  · rintro ⟨hB, -⟩
    exact QjAux.mem_qLn_of_fix (hB _ (by simp [mem_ln01])) (hB _ (by simp [mem_ln01]))
  · intro hB
    obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp hB
    refine ⟨fun p hp => ?_, fun v => ?_⟩
    · have hp2 : p 2 = 0 := hp
      rw [uniTri_mulVec]
      funext k
      fin_cases k <;> simp [hp2]
    · rw [uniTri_mulVec, mem_ln01]
      simp

theorem exists_sl3_map_flag [Finite F] {W p : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 2) (hp : Module.finrank F p = 1) (hpW : p ≤ W) :
    ∃ A : SL3 F,
      W.map (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = ln01 ∧
      p.map (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = pt0 := by
  obtain ⟨u, hu0, rfl⟩ := exists_span_eq_of_finrank_eq_one hp
  have hlt : (F ∙ u) < W := lt_of_le_of_ne hpW fun h => by
    rw [← h, hp] at hW
    omega
  obtain ⟨w, hwW, hwu⟩ := IsConcreteLE.exists_of_lt hlt
  have hli : LinearIndependent F ![u, w] :=
    (LinearIndependent.pair_iff' hu0).mpr fun t ht =>
      hwu (ht ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self u))
  have hli' : LinearIndependent F ![(![1, 0, 0] : Fin 3 → F), ![0, 1, 0]] := by
    refine (LinearIndependent.pair_iff' fun h => ?_).mpr fun t ht => ?_
    · have := congrFun h 0
      simp at this
    · have := congrFun ht 1
      simp at this
  obtain ⟨A, hAu, hAw⟩ := exists_sl3_mulVec_pair hli hli'
  have happ : ∀ v : Fin 3 → F,
      (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) v =
        (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v := fun v => by
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have huW : u ∈ W := hpW (Submodule.mem_span_singleton_self u)
  refine ⟨A, (Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) ?_).symm,
    (Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) ?_).symm⟩
  · have hv2 : v 2 = 0 := hv
    refine ⟨v 0 • u + v 1 • w, W.add_mem (W.smul_mem _ huW) (W.smul_mem _ hwW), ?_⟩
    rw [happ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hAu, hAw]
    funext k
    fin_cases k <;> simp [hv2]
  · rw [LinearEquiv.finrank_map_eq, hW, finrank_ln01]
  · obtain ⟨hv1, hv2⟩ := mem_pt0.mp hv
    refine ⟨v 0 • u, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u), ?_⟩
    rw [happ, Matrix.mulVec_smul, hAu]
    funext k
    fin_cases k <;> simp [hv1, hv2]
  · rw [LinearEquiv.finrank_map_eq, hp, finrank_pt0]

private theorem natImage_conjSL_eq {𝔾 : Type} [Group 𝔾] {K : Subgroup 𝔾} (s : SL3 F)
    (φ : ↥K →* ↥(StatedSL 3 F)) (A : Subgroup 𝔾) :
    natImage (conjSL s φ) A = (natImage φ A).map (MulAut.conj s).toMonoidHom := by
  rw [natImage, natImage, Subgroup.map_map]
  refine congrArg (Subgroup.map · _) (MonoidHom.ext fun a => ?_)
  rw [toSL3_conjSL]
  rfl

private theorem commutator_mem_of_le_normalizer {𝔾 : Type*} [Group 𝔾] {K V : Subgroup 𝔾}
    (hKV : K ≤ Subgroup.normalizer (V : Set 𝔾)) {u a : 𝔾} (hu : u ∈ V) (ha : a ∈ K) :
    ⁅u, a⁆ ∈ V := by
  have hmem : a * u * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV ha) u).mp hu
  have e : ⁅u, a⁆ = u * (a * u * a⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact V.mul_mem hu (V.inv_mem hmem)

end Lin

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)
  {F : Type} [Field F]

@[expose] def ptL (x : Vtx X) (ψ : ↥(stab X x) →* ↥(StatedSL 3 F)) : Subgroup X.Universal where
  carrier := {g | ∃ hg : g ∈ stab X x, toSL3 ψ ⟨g, hg⟩ ∈ (stabE0 : Subgroup (SL3 F))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    rw [show (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : ↥(stab X x)) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
      map_mul]
    exact Subgroup.mul_mem _ ha' hb'
  one_mem' := ⟨Subgroup.one_mem _, by
    rw [show (⟨1, Subgroup.one_mem _⟩ : ↥(stab X x)) = 1 from rfl, map_one]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    rw [show (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : ↥(stab X x)) = (⟨a, ha⟩ : ↥(stab X x))⁻¹ from rfl,
      map_inv]
    exact Subgroup.inv_mem _ ha'

variable {X}

theorem mem_ptL_iff {x : Vtx X} {ψ : ↥(stab X x) →* ↥(StatedSL 3 F)} {g : X.Universal} :
    g ∈ ptL X x ψ ↔ ∃ hg : g ∈ stab X x, toSL3 ψ ⟨g, hg⟩ ∈ (stabE0 : Subgroup (SL3 F)) :=
  Iff.rfl

theorem ptL_le_stab {x : Vtx X} (ψ : ↥(stab X x) →* ↥(StatedSL 3 F)) : ptL X x ψ ≤ stab X x :=
  fun _ hg => (mem_ptL_iff.mp hg).fst

@[expose] noncomputable def ptTheta {x : Vtx X} (ψ : ↥(stab X x) →* ↥(StatedSL 3 F)) :
    ↥(ptL X x ψ) →* SL(2, F) :=
  blockE0.comp (((toSL3 ψ).comp (Subgroup.inclusion (ptL_le_stab ψ))).codRestrict
    (stabE0 : Subgroup (SL3 F)) fun k => (mem_ptL_iff.mp k.2).snd)

theorem ptTheta_apply {x : Vtx X} (ψ : ↥(stab X x) →* ↥(StatedSL 3 F)) (k : ↥(ptL X x ψ)) :
    ptTheta ψ k = blockE0 ⟨toSL3 ψ ⟨k, ptL_le_stab ψ k.2⟩, (mem_ptL_iff.mp k.2).snd⟩ :=
  rfl

theorem ptTheta_surjective {x : Vtx X} {ψ : ↥(stab X x) →* ↥(StatedSL 3 F)}
    (hψs : Function.Surjective ψ) : Function.Surjective (ptTheta ψ) := by
  intro B
  obtain ⟨s, hs⟩ := toSL3_surjective hψs (liftE0 B)
  have hmem : (s : X.Universal) ∈ ptL X x ψ := ⟨s.2, by
    rw [show (⟨(s : X.Universal), s.2⟩ : ↥(stab X x)) = s from rfl, hs]
    exact liftE0_mem B⟩
  refine ⟨⟨s, hmem⟩, ?_⟩
  rw [ptTheta_apply]
  have e : (⟨toSL3 ψ ⟨(s : X.Universal), ptL_le_stab ψ hmem⟩,
      (mem_ptL_iff.mp hmem).snd⟩ : ↥(stabE0 : Subgroup (SL3 F))) = ⟨liftE0 B, liftE0_mem B⟩ :=
    Subtype.ext hs
  rw [e, blockE0_liftE0]

end Def

section Line

variable {A B C : Type} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B} {F : Type} [Field F]

theorem qv_le_ptL {x β : Vtx X} (hxβ : X.treeGraph.Adj x β)
    {ψ : ↥(stab X x) →* ↥(StatedSL 3 F)} (hT : natImage ψ (Qv X β) = qLn) :
    Qv X β ≤ ptL X x ψ := by
  intro t ht
  have hts : t ∈ stab X x := qv_le_stab_of_adj _ hxβ.symm ht
  refine ⟨hts, qLn_le_stabE0 ?_⟩
  rw [← hT]
  exact mem_natImage.mpr ⟨⟨t, hts⟩, ht, rfl⟩

theorem map_ptTheta_qv {x β : Vtx X} {ψ : ↥(stab X x) →* ↥(StatedSL 3 F)}
    (hT : natImage ψ (Qv X β) = qLn) :
    ((Qv X β).subgroupOf (ptL X x ψ)).map (ptTheta ψ) = SL2Model.Rg F := by
  ext B
  rw [Subgroup.mem_map, SL2Model.mem_Rg]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ht
    have hq : toSL3 ψ ⟨t, ptL_le_stab ψ t.2⟩ ∈ (qLn : Subgroup (SL3 F)) := by
      rw [← hT]
      exact mem_natImage.mpr ⟨_, ht, rfl⟩
    obtain ⟨b, c, hbc⟩ := mem_qLn_iff_uniTri.mp hq
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [SL2Model.e12_coe, ptTheta_apply]
    have e : (⟨toSL3 ψ ⟨t, ptL_le_stab ψ t.2⟩, (mem_ptL_iff.mp t.2).snd⟩ :
        ↥(stabE0 : Subgroup (SL3 F))) =
        ⟨uniTri 0 b c, sStar_le_stabE0 (mem_sStar_iff.mpr ⟨0, b, c, rfl⟩)⟩ :=
      Subtype.ext hbc.symm
    rw [e, coe_blockE0_uniTri]
  · rintro ⟨c, rfl⟩
    have hq : uniTri 0 0 c ∈ natImage ψ (Qv X β) := by
      rw [hT]
      exact mem_qLn_iff_uniTri.mpr ⟨0, c, rfl⟩
    obtain ⟨a, ha, hac⟩ := mem_natImage.mp hq
    have haL : (a : X.Universal) ∈ ptL X x ψ := ⟨a.2, by
      rw [show (⟨(a : X.Universal), a.2⟩ : ↥(stab X x)) = a from rfl, hac]
      exact sStar_le_stabE0 (mem_sStar_iff.mpr ⟨0, 0, c, rfl⟩)⟩
    refine ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
    apply Subtype.ext
    rw [SL2Model.e12_coe, ptTheta_apply]
    have e : (⟨toSL3 ψ ⟨a, ptL_le_stab ψ haL⟩, (mem_ptL_iff.mp haL).snd⟩ :
        ↥(stabE0 : Subgroup (SL3 F))) =
        ⟨uniTri 0 0 c, sStar_le_stabE0 (mem_sStar_iff.mpr ⟨0, 0, c, rfl⟩)⟩ :=
      Subtype.ext hac
    rw [e, coe_blockE0_uniTri]

end Line

section Kernel

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]

theorem mem_ptQ_iff_sub_mem_pt0 (h : PUHyp M T L) (hfull : IsSL3Full M T L)
    {x : Vtx (puAmalgam h.le)} (hx : IsMVtx (puAmalgam h.le) x)
    {ψ : ↥(stab (puAmalgam h.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc h.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam h.le).Universal} (hPU : P ≤ Uloc h.le L x)
    (hP : ∀ u : ↥(Uloc h.le L x), (u : (puAmalgam h.le).Universal) ∈ P ↔ natVec hψU u ∈ pt0)
    (g : ↥(stab (puAmalgam h.le) x)) :
    (g : (puAmalgam h.le).Universal) ∈ ptQ (puAmalgam h.le) x P ↔
      ∀ v : Fin 3 → F, ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0 := by
  have hcomm : ∀ u : ↥(Uloc h.le L x),
      ⁅(u : (puAmalgam h.le).Universal), (g : (puAmalgam h.le).Universal)⁆ ∈ P ↔
      ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψU u - natVec hψU u ∈ pt0 := by
    intro u
    have hmem := commutator_mem_of_le_normalizer hψU.1 u.2 g.2
    rw [hP ⟨_, hmem⟩, natVec_commutator hψU g u ⟨_, hmem⟩ rfl, ← neg_sub]
    exact (pt0 : Submodule F (Fin 3 → F)).neg_mem_iff
  constructor
  · rintro ⟨-, -, hz⟩ v
    obtain ⟨u, rfl⟩ := natVec_surjective hψU v
    exact (hcomm u).mp (hz u (uloc_le_zm h hfull hx u.2))
  · intro hg
    have hconj : ∀ k : ↥(stab (puAmalgam h.le) x),
        (∀ v : Fin 3 → F, ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0) →
        ∀ p ∈ P, (k : (puAmalgam h.le).Universal) * p * (k : _)⁻¹ ∈ P := by
      intro k hk p hp
      have hpU := hPU hp
      have hmem : (k : (puAmalgam h.le).Universal) * p * (k : _)⁻¹ ∈ Uloc h.le L x :=
        (Subgroup.mem_normalizer_iff.mp (hψU.1 k.2) p).mp hpU
      refine (hP ⟨_, hmem⟩).mpr ?_
      rw [natVec_conj hψU k ⟨p, hpU⟩ ⟨_, hmem⟩ rfl]
      have := (pt0 : Submodule F (Fin 3 → F)).add_mem (hk (natVec hψU ⟨p, hpU⟩))
        ((hP ⟨p, hpU⟩).mp hp)
      rwa [sub_add_cancel] at this
    have hinv : ∀ v : Fin 3 → F,
        ((toSL3 ψ g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0 := by
      rw [map_inv]
      exact sub_mem_pt0_iff_mem_qPt.mpr (Subgroup.inv_mem _ (sub_mem_pt0_iff_mem_qPt.mp hg))
    refine ⟨g.2, Subgroup.mem_normalizer_iff.mpr fun p => ⟨hconj g hg p, fun hp => ?_⟩,
      fun z hz => ?_⟩
    · have := hconj g⁻¹ hinv _ hp
      simpa [mul_assoc] using this
    · obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc h hfull hx hz
      have hζg : ζ * (g : (puAmalgam h.le).Universal) = (g : _) * ζ :=
        (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hx hζ) g g.2).symm
      have e1 : ⁅u * ζ, (g : (puAmalgam h.le).Universal)⁆ =
          ⁅u, (g : (puAmalgam h.le).Universal)⁆ := by
        simp only [commutatorElement_def]
        calc u * ζ * (g : (puAmalgam h.le).Universal) * (u * ζ)⁻¹ * (g : _)⁻¹
            = u * (ζ * (g : _)) * ζ⁻¹ * u⁻¹ * (g : _)⁻¹ := by group
          _ = u * ((g : _) * ζ) * ζ⁻¹ * u⁻¹ * (g : _)⁻¹ := by rw [hζg]
          _ = u * (g : _) * u⁻¹ * (g : _)⁻¹ := by group
      rw [e1]
      exact (hcomm ⟨u, hu⟩).mpr (hg _)

variable [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}

theorem ptQ_le_ptL (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x)
    (hP : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0) :
    ptQ (puAmalgam c.pu.le) x P ≤ ptL _ x ψ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  intro g hg
  have hgs : g ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp hg).1
  exact ⟨hgs, mem_stabE0_of_sub_mem_pt0
    ((mem_ptQ_iff_sub_mem_pt0 c.pu hfull hx hψU hPU hP ⟨g, hgs⟩).mp hg)⟩

theorem ptTheta_eq_one_iff (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x)
    (hP : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0) (g : ↥(ptL (puAmalgam c.pu.le) x ψ)) :
    ptTheta ψ g = 1 ↔ (g : (puAmalgam c.pu.le).Universal) ∈ ptQ _ x P := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  rw [ptTheta_apply, blockE0_eq_one_iff]
  exact (mem_ptQ_iff_sub_mem_pt0 c.pu hfull hx hψU hPU hP ⟨g, ptL_le_stab ψ g.2⟩).symm

theorem natImage_ptQ (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x)
    (hP : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0) :
    natImage ψ (ptQ (puAmalgam c.pu.le) x P) = qPt := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  ext A
  rw [mem_natImage]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact sub_mem_pt0_iff_mem_qPt.mp ((mem_ptQ_iff_sub_mem_pt0 c.pu hfull hx hψU hPU hP a).mp ha)
  · intro hA
    obtain ⟨a, rfl⟩ := toSL3_surjective hψs A
    exact ⟨a, (mem_ptQ_iff_sub_mem_pt0 c.pu hfull hx hψU hPU hP a).mpr
      (sub_mem_pt0_iff_mem_qPt.mpr hA), rfl⟩

theorem le_uloc_of_isPtOn (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) : P ≤ Uloc c.pu.le L x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  obtain ⟨β', hxβ', -, rfl⟩ := hP
  exact inf_le_right.trans (usup_le_uloc' c.pu hfull hx hxβ')

end Kernel

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem mem_usup_iff_ln01 (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn) (u : ↥(Uloc c.pu.le L x)) :
    (u : (puAmalgam c.pu.le).Universal) ∈ Usup _ x β ↔ natVec hψU u ∈ ln01 := by
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  rw [mem_usup_iff c.pu c.via (h464 G M T L F φ c) hsq hx hxβ hψU, hT, fixN_qLn]

theorem exists_coord_pt (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) :
    ∃ ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      ∃ hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1,
        (∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
          natVec hψU u ∈ pt0) ∧
        natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨β', hxβ', hne, rfl⟩ := hP
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc c.pu c.via hx
  have hW := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ₀).1
  have hW' := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ' hψ₀).1
  have hWW' : fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) β)) ≠ fixN (natImage ψ₀ (Qv _ β')) :=
    fun heq => hne ((S45.eq_iff_of_natVec_iff hψ₀ (usup_le_uloc' c.pu hfull hx hxβ')
      (usup_le_uloc' c.pu hfull hx hxβ) (mem_usup_iff c.pu c.via h464' hsq hx hxβ' hψ₀)
      (mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ₀)).mpr heq.symm)
  obtain ⟨A, hAW, hAp⟩ :=
    exists_sl3_map_flag hW (S45.finrank_inf_eq_one hW hW' hWW') inf_le_left
  have hψ := isSumOfNaturalModulesVia_conjSL hψ₀ A
  have hfix : ∀ δ, fixN (natImage (conjSL A ψ₀) (Qv (puAmalgam c.pu.le) δ)) =
      (fixN (natImage ψ₀ (Qv (puAmalgam c.pu.le) δ))).map
        (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := fun δ => by
    rw [natImage_conjSL_eq, fixN_map_conj]
  refine ⟨conjSL A ψ₀, conjSL_surjective hψ₀s, hψ, fun u => ?_, ?_⟩
  · rw [Subgroup.mem_inf, mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ,
      mem_usup_iff c.pu c.via h464' hsq hx hxβ' hψ, ← Submodule.mem_inf, hfix, hfix,
      ← Submodule.map_inf _ (Matrix.SpecialLinearGroup.toLin' A).injective, hAp]
  · rw [I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hx hxβ hψ, hfix, hAW,
      axisGroup_ln01]

end Coord

end CFSG.Quasithin.MS93.S46R
