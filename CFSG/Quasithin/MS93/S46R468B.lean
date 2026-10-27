module

public import CFSG.Quasithin.MS93.S46R468Pt
public import CFSG.Quasithin.MS93.S46I468

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def S468At (α β : Vtx X) : Prop :=
  ∀ g, IsOddL1 X α β g → ∀ x ∈ Vv X β, ∀ v ∈ Vv X α, ⁅⁅x, g⁆, v⁆ ∈ stabCenter X α

@[expose] def S468Via (α β γ : Vtx X) : Prop :=
  ∀ g, IsOddL1 X α β g → ∀ z ∈ ZM X γ, ∀ v ∈ Vv X α, ⁅⁅z, g⁆, v⁆ ∈ stabCenter X α

variable {X}

private theorem mem_stabCenter_iff' {δ : Vtx X} {z : X.Universal} :
    z ∈ stabCenter X δ ↔ z ∈ stab X δ ∧ ∀ y ∈ stab X δ, y * z = z * y := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hc y y.2), rfl⟩

private theorem conj_mem_stabCenter {δ : Vtx X} {z : X.Universal} (k : X.Universal)
    (hz : z ∈ stabCenter X δ) : k * z * k⁻¹ ∈ stabCenter X (k • δ) := by
  rw [mem_stabCenter_iff'] at hz ⊢
  have e : k⁻¹ * (k * z * k⁻¹) * k = z := by group
  refine ⟨by rw [mem_stab_smul, e]; exact hz.1, fun y hy => ?_⟩
  rw [mem_stab_smul] at hy
  calc y * (k * z * k⁻¹) = k * ((k⁻¹ * y * k) * z) * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * y * k)) * k⁻¹ := by rw [hz.2 _ hy]
    _ = k * z * k⁻¹ * y := by group

theorem isOddL1_conj (k : X.Universal) {α β : Vtx X} {g : X.Universal} (hg : IsOddL1 X α β g) :
    IsOddL1 X (k • α) (k • β) (k * g * k⁻¹) := by
  obtain ⟨hs, hn, hz, ho⟩ := hg
  refine ⟨?_, ?_, fun z hz' => ?_, ?_⟩
  · have e : k⁻¹ * (k * g * k⁻¹) * k = g := by group
    rw [mem_stab_smul, e]
    exact hs
  · rw [qv_smul, normalizer_map_conj]
    exact conj_mem_map_conj hn
  · rw [zm_smul, mem_map_conj] at hz'
    rw [zh_smul]
    have e : ⁅z, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * z * k, g⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_mem_map_conj (hz _ hz')
  · have e : k * g * k⁻¹ = MulAut.conj k g := by rw [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq]
    exact ho

theorem S468At.smul {α β : Vtx X} (h : S468At X α β) (k : X.Universal) :
    S468At X (k • α) (k • β) := by
  intro g hg x hx v hv
  have hg' := isOddL1_conj k⁻¹ hg
  rw [inv_smul_smul, inv_smul_smul, inv_inv] at hg'
  rw [show Vv X (k • β) = (Vv X β).map (MulAut.conj k).toMonoidHom from vi_smul X k β 2,
    mem_map_conj] at hx
  rw [show Vv X (k • α) = (Vv X α).map (MulAut.conj k).toMonoidHom from vi_smul X k α 2,
    mem_map_conj] at hv
  have h1 := conj_mem_stabCenter k (h _ hg' _ hx _ hv)
  have e : k * ⁅⁅k⁻¹ * x * k, k⁻¹ * g * k⁆, k⁻¹ * v * k⁆ * k⁻¹ = ⁅⁅x, g⁆, v⁆ := by
    simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem s468At_smul (k : X.Universal) (α β : Vtx X) :
    S468At X (k • α) (k • β) ↔ S468At X α β := by
  refine ⟨fun h => ?_, fun h => h.smul k⟩
  have := h.smul k⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem S468Via.smul {α β γ : Vtx X} (h : S468Via X α β γ) (k : X.Universal) :
    S468Via X (k • α) (k • β) (k • γ) := by
  intro g hg z hz v hv
  have hg' := isOddL1_conj k⁻¹ hg
  rw [inv_smul_smul, inv_smul_smul, inv_inv] at hg'
  rw [zm_smul, mem_map_conj] at hz
  rw [show Vv X (k • α) = (Vv X α).map (MulAut.conj k).toMonoidHom from vi_smul X k α 2,
    mem_map_conj] at hv
  have h1 := conj_mem_stabCenter k (h _ hg' _ hz _ hv)
  have e : k * ⁅⁅k⁻¹ * z * k, k⁻¹ * g * k⁆, k⁻¹ * v * k⁆ * k⁻¹ = ⁅⁅z, g⁆, v⁆ := by
    simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem s468Via_smul (k : X.Universal) (α β γ : Vtx X) :
    S468Via X (k • α) (k • β) (k • γ) ↔ S468Via X α β γ := by
  refine ⟨fun h => ?_, fun h => h.smul k⟩
  have := h.smul k⁻¹
  rwa [inv_smul_smul, inv_smul_smul, inv_smul_smul] at this

theorem S468At.via {α β γ : Vtx X} (h : S468At X α β) (hβγ : X.treeGraph.Adj β γ)
    (hγ : IsMVtx X γ) : S468Via X α β γ :=
  fun g hg z hz v hv => h g hg z (zm_le_vv_of_adj hβγ hγ hz) v hv

end Def

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem vv_le_stab_self (c : Hyp46 M T L φ) (x : Vtx (puAmalgam c.pu.le)) :
    Vv (puAmalgam c.pu.le) x ≤ stab _ x :=
  (S45.vi_le_qv _ (by rw [SimpleGraph.dist_self, c.b4]; omega)).trans (qv_le_stab _ x)

theorem vv_le_normalizer_zloc (c : Hyp46 M T L φ) (x : Vtx (puAmalgam c.pu.le)) :
    Vv (puAmalgam c.pu.le) x ≤
      Subgroup.normalizer (Zloc c.pu.le L x : Set (puAmalgam c.pu.le).Universal) :=
  (vv_le_stab_self c x).trans (stab_le_normalizer_puTrans c.pu.le (S4A.Zq_normal c.pu) x)

@[expose] def bzero (c : Hyp46 M T L φ) (x : Vtx (puAmalgam c.pu.le)) :
    Subgroup (puAmalgam c.pu.le).Universal where
  carrier := {v | v ∈ Vv (puAmalgam c.pu.le) x ∧
    ∀ w ∈ Vv (puAmalgam c.pu.le) x, ⁅v, w⁆ ∈ Zloc c.pu.le L x}
  one_mem' := ⟨Subgroup.one_mem _, fun w _ => by
    rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro v v' ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨Subgroup.mul_mem _ hv hw, fun w hwV => ?_⟩
    have e : ⁅v * v', w⁆ = v * ⁅v', w⁆ * v⁻¹ * ⁅v, w⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x hv) _).mp
      (hw' w hwV)) (hv' w hwV)
  inv_mem' := by
    rintro v ⟨hv, hv'⟩
    refine ⟨Subgroup.inv_mem _ hv, fun w hwV => ?_⟩
    have e : ⁅v⁻¹, w⁆ = v⁻¹ * ⁅v, w⁆⁻¹ * v⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x (Subgroup.inv_mem _ hv))
      _).mp (Subgroup.inv_mem _ (hv' w hwV))

theorem mem_bzero {c : Hyp46 M T L φ} {x : Vtx (puAmalgam c.pu.le)}
    {v : (puAmalgam c.pu.le).Universal} :
    v ∈ bzero c x ↔ v ∈ Vv (puAmalgam c.pu.le) x ∧
      ∀ w ∈ Vv (puAmalgam c.pu.le) x, ⁅v, w⁆ ∈ Zloc c.pu.le L x :=
  Iff.rfl

theorem bzero_smul (c : Hyp46 M T L φ) (g : (puAmalgam c.pu.le).Universal)
    (x : Vtx (puAmalgam c.pu.le)) :
    bzero c (g • x) = (bzero c x).map (MulAut.conj g).toMonoidHom := by
  ext v
  rw [mem_map_conj, mem_bzero, mem_bzero,
    show Vv (puAmalgam c.pu.le) (g • x) = (Vv _ x).map (MulAut.conj g).toMonoidHom from
      vi_smul _ g x 2, zloc_smul c.pu, mem_map_conj]
  refine and_congr_right fun _ => ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · have h1 := h (g * w * g⁻¹) (conj_mem_map_conj hw)
    rw [mem_map_conj] at h1
    have e : g⁻¹ * ⁅v, g * w * g⁻¹⁆ * g = ⁅g⁻¹ * v * g, w⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at h1
  · rw [mem_map_conj] at hw ⊢
    have e : g⁻¹ * ⁅v, w⁆ * g = ⁅g⁻¹ * v * g, g⁻¹ * w * g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h _ hw

theorem stab_le_normalizer_bzero (c : Hyp46 M T L φ) (x : Vtx (puAmalgam c.pu.le)) :
    stab (puAmalgam c.pu.le) x ≤
      Subgroup.normalizer (bzero c x : Set (puAmalgam c.pu.le).Universal) :=
  stab_le_normalizer_of_smul _ (fun g y => bzero_smul c g y) x

@[expose] def NonDeg (c : Hyp46 M T L φ) (α β γ : Vtx (puAmalgam c.pu.le)) : Prop :=
  (∀ P, IsPtOn (puAmalgam c.pu.le) γ β P →
      ¬ Usup (puAmalgam c.pu.le) α β ≤ P ⊔ Zloc c.pu.le L γ) ∧
    ∀ P, IsPtOn (puAmalgam c.pu.le) α β P →
      ¬ Usup (puAmalgam c.pu.le) γ β ≤ P ⊔ Zloc c.pu.le L α

private theorem nonDeg_half_smul (c : Hyp46 M T L φ) (g : (puAmalgam c.pu.le).Universal)
    {α β γ : Vtx (puAmalgam c.pu.le)}
    (h : ∀ P, IsPtOn (puAmalgam c.pu.le) γ β P →
      ¬ Usup (puAmalgam c.pu.le) α β ≤ P ⊔ Zloc c.pu.le L γ) :
    ∀ P, IsPtOn (puAmalgam c.pu.le) (g • γ) (g • β) P →
      ¬ Usup (puAmalgam c.pu.le) (g • α) (g • β) ≤ P ⊔ Zloc c.pu.le L (g • γ) := by
  intro P hP hle
  have hP' : P = (P.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv P g).symm
  rw [hP', isPtOn_smul] at hP
  rw [hP', usup_smul, zloc_smul c.pu, ← Subgroup.map_sup, map_conj_le_map_conj_iff] at hle
  exact h _ hP hle

theorem NonDeg.smul {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)} (h : NonDeg c α β γ)
    (g : (puAmalgam c.pu.le).Universal) : NonDeg c (g • α) (g • β) (g • γ) :=
  ⟨nonDeg_half_smul c g h.1, nonDeg_half_smul c g h.2⟩

structure BadConf (c : Hyp46 M T L φ) (α α' : Vtx (puAmalgam c.pu.le)) : Prop where
  crit : IsCritical (puAmalgam c.pu.le) α α'
  bad : ¬ S468Via (puAmalgam c.pu.le) α (geo _ α α' 1) (geo _ α α' 2)
  nondeg : NonDeg c α (geo _ α α' 1) (geo _ α α' 2)

theorem BadConf.smul {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α')
    (g : (puAmalgam c.pu.le).Universal) : BadConf c (g • α) (g • α') where
  crit := (isCritical_smul _ g α α').mpr hB.crit
  bad := by
    rw [geo_smul, geo_smul, s468Via_smul]
    exact hB.bad
  nondeg := by
    rw [geo_smul, geo_smul]
    exact hB.nondeg.smul g

theorem BadConf.not_s468At {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)}
    (hB : BadConf c α α') : ¬ S468At (puAmalgam c.pu.le) α (geo _ α α' 1) := fun h =>
  hB.bad (h.via (adj_geo _ (by rw [hB.crit.2.1, c.b4]; omega))
    (isMVtx_geo_two _ c.pu.hyp20 c.pu.critDist_pos hB.crit))

theorem s468_of_s468At
    (h : ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
      (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
      IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β → S468At (puAmalgam c.pu.le) α β) :
    S46.S468 := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ g hg hgN hgZ hodd x hx v hv
  exact h G M T L F φ c α β hα hαβ g ⟨hg, hgN, hgZ, hodd⟩ x hx v hv

end CFSG.Quasithin.MS93.S46R
