module

public import CFSG.Quasithin.MS93.Burnside.RigS12
public import CFSG.Quasithin.MS93.S46IdxLin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support.S45CircQ4
public import CFSG.Quasithin.MS93.Burnside.C1bMain

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section SL3

variable {F : Type} [Field F]

theorem burnsideRig_fix_rH_iff (x : Fin 3 → F) :
    (∀ g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) ↔ x 0 = 0 := by
  constructor
  · intro h
    have h1 := h (rootElt 1 0 1) (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 1))
    rw [CFSG.Quasithin.MS93.rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide)] at h1
    have h2 := congrFun h1 1
    simpa using h2
  · intro h0 g hg
    obtain ⟨s, t, rfl⟩ := S46.Idx.mem_rH_iff.mp hg
    rw [S46.Idx.rootElt10_mul_rootElt20_mulVec, h0]
    have e : (![0, s * 0, t * 0] : Fin 3 → F) = 0 := by
      funext k; fin_cases k <;> simp
    rw [e, add_zero]

theorem burnsideRig_diagPt_conj_rootElt10 (l : F) (hl : l ≠ 0) (t : F) :
    diagPt l hl * rootElt 1 0 t * (diagPt l hl)⁻¹ = rootElt 1 0 (l⁻¹ * l⁻¹ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((diagPt l hl : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 1 0 t : SL3 F) :
      Matrix _ _ F) = ((rootElt 1 0 (l⁻¹ * l⁻¹ * t) : SL3 F) : Matrix _ _ F) *
      ((diagPt l hl : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_rootElt (by decide), diagPt, Matrix.SpecialLinearGroup.diag2n_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  field_simp

theorem burnsideRig_diagPt_conj_rootElt20 (l : F) (hl : l ≠ 0) (t : F) :
    diagPt l hl * rootElt 2 0 t * (diagPt l hl)⁻¹ = rootElt 2 0 (l⁻¹ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((diagPt l hl : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((rootElt 2 0 t : SL3 F) :
      Matrix _ _ F) = ((rootElt 2 0 (l⁻¹ * t) : SL3 F) : Matrix _ _ F) *
      ((diagPt l hl : SL3 F) : Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_rootElt (by decide), diagPt, Matrix.SpecialLinearGroup.diag2n_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  field_simp

theorem burnsideRig_diagPt_conj_mem_rH (l : F) (hl : l ≠ 0) {g : SL3 F}
    (hg : g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) :
    diagPt l hl * g * (diagPt l hl)⁻¹ ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
  obtain ⟨s, t, rfl⟩ := S46.Idx.mem_rH_iff.mp hg
  have e : diagPt l hl * (rootElt 1 0 s * rootElt 2 0 t) * (diagPt l hl)⁻¹ =
      (diagPt l hl * rootElt 1 0 s * (diagPt l hl)⁻¹) *
        (diagPt l hl * rootElt 2 0 t * (diagPt l hl)⁻¹) := by group
  rw [e, burnsideRig_diagPt_conj_rootElt10, burnsideRig_diagPt_conj_rootElt20]
  exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

theorem burnsideRig_diagPt_mem_normalizer_rH (l : F) (hl : l ≠ 0) :
    diagPt l hl ∈ Subgroup.normalizer
      ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨burnsideRig_diagPt_conj_mem_rH l hl, fun hg => ?_⟩
  have hinv : (diagPt l hl)⁻¹ = diagPt l⁻¹ (inv_ne_zero hl) :=
    inv_eq_of_mul_eq_one_right (diagPt_mul_inv l hl)
  have h1 := burnsideRig_diagPt_conj_mem_rH l⁻¹ (inv_ne_zero hl) hg
  rw [← hinv] at h1
  have e : (diagPt l hl)⁻¹ * (diagPt l hl * g * (diagPt l hl)⁻¹) * (diagPt l hl)⁻¹⁻¹ = g := by
    group
  rwa [e] at h1

end SL3

section Local

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideRig_exists_torus (c : Ctx M T L φ) {α β : Vtx (puAmalgam c.hyp.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    (l : F) (hl : l ≠ 0) :
    ∃ e : ↥(stab (puAmalgam c.hyp.le) α), toSL3 ψ e = diagPt l hl ∧
      (e : (puAmalgam c.hyp.le).Universal) ∈
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) := by
  obtain ⟨e, he⟩ := toSL3_surjective hψs (diagPt l hl)
  refine ⟨e, he, c.mem_normalizer_qv_of hα hαβ hψ ?_⟩
  rw [he, hT]
  exact burnsideRig_diagPt_mem_normalizer_rH l hl

theorem burnsideRig_mem_zh_iff (c : Ctx M T L φ) {α β : Vtx (puAmalgam c.hyp.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {u : (puAmalgam c.hyp.le).Universal} (hu : u ∈ Uloc c.hyp.le L α) :
    u ∈ ZH (puAmalgam c.hyp.le) β ↔ (NatSec.ofIsSum hψ).coord u 0 = 0 := by
  set NU := NatSec.ofIsSum hψ with hNU
  have hTs : Qv (puAmalgam c.hyp.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have key : u ∈ ZH (puAmalgam c.hyp.le) β ↔
      u ∈ Subgroup.centralizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) := by
    have h1 := c.uloc_inf_zh hψ hα hαβ
    rw [c.usup_eq_uloc_inf_centralizer hψ hα hαβ] at h1
    constructor
    · intro hz
      have : u ∈ Uloc c.hyp.le L α ⊓ ZH (puAmalgam c.hyp.le) β := ⟨hu, hz⟩
      rw [h1] at this
      exact this.2
    · intro hc
      have : u ∈ Uloc c.hyp.le L α ⊓
          Subgroup.centralizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) :=
        ⟨hu, hc⟩
      rw [← h1] at this
      exact this.2
  rw [key, ← burnsideRig_fix_rH_iff, ← hT]
  constructor
  · intro hc g hg
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    have h1 := NU.coord_conj t hu
    rw [natAct_false] at h1
    rw [← h1]
    have e : (t : (puAmalgam c.hyp.le).Universal) * u * (t : (puAmalgam c.hyp.le).Universal)⁻¹ =
        u := by
      rw [Subgroup.mem_centralizer_iff.mp hc _ htT, mul_inv_cancel_right]
    rw [e]
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    set t' : ↥(stab (puAmalgam c.hyp.le) α) := ⟨t, hTs ht⟩ with ht'
    have h1 := NU.coord_conj t' hu
    rw [natAct_false, hfix _ (mem_natImage.mpr ⟨t', ht, rfl⟩)] at h1
    have h2 := NU.eq_of_coord_eq (NU.conj_mem t' hu) hu h1
    have e : t * u = (t * u * t⁻¹) * t := by group
    rw [e]
    exact congrArg (· * t) h2

theorem burnsideRig_coord_conj_torus (c : Ctx M T L φ) {α : Vtx (puAmalgam c.hyp.le)}
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1)
    {l : F} {hl : l ≠ 0} {e : ↥(stab (puAmalgam c.hyp.le) α)} (he : toSL3 ψ e = diagPt l hl)
    {u : (puAmalgam c.hyp.le).Universal} (hu : u ∈ Uloc c.hyp.le L α) :
    (NatSec.ofIsSum hψ).coord ((e : (puAmalgam c.hyp.le).Universal) * u *
      (e : (puAmalgam c.hyp.le).Universal)⁻¹) 0 = l * (NatSec.ofIsSum hψ).coord u 0 := by
  rw [(NatSec.ofIsSum hψ).coord_conj e hu, natAct_false, he, diagPt_mulVec]
  rfl

theorem burnsideRig_commutator_le_zm_inf_vcirc (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅(Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ⊔ (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)),
        Qv (puAmalgam c.hyp.le) (p a)⁆ ≤
      ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  set X := ZM (puAmalgam h.le) (p a) ⊓ Vcirc h.le L (p (a + 2)) with hX
  have hnX : ∀ g, g ∈ stab (puAmalgam h.le) (p a) → g ∈ stab (puAmalgam h.le) (p (a + 2)) →
      g ∈ Subgroup.normalizer (X : Set (puAmalgam h.le).Universal) := by
    intro g hga hgγ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hX, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ _ hga) x,
      Subgroup.mem_normalizer_iff.mp (c.stab_le_normalizer_vcirc _ hgγ) x]
  have hVγs : Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) ≤ stab _ (p a) :=
    (c.vhat_le_vv hγ).trans ((vi_le_qv _ (by rw [tdist_comm, hd2, c.b8]; omega)).trans
      (qv_le_stab _ _))
  have hVγs' : Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) ≤ stab _ (p (a + 2)) :=
    (c.vhat_le_vv hγ).trans ((c.vv_le_qv' hγ).trans (qv_le_stab _ _))
  have hVαs : Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) ≤ stab _ (p a) :=
    (c.vhat_le_vv hα).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _))
  have hVαs' : Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) ≤ stab _ (p (a + 2)) :=
    (c.vhat_le_vv hα).trans ((vi_le_qv _ (by rw [hd2, c.b8]; omega)).trans (qv_le_stab _ _))
  refine commutator_sup_left_le (fun g hg => hnX g (hVγs hg) (hVγs' hg))
    (fun g hg => hnX g (hVαs hg) (hVαs' hg))
    (burnsideC1b_commutator_vhat_qv_le c hZV hp ha (by omega) (by omega)) ?_
  have hH : ⁅Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a), Qv (puAmalgam h.le) (p a)⁆ ≤
      Hloc h.le L (p a) := by
    refine commutator_sup_left_le
      (((c.vcirc_le_vv _).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _))).trans
        (stab_le_normalizer_hloc c _))
      (((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _)).trans
        (stab_le_normalizer_hloc c _)) le_rfl ?_
    rw [commutator_zm_qv _ h20 hα]
    exact bot_le
  refine hH.trans (le_inf ((hloc_le_zloc c hα).trans (zloc_le_zm h c.full hα)) ?_)
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := (Nat.even_add.mp ha).mpr (by decide)
  rw [show x + 6 + 2 = x + 8 by omega] at hγ hγβ ⊢
  rw [c.hloc_eq_usup' hp hx (by omega) (by omega)]
  obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
  rw [c.usup_eq_uloc_inf_centralizer hψγ hγ (by rw [show x + 7 = x + 6 + 1 by omega]; exact hγβ)]
  exact inf_le_left.trans (uloc_le_vcirc c hγ)

theorem burnsideRig_inf_zh_le (c : Ctx M T L φ) (hq : 4 ≤ Fintype.card F)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p (a + 2)) ⊓ ZH _ (p (a + 1)) ≤
      ZM (puAmalgam c.hyp.le) (p a) ⊓ Vcirc c.hyp.le L (p a) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  obtain ⟨ψα, -, hψα⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := (Nat.even_add.mp ha).mpr (by decide)
  have hHα : Hloc h.le L (p (x + 6)) = Usup (puAmalgam h.le) (p (x + 6 + 2)) (p (x + 6 + 1)) :=
    c.hloc_eq_usup' hp hx (by omega) (by omega)
  have hHγ : Hloc h.le L (p (x + 6 + 2)) = Usup (puAmalgam h.le) (p (x + 6)) (p (x + 6 + 1)) := by
    have := c.hloc_eq_usup hp (x := x + 2) (hx.add even_two) (by omega) (by omega)
    rwa [show x + 2 + 6 = x + 6 + 2 by omega, show x + 2 + 4 = x + 6 by omega,
      show x + 2 + 5 = x + 6 + 1 by omega] at this
  intro z hz
  obtain ⟨⟨hzα, hzγ⟩, hzβ⟩ := hz
  refine ⟨hzα, ?_⟩
  have hzZγ : z ∈ ZM (puAmalgam h.le) (p (x + 6 + 2)) := zh_le_zm _ hγβ hzβ
  have hUH := s45C1aQ4_holds G M T L F φ c hq (p (x + 6 + 2)) hγ ⟨hzγ, hzZγ⟩
  have hn : Uloc h.le L (p (x + 6 + 2)) ≤
      Subgroup.normalizer (Hloc h.le L (p (x + 6 + 2)) : Set (puAmalgam h.le).Universal) :=
    (uloc_le_stab c hγ).trans (stab_le_normalizer_hloc c _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hUH
  obtain ⟨u, hu, k, hk, rfl⟩ := Set.mem_mul.mp hUH
  rw [hHγ] at hk
  have hkβ : k ∈ ZH (puAmalgam h.le) (p (x + 6 + 1)) := by
    rw [c.zh_eq_usup_sup_zloc hψα hα hαβ]; exact Subgroup.mem_sup_left hk
  have hkU : k ∈ Uloc h.le L (p (x + 6)) := by
    rw [c.usup_eq_uloc_inf_centralizer hψα hα hαβ] at hk; exact hk.1
  have huβ : u ∈ ZH (puAmalgam h.le) (p (x + 6 + 1)) := by
    have := (ZH (puAmalgam h.le) (p (x + 6 + 1))).mul_mem hzβ
      ((ZH (puAmalgam h.le) (p (x + 6 + 1))).inv_mem hkβ)
    rwa [mul_inv_cancel_right] at this
  have huH : u ∈ Hloc h.le L (p (x + 6)) := by
    rw [hHα, ← c.uloc_inf_zh hψγ hγ hγβ]
    exact ⟨hu, huβ⟩
  exact Subgroup.mul_mem _ (hloc_le_vcirc c _ huH) (uloc_le_vcirc c hα hkU)

theorem burnsideRig_not_commutator_le_zh (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ¬ ⁅Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)), Qv (puAmalgam c.hyp.le) (p a)⁆ ≤
      ZH (puAmalgam c.hyp.le) (p (a + 1)) := by
  intro hle
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  set Vγ := Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) with hVγ
  have hTsγ : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab _ (p (a + 2)) := qv_le_stab_of_adj _ hγβ.symm
  have hQαT : Qv (puAmalgam h.le) (p a) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hα hαβ
  have hKZ := stab_le_normalizer_zm (puAmalgam h.le) (p (a + 2))
  have hT : ⁅Vγ, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ ZM _ (p (a + 2)) :=
    burnsideRig_commutator_le_of_le_sup (burnsideRig_qv_le_qv_sup_qv c hZV hp ha (by omega)
      (by omega)) ((hQαT.trans hTsγ).trans hKZ) ((qv_le_stab _ _).trans hKZ)
      (hle.trans (zh_le_zm _ hγβ))
      ((Subgroup.commutator_mono (c.vhat_le_vv hγ) le_rfl).trans
        ((c.commutator_vv_qv_le_zloc hγ).trans (zloc_le_zm h c.full hγ)))
  obtain ⟨ψγ, hψγs, hψγ⟩ := exists_natural_Uloc h c.via hγ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hγ hψγs hψγ
  set Nn := NatSec.ofIsSum hd with hNn
  have hTQ : Qv (puAmalgam h.le) (p (a + 1)) ≤ Qv _ (p (a + 2)) := by
    intro t ht
    set t' : ↥(stab (puAmalgam h.le) (p (a + 2))) := ⟨t, hTsγ ht⟩ with ht'
    have h1 : toSL3 ψγ t' = 1 := by
      refine eq_one_of_natAct_mulVec_eq_self d fun y => ?_
      obtain ⟨v, hv, rfl⟩ := Nn.exists_coord_eq y
      have hw1 : t * v⁻¹ * t⁻¹ ∈ Vγ := Nn.conj_mem t' (inv_mem hv)
      have hc : ⁅v, t⁆ ∈ ZM (puAmalgam h.le) (p (a + 2)) :=
        hT (Subgroup.commutator_mem_commutator hv ht)
      have hcV : ⁅v, t⁆ ∈ Vγ := by
        rw [commutatorElement_def, show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group]
        exact mul_mem hv hw1
      have h0 := (Nn.coord_eq_zero_iff hcV).mpr hc
      rw [commutatorElement_def, show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group,
        Nn.coord_mul hv hw1, show t * v⁻¹ * t⁻¹ = (t' : (puAmalgam h.le).Universal) * v⁻¹ *
          (t' : (puAmalgam h.le).Universal)⁻¹ from rfl, Nn.coord_conj t' (inv_mem hv),
        Nn.coord_inv hv, Matrix.mulVec_neg] at h0
      exact (add_neg_eq_zero.mp h0).symm
    have hk : t' ∈ (toSL3 ψγ).ker := h1
    rw [c.ker_toSL3_eq hγ hψγ, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hidx := c.relIndex_qv hγ hγβ
  rw [Subgroup.relIndex_eq_one.mpr hTQ] at hidx
  have hq := Fintype.one_lt_card (α := F)
  have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq
  omega

theorem burnsideRig_exists_inv_mul_mem (c : Ctx M T L φ) {α β : Vtx (puAmalgam c.hyp.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {St : Subgroup (puAmalgam c.hyp.le).Universal} (hStZ : St ≤ ZM (puAmalgam c.hyp.le) α)
    (hinv : ∀ g ∈ stab (puAmalgam c.hyp.le) α, g ∈ Subgroup.normalizer
      (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) →
        ∀ s ∈ St, g * s * g⁻¹ ∈ St)
    (hne : ¬ St ≤ ZH (puAmalgam c.hyp.le) β) :
    ∀ z ∈ ZM (puAmalgam c.hyp.le) α, ∃ s ∈ St, s⁻¹ * z ∈ ZH (puAmalgam c.hyp.le) β := by
  have h := c.hyp
  set NU := NatSec.ofIsSum hψ with hNU
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hZlβ : Zloc h.le L α ≤ ZH (puAmalgam h.le) β := by
    rw [c.zh_eq_usup_sup_zloc hψ hα hαβ]; exact le_sup_right
  obtain ⟨s₀, hs₀, hs₀β⟩ := Set.not_subset.mp hne
  obtain ⟨u₀, hu₀, w₀, hw₀, rfl⟩ := exists_mul_of_mem_zm c hα (hStZ hs₀)
  have hc₀ : NU.coord u₀ 0 ≠ 0 := by
    intro h0
    apply hs₀β
    exact Subgroup.mul_mem _ ((burnsideRig_mem_zh_iff c hα hαβ hψ hT hu₀).mpr h0) (hZlβ hw₀)
  intro z hz
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_zm c hα hz
  by_cases hc : NU.coord u 0 = 0
  · refine ⟨1, St.one_mem, ?_⟩
    rw [inv_one, one_mul]
    exact Subgroup.mul_mem _ ((burnsideRig_mem_zh_iff c hα hαβ hψ hT hu).mpr hc) (hZlβ hw)
  · set l := NU.coord u 0 / NU.coord u₀ 0 with hl
    have hl0 : l ≠ 0 := div_ne_zero hc hc₀
    obtain ⟨e, he, heT⟩ := burnsideRig_exists_torus c hα hαβ hψs hψ hT l hl0
    refine ⟨(e : (puAmalgam h.le).Universal) * (u₀ * w₀) * (e : (puAmalgam h.le).Universal)⁻¹,
      hinv _ e.2 heT _ hs₀, ?_⟩
    have hwe : (e : (puAmalgam h.le).Universal) * w₀ * (e : (puAmalgam h.le).Universal)⁻¹ = w₀ := by
      rw [(Subgroup.mem_centralizer_iff.mp (hZc hw₀)) _ e.2, mul_inv_cancel_right]
    set u' := (e : (puAmalgam h.le).Universal) * u₀ * (e : (puAmalgam h.le).Universal)⁻¹ with hu'
    have hu'U : u' ∈ Uloc h.le L α := NU.conj_mem e hu₀
    have e1 : ((e : (puAmalgam h.le).Universal) * (u₀ * w₀) *
        (e : (puAmalgam h.le).Universal)⁻¹)⁻¹ * (u * w) = w₀⁻¹ * (u'⁻¹ * u) * w := by
      have e2 : (e : (puAmalgam h.le).Universal) * (u₀ * w₀) * (e : (puAmalgam h.le).Universal)⁻¹ =
          u' * ((e : (puAmalgam h.le).Universal) * w₀ * (e : (puAmalgam h.le).Universal)⁻¹) := by
        rw [hu']; group
      rw [e2, hwe]; group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hZlβ hw₀)) ?_) (hZlβ hw)
    refine (burnsideRig_mem_zh_iff c hα hαβ hψ hT (mul_mem (inv_mem hu'U) hu)).mpr ?_
    rw [NU.coord_mul (inv_mem hu'U) hu, NU.coord_inv hu'U, Pi.add_apply, Pi.neg_apply,
      hu', burnsideRig_coord_conj_torus c hψ he hu₀, hl, div_mul_cancel₀ _ hc₀, neg_add_cancel]

theorem burnsideRig_exists_inv_mul_mem_of_torus (c : Ctx M T L φ) {α β : Vtx (puAmalgam c.hyp.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {l : F} {hl : l ≠ 0} (hl1 : l ≠ 1) {e : ↥(stab (puAmalgam c.hyp.le) α)}
    (he : toSL3 ψ e = diagPt l hl) :
    ∀ z ∈ ZM (puAmalgam c.hyp.le) α, ∃ y ∈ ZM (puAmalgam c.hyp.le) α,
      ((e : (puAmalgam c.hyp.le).Universal) * y * (e : (puAmalgam c.hyp.le).Universal)⁻¹ *
        y⁻¹)⁻¹ * z ∈ ZH (puAmalgam c.hyp.le) β := by
  have h := c.hyp
  set NU := NatSec.ofIsSum hψ with hNU
  have hZlβ : Zloc h.le L α ≤ ZH (puAmalgam h.le) β := by
    rw [c.zh_eq_usup_sup_zloc hψ hα hαβ]; exact le_sup_right
  intro z hz
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_zm c hα hz
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  obtain ⟨y, hy, hyc⟩ := NU.exists_coord_eq ![NU.coord u 0 / (l - 1), 0, 0]
  refine ⟨y, uloc_le_zm h c.full hα hy, ?_⟩
  set u' := (e : (puAmalgam h.le).Universal) * y * (e : (puAmalgam h.le).Universal)⁻¹ * y⁻¹
    with hu'
  have hu'U : u' ∈ Uloc h.le L α := mul_mem (NU.conj_mem e hy) (inv_mem hy)
  have e1 : u'⁻¹ * (u * w) = (u'⁻¹ * u) * w := by group
  rw [e1]
  refine Subgroup.mul_mem _ ?_ (hZlβ hw)
  refine (burnsideRig_mem_zh_iff c hα hαβ hψ hT (mul_mem (inv_mem hu'U) hu)).mpr ?_
  rw [NU.coord_mul (inv_mem hu'U) hu, NU.coord_inv hu'U, hu',
    NU.coord_mul (NU.conj_mem e hy) (inv_mem hy), NU.coord_inv hy, Pi.add_apply, Pi.neg_apply,
    Pi.add_apply, Pi.neg_apply, burnsideRig_coord_conj_torus c hψ he hy, hyc]
  simp only [Matrix.cons_val_zero]
  field_simp
  ring

end Local

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
