module

public import CFSG.Quasithin.MS93.S45X0

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem stab_le_normalizer_of_le_centralizer {δ : Vtx (puAmalgam c.hyp.le)}
    {R : Subgroup (puAmalgam c.hyp.le).Universal}
    (hR : R ≤ Subgroup.centralizer (stab (puAmalgam c.hyp.le) δ : Set _)) :
    stab (puAmalgam c.hyp.le) δ ≤ Subgroup.normalizer (R : Set _) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    rw [Subgroup.mem_centralizer_iff.mp (hR hr) g hg, mul_inv_cancel_right]
    exact hr
  · intro hr
    have h1 := Subgroup.mem_centralizer_iff.mp (hR hr) g hg
    have e : r = g * r * g⁻¹ := by
      rw [show g * r * g⁻¹ = g * r * g⁻¹ * g * g⁻¹ by group]
      have : g * (g * r * g⁻¹) = g * r * g⁻¹ * g := h1
      have h2 : g * r * g⁻¹ = r := by
        have := mul_left_cancel (a := g) (this.trans (by group : g * r * g⁻¹ * g = g * r))
        exact this
      rw [h2]; group
    rw [e]
    exact hr

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem commutator_top_vv_le (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h12 : 12 ≤ a)
    (haN : a + 12 ≤ N) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
        whv c.hyp (p a) (p (a + 2)), Vv (puAmalgam c.hyp.le) (p a)⁆ ≤
      critR (puAmalgam c.hyp.le) (p (a - 2)) (p (a + 6)) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc := c.isCritical_of_isGoodPath hp ha2 (show a - 2 + 8 ≤ N by omega)
  rw [show a - 2 + 8 = a + 6 by omega] at hc
  have hg2 : geo (puAmalgam h.le) (p (a - 2)) (p (a + 6)) 2 = p a := by
    rw [hp.eq_geo (i := a - 2) (j := a + 6) (k := a) (by omega) (by omega) (by omega),
      show a - (a - 2) = 2 by omega]
  have hRZ : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ≤ Zloc h.le L (p a) := by
    have := c.critR_le_zloc hc
    rwa [hg2] at this
  have hRn := c.stab_le_normalizer_of_le_centralizer
    (hRZ.trans (zloc_le_centralizer_stab h c.full hα))
  have hVn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 2) (fun g ρ => vi_smul _ g ρ 2) (p a)
  have hVV := (c.commutator_vv_vv hp ha (by omega) (by omega)).1
  have hμα : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ stab (puAmalgam h.le) (p a) :=
    ((c.vhat_le_vv hμ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]
      omega))).trans (qv_le_stab _ _)
  have hWh : whv h (p a) (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
    S4A.conjCl_le_of_le (((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]
      omega))).trans (qv_le_stab _ _))
  refine S46.commutator_sup_le_of_le_normalizer hRn
    (S4A.conjCl_le_of_le hμα) hWh ?_ ?_
  · refine commutator_conjCl_le hRn hμα fun g hg => ?_
    have e : Vv (puAmalgam h.le) (p a) =
        (Vv (puAmalgam h.le) (p a)).map (MulAut.conj g).toMonoidHom :=
      (map_conj_eq_of_mem_normalizer (hVn hg)).symm
    rw [e, ← Subgroup.map_commutator]
    refine (Subgroup.map_mono ?_).trans (map_conj_eq_of_mem_normalizer (hRn hg)).le
    rw [Subgroup.commutator_comm, ← hVV]
    exact Subgroup.commutator_mono le_rfl (c.vhat_le_vv hμ)
  · have hc' := c.whv_le_centralizer_vv hγ (by
      rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega)
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hc']
    exact bot_le

theorem commutator_top_qv_le (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N) {a : ℕ}
    (ha : Even a) (h34 : 34 ≤ a) (haN : a + 27 ≤ N) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
        whv c.hyp (p a) (p (a + 2)), Qv (puAmalgam c.hyp.le) (p a)⁆ ≤
      whv c.hyp (p a) (p (a + 2)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hWhn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (whv h (p a) (p (a + 2)) : Set _) := S4A.le_normalizer_conjCl _ _
  have hQn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_qv _ _
  have hμα : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ stab (puAmalgam h.le) (p a) :=
    ((c.vhat_le_vv hμ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]
      omega))).trans (qv_le_stab _ _)
  have hWh : whv h (p a) (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
    S4A.conjCl_le_of_le (((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]
      omega))).trans (qv_le_stab _ _))
  have hKey : ⁅whv h (p (a + 2)) (p a), Qv (puAmalgam h.le) (p (a + 1))⁆ ≤
      whv h (p a) (p (a + 2)) :=
    (c.commutator_whv_qv_le_vhat_left hZV hQ4 hp ha h34 haN).trans
      (sup_le (c.vhat_le_whv' hZV hp ha (by omega) (by omega)) c.vhat_le_whv_self)
  have hμγ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    have e := c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega] at e
    rw [← e]
    exact c.vhat_le_whv_self
  refine S46.commutator_sup_le_of_le_normalizer hWhn (S4A.conjCl_le_of_le hμα) hWh ?_ ?_
  · refine commutator_conjCl_le hWhn hμα fun g hg => ?_
    rw [show Qv (puAmalgam h.le) (p a) = (Qv (puAmalgam h.le) (p a)).map
      (MulAut.conj g).toMonoidHom from (map_conj_eq_of_mem_normalizer (hQn hg)).symm,
      ← Subgroup.map_commutator]
    refine (Subgroup.map_mono ?_).trans (map_conj_eq_of_mem_normalizer (hWhn hg)).le
    exact (Subgroup.commutator_mono hμγ (qv_le_qv _ h20 hα hαβ)).trans hKey
  · exact (c.commutator_whv_qv_le' hZV hp ha (by omega) (by omega)).trans
      ((le_sup_right.trans (c.vhat_le_whv' hZV hp ha (by omega) (by omega))))

theorem commute_vhat_of_comm (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (haN : a + 2 ≤ N) {x : (puAmalgam c.hyp.le).Universal}
    (hx : x ∈ Qv (puAmalgam c.hyp.le) (p a))
    (hxV : ∀ v ∈ Vv (puAmalgam c.hyp.le) (p a), ⁅x, v⁆ ∈ Zloc c.hyp.le L (p a))
    (hxL : ∀ l ∈ Ltil c.hyp.le L (p a), ⁅x, l⁆ ∈ whv c.hyp (p a) (p (a + 2))) :
    ∀ u ∈ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a), x * u = u * x := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hWc := c.whv_le_centralizer_vv hγ (by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega)
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hLs : Ltil h.le L (p a) ≤ stab (puAmalgam h.le) (p a) := ltil_le_stab h (p a)
  have hVs : Vv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) :=
    (c.vv_le_qv' hα).trans (qv_le_stab _ _)
  have hVn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 2) (fun g ρ => vi_smul _ g ρ 2) (p a)
  have hWs : whv h (p a) (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
    S4A.conjCl_le_of_le ((c.vhat_le_vv hγ).trans ((vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]
      omega)).trans (qv_le_stab _ _)))
  have key : ∀ v ∈ Vv (puAmalgam h.le) (p a), ∀ l ∈ Ltil h.le L (p a),
      x * ⁅v, l⁆ = ⁅v, l⁆ * x := by
    intro v hv l hl
    set r := ⁅x, v⁆ with hr
    set w := ⁅x, l⁆ with hw
    have hrZ := hxV v hv
    have hwW := hxL l hl
    have hr' : x * v * x⁻¹ = r * v := by rw [hr, commutatorElement_def]; group
    have hw' : x * l * x⁻¹ = w * l := by rw [hw, commutatorElement_def]; group
    have hy : v * w * l * v⁻¹ ∈ stab (puAmalgam h.le) (p a) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hVs hv) (hWs hwW)) (hLs hl))
        (Subgroup.inv_mem _ (hVs hv))
    have hrc : r * (v * w * l * v⁻¹) * r⁻¹ = v * w * l * v⁻¹ := by
      rw [← (Subgroup.mem_centralizer_iff.mp (hZc hrZ) _ hy), mul_inv_cancel_right]
    have hz : l * v⁻¹ * l⁻¹ ∈ Vv (puAmalgam h.le) (p a) :=
      (Subgroup.mem_normalizer_iff.mp (hVn (hLs hl)) _).mp (Subgroup.inv_mem _ hv)
    have hwz : w * (l * v⁻¹ * l⁻¹) = (l * v⁻¹ * l⁻¹) * w :=
      (Subgroup.mem_centralizer_iff.mp (hWc hwW) _ hz).symm
    have hconj : x * ⁅v, l⁆ * x⁻¹ = ⁅v, l⁆ := by
      calc x * ⁅v, l⁆ * x⁻¹ = (x * v * x⁻¹) * (x * l * x⁻¹) * (x * v * x⁻¹)⁻¹ *
            (x * l * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
        _ = (r * v) * (w * l) * (r * v)⁻¹ * (w * l)⁻¹ := by rw [hr', hw']
        _ = (r * (v * w * l * v⁻¹) * r⁻¹) * (l⁻¹ * w⁻¹) := by group
        _ = (v * w * l * v⁻¹) * (l⁻¹ * w⁻¹) := by rw [hrc]
        _ = v * (w * (l * v⁻¹ * l⁻¹)) * w⁻¹ := by group
        _ = v * ((l * v⁻¹ * l⁻¹) * w) * w⁻¹ := by rw [hwz]
        _ = ⁅v, l⁆ := by rw [commutatorElement_def]; group
    calc x * ⁅v, l⁆ = x * ⁅v, l⁆ * x⁻¹ * x := by group
      _ = ⁅v, l⁆ * x := by rw [hconj]
  have hc : Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) ≤
      Subgroup.centralizer ({x} : Set (puAmalgam h.le).Universal) := by
    refine sup_le ?_ ?_
    · rw [Vcirc, Subgroup.commutator_le]
      intro v hv l hl
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact key v hv l hl
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hz) _ hx)
  intro u hu
  exact Subgroup.mem_centralizer_iff.mp (hc hu) x rfl

theorem relIndex_top_le (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h12 : 12 ≤ a)
    (haN : a + 12 ≤ N) :
    (Qv (puAmalgam c.hyp.le) (p (a + 2))).relIndex
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
        whv c.hyp (p a) (p (a + 2))) ≤ Fintype.card F := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (p (a + 1)) (p (a + 2)) := hp.adj (a + 1) (by omega)
  have hγ3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
  set X := conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
    whv h (p a) (p (a + 2)) with hX
  have hXV := c.commutator_top_vv_le hp ha h12 haN
  rw [← hX] at hXV
  have hQn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_qv _ _
  have hXQ : X ≤ Qv (puAmalgam h.le) (p a) := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]
      omega))) hQn) (conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]
      omega))) hQn)
  have hXT : X ≤ Qv (puAmalgam h.le) (p (a + 1)) := hXQ.trans (qv_le_qv _ h20 hα hαβ)
  have hXs : X ≤ stab (puAmalgam h.le) (p (a + 2)) := hXT.trans (qv_le_stab_of_adj _ hβγ)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hγ
  rw [← S46.card_natImage_eq_relIndex h c.via hγ hψ hXs]
  have hγβ := hβγ.symm
  set H₁ := fixN (natImage ψ (Qv (puAmalgam h.le) (p (a + 1)))) with hH₁
  set H₃ := fixN (natImage ψ (Qv (puAmalgam h.le) (p (a + 3)))) with hH₃
  have hr1 : Module.finrank F H₁ = 2 := (c.fixN_eq_commN_qv hψ hγ hγβ).2
  have hr3 : Module.finrank F H₃ = 2 := (c.fixN_eq_commN_qv hψ hγ hγ3).2
  have hne : H₁ ≠ H₃ := by
    intro heq
    have hzh := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at hzh
    apply hzh
    rw [← c.usup_eq_iff_zh_eq hψ hγ hγβ hγ3]
    have hU1 : Usup (puAmalgam h.le) (p (a + 2)) (p (a + 1)) ≤ Uloc h.le L (p (a + 2)) := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hγ hγβ]; exact inf_le_left
    have hU3 : Usup (puAmalgam h.le) (p (a + 2)) (p (a + 3)) ≤ Uloc h.le L (p (a + 2)) := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hγ hγ3]; exact inf_le_left
    exact (eq_iff_of_natVec_iff hψ hU1 hU3 (c.mem_usup_iff hψ hγ hγβ)
      (c.mem_usup_iff hψ hγ hγ3)).mpr heq
  set P := H₁ ⊓ H₃ with hP
  have hPc : Nat.card ↥P = Fintype.card F := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_inf_eq_one hr1 hr3 hne, pow_one,
      Nat.card_eq_fintype_card]
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hRU := c.critR_eq_usup_inf hp ha2 (by omega) (by omega)
  rw [show a - 2 + 8 = a + 6 by omega, show a - 2 + 4 = a + 2 by omega,
    show a - 2 + 3 = a + 1 by omega, show a - 2 + 5 = a + 3 by omega] at hRU
  have hsub : ∀ g ∈ natImage ψ X, (∀ v ∈ H₁, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) ∧
      ∀ v, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ P := by
    intro g hg
    obtain ⟨x, hxX, rfl⟩ := mem_natImage.mp hg
    refine ⟨fun v hv => hv _ (mem_natImage.mpr ⟨x, hXT hxX, rfl⟩), fun v => ?_⟩
    obtain ⟨u, rfl⟩ := natVec_surjective hψ v
    have hxu : (x : (puAmalgam h.le).Universal) * u * (x : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L (p (a + 2)) := (Subgroup.mem_normalizer_iff.mp (hψ.1 x.2) _).mp u.2
    have hc : ⁅(x : (puAmalgam h.le).Universal), (u : (puAmalgam h.le).Universal)⁆ ∈
        Usup (puAmalgam h.le) (p (a + 2)) (p (a + 1)) ⊓ Usup _ (p (a + 2)) (p (a + 3)) := by
      rw [← hRU]
      refine hXV (Subgroup.commutator_mem_commutator hxX ?_)
      have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
        rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
      exact c.zm_le_vv_of_dist hγ hd2 (uloc_le_zm h c.full hγ u.2)
    have hcU : ⁅(x : (puAmalgam h.le).Universal), (u : (puAmalgam h.le).Universal)⁆ ∈
        Uloc h.le L (p (a + 2)) := Subgroup.mul_mem _ hxu (Subgroup.inv_mem _ u.2)
    set u' : ↥(Uloc h.le L (p (a + 2))) := ⟨_, hxu⟩ with hu'
    have e1 : natVec hψ u' = ((toSL3 ψ x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ u :=
      natVec_conj hψ x u u' rfl
    have e2 : natVec hψ ⟨_, hcU⟩ = natVec hψ u' - natVec hψ u := by
      have : (⟨_, hcU⟩ : ↥(Uloc h.le L (p (a + 2)))) = u' * u⁻¹ := by
        apply Subtype.ext
        simp [hu', commutatorElement_def]
      rw [this, natVec_mul, natVec_inv, sub_eq_add_neg]
    rw [← e1, ← e2]
    exact ⟨(c.mem_usup_iff hψ hγ hγβ ⟨_, hcU⟩).mp hc.1, (c.mem_usup_iff hψ hγ hγ3 ⟨_, hcU⟩).mp hc.2⟩
  have hle := card_le_of_mulVec_sub_mem hr1 (natImage ψ X : Set (SL3 F))
    (fun g hg => (hsub g hg).1) (fun g hg => (hsub g hg).2)
  rw [hPc] at hle
  exact hle

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
