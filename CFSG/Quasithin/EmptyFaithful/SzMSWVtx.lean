module

public import CFSG.Quasithin.MS93.S45Phi3
public import CFSG.Quasithin.MS93.S45Q4PD
public import CFSG.Quasithin.MS93.S45Cen

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

section GoodPath

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
  {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
include c

theorem exists_W_of_isGoodPath_aux (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    (hQ4 : c.HQ4) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) :
    ∃ W : Subgroup (puAmalgam c.hyp.le).Universal,
      frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤ W ∧
      W ≤ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ : Set _) ∧
      stab (puAmalgam c.hyp.le) (p a) ≤ Subgroup.normalizer (W : Set _) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧
      ¬ W ≤ centerOf (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a),
          Ltil c.hyp.le L (p a)⁆ : Set _)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  obtain ⟨hV2, hVf⟩ := c.isPGroup_commutator_qv_ltil hα
  have hB5 := c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3
  have hV6 := c.top_le_vsix hZV hp hp' ha (by omega) (by omega) hpp'
  have hDD := c.commutator_vsix_le_vhat h14 hSQ hZV hQ4 hp ha h34 haN
  have hF9 := c.inf_whv_sup_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hZW := c.center_whv_le_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hZ₁W := c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hZ₄W := c.zm_le_whv_left hZV hp ha (by omega) (by omega)
  have hR : ⁅ZM (puAmalgam h.le) (p (a - 4)), ZM (puAmalgam h.le) (p (a + 4))⁆ ≠ ⊥ := by
    have := c.critR_ne_bot_of_isGoodPath hp (a := a - 2)
      ((Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))) (by omega) (by omega)
    rwa [show a - 2 - 2 = a - 4 by omega, show a - 2 + 6 = a + 4 by omega] at this
  set Qα := Qv (puAmalgam h.le) (p a) with hQα
  set Lt := Ltil h.le L (p a) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set K := stab (puAmalgam h.le) (p a) with hK
  set Z := ZM (puAmalgam h.le) (p a) with hZ
  set Vc := Vcirc h.le L (p a) with hVc
  set Vh := Vc ⊔ Z with hVh
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set W₁ := conjCl K (ZM (puAmalgam h.le) (p (a + 4))) ⊔ Vh with hW₁
  have hQs : Qα ≤ K := qv_le_stab _ _
  have hKQ : K ≤ Subgroup.normalizer (Qα : Set _) := stab_le_normalizer_qv _ _
  have hLs : Lt ≤ K := ltil_le_stab h _
  have hKL : K ≤ Subgroup.normalizer (Lt : Set _) := stab_le_normalizer_ltil h _
  have hKV : K ≤ Subgroup.normalizer (V : Set _) := S45.le_normalizer_commutator hKQ hKL
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKZ : K ≤ Subgroup.normalizer (Z : Set _) := stab_le_normalizer_zm _ _
  have hKVc : K ≤ Subgroup.normalizer (Vc : Set _) := c.stab_le_normalizer_vcirc _
  have hKVh : K ≤ Subgroup.normalizer (Vh : Set _) := le_normalizer_sup hKVc hKZ
  have hKWh : K ≤ Subgroup.normalizer (Wh : Set _) := S4A.le_normalizer_conjCl _ _
  have hKW₁ : K ≤ Subgroup.normalizer (W₁ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKVh
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hWhs : Wh ≤ K := (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans hQs
  have hW₁Wh : W₁ ≤ Wh :=
    sup_le (conjCl_le_of_le_normalizer hZ₁W hKWh) hVhWh
  have hVhW₁ : Vh ≤ W₁ := le_sup_right
  have hZW₁ : ZM (puAmalgam h.le) (p (a + 4)) ≤ W₁ := (S4A.le_conjCl _ _).trans le_sup_left
  have hVV6 : V ≤ conjCl K (whv h (p (a + 2)) (p a)) := hB5.trans hV6
  have hΦ : frattiniIn V ≤ V ⊓ Vh := by
    refine frattiniIn_le_of hV2 (le_inf ?_ ?_) fun v hv => ⟨pow_mem hv 2, ?_⟩
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer
    · exact (Subgroup.commutator_mono hVV6 hVV6).trans hDD
    · exact hDD (c.sq_mem_commutator_vsix hZV hp ha h34 (by omega) (hVV6 hv))
  have hΦVh : frattiniIn V ≤ Vh := hΦ.trans inf_le_right
  have hVhab : ⁅Vh, Vh⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hVhWh.trans hWhC)
  have hZQ4 : ∀ k ∈ K, ⁅ZM (puAmalgam h.le) (p (a + 4)),
      (ZM (puAmalgam h.le) (p (a + 4))).map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    intro k hk
    rw [← zm_smul, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (zm_le_centralizer_qv _ h20 hμ).trans
      (Subgroup.centralizer_le (hQ4 p N hp a ha (by omega) (by omega) k hk))
  have hab₁ : ⁅W₁, W₁⁆ = ⊥ := commutator_conjCl_sup_eq_bot (hZ₁W.trans hWhs) hZQ4 hVhab
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ((le_sup_left.trans hW₁Wh).trans hWhC))
  refine ⟨V ⊓ W₁, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hΦ.trans (inf_le_inf_left _ hVhW₁)
  ·
    exact inf_le_inf_left _ ((hW₁Wh.trans hWhC).trans (Subgroup.centralizer_le hΦVh))
  ·
    exact le_normalizer_inf hKV hKW₁
  ·
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hab₁) (Subgroup.mem_inf.mp hx).2)) y
      (Subgroup.mem_inf.mp hy).2).symm
  ·
    intro hcen
    have hVWh : V ⊓ Wh ≤ V ⊓ Subgroup.centralizer (frattiniIn V : Set _) :=
      inf_le_inf_left _ (hWhC.trans (Subgroup.centralizer_le hΦVh))
    have hWz : ∀ z ∈ V ⊓ W₁, Wh ≤ Subgroup.centralizer ({z} : Set _) := by
      intro z hz
      have hzC := (Subgroup.mem_inf.mp (hcen hz)).2
      rw [← hF9]
      refine sup_le (fun v hv => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hzC v (hVWh hv)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hWhC (hW₁Wh (Subgroup.mem_inf.mp hz).2)) u hu
    have hVW₁Vh : V ⊓ W₁ ≤ Vh := by
      intro z hz
      refine hZW (Subgroup.mem_inf.mpr ⟨hW₁Wh (Subgroup.mem_inf.mp hz).2, ?_⟩)
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mp (hWz z hz hw)
    have hW₁Vh : W₁ ≤ Vh := by
      intro w hw
      have hwmem : w ∈ ((V ⊓ Wh ⊔ Vh : Subgroup _) : Set _) := hF9.ge (hW₁Wh hw)
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (V ⊓ Wh) Vh
        (inf_le_left.trans ((hVQ.trans hQs).trans hKVh))] at hwmem
      obtain ⟨v, hv, u, hu, rfl⟩ := hwmem
      have hvW₁ : v ∈ W₁ := by
        have := W₁.mul_mem hw (W₁.inv_mem (hVhW₁ hu))
        rwa [mul_inv_cancel_right] at this
      exact Vh.mul_mem (hVW₁Vh ⟨(Subgroup.mem_inf.mp hv).1, hvW₁⟩) hu
    exact hR ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (hZ₄W.trans (hWhC.trans (Subgroup.centralizer_le (hZW₁.trans hW₁Vh)))))

theorem exists_W_of_isGoodPath (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    (hp : IsGoodPath _ p N) (hN : 64 ≤ N) {δ : Vtx (puAmalgam c.hyp.le)} (hδ : p 34 = δ) :
    ∃ W : Subgroup (puAmalgam c.hyp.le).Universal,
      frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ≤ W ∧
      W ≤ ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ : Set _) ∧
      stab (puAmalgam c.hyp.le) δ ≤ Subgroup.normalizer (W : Set _) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧
      ¬ W ≤ centerOf (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
        Subgroup.centralizer (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ,
          Ltil c.hyp.le L δ⁆ : Set _)) := by
  subst hδ
  exact exists_W_of_isGoodPath_aux c h14 hSQ hZV (S45Q4.hQ4 c) hp (a := 34) (by decide) le_rfl
    (by omega)

end GoodPath

end CFSG.Quasithin.SzMSW
