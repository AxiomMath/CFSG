module

public import CFSG.Quasithin.MS93.S45Phi1

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

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem commutator_vsix_le_vhat (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a)),
        conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a))⁆ ≤
      Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) := by
  have h := c.hyp
  have h20 := h.hyp20
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) (p (k + 34 + 2)) = 2 := by
    rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega
  have hd2' : (puAmalgam h.le).treeGraph.dist (p (k + 34 + 2)) (p (k + 34)) = 2 := by
    rw [tdist_comm]; exact hd2
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p (k + 34)) (p (k + 34 + 1)) :=
    hp.adj (k + 34) (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (k + 34 + 2)) (p (k + 34 + 1)) :=
    (hp.adj (k + 34 + 1) (by omega)).symm
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα hαβ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  set Vh := Vcirc h.le L (p (k + 34)) ⊔ ZM (puAmalgam h.le) (p (k + 34)) with hVh
  set Vγ := Vcirc h.le L (p (k + 34 + 2)) ⊔ ZM (puAmalgam h.le) (p (k + 34 + 2)) with hVγ
  set Wh := whv h (p (k + 34)) (p (k + 34 + 2)) with hWh
  set Wγ := whv h (p (k + 34 + 2)) (p (k + 34)) with hWγ
  set Tβ := Qv (puAmalgam h.le) (p (k + 34 + 1)) with hTβ
  have hKVh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hWγQ : Wγ ≤ Qv (puAmalgam h.le) (p (k + 34)) :=
    c.whv_le_qv_of_dist hα hd2' (by rw [hd2']; decide)
  have hWγs : Wγ ≤ stab (puAmalgam h.le) (p (k + 34)) := hWγQ.trans (qv_le_stab _ _)
  have hTs : Tβ ≤ stab (puAmalgam h.le) (p (k + 34)) := qv_le_stab_of_adj _ hαβ.symm
  have hkey : ⁅Wγ, Tβ⁆ ≤ Vh ⊔ Vγ :=
    c.commutator_whv_qv_le_vhat_left hZV hQ4 hp ha h34 (by omega)
  have hZ2V : ZM (puAmalgam h.le) (p (k + 34 + 2)) ≤ Vh :=
    c.zm_le_vhat_right hZV hp ha (by omega) (by omega)
  have hA1 : ⁅Vγ, Tβ⁆ ≤ Vh := (c.commutator_vhat_qv_le_left hZV hp ha (by omega)
    (by omega)).trans (sup_le le_sup_right hZ2V)
  have hVhT : ⁅Vh, Tβ⁆ ≤ Vh := Subgroup.le_normalizer_iff_commutator_le_left.mp (hTs.trans hKVh)
  have hVγW : Vγ ≤ Wh := c.vhat_le_whv_self
  have hVhW : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hWγQ2 : ⁅Wγ, Qv (puAmalgam h.le) (p (k + 34 + 2))⁆ ≤ ZM _ (p (k + 34 + 2)) := by
    have := c.commutator_whv_qv_le hZV hp (a := k + 34 + 2) (ha.add even_two) (by omega)
      (by omega)
    rwa [show k + 34 + 2 - 2 = k + 34 by omega] at this
  have hWγC2 : Wγ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) (p (k + 34 + 2)) : Set _) :=
    (c.whv_le_qv_of_dist hα hd2' (by simp)).trans (Subgroup.le_centralizer_iff.mp
      (zm_le_centralizer_qv _ h20 hγ))
  have hcomm2 : ∀ ρ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (p (k + 34)) ρ →
      Module.finrank F ↥(commN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 :=
    fun ρ hρ => (c.natImage_qv_props hα hρ hψ).2.2.2
  have hcommEq : ∀ ρ ρ' : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (p (k + 34)) ρ →
      (puAmalgam h.le).treeGraph.Adj (p (k + 34)) ρ' →
      (commN (natImage ψ (Qv (puAmalgam h.le) ρ)) = commN (natImage ψ (Qv _ ρ')) ↔
        ZH (puAmalgam h.le) ρ = ZH _ ρ') := by
    intro ρ ρ' hρ hρ'
    rw [← (c.natImage_qv_props hα hρ hψ).2.2.1, ← (c.natImage_qv_props hα hρ' hψ).2.2.1,
      ← c.usup_eq_iff_zh_eq hψ hα hρ hρ']
    exact (eq_iff_of_natVec_iff hψ
      (by rw [c.usup_eq_uloc_inf_centralizer hψ hα hρ]; exact inf_le_left)
      (by rw [c.usup_eq_uloc_inf_centralizer hψ hα hρ']; exact inf_le_left)
      (c.mem_usup_iff hψ hα hρ) (c.mem_usup_iff hψ hα hρ')).symm
  refine commutator_conjCl_conjCl_le hKVh hWγs fun g hg => ?_
  have hgα : g • p (k + 34) = p (k + 34) := (mem_stab _).mp hg
  set γ := g • p (k + 34 + 1) with hγdef
  have hγadj : (puAmalgam h.le).treeGraph.Adj (p (k + 34)) γ := by
    rw [← hgα]; exact (adj_smul _ _ _ _).mpr hαβ
  have hTγ : Tβ.map (MulAut.conj g).toMonoidHom = Qv (puAmalgam h.le) γ := (qv_smul _ g _).symm
  have hWγg : Wγ.map (MulAut.conj g).toMonoidHom ≤ Tβ := by
    have hd3 : (puAmalgam h.le).treeGraph.dist (p (k + 34 + 2)) (g⁻¹ • p (k + 34 + 1)) ≤ 3 := by
      have h1 := dist_triangle (puAmalgam h.le) (p (k + 34 + 2)) (p (k + 34))
        (g⁻¹ • p (k + 34 + 1))
      have h2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) (g⁻¹ • p (k + 34 + 1)) = 1 := by
        have hgα' : g⁻¹ • p (k + 34) = p (k + 34) := by
          rw [← hgα, inv_smul_smul, hgα]
        rw [← hgα', dist_smul]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hαβ
      omega
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (c.whv_le_qv_of_dist hα hd2' hd3)
    rwa [← qv_smul, smul_inv_smul] at this
  have hdγ : (puAmalgam h.le).treeGraph.dist (p (k + 34 + 2)) γ ≤ 3 := by
    have h1 := dist_triangle (puAmalgam h.le) (p (k + 34 + 2)) (p (k + 34)) γ
    have h2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) γ = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hγadj
    omega
  have hWγTγ : Wγ ≤ Qv (puAmalgam h.le) γ := c.whv_le_qv_of_dist hα hd2' hdγ
  by_cases hZ : ZH (puAmalgam h.le) γ = ZH _ (p (k + 34 + 1))
  ·
    have hcEq : commN (natImage ψ (Qv (puAmalgam h.le) γ)) = commN (natImage ψ Tβ) :=
      (hcommEq γ _ hγadj hαβ).mpr hZ
    set Nn := NatSec.ofIsSum hd with hNn
    have himg := c.img_zm_eq' hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ
      hd hZ2V (c.usup_le_zm hγ hγβ hαβ) (c.not_zm_le_zm_right hp ha (by omega) (by omega))
    set s := toSL3 ψ ⟨g, hg⟩ with hs
    have hsub : ZM (puAmalgam h.le) (p (k + 34 + 2)) ≤
        ZM (puAmalgam h.le) (p (k + 34)) ⊔
          (ZM (puAmalgam h.le) (p (k + 34 + 2))).map (MulAut.conj g).toMonoidHom := by
      intro z hz
      have hzV := hZ2V hz
      set y := Nn.coord z with hy
      have hyfix : ∀ e ∈ natImage ψ Tβ, dualMat e *ᵥ y = y :=
        (himg y).mpr (Nn.mem_img.mpr ⟨z, hz, hzV, rfl⟩)
      have hyfix' : ∀ e ∈ natImage ψ (Qv (puAmalgam h.le) γ), dualMat e *ᵥ y = y := by
        rw [dualMat_fixed_iff, hcEq, ← dualMat_fixed_iff]
        exact hyfix
      set y' := dualMat s⁻¹ *ᵥ y with hy'
      have hy'fix : ∀ e ∈ natImage ψ Tβ, dualMat e *ᵥ y' = y' := by
        intro e he
        obtain ⟨t, htT, rfl⟩ := mem_natImage.mp he
        have hgt : ((⟨g, hg⟩ * t * ⟨g, hg⟩⁻¹ : ↥(stab (puAmalgam h.le) (p (k + 34)))) :
            (puAmalgam h.le).Universal) ∈
            Qv (puAmalgam h.le) γ := by
          rw [← hTγ]
          exact ⟨t, htT, by simp [MulAut.conj_apply]⟩
        have h1 := hyfix' _ (mem_natImage.mpr ⟨_, hgt, rfl⟩)
        rw [map_mul, map_mul, map_inv, ← hs] at h1
        have e : toSL3 ψ t * s⁻¹ = s⁻¹ * (s * toSL3 ψ t * s⁻¹) := by group
        calc dualMat (toSL3 ψ t) *ᵥ y' = dualMat (toSL3 ψ t * s⁻¹) *ᵥ y := by
              rw [hy', Matrix.mulVec_mulVec, dualMat_mul]
          _ = dualMat s⁻¹ *ᵥ (dualMat (s * toSL3 ψ t * s⁻¹) *ᵥ y) := by
              rw [e, dualMat_mul, Matrix.mulVec_mulVec]
          _ = y' := by rw [h1, hy']
      obtain ⟨z', hz', hz'V, hz'y⟩ := Nn.mem_img.mp ((himg y').mp hy'fix)
      have hgz' : g * z' * g⁻¹ ∈ Vh :=
        (Subgroup.mem_normalizer_iff.mp (hKVh hg) _).mp hz'V
      have hcoord : Nn.coord (g * z' * g⁻¹) = Nn.coord z := by
        have hc := Nn.coord_conj ⟨g, hg⟩ hz'V
        change Nn.coord (g * z' * g⁻¹) = natAct true s *ᵥ Nn.coord z' at hc
        rw [hc, natAct_true, hz'y, hy', Matrix.mulVec_mulVec, ← dualMat_mul, mul_inv_cancel,
          dualMat_one, Matrix.one_mulVec]
      have hrest := Nn.inv_mul_mem_of_coord_eq hgz' hzV hcoord
      have e : z = (g * z' * g⁻¹) * ((g * z' * g⁻¹)⁻¹ * z) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨z', hz', rfl⟩)
        (Subgroup.mem_sup_left hrest)
    have hWgQ2 : Wγ.map (MulAut.conj g).toMonoidHom ≤ Qv (puAmalgam h.le) (p (k + 34 + 2)) := by
      rw [← c.cent (p (k + 34 + 2)) (p (k + 34 + 1)) hγ hγβ]
      refine le_inf hWγg ?_
      have hA : Wγ.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.centralizer (ZM (puAmalgam h.le) (p (k + 34)) : Set _) :=
        (Subgroup.map_mono hWγQ).trans ((map_conj_eq_of_mem_normalizer
          (stab_le_normalizer_qv _ _ hg)).le.trans (Subgroup.le_centralizer_iff.mp
          (zm_le_centralizer_qv _ h20 hα)))
      have hB : Wγ.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer
          (((ZM (puAmalgam h.le) (p (k + 34 + 2))).map (MulAut.conj g).toMonoidHom :
            Subgroup _) : Set _) := by
        rintro _ ⟨w₀, hw₀, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp (hWγC2 hw₀) z hz
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * z * g⁻¹ * (g * w₀ * g⁻¹) = g * (z * w₀) * g⁻¹ := by group
          _ = g * (w₀ * z) * g⁻¹ := by rw [this]
          _ = g * w₀ * g⁻¹ * (g * z * g⁻¹) := by group
      exact (Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp hA)
        (Subgroup.le_centralizer_iff.mp hB))).trans (Subgroup.centralizer_le hsub)
    exact (Subgroup.commutator_mono le_rfl hWgQ2).trans (hWγQ2.trans hZ2V)
  ·
    have hne : commN (natImage ψ Tβ) ≠ commN (natImage ψ (Qv (puAmalgam h.le) γ)) :=
      fun heq => hZ ((hcommEq _ γ hαβ hγadj).mp heq).symm
    have hP₁ : ⁅Wγ, Wγ.map (MulAut.conj g).toMonoidHom⁆ ≤ Vh ⊔ Vγ :=
      (Subgroup.commutator_mono le_rfl hWγg).trans hkey
    have hP₂ : ⁅Wγ, Wγ.map (MulAut.conj g).toMonoidHom⁆ ≤
        Vh ⊔ Vγ.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_comm]
      refine (Subgroup.commutator_mono le_rfl (hWγTγ.trans hTγ.ge)).trans ?_
      rw [← Subgroup.map_commutator]
      refine (Subgroup.map_mono hkey).trans ?_
      rw [Subgroup.map_sup Vh Vγ, map_conj_eq_of_mem_normalizer (hKVh hg)]
    have hVhs : Vh ≤ stab (puAmalgam h.le) (p (k + 34)) :=
      (c.vhat_le_vv hα).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _))
    have hWhs : Wh ≤ stab (puAmalgam h.le) (p (k + 34)) :=
      (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans (qv_le_stab _ _)
    have hC₁ : ⁅Vh ⊔ Vγ, Tβ⁆ ≤ Vh :=
      commutator_sup_left_le (hVhs.trans hKVh) ((hVγW.trans hWhs).trans hKVh) hVhT hA1
    have hC₂ : ⁅Vh ⊔ Vγ.map (MulAut.conj g).toMonoidHom, Qv (puAmalgam h.le) γ⁆ ≤ Vh := by
      have e1 : Vh ⊔ Vγ.map (MulAut.conj g).toMonoidHom =
          (Vh ⊔ Vγ).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_sup Vh Vγ, map_conj_eq_of_mem_normalizer (hKVh hg)]
      rw [e1, ← hTγ, ← Subgroup.map_commutator]
      exact (Subgroup.map_mono hC₁).trans (map_conj_eq_of_mem_normalizer (hKVh hg)).le
    intro x hx
    have hxW : x ∈ Wh := sup_le hVhW hVγW (hP₁ hx)
    rw [← hsup2] at hxW
    exact mem_of_commutator_mem_two h₁m h₂m hinf2 ((le_sup_left.trans hsup2.le).trans hWhs)
      (hcomm2 _ hαβ) (hcomm2 _ hγadj) hne hxW
      (fun t ht => hC₁ (Subgroup.commutator_mem_commutator (hP₁ hx) ht))
      (fun t ht => hC₂ (Subgroup.commutator_mem_commutator (hP₂ hx) ht))

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
