module

public import CFSG.Quasithin.MS93.S45IV
import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

theorem dualMat_mulVec_sub_of_commN_le {F : Type} [Field F] {A : Subgroup (SL3 F)}
    (hA : commN A ≤ fixN A) {a b : SL3 F} (ha : a ∈ A) (hb : b ∈ A) (y : Fin 3 → F) :
    dualMat a *ᵥ (dualMat b *ᵥ y - y) = dualMat b *ᵥ y - y := by
  set Ma : Matrix (Fin 3) (Fin 3) F := ((a⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) - 1 with hMa
  set Mb : Matrix (Fin 3) (Fin 3) F := ((b⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) - 1 with hMb
  have hz : Ma * Mb = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hMa, hMb, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    have := hA (sub_mem_commN (inv_mem hb) (Pi.single i 1)) _ (inv_mem ha)
    rw [this, sub_self]
  have hzT : (dualMat a - 1) * (dualMat b - 1) = 0 := by
    have e1 : dualMat a - 1 = Maᵀ := by rw [hMa, Matrix.transpose_sub, Matrix.transpose_one]; rfl
    have e2 : dualMat b - 1 = Mbᵀ := by rw [hMb, Matrix.transpose_sub, Matrix.transpose_one]; rfl
    rw [e1, e2, ← Matrix.transpose_mul]
    have hz' : Mb * Ma = 0 := by
      apply Matrix.ext_of_mulVec_single
      intro i
      rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hMa, hMb, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      have := hA (sub_mem_commN (inv_mem ha) (Pi.single i 1)) _ (inv_mem hb)
      rw [this, sub_self]
    rw [hz', Matrix.transpose_zero]
  have h1 : ((dualMat a - 1) * (dualMat b - 1)) *ᵥ y = 0 := by rw [hzT, Matrix.zero_mulVec]
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_sub] at h1
  rw [Matrix.mulVec_sub]
  linear_combination h1

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem img_zm_eq' (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x) (hxN : x + 14 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p (x + 6))) →* ↥(StatedSL 3 F)}
    (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) (Uloc c.hyp.le L (p (x + 6))) ⊥ ψ
      false 1)
    {V' Z' : Subgroup (puAmalgam c.hyp.le).Universal}
    (hd : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) V' Z' ψ true 1)
    (hZμV : ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ V')
    (hHB : Usup (puAmalgam c.hyp.le) (p (x + 8)) (p (x + 7)) ≤ Z')
    (hZne : ¬ ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Z') :
    ∀ y : Fin 3 → F, (∀ a ∈ natImage ψ (Qv (puAmalgam c.hyp.le) (p (x + 7))), dualMat a *ᵥ y = y) ↔
      y ∈ (NatSec.ofIsSum hd).img (ZM (puAmalgam c.hyp.le) (p (x + 8))) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hMδ := hM (x + 6) (by omega) (hx.add (by decide))
  have hMμ := hM (x + 8) (by omega) (hx.add (by decide))
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  set Nn := NatSec.ofIsSum hd with hNn
  set A := natImage ψ (Qv (puAmalgam h.le) (p (x + 7))) with hAdef
  obtain ⟨hA2, hAc, hfc, h2⟩ := c.natImage_qv_props hMδ hδβ hψ
  set S := Nn.img (ZM (puAmalgam h.le) (p (x + 8))) with hSdef
  have hSfix : ∀ y ∈ S, ∀ a ∈ A, dualMat a *ᵥ y = y := by
    intro y hy a ha
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp ha
    have h1 := Nn.coord_conj t hzV
    rw [natAct_true] at h1
    rw [← h1]
    have hw : z⁻¹ * ((t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹) ∈
        Z' := by
      have e : z⁻¹ * ((t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹) =
          ⁅z⁻¹, (t : (puAmalgam h.le).Universal)⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      refine hHB ?_
      rw [Usup, zv_of_isMVtx _ hMμ]
      exact Subgroup.commutator_mem_commutator (inv_mem hzμ) ht
    have h2 := (Nn.coord_eq_zero_iff (Subgroup.mul_mem _ (inv_mem hzV) (Nn.conj_mem t hzV))).mpr hw
    rw [Nn.coord_mul (inv_mem hzV) (Nn.conj_mem t hzV), Nn.coord_inv hzV, neg_add_eq_zero] at h2
    exact h2.symm
  obtain ⟨z₀, hz₀μ, hz₀B⟩ := Set.not_subset.mp hZne
  have hne : ∃ y ∈ S, y ≠ 0 := ⟨Nn.coord z₀, Nn.mem_img.mpr ⟨z₀, hz₀μ, hZμV hz₀μ, rfl⟩,
    fun h0 => hz₀B ((Nn.coord_eq_zero_iff (hZμV hz₀μ)).mp h0)⟩
  have hinv : ∀ g ∈ Subgroup.normalizer (A : Set (SL3 F)), ∀ y ∈ S, dualMat g *ᵥ y ∈ S := by
    intro g' hg' y hy
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    obtain ⟨g, rfl⟩ := toSL3_surjective hψs g'
    have hgT := c.mem_normalizer_qv_of hMδ hδβ hψ hg'
    have hgZ := c.normalizer_zm_right hp hx h4 (by omega) ⟨g.2, hgT⟩
    refine Nn.mem_img.mpr ⟨g * z * (g : (puAmalgam h.le).Universal)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgZ z).mp hzμ, Nn.conj_mem g hzV, ?_⟩
    rw [Nn.coord_conj g hzV, natAct_true]
  have hall := (dual_fix_of_normalizer hA2 hAc hfc h2).1 S hSfix hne hinv
  intro y
  exact ⟨fun hy => hall y hy, fun hy => hSfix y hy⟩


theorem zm_le_vhat_left (hZV : c.HZV) (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x)
    (h4 : 4 ≤ x) (hxN : x + 14 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (x + 4)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
  have h1 := hZV p N hp x hx h4 hxN
  obtain ⟨g, hg, hgx⟩ := c.straight_of_isGoodPath hp (y := x + 4) (hx.add (by decide)) (by omega)
  rw [show x + 4 + 2 = x + 6 by omega] at hg
  rw [show x + 4 + 4 = x + 8 by omega] at hgx
  have hn : stab (puAmalgam c.hyp.le) (p (x + 6)) ≤ Subgroup.normalizer
      ((Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM (puAmalgam c.hyp.le) (p (x + 6)) : Subgroup _) :
        Set (puAmalgam c.hyp.le).Universal) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  rw [← hgx, zm_smul]
  rintro _ ⟨z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hn hg) z).mp (h1 hz)

theorem commutator_vhat_qv_le (hZV : c.HZV) (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x)
    (h4 : 4 ≤ x) (hxN : x + 14 ≤ N) :
    ⁅Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)), Qv (puAmalgam c.hyp.le) (p (x + 7))⁆ ≤
      ZM _ (p (x + 8)) ⊔ ZM _ (p (x + 6)) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hMδ := hM (x + 6) (by omega) (hx.add (by decide))
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hMδ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hMδ hψs hψ
  have hdt := c.dual_eq_true hp hx h4 hxN hψs hψ (c.isSum_bloc hMδ hd)
  subst hdt
  set Nn := NatSec.ofIsSum hd with hNn
  have hZμV := hZV p N hp x hx h4 hxN
  have hHZ : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ≤ ZM _ (p (x + 6)) := by
    rw [← c.hloc_eq_usup' hp hx h4 (by omega)]
    exact (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans
      ((c.commutator_vv_qv_le_zloc hMδ).trans (zloc_le_zm h c.full hMδ))
  have hZne : ¬ ZM (puAmalgam h.le) (p (x + 8)) ≤ ZM _ (p (x + 6)) := by
    intro hle
    have hcrit : IsCritical (puAmalgam h.le) (p (x + 6)) (p (x + 14)) := by
      have := c.isCritical_of_isGoodPath hp (y := x + 6) (hx.add (by decide)) (by omega)
      rwa [show x + 6 + 8 = x + 14 by omega] at this
    have hgeo : geo (puAmalgam h.le) (p (x + 6)) (p (x + 14)) 2 = p (x + 8) := by
      rw [hp.eq_geo (i := x + 6) (j := x + 14) (k := x + 8) (by omega) (by omega) (by omega),
        show x + 8 - (x + 6) = 2 by omega]
    have hB := c.not_zm_le_bloc hcrit
    rw [hgeo] at hB
    exact hB (hle.trans (zm_le_bloc h (by rw [c.b8]; norm_num) hMδ))
  have himg := c.img_zm_eq' hp hx h4 hxN hψs hψ hd hZμV hHZ hZne
  obtain ⟨-, -, hfc, -⟩ := c.natImage_qv_props hMδ hδβ hψ
  have hTs : Qv (puAmalgam h.le) (p (x + 7)) ≤ stab _ (p (x + 6)) := qv_le_stab_of_adj _ hδβ.symm
  rw [Subgroup.commutator_le]
  intro v hv t ht
  set t' : ↥(stab (puAmalgam h.le) (p (x + 6))) := ⟨t, hTs ht⟩ with ht'
  have hw1 : t * v⁻¹ * t⁻¹ ∈ Vcirc h.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) :=
    Nn.conj_mem t' (inv_mem hv)
  have hwV : ⁅v, t⁆ ∈ Vcirc h.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
    rw [commutatorElement_def, show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group]
    exact mul_mem hv hw1
  have hcoord : Nn.coord ⁅v, t⁆ = Nn.coord v -
      dualMat (toSL3 ψ t') *ᵥ Nn.coord v := by
    rw [commutatorElement_def, show v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) by group,
      Nn.coord_mul hv hw1, show t * v⁻¹ * t⁻¹ = (t' : (puAmalgam h.le).Universal) * v⁻¹ *
        (t' : (puAmalgam h.le).Universal)⁻¹ from rfl, Nn.coord_conj t' (inv_mem hv), natAct_true,
      Nn.coord_inv hv, Matrix.mulVec_neg, sub_eq_add_neg]
  have hfix : ∀ a ∈ natImage ψ (Qv (puAmalgam h.le) (p (x + 7))),
      dualMat a *ᵥ Nn.coord ⁅v, t⁆ = Nn.coord ⁅v, t⁆ := by
    intro a ha
    have hq := dualMat_mulVec_sub_of_commN_le (hfc ▸ le_rfl) ha
      (mem_natImage.mpr ⟨t', ht, rfl⟩) (Nn.coord v)
    rw [hcoord, ← neg_sub, Matrix.mulVec_neg, hq]
  obtain ⟨z, hzμ, hzV, hze⟩ := Nn.mem_img.mp ((himg _).mp hfix)
  have hw : z⁻¹ * ⁅v, t⁆ ∈ ZM (puAmalgam h.le) (p (x + 6)) := by
    refine (Nn.coord_eq_zero_iff (mul_mem (inv_mem hzV) hwV)).mp ?_
    rw [Nn.coord_mul (inv_mem hzV) hwV, Nn.coord_inv hzV, hze, neg_add_cancel]
  have e : ⁅v, t⁆ = z * (z⁻¹ * ⁅v, t⁆) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hzμ) (Subgroup.mem_sup_right hw)

theorem commutator_vhat_qv_le_zm (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h10 : 10 ≤ a) (haN : a + 14 ≤ N) :
    ⁅Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a), Qv (puAmalgam c.hyp.le) (p (a + 2))⁆ ≤
      ZM _ (p (a + 2)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := (Nat.even_add.mp ha).mpr (by decide)
  have hM6 := hM (x + 6) (by omega) ha
  have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
  have hM10 := hM (x + 10) (by omega) (hx.add (by decide))
  have ha87 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  have ha67 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  rw [show x + 6 + 2 = x + 8 by omega]
  have hiv := c.qv_le_whv_sup_qv hZV hp (y := x + 10) (hx.add (by decide)) (by omega) (by omega)
  rw [show x + 10 - 3 = x + 7 by omega, show x + 10 - 2 = x + 8 by omega,
    show x + 10 - 4 = x + 6 by omega] at hiv
  have hQ8 : Qv (puAmalgam h.le) (p (x + 8)) ≤ Qv _ (p (x + 7)) := qv_le_qv _ h20 hM8 ha87
  set W := whv h (p (x + 10)) (p (x + 8)) with hWdef
  have hWT : W ≤ Qv (puAmalgam h.le) (p (x + 7)) := by
    have := c.whv_le_qv hp (y := x + 10) (hx.add (by decide)) (by omega) (by omega)
    rwa [show x + 10 - 2 = x + 8 by omega, show x + 10 - 3 = x + 7 by omega] at this
  have hT8 : Qv (puAmalgam h.le) (p (x + 7)) ≤ stab _ (p (x + 8)) := qv_le_stab_of_adj _ ha87.symm
  have hZ8n := stab_le_normalizer_zm (puAmalgam h.le) (p (x + 8))
  have hHa : ⁅Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6)), Qv _ (p (x + 6))⁆ ≤
      ZM _ (p (x + 8)) := by
    have hV6 : Vv (puAmalgam h.le) (p (x + 6)) ≤ stab _ (p (x + 8)) :=
      (c.vv_le_qv' hM6).trans ((qv_le_qv _ h20 hM6 ha67).trans hT8)
    refine commutator_sup_left_le ((c.vcirc_le_vv _).trans (hV6.trans hZ8n))
      ((zm_le_vv h hM6).trans (hV6.trans hZ8n)) ?_ ?_
    · rw [← Hloc, c.hloc_eq_usup' hp (x := x) hx (by omega) (by omega)]
      rw [c.usup_eq_uloc_inf_centralizer (exists_natural_Uloc h c.via hM8).choose_spec.2 hM8 ha87]
      exact inf_le_left.trans (uloc_le_zm h c.full hM8)
    · rw [commutator_zm_qv _ h20 hM6]; exact bot_le
  have hWa :
      ⁅W, Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6))⁆ ≤ ZM _ (p (x + 8)) := by
    have h1 : ⁅W, Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6))⁆ ≤
        ZM _ (p (x + 8)) ⊔ ZM _ (p (x + 6)) := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl hWT).trans
        (c.commutator_vhat_qv_le hZV hp hx (by omega) (by omega))
    have h2 : ⁅W, Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6))⁆ ≤
        Vcirc h.le L (p (x + 10)) ⊔ ZM _ (p (x + 10)) := by
      have hVQ : Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6)) ≤ Qv _ (p (x + 10)) :=
        sup_le ((c.vcirc_le_vv _).trans (vi_le_qv _ (by
          rw [hd' (x + 6) (x + 10) (by omega) (by omega), c.b8]; omega)))
          ((zm_le_vv h hM6).trans (vi_le_qv _ (by
          rw [hd' (x + 6) (x + 10) (by omega) (by omega), c.b8]; omega)))
      refine (Subgroup.commutator_mono le_rfl hVQ).trans ?_
      have hn10 : stab (puAmalgam h.le) (p (x + 10)) ≤ Subgroup.normalizer
          ((Vcirc h.le L (p (x + 10)) ⊔ ZM (puAmalgam h.le) (p (x + 10)) : Subgroup _) :
            Set (puAmalgam h.le).Universal) :=
        le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
      have hV8s :
          Vcirc h.le L (p (x + 8)) ⊔ ZM (puAmalgam h.le) (p (x + 8)) ≤ stab _ (p (x + 10)) :=
        sup_le ((c.vcirc_le_vv _).trans (vi_le_qv _ (by
          rw [hd' (x + 8) (x + 10) (by omega) (by omega), c.b8]; omega) |>.trans
            (qv_le_stab _ _)))
          ((zm_le_vv h hM8).trans (vi_le_qv _ (by
          rw [hd' (x + 8) (x + 10) (by omega) (by omega), c.b8]; omega) |>.trans
            (qv_le_stab _ _)))
      refine S4A.commutator_conjCl_le hn10 (stab_le_normalizer_qv _ _) (hV8s.trans hn10) ?_
      have h3 := c.commutator_vhat_qv_le hZV hp (x := x + 2) (hx.add (by decide)) (by omega)
        (by omega)
      rw [show x + 2 + 6 = x + 8 by omega, show x + 2 + 7 = x + 9 by omega,
        show x + 2 + 8 = x + 10 by omega] at h3
      have ha109 : (puAmalgam h.le).treeGraph.Adj (p (x + 10)) (p (x + 9)) :=
        (hp.adj (x + 9) (by omega)).symm
      refine (Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hM10 ha109)).trans
        (h3.trans (sup_le le_sup_right ?_))
      have := c.zm_le_vhat_left hZV hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega)
      rwa [show x + 4 + 4 = x + 8 by omega, show x + 4 + 6 = x + 10 by omega] at this
    have hZ8V :
        ZM (puAmalgam h.le) (p (x + 8)) ≤ Vcirc h.le L (p (x + 10)) ⊔ ZM _ (p (x + 10)) := by
      have := c.zm_le_vhat_left hZV hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega)
      rwa [show x + 4 + 4 = x + 8 by omega, show x + 4 + 6 = x + 10 by omega] at this
    have hd86 : (puAmalgam h.le).treeGraph.dist (p (x + 8)) (p (x + 6)) <
        critDist (puAmalgam h.le) := by
      rw [tdist_comm, hd' (x + 6) (x + 8) (by omega) (by omega), c.b8]; omega
    have hZ8n6 : ZM (puAmalgam h.le) (p (x + 8)) ≤
        Subgroup.normalizer (ZM (puAmalgam h.le) (p (x + 6)) : Set _) :=
      (zm_le_qv_of_dist_lt _ hM8 hd86).trans ((qv_le_stab _ _).trans (stab_le_normalizer_zm _ _))
    have hcap : (ZM (puAmalgam h.le) (p (x + 8)) ⊔ ZM _ (p (x + 6))) ⊓
        (Vcirc h.le L (p (x + 10)) ⊔ ZM _ (p (x + 10))) ≤ ZM _ (p (x + 8)) := by
      rw [sup_inf_eq_of_le hZ8V hZ8n6]
      refine sup_le le_rfl ?_
      intro z hz
      have hc := c.isCritical_of_isGoodPath hp (y := x + 6) ha (by omega)
      rw [show x + 6 + 8 = x + 14 by omega] at hc
      obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM6
      have hd613 : (puAmalgam h.le).treeGraph.dist (p (x + 6)) (p (x + 13)) <
          critDist (puAmalgam h.le) := by
        rw [hd' (x + 6) (x + 13) (by omega) (by omega), c.b8]; omega
      have hzT : z ∈ Qv (puAmalgam h.le) (p (x + 13)) := zm_le_qv_of_dist_lt _ hM6 hd613 hz.1
      have hzC : z ∈ Subgroup.centralizer (ZM (puAmalgam h.le) (p (x + 14)) : Set _) := by
        have := c.vi_le_centralizer_zm (β := p (x + 10)) (i := 2) (hM (x + 14) (by omega)
          (hx.add (by decide))) (by rw [hd' (x + 10) (x + 14) (by omega) (by omega)]; omega)
        exact this (sup_le (c.vcirc_le_vv _) (zm_le_vv h hM10) hz.2)
      have hzQ : z ∈ Qv (puAmalgam h.le) (p (x + 14)) := by
        rw [← c.cent (p (x + 14)) (p (x + 13)) (hM (x + 14) (by omega) (hx.add (by decide)))
          (hp.adj (x + 13) (by omega)).symm]
        exact ⟨hzT, hzC⟩
      have h1 := c.zm_inf_qv hc hψ
      have hg1 : geo (puAmalgam h.le) (p (x + 6)) (p (x + 14)) 1 = p (x + 7) := by
        rw [hp.eq_geo (i := x + 6) (j := x + 14) (k := x + 7) (by omega) (by omega) (by omega),
          show x + 7 - (x + 6) = 1 by omega]
      rw [hg1] at h1
      have : z ∈ ZH (puAmalgam h.le) (p (x + 7)) := by rw [← h1]; exact ⟨hz.1, hzQ⟩
      exact zh_le_zm _ ha87 this
    exact le_inf h1 h2 |>.trans hcap
  refine (Subgroup.commutator_mono le_rfl (hQ8.trans hiv)).trans ?_
  rw [Subgroup.commutator_comm]
  refine commutator_sup_left_le (hWT.trans (hT8.trans hZ8n))
    ((qv_le_qv _ h20 hM6 ha67).trans (hT8.trans hZ8n)) hWa ?_
  rw [Subgroup.commutator_comm]
  exact hHa

theorem commutator_whv_qv_le (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h12 : 12 ≤ a) (haN : a + 12 ≤ N) :
    ⁅whv c.hyp (p a) (p (a - 2)), Qv (puAmalgam c.hyp.le) (p a)⁆ ≤ ZM _ (p a) := by
  have h := c.hyp
  have ha2 : Even (a - 2) := by obtain ⟨k, hk⟩ := ha; exact ⟨k - 1, by omega⟩
  have hii := c.commutator_vhat_qv_le_zm hZV hp ha2 (by omega) (by omega)
  rw [show a - 2 + 2 = a by omega] at hii
  have hM : IsMVtx (puAmalgam h.le) (p (a - 2)) := by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := a - 2) (by omega) hp.mvtx ha2
    rwa [zero_add] at this
  have hVs : Vcirc h.le L (p (a - 2)) ⊔ ZM (puAmalgam h.le) (p (a - 2)) ≤ stab _ (p a) :=
    sup_le ((c.vcirc_le_vv _).trans (vi_le_qv _ (by
      rw [hp.dist_eq' (show a - 2 ≤ a by omega) (by omega), c.b8]; omega) |>.trans
        (qv_le_stab _ _)))
      ((zm_le_vv h hM).trans (vi_le_qv _ (by
      rw [hp.dist_eq' (show a - 2 ≤ a by omega) (by omega), c.b8]; omega) |>.trans
        (qv_le_stab _ _)))
  exact S4A.commutator_conjCl_le (stab_le_normalizer_zm _ _) (stab_le_normalizer_qv _ _)
    (hVs.trans (stab_le_normalizer_zm _ _)) hii

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
