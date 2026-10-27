module

public import CFSG.Quasithin.MS93.S45M1
public import CFSG.Quasithin.MS93.S45Q4PD

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem exists_commutator_not_mem_vhat (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {d : ℕ} (hd : Even d)
    (h24 : 24 ≤ d) (hdN : d + 24 ≤ N) :
    ∃ z ∈ ZM (puAmalgam c.hyp.le) (p (d + 4)), ∃ y ∈ ZM (puAmalgam c.hyp.le) (p (d - 8)),
      ⁅z, y⁆ ∉ Vcirc c.hyp.le L (p d) ⊔ ZM _ (p d) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hQ4 := S45Q4.hQ4 c
  have hδ := c.isMVtx_of_isGoodPath hp (k := d) (by omega) hd
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p d) (p (d + 1)) := hp.adj d (by omega)
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hδ hδβ
  have hW := c.mid_isSum h14 hSQ hZV hQ4 hp hd (by omega) (by omega) hψs hψ hT
  set Nn := NatSec.ofIsSum hW with hNn
  set Vh := Vcirc h.le L (p d) ⊔ ZM (puAmalgam h.le) (p d) with hVh
  set W := conjCl (stab (puAmalgam h.le) (p d)) (ZM (puAmalgam h.le) (p (d + 4))) ⊔ Vh with hWd
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hcrit4 : IsCritical (puAmalgam h.le) (p (d + 4)) (p (d - 4)) := by
    have := hp.crit (d - 4) (by obtain ⟨k, hk⟩ := hd; exact ⟨k - 2, by omega⟩) (by omega)
    rwa [show d - 4 + 8 = d + 4 by omega] at this
  have hVQ : Vv (puAmalgam h.le) (p d) ≤ Qv _ (p (d - 4)) :=
    vi_le_qv _ (by rw [tdist_comm, hd' (d - 4) d (by omega) (by omega), c.b8]; omega)
  obtain ⟨z, hzZ, hzV⟩ : ∃ z ∈ ZM (puAmalgam h.le) (p (d + 4)), z ∉ Vh := by
    by_contra hcon
    push Not at hcon
    exact hcrit4.2.2 fun x hx => hVQ (c.vhat_le_vv hδ (hcon x hx))
  have hzW : z ∈ W := Subgroup.mem_sup_left (S4A.le_conjCl _ _ hzZ)
  have hz0 : Nn.coord z ≠ 0 := fun h0 => hzV ((Nn.coord_eq_zero_iff hzW).mp h0)
  have hTd : Qv (puAmalgam h.le) (p (d + 1)) ≤ stab _ (p d) := qv_le_stab_of_adj _ hδβ.symm
  have hfix : ∀ t : ↥(stab (puAmalgam h.le) (p d)), (t : (puAmalgam h.le).Universal) ∈
      Qv (puAmalgam h.le) (p (d + 1)) → dualMat (toSL3 ψ t) *ᵥ Nn.coord z = Nn.coord z := by
    intro t ht
    have h1 := c.commutator_vhat_qv_le_left hZV hp (a := d) hd (by omega) (by omega)
    have h2 := c.zm_le_vhat_right hZV hp (a := d + 2) (hd.add even_two) (by omega) (by omega)
    rw [show d + 2 + 2 = d + 4 by omega] at h2
    have h3 := c.zm_le_vhat_right hZV hp (a := d) hd (by omega) (by omega)
    have hm : ⁅z⁻¹, (t : (puAmalgam h.le).Universal)⁆ ∈
        ZM (puAmalgam h.le) (p d) ⊔ ZM _ (p (d + 2)) :=
      h1 (Subgroup.commutator_mem_commutator (inv_mem (h2 hzZ)) ht)
    have e : ⁅z⁻¹, (t : (puAmalgam h.le).Universal)⁆ =
        z⁻¹ * ((t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e] at hm
    have hmV : z⁻¹ * ((t : (puAmalgam h.le).Universal) * z *
        (t : (puAmalgam h.le).Universal)⁻¹) ∈ Vh := (sup_le le_sup_right h3) hm
    have htz : (t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹ ∈ W :=
      Nn.conj_mem t hzW
    have h0 := (Nn.coord_eq_zero_iff (W.mul_mem (W.inv_mem hzW) htz)).mpr hmV
    rw [Nn.coord_mul (W.inv_mem hzW) htz, Nn.coord_inv hzW, neg_add_eq_zero] at h0
    have hc := Nn.coord_conj t hzW
    rw [natAct_true] at hc
    rw [← hc, ← h0]
  have hcoord : ∀ i j : Fin 3, i ≠ j → j = 0 → Nn.coord z i = 0 := by
    intro i j hij hj
    have hmem : rootElt i j (1 : F) ∈ natImage ψ (Qv (puAmalgam h.le) (p (d + 1))) := by
      rw [hT]
      subst hj
      fin_cases i
      · exact absurd rfl hij
      · exact Subgroup.mem_sup_left (rootElt_mem_rootGroup _ _ _)
      · exact Subgroup.mem_sup_right (rootElt_mem_rootGroup _ _ _)
    obtain ⟨t, ht, hte⟩ := mem_natImage.mp hmem
    have h1 := hfix t ht
    rw [hte, dualMat_rootElt_mulVec hij, add_eq_left] at h1
    have h2 := congrFun h1 j
    simpa using h2
  have hz1 : Nn.coord z 1 = 0 := hcoord 1 0 (by decide) rfl
  have hz2 : Nn.coord z 2 = 0 := hcoord 2 0 (by decide) rfl
  have hz00 : Nn.coord z 0 ≠ 0 := by
    intro h0
    apply hz0
    funext k
    fin_cases k
    · exact h0
    · exact hz1
    · exact hz2
  have hcrit8 : IsCritical (puAmalgam h.le) (p d) (p (d - 8)) := by
    have := hp.crit (d - 8) (by obtain ⟨k, hk⟩ := hd; exact ⟨k - 4, by omega⟩) (by omega)
    rwa [show d - 8 + 8 = d by omega] at this
  have hZs : ZM (puAmalgam h.le) (p (d - 8)) ≤ stab _ (p d) :=
    zm_le_stab_of_isCritical _ h20 c.bpos hcrit8
  have hpe := hp.pe d hd (by omega) (by omega)
  rw [c.le_normalizer_usup_iff hψ hδ hδβ hZs (c.mem_usup_iff hψ hδ hδβ)] at hpe
  push Not at hpe
  obtain ⟨e, he, w, hw, hew⟩ := hpe
  obtain ⟨y, hy, rfl⟩ := mem_natImage.mp he
  have hfixN : ∀ v : Fin 3 → F,
      v ∈ fixN (natImage ψ (Qv (puAmalgam h.le) (p (d + 1)))) ↔ v 0 = 0 := by
    intro v
    rw [hT, fixN_sup, fixN_rootGroup (i := 1) (j := 0) (by decide),
      fixN_rootGroup (i := 2) (j := 0) (by decide), Submodule.mem_inf]
    exact ⟨fun hv => hv.1, fun hv => ⟨hv, hv⟩⟩
  rw [hfixN] at hw hew
  have hmove : dualMat (toSL3 ψ y) *ᵥ Nn.coord z ≠ Nn.coord z := by
    intro hfy
    apply hew
    have h1 := dualMat_mulVec_dotProduct (toSL3 ψ y) (Nn.coord z) w
    rw [hfy] at h1
    have hzw : Nn.coord z ⬝ᵥ w = 0 := by
      simp [dotProduct, Fin.sum_univ_three, hw, hz1, hz2]
    rw [hzw] at h1
    simp only [dotProduct, Fin.sum_univ_three, hz1, hz2, zero_mul, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hz00
  refine ⟨z, hzZ, y, hy, fun hm => hmove ?_⟩
  have hyz : (y : (puAmalgam h.le).Universal) * z⁻¹ * (y : (puAmalgam h.le).Universal)⁻¹ ∈ W :=
    Nn.conj_mem y (W.inv_mem hzW)
  have e : ⁅z, (y : (puAmalgam h.le).Universal)⁆ =
      z * ((y : (puAmalgam h.le).Universal) * z⁻¹ * (y : (puAmalgam h.le).Universal)⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e] at hm
  have h0 := (Nn.coord_eq_zero_iff (W.mul_mem hzW hyz)).mpr hm
  rw [Nn.coord_mul hzW hyz, Nn.coord_conj y (W.inv_mem hzW), natAct_true, Nn.coord_inv hzW,
    Matrix.mulVec_neg, add_neg_eq_zero] at h0
  exact h0.symm

end CFSG.Quasithin.MS93.S45R
