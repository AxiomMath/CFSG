module

public import CFSG.Quasithin.MS93.S45Crit
import CFSG.Quasithin.MS93.S4A42Coc
public import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section Path

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem isMVtx_add (hp : IsNBPath _ p N) {x k : ℕ} (hk : x + k ≤ N) (hx : IsMVtx _ (p x))
    (hev : Even k) : IsMVtx (puAmalgam c.hyp.le) (p (x + k)) := by
  have h := even_dist_iff (puAmalgam c.hyp.le) (p x) (p (x + k))
  rw [hp.dist_eq k hk] at h
  exact (h.mp hev).mp hx

theorem critR_le_usup_inf (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 8 ≤ N)
    (hc : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hs : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 2)), g • p (x + 4) = p x) :
    critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≤
      Usup _ (p (x + 4)) (p (x + 3)) ⊓ Usup _ (p (x + 4)) (p (x + 5)) := by
  have h := c.hyp
  have hx := hc.1
  have hM2 := c.isMVtx_add hp (k := 2) (by omega) hx even_two
  have hM4 := c.isMVtx_add hp (k := 4) (by omega) hx (by decide)
  have hM6 := c.isMVtx_add hp (k := 6) (by omega) hx (by decide)
  have g2 : geo (puAmalgam h.le) (p x) (p (x + 8)) 2 = p (x + 2) := by
    rw [hp.eq_geo (i := x) (j := x + 8) (k := x + 2) (by omega) (by omega) hxN,
      show x + 2 - x = 2 by omega]
  have g6 : geo (puAmalgam h.le) (p (x + 8)) (p x) 2 = p (x + 6) := by
    rw [hp.eq_geo_rev (i := x) (j := x + 8) (k := x + 6) (by omega) (by omega) hxN,
      show x + 8 - (x + 6) = 2 by omega]
  have hZ2 := c.critR_le_zloc hc
  rw [g2] at hZ2
  have hZ6 := c.critR_le_zloc' hc
  rw [g6] at hZ6
  have hU0 := c.critR_le_uloc hc
  obtain ⟨g, hg, hgx⟩ := hs
  have hU4 : critR (puAmalgam h.le) (p x) (p (x + 8)) ≤ Uloc h.le L (p (x + 4)) := by
    intro r hr
    have hrc : r ∈ Subgroup.centralizer (stab (puAmalgam h.le) (p (x + 2)) : Set _) :=
      zloc_le_centralizer_stab h c.full hM2 (hZ2 hr)
    have hgr : g⁻¹ * r * g⁻¹⁻¹ = r := by
      have := (Subgroup.mem_centralizer_iff.mp hrc) g⁻¹ (inv_mem hg)
      rw [inv_inv, this, inv_mul_cancel_right]
    have hpx : g⁻¹ • p x = p (x + 4) := by rw [← hgx, inv_smul_smul]
    rw [← hpx, uloc_smul h]
    refine ⟨r, hU0 hr, ?_⟩
    rw [inv_inv] at hgr
    simpa [MulAut.conj_apply] using hgr
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  have ha3 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 3)) :=
    (hp.adj (x + 3) (by omega)).symm
  have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
  have ha23 : (puAmalgam h.le).treeGraph.Adj (p (x + 2)) (p (x + 3)) := hp.adj (x + 2) (by omega)
  have ha65 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 5)) :=
    (hp.adj (x + 5) (by omega)).symm
  refine le_inf ?_ ?_
  · rw [← c.uloc_inf_zh hψ hM4 ha3]
    exact le_inf hU4 (hZ2.trans (zloc_le_zh h c.full hM2 ha23))
  · rw [← c.uloc_inf_zh hψ hM4 ha5]
    exact le_inf hU4 (hZ6.trans (zloc_le_zh h c.full hM6 ha65))

theorem card_critR (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 8 ≤ N)
    (hc : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hs : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 2)), g • p (x + 4) = p x)
    (hgpd : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5))) :
    Nat.card ↥(critR (puAmalgam c.hyp.le) (p x) (p (x + 8))) = Fintype.card F := by
  have h := c.hyp
  have hx := hc.1
  have hM4 := c.isMVtx_add hp (k := 4) (by omega) hx (by decide)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  have ha3 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 3)) :=
    (hp.adj (x + 3) (by omega)).symm
  have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
  have hne : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ≠ Usup _ (p (x + 4)) (p (x + 5)) :=
    fun heq => hgpd ((c.usup_eq_iff_zh_eq hψ hM4 ha3 ha5).mp heq)
  have hcard := c.card_usup_inf_usup hψ hM4 ha3 ha5 hne
  have hfin : Finite ↥(Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ⊓
      Usup _ (p (x + 4)) (p (x + 5))) := Nat.finite_of_card_ne_zero (by
        rw [hcard]; exact Fintype.card_ne_zero)
  have hle := Subgroup.card_le_of_le (c.critR_le_usup_inf hp hxN hc hs)
  rw [hcard] at hle
  obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.via hx
  obtain ⟨ψ₈, -, hψ₈⟩ := exists_natural_Uloc h c.via (c.isCritical_symm hc).1
  have hcore := s35_core h c.cent c.via hc hψ₀ hψ₈
  have hR := hcore.2.2.2.1
  have hcomm := commN_ne_bot hcore.2.2.2.2.2
  have hpos : 1 ≤ Module.finrank F ↥(commN (natImage ψ₀ (ZM (puAmalgam h.le) (p (x + 8))))) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hcomm (Submodule.finrank_eq_zero.mp h0)
  have hge : Fintype.card F ≤ Nat.card ↥(critR (puAmalgam h.le) (p x) (p (x + 8))) := by
    rw [hR, Nat.card_eq_fintype_card]
    calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos hpos
  omega

theorem mem_critR_iff {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x')
    {ψ : ↥(stab (puAmalgam c.hyp.le) x) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.hyp.le L x) ⊥ ψ false 1)
    (v : ↥(Uloc c.hyp.le L x)) :
    (v : (puAmalgam c.hyp.le).Universal) ∈ critR _ x x' ↔
      natVec hψ v ∈ commN (natImage ψ (ZM (puAmalgam c.hyp.le) x')) := by
  have hZs : ZM (puAmalgam c.hyp.le) x' ≤ stab _ x :=
    zm_le_stab_of_isCritical _ c.hyp.hyp20 c.bpos hc
  rw [critR, commutator_zm_eq_uloc c.hyp c.full hc.1 hZs]
  exact S4A.mem_commutator_iff_natVec hψ hZs v

theorem critR_ne_of_not_le_normalizer (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 12 ≤ N)
    (hc : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hc' : IsCritical (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 12)))
    (hs : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), g • p (x + 8) = p (x + 4))
    (hpe : ¬ ZM (puAmalgam c.hyp.le) (p x) ≤
      Subgroup.normalizer (Usup _ (p (x + 8)) (p (x + 9)) : Set (puAmalgam c.hyp.le).Universal)) :
    critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≠ critR _ (p (x + 4)) (p (x + 12)) := by
  intro heq
  apply hpe
  have h := c.hyp
  have hW := (c.critR_le_usup_inf (x := x + 4) hp (by omega) hc'
    (by simpa [show x + 4 + 2 = x + 6 by omega, show x + 4 + 4 = x + 8 by omega] using hs)).trans
    inf_le_right
  rw [show x + 4 + 4 = x + 8 by omega, show x + 4 + 5 = x + 9 by omega, ← heq] at hW
  have hM8 := c.isMVtx_add hp (k := 8) (by omega) hc.1 (by decide)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  have ha9 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 9)) := hp.adj (x + 8) (by omega)
  have hWU : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 9)) ≤ ZM _ (p (x + 8)) :=
    ((c.usup_eq_uloc_inf_centralizer hψ hM8 ha9) ▸ inf_le_left).trans (uloc_le_zm h c.full hM8)
  have key : ∀ z ∈ ZM (puAmalgam h.le) (p x), ∀ w ∈ Usup (puAmalgam h.le) (p (x + 8)) (p (x + 9)),
      z * w * z⁻¹ ∈ Usup (puAmalgam h.le) (p (x + 8)) (p (x + 9)) := by
    intro z hz w hw
    have hcomm : ⁅z, w⁆ ∈ critR (puAmalgam h.le) (p x) (p (x + 8)) :=
      Subgroup.commutator_mem_commutator hz (hWU hw)
    have : z * w * z⁻¹ = ⁅z, w⁆ * w := by rw [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ (hW hcomm) hw
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key z hz w
  · intro hw
    have hz2 : z⁻¹ ∈ ZM (puAmalgam h.le) (p x) := inv_mem hz
    have := key z⁻¹ hz2 _ hw
    simpa [mul_assoc] using this

theorem critR_eq_smul {x x' y : Vtx (puAmalgam c.hyp.le)} (hy : IsMVtx _ y)
    (hR : critR (puAmalgam c.hyp.le) x x' ≤ Zloc c.hyp.le L y)
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab _ y) :
    critR (puAmalgam c.hyp.le) x x' ≤ critR _ (g • x) (g • x') := by
  intro r hr
  have hrc : r ∈ Subgroup.centralizer (stab (puAmalgam c.hyp.le) y : Set _) :=
    zloc_le_centralizer_stab c.hyp c.full hy (hR hr)
  have hgr : g * r * g⁻¹ = r := by
    rw [(Subgroup.mem_centralizer_iff.mp hrc) g hg, mul_inv_cancel_right]
  rw [critR, zm_smul, zm_smul, ← Subgroup.map_commutator]
  exact ⟨r, hr, by simpa [MulAut.conj_apply] using hgr⟩

theorem commutator_zm_qv_eq_usup (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 12 ≤ N)
    (hc0 : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hc4 : IsCritical (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 12)))
    (hs2 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 2)), g • p (x + 4) = p x)
    (hs6 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), g • p (x + 8) = p (x + 4))
    (hgpd4 : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5)))
    (hgpd8 : ZH (puAmalgam c.hyp.le) (p (x + 7)) ≠ ZH _ (p (x + 9)))
    (hne : critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≠ critR _ (p (x + 4)) (p (x + 12))) :
    critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ⊔ critR _ (p (x + 4)) (p (x + 12)) =
        Usup _ (p (x + 4)) (p (x + 5)) ∧
      ⁅ZM (puAmalgam c.hyp.le) (p (x + 4)), Qv _ (p (x + 6))⁆ = Usup _ (p (x + 4)) (p (x + 5)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hx := hc0.1
  have hM4 := c.isMVtx_add hp (k := 4) (by omega) hx (by decide)
  have hM6 := c.isMVtx_add hp (k := 6) (by omega) hx (by decide)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  have ha3 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 3)) :=
    (hp.adj (x + 3) (by omega)).symm
  have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
  have ha65 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 5)) :=
    (hp.adj (x + 5) (by omega)).symm
  set R₂ := critR (puAmalgam h.le) (p x) (p (x + 8)) with hR₂
  set R₁ := critR (puAmalgam h.le) (p (x + 4)) (p (x + 12)) with hR₁
  set W := Usup (puAmalgam h.le) (p (x + 4)) (p (x + 5)) with hWdef
  set C := ⁅ZM (puAmalgam h.le) (p (x + 4)), Qv _ (p (x + 6))⁆ with hCdef
  have hWU : W ≤ Uloc h.le L (p (x + 4)) := by
    rw [hWdef, c.usup_eq_uloc_inf_centralizer hψ hM4 ha5]; exact inf_le_left
  have hCW : C ≤ W := by
    rw [hCdef, hWdef, Usup, zv_of_isMVtx _ hM4]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hM6 ha65)
  have hR1C : R₁ ≤ C := by
    refine Subgroup.commutator_mono le_rfl (zm_le_qv_of_dist_lt _ (c.isCritical_symm hc4).1 ?_)
    rw [tdist_comm, hp.dist_eq' (show x + 6 ≤ x + 12 by omega) hxN, c.b8]
    omega
  have hR2C : R₂ ≤ C := by
    obtain ⟨g, hg, hgx⟩ := hs6
    have g6 : geo (puAmalgam h.le) (p (x + 8)) (p x) 2 = p (x + 6) := by
      rw [hp.eq_geo_rev (i := x) (j := x + 8) (k := x + 6) (by omega) (by omega) (by omega),
        show x + 8 - (x + 6) = 2 by omega]
    have hZ6 := c.critR_le_zloc' hc0
    rw [g6] at hZ6
    refine (c.critR_eq_smul hM6 hZ6 hg).trans ?_
    rw [hgx, critR, Subgroup.commutator_comm]
    refine Subgroup.commutator_mono le_rfl (zm_le_qv_of_dist_lt _ ((isMVtx_smul _ g _).mpr hx) ?_)
    have hg6 : g • p (x + 6) = p (x + 6) := (mem_stab _).mp hg
    rw [← hg6, dist_smul, hp.dist_eq' (show x ≤ x + 6 by omega) (by omega), c.b8]
    omega
  have hcard1 : Nat.card ↥R₁ = Fintype.card F := by
    have := c.card_critR (x := x + 4) hp (by omega) hc4
      (by simpa [show x + 4 + 2 = x + 6 by omega, show x + 4 + 4 = x + 8 by omega] using hs6)
      (by simpa [show x + 4 + 3 = x + 7 by omega, show x + 4 + 5 = x + 9 by omega] using hgpd8)
    simpa [show x + 4 + 8 = x + 12 by omega] using this
  have hcard2 : Nat.card ↥R₂ = Fintype.card F := c.card_critR hp (by omega) hc0 hs2 hgpd4
  have hne35 : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ≠ Usup _ (p (x + 4)) (p (x + 5)) :=
    fun heq => hgpd4 ((c.usup_eq_iff_zh_eq hψ hM4 ha3 ha5).mp heq)
  have hcard35 := c.card_usup_inf_usup hψ hM4 ha3 ha5 hne35
  have hfin35 : Finite ↥(Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ⊓
      Usup _ (p (x + 4)) (p (x + 5))) := Nat.finite_of_card_ne_zero (by
        rw [hcard35]; exact Fintype.card_ne_zero)
  have hR2eq :
      R₂ = Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ⊓ Usup _ (p (x + 4)) (p (x + 5)) :=
    Subgroup.eq_of_le_of_card_ge (c.critR_le_usup_inf hp (by omega) hc0 hs2)
      (by rw [hcard35, hcard2])
  have hR1U : R₁ ≤ Uloc h.le L (p (x + 4)) := c.critR_le_uloc hc4
  have hR2U : R₂ ≤ Uloc h.le L (p (x + 4)) := hR2eq ▸ inf_le_right.trans hWU
  set S₁ := commN (natImage ψ (ZM (puAmalgam h.le) (p (x + 12)))) with hS₁
  set S₂ := fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 3)))) ⊓
    fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 5)))) with hS₂
  have hS1 : ∀ v : ↥(Uloc h.le L (p (x + 4))), (v : (puAmalgam h.le).Universal) ∈ R₁ ↔
      natVec hψ v ∈ S₁ := c.mem_critR_iff hc4 hψ
  have hS2 : ∀ v : ↥(Uloc h.le L (p (x + 4))), (v : (puAmalgam h.le).Universal) ∈ R₂ ↔
      natVec hψ v ∈ S₂ := by
    intro v
    rw [hR2eq, Subgroup.mem_inf, c.mem_usup_iff hψ hM4 ha3, c.mem_usup_iff hψ hM4 ha5,
      Submodule.mem_inf]
  have hf1 : Module.finrank F ↥S₁ = 1 := by
    have h1 := card_eq_of_natVec_iff hψ hR1U hS1
    rw [hcard1, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h1
    have h1' : Fintype.card F ^ 1 = Fintype.card F ^ Module.finrank F ↥S₁ := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective Fintype.one_lt_card h1').symm
  have hf2 : Module.finrank F ↥S₂ = 1 := by
    have h1 := card_eq_of_natVec_iff hψ hR2U hS2
    rw [hcard2, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h1
    have h1' : Fintype.card F ^ 1 = Fintype.card F ^ Module.finrank F ↥S₂ := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective Fintype.one_lt_card h1').symm
  have hSne : S₁ ≠ S₂ := fun heq => hne ((eq_iff_of_natVec_iff hψ hR2U hR1U hS2 hS1).mpr heq.symm)
  have hinf : R₁ ⊓ R₂ = ⊥ := by
    have hS : ∀ v : ↥(Uloc h.le L (p (x + 4))), (v : (puAmalgam h.le).Universal) ∈ R₁ ⊓ R₂ ↔
        natVec hψ v ∈ S₁ ⊓ S₂ := by
      intro v; rw [Subgroup.mem_inf, hS1, hS2]; exact Submodule.mem_inf.symm
    have hf0 : Module.finrank F ↥(S₁ ⊓ S₂) = 0 := by
      have hle : Module.finrank F ↥(S₁ ⊓ S₂) ≤ 1 := hf1 ▸ Submodule.finrank_mono inf_le_left
      by_contra h0
      have e1 : S₁ ⊓ S₂ = S₁ := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : S₁ ⊓ S₂ = S₂ := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hSne (e1.symm.trans e2)
    have hc := card_eq_of_natVec_iff hψ (inf_le_left.trans hR1U) hS
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(S₁ ⊓ S₂)), hf0, pow_zero] at hc
    exact Subgroup.eq_bot_of_card_eq _ hc
  have hab : R₂ ≤ Subgroup.centralizer (R₁ : Set (puAmalgam h.le).Universal) := by
    have hUab := (isElemAbelian_zm _ h20 h.critDist_pos hM4).1
    rw [isMulCommutative_subgroup_iff] at hUab
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hUab z (uloc_le_zm h c.full hM4 (hR1U hz)) y (uloc_le_zm h c.full hM4 (hR2U hy))
  have hcard12 : Nat.card ↥(R₁ ⊔ R₂) = Fintype.card F ^ 2 := by
    rw [card_sup_of_commute hab hinf, hcard1, hcard2, sq]
  have hcardW := c.card_usup hψ hM4 ha5
  have hfinW : Finite ↥W := Nat.finite_of_card_ne_zero (by
    rw [hcardW]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hRW : R₁ ⊔ R₂ = W :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hR1C.trans hCW) (hR2C.trans hCW))
      (by rw [hcardW, hcard12])
  refine ⟨by rw [sup_comm]; exact hRW, le_antisymm hCW ?_⟩
  rw [← hRW]
  exact sup_le hR1C hR2C

theorem usup_le_zloc (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 12 ≤ N)
    (hc0 : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hc4 : IsCritical (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 12)))
    (hs2 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 2)), g • p (x + 4) = p x)
    (hs6 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), g • p (x + 8) = p (x + 4))
    (hgpd4 : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5)))
    (hgpd8 : ZH (puAmalgam c.hyp.le) (p (x + 7)) ≠ ZH _ (p (x + 9)))
    (hne : critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≠ critR _ (p (x + 4)) (p (x + 12))) :
    Usup (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 5)) ≤ Zloc c.hyp.le L (p (x + 6)) := by
  rw [← (c.commutator_zm_qv_eq_usup hp hxN hc0 hc4 hs2 hs6 hgpd4 hgpd8 hne).2]
  have hM6 := c.isMVtx_add hp (k := 6) (by omega) hc0.1 (by decide)
  have hZ : ZM (puAmalgam c.hyp.le) (p (x + 4)) ≤ Vv _ (p (x + 6)) := by
    have := zv_le_vi (puAmalgam c.hyp.le) (δ := p (x + 6)) (ρ := p (x + 4)) (i := 2)
      (by rw [tdist_comm, hp.dist_eq' (show x + 4 ≤ x + 6 by omega) (by omega)]; omega)
    rwa [zv_of_isMVtx _ (c.isMVtx_add hp (k := 4) (by omega) hc0.1 (by decide))] at this
  exact (Subgroup.commutator_mono hZ le_rfl).trans (c.commutator_vv_qv_le_zloc hM6)

theorem usup_eq_usup (hp : IsNBPath _ p N) {x : ℕ} (hxN : x + 12 ≤ N)
    (hc0 : IsCritical (puAmalgam c.hyp.le) (p x) (p (x + 8)))
    (hc4 : IsCritical (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 12)))
    (hs2 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 2)), g • p (x + 4) = p x)
    (hs6 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), g • p (x + 8) = p (x + 4))
    (hgpd4 : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5)))
    (hgpd8 : ZH (puAmalgam c.hyp.le) (p (x + 7)) ≠ ZH _ (p (x + 9)))
    (hne : critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≠ critR _ (p (x + 4)) (p (x + 12))) :
    Usup (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 5)) = Usup _ (p (x + 8)) (p (x + 7)) := by
  have h := c.hyp
  have hx := hc0.1
  have hM4 := c.isMVtx_add hp (k := 4) (by omega) hx (by decide)
  have hM6 := c.isMVtx_add hp (k := 6) (by omega) hx (by decide)
  have hM8 := c.isMVtx_add hp (k := 8) (by omega) hx (by decide)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h c.via hM8
  have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
  have ha7 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  have ha67 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have hS4 := (c.commutator_zm_qv_eq_usup hp hxN hc0 hc4 hs2 hs6 hgpd4 hgpd8 hne).1
  have hR1 : critR (puAmalgam h.le) (p (x + 4)) (p (x + 12)) ≤ Usup _ (p (x + 8)) (p (x + 7)) := by
    have := c.critR_le_usup_inf (x := x + 4) hp (by omega) hc4
      (by simpa [show x + 4 + 2 = x + 6 by omega, show x + 4 + 4 = x + 8 by omega] using hs6)
    simpa [show x + 4 + 8 = x + 12 by omega, show x + 4 + 4 = x + 8 by omega,
      show x + 4 + 3 = x + 7 by omega] using this.trans inf_le_left
  have hR2 : critR (puAmalgam h.le) (p x) (p (x + 8)) ≤ Usup _ (p (x + 8)) (p (x + 7)) := by
    have g6 : geo (puAmalgam h.le) (p (x + 8)) (p x) 2 = p (x + 6) := by
      rw [hp.eq_geo_rev (i := x) (j := x + 8) (k := x + 6) (by omega) (by omega) (by omega),
        show x + 8 - (x + 6) = 2 by omega]
    have hZ6 := c.critR_le_zloc' hc0
    rw [g6] at hZ6
    rw [← c.uloc_inf_zh hψ' hM8 ha7]
    exact le_inf (c.critR_le_uloc' hc0) (hZ6.trans (zloc_le_zh h c.full hM6 ha67))
  have hle : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 5)) ≤ Usup _ (p (x + 8)) (p (x + 7)) := by
    rw [← hS4]; exact sup_le hR2 hR1
  have hcard' := c.card_usup hψ' hM8 ha7
  have hfin : Finite ↥(Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ Fintype.card_ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', c.card_usup hψ hM4 ha5])

end Path

end Ctx

end CFSG.Quasithin.MS93.S45
