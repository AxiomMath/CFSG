module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91N5
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conj_mem_Q91 (hc : Ctx M Q Z B) {a : G} (ha : a ∈ M) {y : G} (hy : y ∈ Q) :
    a * y * a⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy

def centModQ (hc : Ctx M Q Z B) (b : G) : Subgroup G where
  carrier := {g | g ∈ M ∧ ⁅g, b⁆ ∈ Q}
  mul_mem' := by
    rintro g g' ⟨hg, hgb⟩ ⟨hg', hgb'⟩
    refine ⟨M.mul_mem hg hg', ?_⟩
    have e : ⁅g * g', b⁆ = g * ⁅g', b⁆ * g⁻¹ * ⁅g, b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem (conj_mem_Q91 hc hg hgb') hgb
  one_mem' := ⟨M.one_mem, by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro g ⟨hg, hgb⟩
    refine ⟨M.inv_mem hg, ?_⟩
    have e : ⁅g⁻¹, b⁆ = g⁻¹ * ⁅g, b⁆⁻¹ * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := conj_mem_Q91 hc (M.inv_mem hg) (Q.inv_mem hgb)
    simpa using this

theorem isCentrePre_le_CN91 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ hc.CN t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQN : Q ≤ hc.CN t := sec9_Q_le_CN hc ht
  obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk⟩ := exists_psi91 hs
  haveI := hch
  intro x hx
  have hxR : x ∈ Rt M (LB M Q B) t := hZ0.le hx
  have hxz : ψ ⟨x, hxR⟩ ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
    rw [Subgroup.mem_center_iff]
    intro p
    obtain ⟨s, rfl⟩ := hψs p
    have hQs : ⁅x, (s : G)⁆ ∈ Q := hZ0.comm_mem hx s.2
    have h1 : ψ ⁅(⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)), s⁆ = 1 := by
      have : ⁅(⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)), s⁆ ∈ ψ.ker := by
        rw [hψk, Subgroup.mem_subgroupOf]
        exact hQN hQs
      exact this
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [Subgroup.center_prod, center_statedSL_two_eq_bot, Subgroup.bot_prod_bot,
    Subgroup.mem_bot] at hxz
  have : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ ψ.ker := hxz
  rw [hψk, Subgroup.mem_subgroupOf] at this
  exact this

theorem isCentrePre_eq_inf91 {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t)
    (hr : Sec7A hc t r)
    (hprod : ∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
      ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b)
    (hcomm : ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B), ⁅s, x⁆ ∈ Q)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Z0 = LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]; exact le_sup_right
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hZL : Z0 ≤ LB M Q B := by
    intro s hs0
    have hsN := isCentrePre_le_CN91 hs hZ0 hs0
    obtain ⟨a, ha, b, hb, hsab⟩ := hprod s hsN
    have haM : a ∈ M := hc.LB_le_M ha.1
    have hbe : b = a⁻¹ * s := by rw [hsab]; group
    have hl : ∀ l ∈ LB M Q B, ⁅l, b⁆ ∈ Q := by
      intro l hl
      have e : ⁅l, b⁆ = ⁅l, a⁻¹⁆ * (a⁻¹ * ⁅l, s⁆ * a) := by
        rw [hbe]; simp only [commutatorElement_def]; group
      rw [e]
      have h1 : ⁅l, a⁻¹⁆ ∈ Q := hc.commutator_LB_le_Q
        (Subgroup.commutator_mem_commutator hl ((LB M Q B).inv_mem ha.1))
      have h2 : ⁅l, s⁆ ∈ Q := by
        rw [← commutatorElement_inv]
        exact Q.inv_mem (hZ0.comm_mem hs0 (hLR hl))
      have h3 := conj_mem_Q91 hc (M.inv_mem haM) h2
      rw [inv_inv] at h3
      exact Q.mul_mem h1 h3
    have hm : ∀ m ∈ LB M Q (conjSubgroup r B), ⁅m, b⁆ ∈ Q := fun m hm =>
      hcr.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hm hb.1)
    have hle : LB M Q B ⊔ LB M Q (conjSubgroup r B) ≤ centModQ hc b :=
      sup_le (fun l hl' => ⟨hc.LB_le_M hl', hl l hl'⟩)
        (fun m hm' => ⟨hcr.LB_le_M hm', hm m hm'⟩)
    have hbZ0 : b ∈ Z0 := by
      refine (hZ0 b).mpr ⟨hL'R hb.1, fun g hg => ?_⟩
      rw [hr.gen] at hg
      have := (hle hg).2
      rw [← commutatorElement_inv]
      exact Q.inv_mem this
    have hbL : b ∈ LB M Q B := by
      have hb' : b ∈ conjSubgroup r (LB M Q B) := hLA ▸ hb.1
      have hc' : r⁻¹ * b * r ∈ LB M Q B := mem_conjSubgroup.mp hb'
      have hq : ⁅b, r⁻¹⁆ ∈ Q := hZ0.comm_mem hbZ0 ((Rt M (LB M Q B) t).inv_mem hrR)
      have e : b = ⁅b, r⁻¹⁆ * (r⁻¹ * b * r) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (LB M Q B).mul_mem (hQL hq) hc'
    rw [hsab]
    exact (LB M Q B).mul_mem ha.1 hbL
  have hZL' : Z0 ≤ LB M Q (conjSubgroup r B) := by
    rw [hLA]
    exact sec7ctr_Z0_le_conj_LB hc hZ0 hZL hrR
  refine le_antisymm (le_inf hZL hZL') fun x hx => ?_
  refine (hZ0 x).mpr ⟨hLR hx.1, fun g hg => ?_⟩
  rw [← commutatorElement_inv]
  exact Q.inv_mem (hcomm g hg x hx)

theorem card_centrePre_le91 (h34 : Stroth34Statement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZL : Z0 ≤ LB M Q B) :
    Nat.card Z0 ≤ Nat.card Q * Nat.card Z := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  refine h311bCard G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht hs5.notQ
    (sec9_Rt_ne_LB h34 hs) (sec9_not_SLNat hs) Z0 fun x => ⟨fun hx => ⟨hZL hx, fun g hg => ?_⟩,
      fun ⟨hxL, hxg⟩ => ?_⟩
  · rw [← commutatorElement_inv]
    exact Q.inv_mem (hZ0.comm_mem hx hg)
  · refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) ht hxL, fun g hg => ?_⟩
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hxg g hg)

theorem sec7A_of_polar91 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hNC : Sec9NCommStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {K : Type} [Field K] [Finite K]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u) (r : ↥(Rt M (LB M Q B) t))
    (hne : polar (quadPlus 2 K) u ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0) :
    Sec7A hc t (r : G) := by
  classical
  have hs5 := hs.toSec5
  have hplane := (hypPlane_iff_polar91 h34 hs P r).mpr hne
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hrX : (φ r : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hQu' : quadPlus 2 K ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = 0 := by
    rw [E.quad_mulVec hrX]
    exact P.sing
  have hL2 := sec7_conj_LomGL E φ P.range r P.root
  rw [← hc.LB_conj (hc.Rt_le_M t r.2)] at hL2
  have hgen := le_sup_secOmega E hQ φ P.range P.ker P.sing hQu' hne P.root hL2
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem
  have hL'R : LB M Q (conjSubgroup (r : G) B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs5.mem r.2
  have hgen' : Rt M (LB M Q B) t =
      hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup (r : G) B) :=
    le_antisymm (by rw [sup_assoc]; exact hgen)
      (sup_le (sup_le (sec9_CN_le_Rt hc t) hLR) hL'R)
  have hcore := hc.sec51_core h35 hs5.mem r.2
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
    (hNC G M Q Z B hc n t hs) hgen'
  have hNle : hc.CN t ≤ LB M Q B ⊔ LB M Q (conjSubgroup (r : G) B) := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hcore.1 x hx
    exact Subgroup.mul_mem_sup ha.1 hb.1
  refine ⟨r.2, hplane, ?_⟩
  rw [sup_eq_right.mpr hNle] at hgen
  exact le_antisymm hgen (sup_le hLR hL'R)

end HS9

end CFSG.RankThree.GF2n.Stroth80
