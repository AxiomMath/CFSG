module

public import CFSG.LinearAlgebra.LinearGroups.HuaRingHom
public import CFSG.RankThree.GF2n.Stroth80.Sec11TorusFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec11TorusSpace
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusComm
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusScale
import CFSG.RankThree.GF2n.Stroth80.Basic
import CFSG.RankThree.GF2n.Stroth80.Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace LBFrame

variable (fr : LBFrame Q Z B)

@[expose] noncomputable def lbPhi (t : fr.K) (a : G) : G := ⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆⁆

theorem lbPhi_mem (hc : Ctx M Q Z B) (t : fr.K) {a : G} (ha : a ∈ QB B ⊓ M) :
    fr.lbPhi t a ∈ QB B ⊓ M :=
  hc.comm_QB_P_mem (fr.lbRootL_mem 1) (hc.comm_Q_PB_mem (fr.lbRootU_mem t) ha)

theorem lbPhi_congr (hc : Ctx M Q Z B) (t : fr.K) {a a' : G} (ha : a ∈ QB B ⊓ M)
    (ha' : a' ∈ QB B ⊓ M) (h : a⁻¹ * a' ∈ Q) : (fr.lbPhi t a)⁻¹ * fr.lbPhi t a' ∈ Q :=
  hc.comm_QB_P_congr_right (fr.lbRootL_mem 1) (hc.comm_Q_PB_mem (fr.lbRootU_mem t) ha)
    (hc.comm_Q_PB_mem (fr.lbRootU_mem t) ha')
    (hc.comm_Q_PB_congr_right (fr.lbRootU_mem t) ha ha' h)

theorem lbPhi_mul (hc : Ctx M Q Z B) (t : fr.K) {a a' : G} (ha : a ∈ QB B ⊓ M)
    (ha' : a' ∈ QB B ⊓ M) : (fr.lbPhi t a * fr.lbPhi t a')⁻¹ * fr.lbPhi t (a * a') ∈ Q := by
  have hx := fr.lbRootU_mem t
  have hu := fr.lbRootL_mem 1
  have hn := hc.comm_Q_PB_mem hx ha
  have hn' := hc.comm_Q_PB_mem hx ha'
  have hnn : ⁅fr.lbRootU t, a⁆ * ⁅fr.lbRootU t, a'⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.mul_mem _ hn hn'
  have hp := hc.comm_Q_PB_mem hx (Subgroup.mul_mem _ ha ha')
  have h1 := hc.comm_QB_P_mul_right hu hn hn'
  have h2 := hc.comm_QB_P_congr_right hu hnn hp (hc.comm_Q_PB_mul_right hx ha ha')
  have e : (fr.lbPhi t a * fr.lbPhi t a')⁻¹ * fr.lbPhi t (a * a') =
      ((fr.lbPhi t a * fr.lbPhi t a')⁻¹ *
        ⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆ * ⁅fr.lbRootU t, a'⁆⁆) *
      (⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆ * ⁅fr.lbRootU t, a'⁆⁆⁻¹ * fr.lbPhi t (a * a')) := by
    group
  rw [e]
  exact Q.mul_mem h1 h2

theorem lbPhi_add (hc : Ctx M Q Z B) (s t : fr.K) {a : G} (ha : a ∈ QB B ⊓ M) :
    (fr.lbPhi s a * fr.lbPhi t a)⁻¹ * fr.lbPhi (s + t) a ∈ Q := by
  have hxs := fr.lbRootU_mem s
  have hxt := fr.lbRootU_mem t
  have hxst := fr.lbRootU_mem (s + t)
  have hu := fr.lbRootL_mem 1
  have hφ : fr.φ ⟨fr.lbRootU s * fr.lbRootU t, Subgroup.mem_sup_left (Q.mul_mem hxs hxt)⟩ =
      fr.φ ⟨fr.lbRootU (s + t), Subgroup.mem_sup_left hxst⟩ := by
    rw [fr.phi_lbRootU (s + t), ← Timmesfeld.RankOne.upperElt_mul, ← fr.phi_lbRootU s,
      ← fr.phi_lbRootU t, ← map_mul]
    rfl
  have hC := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
    (fr.mem_centralizer_of_phi_eq hc hφ)
  have h1 := hc.comm_Q_PB_congr_left (Q.mul_mem hxs hxt) hxst hC ha
  have h2 := hc.comm_Q_PB_mul_left hxs hxt ha
  have hn := hc.comm_Q_PB_mem hxs ha
  have hn' := hc.comm_Q_PB_mem hxt ha
  have hst := hc.comm_Q_PB_mem hxst ha
  have hnn : ⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.mul_mem _ hn hn'
  have h3 : (⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆)⁻¹ * ⁅fr.lbRootU (s + t), a⁆ ∈ QB B := by
    have e : (⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆)⁻¹ * ⁅fr.lbRootU (s + t), a⁆ =
        ((⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆)⁻¹ * ⁅fr.lbRootU s * fr.lbRootU t, a⁆) *
          (⁅fr.lbRootU s * fr.lbRootU t, a⁆⁻¹ * ⁅fr.lbRootU (s + t), a⁆) := by
      group
    rw [e]
    exact (QB B).mul_mem ((Ctx.Z_le_QB hc).1 h2) h1
  have h4 := hc.comm_QB_P_mul_right hu hn hn'
  have h5 := hc.comm_QB_P_congr_right hu hnn hst h3
  have e : (fr.lbPhi s a * fr.lbPhi t a)⁻¹ * fr.lbPhi (s + t) a =
      ((fr.lbPhi s a * fr.lbPhi t a)⁻¹ *
        ⁅fr.lbRootL 1, ⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆⁆) *
      (⁅fr.lbRootL 1, ⁅fr.lbRootU s, a⁆ * ⁅fr.lbRootU t, a⁆⁆⁻¹ * fr.lbPhi (s + t) a) := by
    group
  rw [e]
  exact Q.mul_mem h4 h5

theorem lbPhi_one (hc : Ctx M Q Z B) {a : G} (ha : a ∈ QB B ⊓ M) : fr.lbPhi 1 a * a ∈ Q := by
  have hw := fr.conj_lbWeylU hc (one_ne_zero : (1 : fr.K) ≠ 0)
  have hp := hc.conj_PB_mem_P_of_swap hw.1 hw.2 ha
  rw [lbWeylU, inv_one] at hp
  exact hc.weylQ_comm_comm_PB (fr.lbRootU_mem 1) (fr.lbRootL_mem 1) ha hp.1

omit [Finite G] in
private theorem lbWeylU_one_eq : fr.lbWeylU 1 = fr.lbRootU 1 * fr.lbRootL 1 * fr.lbRootU 1 := by
  rw [lbWeylU, inv_one]

private theorem conj_lbWeylU_one_mem (hc : Ctx M Q Z B) (s : fr.K) :
    fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹ ∈ QB B := by
  have hw := fr.conj_lbWeylU hc (one_ne_zero : (1 : fr.K) ≠ 0)
  rw [← (hc.conj_Q_QB_of_swap hw.1 hw.2).1, mem_conjSubgroup,
    show (fr.lbWeylU 1)⁻¹ * (fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹) * fr.lbWeylU 1 =
      fr.lbRootU s by group]
  exact fr.lbRootU_mem s

private theorem comm_lbRootL_congr_weyl (hc : Ctx M Q Z B) (s : fr.K) {p : G}
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅fr.lbRootL s, p⁆⁻¹ * (fr.lbWeylU 1 *
      ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆ * (fr.lbWeylU 1)⁻¹) ∈ Q := by
  have hv := fr.conj_lbWeylU_one_mem hc s
  have hC := fr.mem_centralizer_of_phi_eq hc
    (g := ⟨fr.lbRootL s, Subgroup.mem_sup_right (fr.lbRootL_mem s)⟩)
    (g' := ⟨_, Subgroup.mem_sup_right hv⟩)
    ((fr.phi_lbRootL s).trans (fr.phi_conj_lbWeylU_one s _).symm)
  have h1 := hc.comm_QB_P_congr_left (fr.lbRootL_mem s) hv
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hC) hp
  rwa [show ⁅fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹, p⁆ =
      fr.lbWeylU 1 * ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆ * (fr.lbWeylU 1)⁻¹ by
    simp only [commutatorElement_def]; group] at h1

private theorem conj_inv_lbWeylU_one (hc : Ctx M Q Z B) {p : G}
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ((fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1)⁻¹ * ⁅fr.lbRootL 1, p⁆ ∈ Q := by
  have hx1 := fr.lbRootU_mem 1
  have hu1 := fr.lbRootL_mem 1
  have h8 := hc.weylQ_conj_P (Q.inv_mem hx1) ((QB B).inv_mem hu1) hp
  rw [show (fr.lbRootU 1)⁻¹ * (fr.lbRootL 1)⁻¹ * (fr.lbRootU 1)⁻¹ * p *
      ((fr.lbRootU 1)⁻¹ * (fr.lbRootL 1)⁻¹ * (fr.lbRootU 1)⁻¹)⁻¹ =
      (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1 by rw [fr.lbWeylU_one_eq]; group] at h8
  have hφu : fr.φ ⟨(fr.lbRootL 1)⁻¹, Subgroup.mem_sup_right ((QB B).inv_mem hu1)⟩ =
      fr.φ ⟨fr.lbRootL 1, Subgroup.mem_sup_right hu1⟩ := by
    rw [show (⟨(fr.lbRootL 1)⁻¹, Subgroup.mem_sup_right ((QB B).inv_mem hu1)⟩ : ↥(Q ⊔ QB B)) =
      (⟨fr.lbRootL 1, Subgroup.mem_sup_right hu1⟩)⁻¹ from rfl, map_inv, fr.phi_lbRootL]
    exact inv_eq_of_mul_eq_one_right (by
      rw [Timmesfeld.RankOne.lowerElt_mul, CharTwo.add_self_eq_zero,
        Timmesfeld.RankOne.lowerElt_zero])
  have h8' := hc.comm_QB_P_congr_left ((QB B).inv_mem hu1) hu1
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)
      (fr.mem_centralizer_of_phi_eq hc hφu)) hp
  have e : ((fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1)⁻¹ * ⁅fr.lbRootL 1, p⁆ =
      (⁅(fr.lbRootL 1)⁻¹, p⁆⁻¹ * ((fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1))⁻¹ *
        (⁅(fr.lbRootL 1)⁻¹, p⁆⁻¹ * ⁅fr.lbRootL 1, p⁆) := by group
  rw [e]
  exact Q.mul_mem (Q.inv_mem h8) h8'

theorem comm_lbRootL_lbPhi (hc : Ctx M Q Z B) (s : fr.K) {p : G}
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅fr.lbRootL s, p⁆⁻¹ * fr.lbPhi s ⁅fr.lbRootL 1, p⁆ ∈ Q := by
  have hu1 := fr.lbRootL_mem 1
  have hw := fr.conj_lbWeylU hc (one_ne_zero : (1 : fr.K) ≠ 0)
  have hwi := conjSubgroup_inv_swap hw.1 hw.2
  have ha := hc.conj_P_mem_PB_of_swap hwi.1 hwi.2 hp
  rw [inv_inv] at ha
  have hm := hc.comm_QB_P_mem hu1 hp
  have h9 := hc.comm_Q_PB_congr_right (fr.lbRootU_mem s) ha hm (fr.conj_inv_lbWeylU_one hc hp)
  have hn := hc.comm_Q_PB_mem (fr.lbRootU_mem s) ha
  have hn' := hc.comm_Q_PB_mem (fr.lbRootU_mem s) hm
  have h7 := hc.weylQ_conj_P (fr.lbRootU_mem 1) hu1 hn
  rw [← fr.lbWeylU_one_eq] at h7
  have h10 := hc.comm_QB_P_congr_right hu1 hn hn' h9
  have h1 := fr.comm_lbRootL_congr_weyl hc s hp
  have e : ⁅fr.lbRootL s, p⁆⁻¹ * fr.lbPhi s ⁅fr.lbRootL 1, p⁆ =
      (⁅fr.lbRootL s, p⁆⁻¹ * (fr.lbWeylU 1 *
        ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆ * (fr.lbWeylU 1)⁻¹)) *
      (⁅fr.lbRootL 1, ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆⁆⁻¹ * (fr.lbWeylU 1 *
        ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆ * (fr.lbWeylU 1)⁻¹))⁻¹ *
      (⁅fr.lbRootL 1, ⁅fr.lbRootU s, (fr.lbWeylU 1)⁻¹ * p * fr.lbWeylU 1⁆⁆⁻¹ *
        ⁅fr.lbRootL 1, ⁅fr.lbRootU s, ⁅fr.lbRootL 1, p⁆⁆⁆) := by
    simp only [lbPhi]
    group
  rw [e]
  exact Q.mul_mem (Q.mul_mem h1 (Q.inv_mem h7)) h10

theorem lbPhi_inv_mul (hc : Ctx M Q Z B) {t : fr.K} (ht : t ≠ 0) {a : G} (ha : a ∈ QB B ⊓ M) :
    fr.lbPhi t⁻¹ (fr.lbPhi t a) * a ∈ Q := by
  have hp := hc.comm_Q_PB_mem (fr.lbRootU_mem t) ha
  have h1 := fr.comm_lbRootL_lbPhi hc t⁻¹ hp
  have hw := fr.conj_lbWeylU hc ht
  have h2 := hc.weylQ_comm_comm_PB (fr.lbRootU_mem t) (fr.lbRootL_mem t⁻¹) ha
    (hc.conj_PB_mem_P_of_swap hw.1 hw.2 ha).1
  have hA := (hc.comm_QB_P_mem (fr.lbRootL_mem t⁻¹) hp).2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hA) _).mp h1
  show fr.lbPhi t⁻¹ ⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆⁆ * a ∈ Q
  have e : fr.lbPhi t⁻¹ ⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆⁆ * a =
      ⁅fr.lbRootL t⁻¹, ⁅fr.lbRootU t, a⁆⁆ * (⁅fr.lbRootL t⁻¹, ⁅fr.lbRootU t, a⁆⁆⁻¹ *
        fr.lbPhi t⁻¹ ⁅fr.lbRootL 1, ⁅fr.lbRootU t, a⁆⁆) * ⁅fr.lbRootL t⁻¹, ⁅fr.lbRootU t, a⁆⁆⁻¹ *
      (⁅fr.lbRootL t⁻¹, ⁅fr.lbRootU t, a⁆⁆ * a) := by
    group
  rw [e]
  exact Q.mul_mem h3 h2

variable [(Q.subgroupOf M).Normal]

theorem lbPhiEnd_map_add (hc : Ctx M Q Z B) (t : fr.K) (v w : LBSpace M Q B) :
    lbVec M Q B (fr.lbPhi t (lbLift hc (v + w))) =
      lbVec M Q B (fr.lbPhi t (lbLift hc v)) + lbVec M Q B (fr.lbPhi t (lbLift hc w)) := by
  have hv := lbLift_mem hc v
  have hw := lbLift_mem hc w
  have hvw := lbLift_mem hc (v + w)
  have hm : lbLift hc v * lbLift hc w ∈ QB B ⊓ M := Subgroup.mul_mem _ hv hw
  have h1 : (lbLift hc (v + w))⁻¹ * (lbLift hc v * lbLift hc w) ∈ Q := by
    rw [← lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hvw) (mem_LB_of_mem_QB_inf hm),
      lbVec_mul hc (mem_LB_of_mem_QB_inf hv) (mem_LB_of_mem_QB_inf hw), lbVec_lbLift,
      lbVec_lbLift, lbVec_lbLift]
  have h2 := fr.lbPhi_congr hc t hvw hm h1
  have h3 := fr.lbPhi_mul hc t hv hw
  have hpv := mem_LB_of_mem_QB_inf (Q := Q) (fr.lbPhi_mem hc t hv)
  have hpw := mem_LB_of_mem_QB_inf (Q := Q) (fr.lbPhi_mem hc t hw)
  rw [← lbVec_mul hc hpv hpw, lbVec_eq_iff hc (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc t hvw))
    (Subgroup.mul_mem _ hpv hpw)]
  have e : (fr.lbPhi t (lbLift hc (v + w)))⁻¹ *
      (fr.lbPhi t (lbLift hc v) * fr.lbPhi t (lbLift hc w)) =
      ((fr.lbPhi t (lbLift hc (v + w)))⁻¹ * fr.lbPhi t (lbLift hc v * lbLift hc w)) *
      ((fr.lbPhi t (lbLift hc v) * fr.lbPhi t (lbLift hc w))⁻¹ *
        fr.lbPhi t (lbLift hc v * lbLift hc w))⁻¹ := by
    group
  rw [e]
  exact Q.mul_mem h2 (Q.inv_mem h3)

@[expose] noncomputable def lbPhiEnd (hc : Ctx M Q Z B) (t : fr.K) :
    AddMonoid.End (LBSpace M Q B) :=
  AddMonoidHom.mk' (fun v => lbVec M Q B (fr.lbPhi t (lbLift hc v))) (fr.lbPhiEnd_map_add hc t)

theorem lbPhiEnd_lbVec (hc : Ctx M Q Z B) (t : fr.K) {a : G} (ha : a ∈ QB B ⊓ M) :
    fr.lbPhiEnd hc t (lbVec M Q B a) = lbVec M Q B (fr.lbPhi t a) := by
  show lbVec M Q B (fr.lbPhi t (lbLift hc (lbVec M Q B a))) = lbVec M Q B (fr.lbPhi t a)
  have hl := lbLift_mem hc (lbVec M Q B a)
  have h := (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hl) (mem_LB_of_mem_QB_inf ha)).mp
    (lbVec_lbLift hc _)
  exact (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc t hl))
    (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc t ha))).mpr (fr.lbPhi_congr hc t hl ha h)

theorem lbPhiEnd_add (hc : Ctx M Q Z B) (s t : fr.K) :
    fr.lbPhiEnd hc (s + t) = fr.lbPhiEnd hc s + fr.lbPhiEnd hc t := by
  refine AddMonoidHom.ext fun v => ?_
  have ha := lbLift_mem hc v
  have hs := mem_LB_of_mem_QB_inf (Q := Q) (fr.lbPhi_mem hc s ha)
  have ht := mem_LB_of_mem_QB_inf (Q := Q) (fr.lbPhi_mem hc t ha)
  show lbVec M Q B (fr.lbPhi (s + t) (lbLift hc v)) =
    lbVec M Q B (fr.lbPhi s (lbLift hc v)) + lbVec M Q B (fr.lbPhi t (lbLift hc v))
  rw [← lbVec_mul hc hs ht, eq_comm,
    lbVec_eq_iff hc (Subgroup.mul_mem _ hs ht) (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc _ ha))]
  exact fr.lbPhi_add hc s t ha

theorem lbPhiEnd_one (hc : Ctx M Q Z B) : fr.lbPhiEnd hc 1 = 1 := by
  refine AddMonoidHom.ext fun v => ?_
  have ha := lbLift_mem hc v
  show lbVec M Q B (fr.lbPhi 1 (lbLift hc v)) = v
  rw [lbVec_eq_of_mul_mem hc (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc 1 ha))
    (mem_LB_of_mem_QB_inf ha) (fr.lbPhi_one hc ha), lbVec_lbLift]

theorem lbPhiEnd_inv_mul (hc : Ctx M Q Z B) {t : fr.K} (ht : t ≠ 0) :
    fr.lbPhiEnd hc t⁻¹ * fr.lbPhiEnd hc t = 1 := by
  refine AddMonoidHom.ext fun v => ?_
  have ha := lbLift_mem hc v
  have hp := fr.lbPhi_mem hc t ha
  show fr.lbPhiEnd hc t⁻¹ (lbVec M Q B (fr.lbPhi t (lbLift hc v))) = v
  rw [fr.lbPhiEnd_lbVec hc t⁻¹ hp, lbVec_eq_of_mul_mem hc
    (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc t⁻¹ hp)) (mem_LB_of_mem_QB_inf ha)
    (fr.lbPhi_inv_mul hc ht ha), lbVec_lbLift]

@[expose] noncomputable def lbPhiAdd (hc : Ctx M Q Z B) : fr.K →+ AddMonoid.End (LBSpace M Q B) :=
  AddMonoidHom.mk' (fr.lbPhiEnd hc) (fr.lbPhiEnd_add hc)

@[expose] noncomputable def lbPhiHom (hc : Ctx M Q Z B) : fr.K →+* AddMonoid.End (LBSpace M Q B) :=
  CFSG.LinearGroups.huaRingHom (fr.lbPhiAdd hc) (fr.lbPhiEnd_one hc)
    (fun _ ht => fr.lbPhiEnd_inv_mul hc ht)

theorem lbPhiHom_apply (hc : Ctx M Q Z B) (t : fr.K) : fr.lbPhiHom hc t = fr.lbPhiEnd hc t :=
  rfl

theorem lbPhiHom_add_apply (hc : Ctx M Q Z B) (s t : fr.K) (v : LBSpace M Q B) :
    fr.lbPhiHom hc (s + t) v = fr.lbPhiHom hc s v + fr.lbPhiHom hc t v :=
  congrArg (fun f : AddMonoid.End (LBSpace M Q B) => f v) (map_add (fr.lbPhiHom hc) s t)

theorem lbPhiHom_mul_apply (hc : Ctx M Q Z B) (s t : fr.K) (v : LBSpace M Q B) :
    fr.lbPhiHom hc (s * t) v = fr.lbPhiHom hc s (fr.lbPhiHom hc t v) :=
  congrArg (fun f : AddMonoid.End (LBSpace M Q B) => f v) (map_mul (fr.lbPhiHom hc) s t)

theorem lbPhiHom_one_apply (hc : Ctx M Q Z B) (v : LBSpace M Q B) : fr.lbPhiHom hc 1 v = v :=
  congrArg (fun f : AddMonoid.End (LBSpace M Q B) => f v) (map_one (fr.lbPhiHom hc))

theorem lbPhi_mul_mul (hc : Ctx M Q Z B) (s t : fr.K) {a : G} (ha : a ∈ QB B ⊓ M) :
    (fr.lbPhi (s * t) a)⁻¹ * fr.lbPhi s (fr.lbPhi t a) ∈ Q := by
  have ht := fr.lbPhi_mem hc t ha
  rw [← lbVec_eq_iff hc (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc _ ha))
    (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc s ht)), ← fr.lbPhiEnd_lbVec hc _ ha,
    ← fr.lbPhiEnd_lbVec hc s ht, ← fr.lbPhiEnd_lbVec hc t ha, ← fr.lbPhiHom_apply,
    ← fr.lbPhiHom_apply, ← fr.lbPhiHom_apply, map_mul]
  rfl

theorem lbPhi_conj (hc : Ctx M Q Z B) {k : G} (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkB : k ∈ Subgroup.normalizer (B : Set G)) (t : fr.K) {a : G} (ha : a ∈ QB B ⊓ M) :
    (k * fr.lbPhi t a * k⁻¹)⁻¹ * fr.lbPhi t (k * a * k⁻¹) ∈ Q := by
  obtain ⟨μ, hμ, hup, hlow⟩ := fr.exists_scale hc hkZ hkB
  have hkM : k ∈ M := hc.hyp.normalizer_Z.1 ▸ Subgroup.centralizer_le_normalizer _ hkZ
  have hx := fr.lbRootU_mem t
  have hu := fr.lbRootL_mem 1
  have hkx : k * fr.lbRootU t * k⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hkM) _).mp hx
  have hku : k * fr.lbRootL 1 * k⁻¹ ∈ QB B :=
    (Subgroup.mem_normalizer_iff.mp (hc.normalizer_B_le_normalizer_QB hkB) _).mp hu
  have hφx := hup _ hx t (fr.phi_lbRootU t) (Subgroup.mem_sup_left hkx)
  have hφu := hlow _ hu 1 (fr.phi_lbRootL 1) (Subgroup.mem_sup_right hku)
  rw [mul_one] at hφu
  have hCx := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
    (fr.mem_centralizer_of_phi_eq hc ((fr.phi_lbRootU (μ * t)).trans hφx.symm))
  have hCu := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)
    (fr.mem_centralizer_of_phi_eq hc ((fr.phi_lbRootL μ⁻¹).trans hφu.symm))
  have ha' : k * a * k⁻¹ ∈ QB B ⊓ M :=
    ⟨(Subgroup.mem_normalizer_iff.mp (hc.normalizer_B_le_normalizer_QB hkB) a).mp ha.1,
      M.mul_mem (M.mul_mem hkM ha.2) (M.inv_mem hkM)⟩
  have h1 := hc.comm_Q_PB_congr_left (fr.lbRootU_mem (μ * t)) hkx hCx ha'
  have hN'' := hc.comm_Q_PB_mem (fr.lbRootU_mem (μ * t)) ha'
  have hN' := hc.comm_Q_PB_mem hkx ha'
  have h2 := hc.comm_QB_P_congr_left (fr.lbRootL_mem μ⁻¹) hku hCu hN'
  have h3 := hc.comm_QB_P_congr_right (fr.lbRootL_mem μ⁻¹) hN'' hN' h1
  have h4 : ⁅fr.lbRootL μ⁻¹, ⁅fr.lbRootU (μ * t), k * a * k⁻¹⁆⁆⁻¹ *
      fr.lbPhi μ⁻¹ (fr.lbPhi (μ * t) (k * a * k⁻¹)) ∈ Q := fr.comm_lbRootL_lbPhi hc μ⁻¹ hN''
  have h5 := fr.lbPhi_mul_mul hc μ⁻¹ (μ * t) ha'
  rw [inv_mul_cancel_left₀ hμ] at h5
  have e0 : k * fr.lbPhi t a * k⁻¹ =
      ⁅k * fr.lbRootL 1 * k⁻¹, ⁅k * fr.lbRootU t * k⁻¹, k * a * k⁻¹⁆⁆ := by
    simp only [lbPhi, commutatorElement_def]
    group
  rw [e0]
  have e : (⁅k * fr.lbRootL 1 * k⁻¹, ⁅k * fr.lbRootU t * k⁻¹, k * a * k⁻¹⁆⁆)⁻¹ *
      fr.lbPhi t (k * a * k⁻¹) =
      (⁅fr.lbRootL μ⁻¹, ⁅k * fr.lbRootU t * k⁻¹, k * a * k⁻¹⁆⁆⁻¹ *
        ⁅k * fr.lbRootL 1 * k⁻¹, ⁅k * fr.lbRootU t * k⁻¹, k * a * k⁻¹⁆⁆)⁻¹ *
      (⁅fr.lbRootL μ⁻¹, ⁅fr.lbRootU (μ * t), k * a * k⁻¹⁆⁆⁻¹ *
        ⁅fr.lbRootL μ⁻¹, ⁅k * fr.lbRootU t * k⁻¹, k * a * k⁻¹⁆⁆)⁻¹ *
      (⁅fr.lbRootL μ⁻¹, ⁅fr.lbRootU (μ * t), k * a * k⁻¹⁆⁆⁻¹ *
        fr.lbPhi μ⁻¹ (fr.lbPhi (μ * t) (k * a * k⁻¹))) *
      ((fr.lbPhi t (k * a * k⁻¹))⁻¹ * fr.lbPhi μ⁻¹ (fr.lbPhi (μ * t) (k * a * k⁻¹)))⁻¹ := by
    group
  rw [e]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.inv_mem h2) (Q.inv_mem h3)) h4) (Q.inv_mem h5)

end LBFrame

end CFSG.RankThree.GF2n.Stroth80
