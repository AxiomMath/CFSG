module

public import CFSG.RankThree.GF2n.Tim79CentBasic

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

private theorem centralizer_L_le_centralizer_W (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G) :=
  Subgroup.centralizer_le (H.L_facts hgV hgQ).1

private theorem V_le_centralizer_L (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) :
    V ≤ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) := by
  obtain ⟨hWL, hLab, -, -⟩ := H.L_facts hgV hgQ
  exact fun v hv => Subgroup.mem_centralizer_iff.mpr fun l hl =>
    hLab l hl v (hWL (Subgroup.mem_sup_left hv))

private theorem mem_normalizer_Q_of_mem_CW (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) {z : G}
    (hz : z ∈ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) :
    z ∈ Subgroup.normalizer (Q : Set G) :=
  (H.toHyp218 hgV hgQ).M_le_normalizer_Q ((H.toHyp218 hgV hgQ).mem_M_of_mem_centralizer hz)

private theorem mem_normalizer_Qg_of_mem_CW (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) {z : G}
    (hz : z ∈ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) :
    z ∈ Subgroup.normalizer ((conjSubgroup g Q : Subgroup G) : Set G) := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  have := h.mem_normalizer_Pg (s := z) fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hz a (h.V1_le_W ha)).symm
  rwa [hPQ] at this

private theorem comm_mem_L_of_RQ_Rg (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {x y : G}
    (hx : x ∈ Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G))
    (hy : y ∈ conjSubgroup g Q ⊓
      Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) :
    ⁅x, y⁆ ∈ Q ⊓ conjSubgroup g Q := by
  have hxg := mem_normalizer_Qg_of_mem_CW H hgV hgQ hx.2
  have hyQ := mem_normalizer_Q_of_mem_CW H hgV hgQ hy.2
  refine ⟨?_, ?_⟩
  · have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hx.1 ((Subgroup.mem_normalizer_iff.mp hyQ _).mp
      (Subgroup.inv_mem _ hx.1))
  · have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxg _).mp hy.1)
      (Subgroup.inv_mem _ hy.1)

theorem Hyp79.conj_mem_C (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {z c : G} (hz : z ∈ Q ⊔ conjSubgroup g Q)
    (hc : c ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    z * c * z⁻¹ ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hz hc.1) (Subgroup.inv_mem _ hz),
    Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have hl' : z⁻¹ * l * z ∈ Q ⊓ conjSubgroup g Q := by
    have := H.L_normal hgV hgQ z⁻¹ (Subgroup.inv_mem _ hz) l hl
    rwa [inv_inv] at this
  have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
  calc l * (z * c * z⁻¹) = z * ((z⁻¹ * l * z) * c) * z⁻¹ := by group
    _ = z * (c * (z⁻¹ * l * z)) * z⁻¹ := by rw [h1]
    _ = z * c * z⁻¹ * l := by group

theorem Hyp79.comm_mem_W_of_mem_inf_centralizer (H : Hyp79 M V Q) {g : G}
    (hgV : conjSubgroup g V ≠ V) (hgQ : conjSubgroup g V ≤ Q) {a b : G}
    (ha : a ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G))
    (hb : b ∈ conjSubgroup g Q ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅a, b⁆ ∈ V ⊔ conjSubgroup g V := by
  have h := H.toHyp218 hgV hgQ
  have hPQ := (h.conclusions H.q4 rfl).2.2.2.1
  obtain ⟨y, hy⟩ := h.exists_isOpp
  have hCLW := centralizer_L_le_centralizer_W H hgV hgQ
  have h1 : ⁅⁅conjSubgroup g Q ⊓
        Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G),
      Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)⁆,
      Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)⁆ = ⊥ := by
    have hle : ⁅conjSubgroup g Q ⊓
          Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G),
        Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)⁆ ≤
        Q ⊓ conjSubgroup g Q := Subgroup.commutator_le.mpr fun b' hb' x hx => by
      rw [← commutatorElement_inv]
      exact inv_mem (comm_mem_L_of_RQ_Rg H hgV hgQ hx ⟨hb'.1, hCLW hb'.2⟩)
    refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun z hz a' ha' => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp ha'.2 z (hle hz)
  have h2 : ⁅⁅Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G),
      Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)⁆,
      conjSubgroup g Q ⊓
        Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)⁆ = ⊥ := by
    have hle : ⁅Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G),
        Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)⁆ ≤ V :=
      Subgroup.commutator_le.mpr fun x hx a' ha' => H.comm_mem_V hx.1 ha'.1
    refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun z hz b' hb' => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hCLW hb'.2) z (Subgroup.mem_sup_left (hle hz))
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hcomm : ∀ r ∈ Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G),
      r * ⁅a, b⁆ = ⁅a, b⁆ * r := by
    intro r hr
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator ha hb) hr
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  have hbQ := mem_normalizer_Q_of_mem_CW H hgV hgQ (hCLW hb.2)
  have hQab : ⁅a, b⁆ ∈ Q := by
    have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ha.1 ((Subgroup.mem_normalizer_iff.mp hbQ _).mp
      (Subgroup.inv_mem _ ha.1))
  have hD := h.inf_centralizer_D hy
  rw [hPQ] at hD
  rw [← hD]
  exact ⟨hQab, Subgroup.mem_centralizer_iff.mpr hcomm⟩

private theorem exists_mul_of_mem_R (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {r : G}
    (hr : r ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G)) :
    ∃ x ∈ Q ⊓ Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G),
      ∃ y ∈ conjSubgroup g Q ⊓
        Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G), r = x * y := by
  rw [H.centralizer_W_eq_sup hgV hgQ] at hr
  refine exists_mul_of_mem_sup (fun y hy => ?_) hr
  exact mem_normalizer_inf (mem_normalizer_Q_of_mem_CW H hgV hgQ hy.2)
    (Subgroup.le_normalizer hy.2)

theorem Hyp79.exists_mul_of_mem_C (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {r : G}
    (hr : r ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ∃ a ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G),
      ∃ b ∈ conjSubgroup g Q ⊓
        Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G), r = a * b := by
  have hCLW := centralizer_L_le_centralizer_W H hgV hgQ
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_R H hgV hgQ ⟨hr.1, hCLW hr.2⟩
  have hVU : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hgV
  have key : ∀ l ∈ Q ⊓ conjSubgroup g Q, ⁅x, l⁆ = 1 ∧ ⁅y, l⁆ = 1 := by
    intro l hl
    have hu : ⁅y, l⁆ ∈ conjSubgroup g V := H.comm_mem_conj g hy.1 hl.2
    have hv : ⁅x, l⁆ ∈ V := H.comm_mem_V hx.1 hl.1
    have hxu : x * ⁅y, l⁆ = ⁅y, l⁆ * x :=
      (Subgroup.mem_centralizer_iff.mp hx.2 _ (Subgroup.mem_sup_right hu)).symm
    have hrl : l * (x * y) = (x * y) * l := Subgroup.mem_centralizer_iff.mp hr.2 l hl
    have e1 : x * y * l * (x * y)⁻¹ * l⁻¹ = (x * ⁅y, l⁆ * x⁻¹) * ⁅x, l⁆ := by
      simp only [commutatorElement_def]; group
    have e2 : x * ⁅y, l⁆ * x⁻¹ = ⁅y, l⁆ := by rw [hxu]; group
    have e3 : x * y * l * (x * y)⁻¹ * l⁻¹ = 1 := by rw [← hrl]; group
    rw [e2, e3] at e1
    have hxl : ⁅x, l⁆ = ⁅y, l⁆⁻¹ := eq_inv_of_mul_eq_one_right e1.symm
    have h0 : ⁅x, l⁆ ∈ V ⊓ conjSubgroup g V := ⟨hv, hxl ▸ Subgroup.inv_mem _ hu⟩
    rw [hVU, Subgroup.mem_bot] at h0
    refine ⟨h0, ?_⟩
    exact inv_eq_one.mp (hxl.symm.trans h0)
  exact ⟨x, ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (commutatorElement_eq_one_iff_mul_comm.mp (key l hl).1).symm⟩, y,
    ⟨hy.1, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (commutatorElement_eq_one_iff_mul_comm.mp (key l hl).2).symm⟩, rfl⟩

private theorem comm_mem_W_C₁_C (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {a c' : G}
    (ha : a ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G))
    (hc' : c' ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅a, c'⁆ ∈ V ⊔ conjSubgroup g V := by
  obtain ⟨a', ha', b', hb', rfl⟩ := Hyp79.exists_mul_of_mem_C H hgV hgQ hc'
  have e : ⁅a, a' * b'⁆ = ⁅a, a'⁆ * (a' * ⁅a, b'⁆ * a'⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hW : a' * ⁅a, b'⁆ * a'⁻¹ ∈ V ⊔ conjSubgroup g V :=
    (Subgroup.mem_normalizer_iff.mp
      (H.sup_le_normalizer_W hgV hgQ (Subgroup.mem_sup_left ha'.1)) _).mp
      (Hyp79.comm_mem_W_of_mem_inf_centralizer H hgV hgQ ha hb')
  exact mul_mem (Subgroup.mem_sup_left (H.comm_mem_V ha.1 ha'.1)) hW

private theorem comm_mem_W_C₂_C (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {b c' : G}
    (hb : b ∈ conjSubgroup g Q ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G))
    (hc' : c' ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅b, c'⁆ ∈ V ⊔ conjSubgroup g V := by
  obtain ⟨a', ha', b', hb', rfl⟩ := Hyp79.exists_mul_of_mem_C H hgV hgQ hc'
  have e : ⁅b, a' * b'⁆ = ⁅b, a'⁆ * (a' * ⁅b, b'⁆ * a'⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅b, a'⁆ ∈ V ⊔ conjSubgroup g V := by
    rw [← commutatorElement_inv]
    exact inv_mem (Hyp79.comm_mem_W_of_mem_inf_centralizer H hgV hgQ ha' hb)
  have h2 : a' * ⁅b, b'⁆ * a'⁻¹ ∈ V ⊔ conjSubgroup g V :=
    (Subgroup.mem_normalizer_iff.mp
      (H.sup_le_normalizer_W hgV hgQ (Subgroup.mem_sup_left ha'.1)) _).mp
      (Subgroup.mem_sup_right (H.comm_mem_conj g hb.1 hb'.1))
  exact mul_mem h1 h2

theorem Hyp79.comm_mem_W_of_mem_C (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {c c' : G}
    (hc : c ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G))
    (hc' : c' ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅c, c'⁆ ∈ V ⊔ conjSubgroup g V := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Hyp79.exists_mul_of_mem_C H hgV hgQ hc
  have e : ⁅a * b, c'⁆ = a * ⁅b, c'⁆ * a⁻¹ * ⁅a, c'⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : a * ⁅b, c'⁆ * a⁻¹ ∈ V ⊔ conjSubgroup g V :=
    (Subgroup.mem_normalizer_iff.mp
      (H.sup_le_normalizer_W hgV hgQ (Subgroup.mem_sup_left ha.1)) _).mp
      (comm_mem_W_C₂_C H hgV hgQ hb hc')
  exact mul_mem h1 (comm_mem_W_C₁_C H hgV hgQ ha hc')

theorem Hyp79.comm_mem_L_of_mem_CW (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {r c : G}
    (hr : r ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((V ⊔ conjSubgroup g V : Subgroup G) : Set G))
    (hc : c ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅r, c⁆ ∈ Q ⊓ conjSubgroup g Q := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_R H hgV hgQ hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Hyp79.exists_mul_of_mem_C H hgV hgQ hc
  obtain ⟨hWL, -, -, -⟩ := H.L_facts hgV hgQ
  have hCLW := centralizer_L_le_centralizer_W H hgV hgQ
  have hLn := H.L_normal hgV hgQ
  have hxab : ⁅x, a * b⁆ ∈ Q ⊓ conjSubgroup g Q := by
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hWL (Subgroup.mem_sup_left (H.comm_mem_V hx.1 ha.1)))
      (hLn a (Subgroup.mem_sup_left ha.1) _
        (comm_mem_L_of_RQ_Rg H hgV hgQ hx ⟨hb.1, hCLW hb.2⟩))
  have hyab : ⁅y, a * b⁆ ∈ Q ⊓ conjSubgroup g Q := by
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅y, a⁆ ∈ Q ⊓ conjSubgroup g Q := by
      rw [← commutatorElement_inv]
      exact inv_mem (comm_mem_L_of_RQ_Rg H hgV hgQ ⟨ha.1, hCLW ha.2⟩ hy)
    have h2 : ⁅y, b⁆ ∈ Q ⊓ conjSubgroup g Q :=
      hWL (Subgroup.mem_sup_right (H.comm_mem_conj g hy.1 hb.1))
    rw [e]
    exact mul_mem h1 (hLn a (Subgroup.mem_sup_left ha.1) _ h2)
  have e : ⁅x * y, a * b⁆ = x * ⁅y, a * b⁆ * x⁻¹ * ⁅x, a * b⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (hLn x (Subgroup.mem_sup_left hx.1) _ hyab) hxab

theorem Hyp79.comm_mem_inf_centralizer (H : Hyp79 M V Q) {g : G} (hgV : conjSubgroup g V ≠ V)
    (hgQ : conjSubgroup g V ≤ Q) {x c : G} (hx : x ∈ Q)
    (hc : c ∈ (Q ⊔ conjSubgroup g Q) ⊓
      Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G)) :
    ⁅x, c⁆ ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Hyp79.exists_mul_of_mem_C H hgV hgQ hc
  have hCLW := centralizer_L_le_centralizer_W H hgV hgQ
  have hbQ := mem_normalizer_Q_of_mem_CW H hgV hgQ (hCLW hb.2)
  have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅x, a⁆ ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) :=
    ⟨H.V_le_Q (H.comm_mem_V hx ha.1), V_le_centralizer_L H hgV hgQ (H.comm_mem_V hx ha.1)⟩
  have h2 : ⁅x, b⁆ ∈ Q ⊓ Subgroup.centralizer ((Q ⊓ conjSubgroup g Q : Subgroup G) : Set G) := by
    refine ⟨?_, ?_⟩
    · have e' : ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
      rw [e']
      exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp hbQ _).mp (inv_mem hx))
    · have e' : ⁅x, b⁆ = (x * b * x⁻¹) * b⁻¹ := by rw [commutatorElement_def]
      rw [e']
      exact Subgroup.mul_mem _ (Hyp79.conj_mem_C H hgV hgQ (Subgroup.mem_sup_left hx)
        ⟨Subgroup.mem_sup_right hb.1, hb.2⟩).2 (Subgroup.inv_mem _ hb.2)
  exact Subgroup.mul_mem _ h1 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha h2)
    (Subgroup.inv_mem _ ha))

end CFSG.RankThree.GF2n.Tim79
