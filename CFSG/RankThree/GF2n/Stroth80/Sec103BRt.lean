module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Three
public import CFSG.RankThree.GF2n.Stroth80.Sec10ConjFix

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem comm_conj_inv_eq {t j h : G} (hjt : Commute j t)
    (hjZ : ∀ z ∈ Z, j * z * j⁻¹ = z) (hZ : ⁅t, h⁆ ∈ Z) :
    ⁅t, j⁻¹ * h * j⁆ = ⁅t, h⁆ := by
  have hjZ' : j⁻¹ * ⁅t, h⁆ * j = ⁅t, h⁆ := by
    calc j⁻¹ * ⁅t, h⁆ * j = j⁻¹ * (j * ⁅t, h⁆ * j⁻¹) * j := by rw [hjZ _ hZ]
      _ = ⁅t, h⁆ := by group
  calc ⁅t, j⁻¹ * h * j⁆ = (t * j⁻¹) * h * (j * t⁻¹) * (j⁻¹ * h⁻¹ * j) := by
        simp only [commutatorElement_def]; group
    _ = (j⁻¹ * t) * h * (t⁻¹ * j) * (j⁻¹ * h⁻¹ * j) := by
        rw [hjt.inv_left.eq, hjt.inv_right.eq]
    _ = j⁻¹ * ⁅t, h⁆ * j := by simp only [commutatorElement_def]; group
    _ = ⁅t, h⁆ := hjZ'

private theorem commute_conj_mul_inv (hc : Ctx M Q Z B) {t j h : G} (htM : t ∈ M)
    (hhQ : h ∈ Q) (hjM : j ∈ M) (hjt : Commute j t)
    (hcomm' : ⁅t, j⁻¹ * h * j⁆ = ⁅t, h⁆) (hZ : ⁅t, h⁆ ∈ Z) :
    (j⁻¹ * h * j) * h⁻¹ * t = t * ((j⁻¹ * h * j) * h⁻¹) := by
  set v := ⁅t, h⁆ with hv
  have hvZ : v ∈ Z := hZ
  have hv2 : v * v = 1 := by rw [← pow_two]; exact Z_sq hc.hyp hvZ
  have h'Q : j⁻¹ * h * j ∈ Q := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hjM)) h).mp hhQ
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have ht_hi : ⁅t, h⁻¹⁆ = v := by
    rw [commutatorElement_inv_right, ← commutatorElement_inv, hvinv]
    calc h⁻¹ * v * h = (v * h⁻¹) * h := by
          exact congrArg (· * h) (Z_central hc.hyp hvZ (Q.inv_mem hhQ)).symm
      _ = v := by group
  have hv_h' : (j⁻¹ * h * j) * v = v * (j⁻¹ * h * j) :=
    (Z_central hc.hyp hvZ h'Q).symm
  have e : ⁅t, (j⁻¹ * h * j) * h⁻¹⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj, hcomm', ht_hi]
    calc v * (j⁻¹ * h * j) * v * (j⁻¹ * h * j)⁻¹ =
        v * ((j⁻¹ * h * j) * v) * (j⁻¹ * h * j)⁻¹ := by group
      _ = v * (v * (j⁻¹ * h * j)) * (j⁻¹ * h * j)⁻¹ := by rw [hv_h']
      _ = (v * v) * ((j⁻¹ * h * j) * (j⁻¹ * h * j)⁻¹) := by group
      _ = 1 := by rw [hv2]; group
  exact (commutatorElement_eq_one_iff_mul_comm.mp e).symm

private theorem mem_inf_centralizer_conj_mul_inv (hc : Ctx M Q Z B) {t j h : G}
    (htM : t ∈ M) (hjM : j ∈ M) (hjt : Commute j t)
    (hjZ : ∀ z ∈ Z, j * z * j⁻¹ = z) (hQ1 : h ∈ Q1 hc t) :
    (j⁻¹ * h * j) * h⁻¹ ∈ Q ⊓ Subgroup.centralizer ({t} : Set G) := by
  have hhQ : h ∈ Q := ((hc.mem_Q1_iff htM).mp hQ1).1
  have hZ : ⁅t, h⁆ ∈ Z := ((hc.mem_Q1_iff htM).mp hQ1).2
  have h'Q : j⁻¹ * h * j ∈ Q := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hjM)) h).mp hhQ
  have hcomm' : ⁅t, j⁻¹ * h * j⁆ = ⁅t, h⁆ := comm_conj_inv_eq hjt hjZ hZ
  exact ⟨Q.mul_mem h'Q (Q.inv_mem hhQ),
    Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_conj_mul_inv hc htM hhQ hjM hjt hcomm' hZ)⟩

private theorem comm_conj_eq (hc : Ctx M Q Z B) {t j a h : G} (htM : t ∈ M) (hjM : j ∈ M)
    (hjt : Commute j t) (hjZ : ∀ z ∈ Z, j * z * j⁻¹ = z) (haQ : a ∈ Q)
    (hak : ∀ k ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), k * a = a * k)
    (hQ1 : h ∈ Q1 hc t) : ⁅h, j * a * j⁻¹⁆ = ⁅h, a⁆ := by
  have hhQ : h ∈ Q := ((hc.mem_Q1_iff htM).mp hQ1).1
  set k := (j⁻¹ * h * j) * h⁻¹ with hk
  have hkC : k ∈ Q ⊓ Subgroup.centralizer ({t} : Set G) :=
    mem_inf_centralizer_conj_mul_inv hc htM hjM hjt hjZ hQ1
  have hka : ⁅k, a⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hak k hkC)
  have h2 : ⁅j⁻¹ * h * j, a⁆ = k * ⁅h, a⁆ * k⁻¹ := by
    have hkh : j⁻¹ * h * j = k * h := by rw [hk]; group
    rw [hkh, commutatorElement_mul_left_eq_conj_mul, hka, mul_one]
  have hZha : ⁅h, a⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hhQ haQ
  have hjkQ : j * k * j⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hjM) k).mp hkC.1
  have h4 : j * (k * ⁅h, a⁆ * k⁻¹) * j⁻¹ = ⁅h, a⁆ := by
    have e : j * (k * ⁅h, a⁆ * k⁻¹) * j⁻¹ =
        (j * k * j⁻¹) * (j * ⁅h, a⁆ * j⁻¹) * (j * k * j⁻¹)⁻¹ := by group
    rw [e, hjZ _ hZha, ← Z_central hc.hyp hZha hjkQ]
    group
  calc ⁅h, j * a * j⁻¹⁆ = j * ⁅j⁻¹ * h * j, a⁆ * j⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = j * (k * ⁅h, a⁆ * k⁻¹) * j⁻¹ := by rw [h2]
    _ = ⁅h, a⁆ := h4

private theorem inv_mul_conj_mul_commute {a j t : G} (hjt : Commute j t) (hat : Commute a t) :
    a⁻¹ * (j * a * j⁻¹) * t = t * (a⁻¹ * (j * a * j⁻¹)) := by
  have hja_t : j * a * j⁻¹ * t = t * (j * a * j⁻¹) := by
    calc j * a * j⁻¹ * t = j * a * (j⁻¹ * t) := by group
      _ = j * a * (t * j⁻¹) := by rw [hjt.inv_left.eq]
      _ = j * (a * t) * j⁻¹ := by group
      _ = j * (t * a) * j⁻¹ := by rw [hat]
      _ = (j * t) * a * j⁻¹ := by group
      _ = (t * j) * a * j⁻¹ := by rw [hjt]
      _ = t * (j * a * j⁻¹) := by group
  calc a⁻¹ * (j * a * j⁻¹) * t = a⁻¹ * (j * a * j⁻¹ * t) := by group
    _ = a⁻¹ * (t * (j * a * j⁻¹)) := by rw [hja_t]
    _ = (a⁻¹ * t) * (j * a * j⁻¹) := by group
    _ = (t * a⁻¹) * (j * a * j⁻¹) := by rw [hat.inv_left.eq]
    _ = t * (a⁻¹ * (j * a * j⁻¹)) := by group

private theorem mem_Ut_of_centralizes_Q1 (hc : Ctx M Q Z B) {t d : G} (ht : t ∈ LB M Q B)
    (hdQ1 : d ∈ Q1 hc t) (hcent : ∀ h ∈ Q1 hc t, h * d = d * h) :
    d ∈ Ut Q Z t := by
  rw [hc.Ut_eq_center_Q1 ht]
  refine Subgroup.mem_map.mpr ⟨⟨d, hdQ1⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  exact Subtype.ext (hcent h h.2)

theorem Ctx.comm_mem_Ut_of_commute (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {j : G}
    (hj : j ∈ H0 M Z) (hjt : j * t = t * j) {a : G} (haQ : a ∈ Q) (hat : a * t = t * a)
    (haC : a ∈ Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G))) :
    ⁅j, a⁆ ∈ Ut Q Z t := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hjM : j ∈ M := hj.1
  have hjtc : Commute j t := hjt
  have hatc : Commute a t := hat
  have hjZ : ∀ z ∈ Z, j * z * j⁻¹ = z := fun z hz => by
    have h := Subgroup.mem_centralizer_iff.mp hj.2 z hz
    rw [← h]; group
  have haQ1 : a ∈ Q1 hc t := (hc.mem_Q1_iff htM).mpr ⟨haQ, by
    have h1 : ⁅t, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hat.symm
    rw [h1]
    exact Z.one_mem⟩
  set d : G := a⁻¹ * (j * a * j⁻¹) with hd
  have hjaQ : j * a * j⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hjM) a).mp haQ
  have hdQ : d ∈ Q := Q.mul_mem (Q.inv_mem haQ) hjaQ
  have hdt : d * t = t * d := by
    rw [hd]
    exact inv_mul_conj_mul_commute hjtc hatc
  have hdQ1 : d ∈ Q1 hc t := (hc.mem_Q1_iff htM).mpr ⟨hdQ, by
    have h1 : ⁅t, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hdt.symm
    rw [h1]; exact Z.one_mem⟩
  have hcent : ∀ h : G, h ∈ Q1 hc t → h * d = d * h := fun h hh => by
    have h := mul_comm_of_comm_eq (comm_conj_eq hc htM hjM hjtc hjZ haQ
      (fun k hk => Subgroup.mem_centralizer_iff.mp haC.2 k hk) hh)
    rwa [← hd] at h
  have hdU : d ∈ Ut Q Z t := mem_Ut_of_centralizes_Q1 hc ht hdQ1 hcent
  have hda : a * d * a⁻¹ = d := by
    calc a * d * a⁻¹ = (d * a) * a⁻¹ := by rw [hcent a haQ1]
      _ = d := by group
  have hja : ⁅j, a⁆ = d := by
    calc ⁅j, a⁆ = a * d * a⁻¹ := by
          rw [hd]; simp only [commutatorElement_def]; group
      _ = d := hda
  rw [hja]
  exact hdU

private theorem Good101.exists_split_Rt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    ∃ j ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∃ q ∈ Q, j * q = r := by
  have h102 : Rt M (LB M Q B) t =
      Q ⊔ (Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)) :=
    stroth_10_2 (stroth_5_7 h34 hspread) G M Q Z B hc n t H ht
  have hr' : r ∈ (Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)) ⊔ Q := by
    rw [sup_comm, ← h102]
    exact hr
  exact exists_mul_of_mem_sup_of_le_normalizer
    (fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t (Subgroup.mem_inf.mp hx).1)) hr'

private theorem comm_mem_inf_QB_inf_Ut (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {j a : G} (hjR : j ∈ Rt M (LB M Q B) t)
    (hjt : Commute j t) (ha : a ∈ Q ⊓ QB Y) :
    ⁅j, a⁆ ∈ Q ⊓ QB Y ⊓ Ut Q Z t := by
  have hjH0 : j ∈ H0 M Z := hc.Rt_le_H0 t hjR
  have hjM : j ∈ M := hjH0.1
  have hat : a * t = t * a := (Sit.QB_comm_X hs hs.mem ha.2).symm
  have haC : a ∈ Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)) :=
    ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      ((smith_1_13 hs).2.2.2.2 a ha y hy).symm⟩
  have hUt : ⁅j, a⁆ ∈ Ut Q Z t :=
    hc.comm_mem_Ut_of_commute ht hjH0 hjt ha.1 hat haC
  obtain ⟨g, hg⟩ := hs.conj
  have htYj : t ∈ conjSubgroup j Y := mem_conjSubgroup.mpr (by
    rw [show j⁻¹ * t * j = t from by rw [hjt.inv_left.eq]; group]
    exact hs.mem)
  have hYj : conjSubgroup j Y = Y := by
    rw [hg, ← conjSubgroup_mul] at htYj ⊢
    exact (conjSubgroup_eq_of_mem_ne_one hs.hyp hs.ne_one (hg ▸ hs.mem) htYj).symm
  have hQBj : conjSubgroup j (QB Y) = QB Y := by
    rw [← QB_conj, hYj]
  have hjaQB : j * a * j⁻¹ ∈ QB Y := by
    have hmem : j * a * j⁻¹ ∈ conjSubgroup j (QB Y) := mem_conjSubgroup.mpr (by
      rw [show j⁻¹ * (j * a * j⁻¹) * j = a by group]
      exact ha.2)
    rwa [hQBj] at hmem
  have hjaQ : j * a * j⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hjM) a).mp ha.1
  exact ⟨⟨Q.mul_mem hjaQ (Q.inv_mem ha.1),
    (QB Y).mul_mem hjaQB ((QB Y).inv_mem ha.2)⟩, hUt⟩

theorem Good101.comm_Rt_mem_Vt_of_not_caseA (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hB : ¬ CaseA Q Z t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {a : G} (ha : a ∈ Q ⊓ QB Y) :
    ⁅r, a⁆ ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨j, hj, q, hq, hqj⟩ := ht.exists_split_Rt h34 hspread H hr
  have hja : ⁅j, a⁆ ∈ Q ⊓ QB Y ⊓ Ut Q Z t :=
    comm_mem_inf_QB_inf_Ut hc ht.mem_LB hs hj.1
      (Subgroup.mem_centralizer_singleton_iff.mp hj.2) ha
  have hjaV := Good101.inf_QB_inf_Ut_le_Vt_of_not_caseA h34 hspread H ht hs hB hja
  have hqZ : ⁅q, a⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hq ha.1
  have hjH0 : j ∈ H0 M Z := hc.Rt_le_H0 t hj.1
  have hjZ : j * ⁅q, a⁆ * j⁻¹ = ⁅q, a⁆ := by
    have h := Subgroup.mem_centralizer_iff.mp hjH0.2 ⁅q, a⁆ hqZ
    rw [← h]; group
  have e : ⁅r, a⁆ = ⁅q, a⁆ * ⁅j, a⁆ := by
    rw [← hqj, commutatorElement_mul_left_eq_conj_mul, hjZ]
  rw [e]
  exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hqZ) hjaV

end CFSG.RankThree.GF2n.Stroth80
