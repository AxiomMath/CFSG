module

public import CFSG.Monster.B.CTIB.Cosets
public import CFSG.Monster.B.CTIB.CensusCert
public import CFSG.Monster.B.CTIB.OrbitList
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native
  CFSG.Monster.B.CTIB.Kernel CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess

theorem wAct_mul_gen (v : L2) (k k' : Kstab v) : wAct v (k * k') = wAct v k' * wAct v k := by
  have := (KvAct v).map_mul k k'
  have h := congrArg MulOpposite.unop this
  simpa [KvAct] using h

theorem wAct_one_gen (v : L2) : wAct v 1 = 1 := by
  have := (KvAct v).map_one
  have h := congrArg MulOpposite.unop this
  simpa [KvAct] using h

@[expose, reducible] noncomputable def kvLeft (v : L2) : MulAction (Kstab v) (Wv v) where
  smul k w := wAct v k⁻¹ w
  one_smul w := by
    show wAct v 1⁻¹ w = w
    rw [inv_one, wAct_one_gen, Module.End.one_apply]
  mul_smul k k' w := by
    show wAct v (k * k')⁻¹ w = wAct v k⁻¹ (wAct v k'⁻¹ w)
    rw [mul_inv_rev, wAct_mul_gen, Module.End.mul_apply]

attribute [local instance] kvLeft

theorem kvLeft_smul {v : L2} (k : Kstab v) (w : Wv v) : k • w = wAct v k⁻¹ w := rfl

@[expose] noncomputable def vecW (v : ℕ) : WS := psiS (qS v)

theorem psiS_qS_congr {a b : ℕ} (h : Code.bvec 22 a = Code.bvec 22 b) :
    psiS (qS a) = psiS (qS b) := by
  rw [psiS_qS, psiS_qS]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := congrFun h ⟨i, Finset.mem_range.1 hi⟩
  simp only [Code.bvec_apply] at this
  have e : a.testBit i = b.testBit i := by
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  rw [e]

theorem vecW_injOn :
    Set.InjOn vecW (Set.Iio (2 ^ 22)) := by
  intro a ha b hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 22
  · exact testBit_eq_of_psiS h hi
  · have ha' : a < 2 ^ i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb' : b < 2 ^ i := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']

theorem psiS_conj {g y : Sbp} (hg : g.unop ∈ Jbar) (hy : y ∈ Qs) :
    psiS (g⁻¹ * y * g) = wAct _ (jbarToKv ⟨g.unop⁻¹, Jbar.inv_mem hg⟩) (psiS y) := by
  have hc := psiBar_conj (Jbar.inv_mem hg) hy
  have hmem := conj_mem_Qs hg hy
  rw [psiS_of_mem hmem, psiS_of_mem hy]
  have e : (⟨(g⁻¹ * y * g).unop, hmem⟩ : Ebar) =
      ⟨(g.unop⁻¹)⁻¹ * y.unop * g.unop⁻¹, conj_mem_Ebar (Jbar.inv_mem hg) hy⟩ :=
    Subtype.ext (show (g⁻¹ * y * g).unop = (g.unop⁻¹)⁻¹ * y.unop * g.unop⁻¹ by
      rw [unop_mul, unop_mul, unop_inv, inv_inv, mul_assoc])
  rw [e, hc, toAdd_ofAdd]

@[expose] noncomputable def censusGen
    (m : ℕ) : Kstab (phi0 (coordOf rStar)) :=
  if m = 0 then (jbarToKv ⟨(gs 0).unop⁻¹, Jbar.inv_mem gs0_mem_Jbar⟩)⁻¹
  else (jbarToKv ⟨(gs 1).unop⁻¹, Jbar.inv_mem gs1_mem_Jbar⟩)⁻¹

theorem censusGen_smul
    {m : ℕ} (hm : m < 2) (w : WS) :
    censusGen m • w = wAct _ (jbarToKv ⟨(gs m).unop⁻¹, Jbar.inv_mem (gs_mem_Jbar hm)⟩) w := by
  rw [kvLeft_smul, censusGen]
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · rw [ite_eq_left rfl, inv_inv]
  · rw [ite_eq_right (by decide), inv_inv]

theorem bvec_signedImg (rows : List ℕ) (signs i : ℕ) :
    Code.bvec 22 (signedImg rows signs i) = Code.bvec 22 (rows.getD i 0) := by
  funext j
  have h : (signedImg rows signs i).testBit j = (rows.getD i 0).testBit j := by
    rw [signedImg, Nat.testBit_or]
    split_ifs
    · have hj : ¬ 22 = (j : ℕ) := by have := j.2; omega
      rw [Nat.testBit_two_pow, decide_eq_false hj, Bool.or_false]
    · rw [Nat.zero_testBit, Bool.or_false]
  rw [Code.bvec_apply, Code.bvec_apply, h]

theorem vecW_censusAct
    {m : ℕ} (hm : m < 2) (v : ℕ) :
    vecW (censusAct m v) = censusGen m • vecW v := by
  rw [censusGen_smul hm]
  unfold vecW
  rw [← psiS_conj (gs_mem_Jbar hm) (qS_mem v),
    conj_qS (gs_mem_Jbar hm) (fun i hi => conj_gs hm hi)]
  refine psiS_qS_congr ?_
  rw [autApply, bvec_autApplyN, censusAct, Max2.Native.act22, Max2.bvec_actGo, Code.bvec_zero,
    zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [genImgs_getD hj', bvec_signedImg]
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · rw [ite_eq_left (show (0 : ℕ) = 0 from rfl), ite_eq_left (show (0 : ℕ) = 0 from rfl),
      ← r1Rows_eq j hj']
  · rw [ite_eq_right (show ¬ (1 : ℕ) = 0 by decide), ite_eq_right (show ¬ (1 : ℕ) = 0 by decide),
      ← r2Rows_eq j hj']

theorem Jbar_closure_gs :
    Jbar = Subgroup.closure {(gs 0).unop, (gs 1).unop} := by
  have h := (pinned_B_max2_full_native_centralizer_and_two_part betaS_explicit iotaS iotaS_beta).1
  rw [← h, LB, KB, MonoidHom.map_closure, Set.image_pair, Subgroup.unop_closure]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left; exact congrArg unop h
    · right; exact congrArg unop h
  · rintro (h | h)
    · left; rw [h]; rfl
    · right; rw [h]; rfl

theorem jbarToKv_gs0 :
    jbarToKv ⟨(gs 0).unop, gs0_mem_Jbar⟩ = censusGen 0 := by
  rw [censusGen, ite_eq_left rfl, ← map_inv]
  congr 1
  exact Subtype.ext (inv_inv _).symm

theorem jbarToKv_gs1 :
    jbarToKv ⟨(gs 1).unop, gs1_mem_Jbar⟩ = censusGen 1 := by
  rw [censusGen, ite_eq_right (by decide), ← map_inv]
  congr 1
  exact Subtype.ext (inv_inv _).symm

theorem closure_censusGen :
    Subgroup.closure (censusGen '' {m | m < 2}) = ⊤ := by
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, hg⟩ := jbarToKv_surjective k
  rw [← hg]
  have key : ∀ y, y ∈ Subgroup.closure ({(gs 0).unop, (gs 1).unop} : Set Cbar) →
      ∀ hy : y ∈ Jbar, jbarToKv ⟨y, hy⟩ ∈ Subgroup.closure (censusGen '' {m | m < 2}) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      intro hx'
      rcases hx with rfl | hx
      · rw [jbarToKv_gs0]
        exact Subgroup.subset_closure ⟨0, by norm_num, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [jbarToKv_gs1]
        exact Subgroup.subset_closure ⟨1, by norm_num, rfl⟩
    | one =>
      intro _
      rw [show (⟨1, _⟩ : Jbar) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      intro hab
      have ha' : a ∈ Jbar := Jbar_closure_gs ▸ ha
      have hb' : b ∈ Jbar := Jbar_closure_gs ▸ hb
      rw [show (⟨a * b, hab⟩ : Jbar) = ⟨a, ha'⟩ * ⟨b, hb'⟩ from rfl, map_mul]
      exact Subgroup.mul_mem _ (iha ha') (ihb hb')
    | inv a ha iha =>
      intro hai
      have ha' : a ∈ Jbar := Jbar_closure_gs ▸ ha
      rw [show (⟨a⁻¹, hai⟩ : Jbar) = (⟨a, ha'⟩ : Jbar)⁻¹ from rfl, map_inv]
      exact Subgroup.inv_mem _ (iha ha')
  exact key g (Jbar_closure_gs ▸ g.2) g.2

@[expose] def jOrbit (y : Sbp) : Set WS := {w | ∃ g ∈ Jbar.op, w = psiS (g⁻¹ * y * g)}

theorem jOrbit_eq_orbit
    {y : Sbp} (hy : y ∈ Qs) :
    jOrbit y = MulAction.orbit (Subgroup.closure (censusGen '' {m | m < 2})) (psiS y) := by
  rw [closure_censusGen]
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨(jbarToKv ⟨g.unop⁻¹, Jbar.inv_mem hg⟩)⁻¹, Subgroup.mem_top _⟩, ?_⟩
    show (jbarToKv ⟨g.unop⁻¹, Jbar.inv_mem hg⟩)⁻¹ • psiS y = psiS (g⁻¹ * y * g)
    rw [kvLeft_smul, inv_inv, psiS_conj hg hy]
  · rintro ⟨⟨k, -⟩, rfl⟩
    obtain ⟨g', hg'⟩ := jbarToKv_surjective k⁻¹
    refine ⟨op (g'.val⁻¹), Jbar.inv_mem g'.2, ?_⟩
    show k • psiS y = psiS ((op (g'.val⁻¹))⁻¹ * y * op (g'.val⁻¹))
    rw [psiS_conj (g := op (g'.val⁻¹)) (Jbar.inv_mem g'.2) hy, kvLeft_smul, ← hg']
    have e : (⟨(op (g'.val⁻¹)).unop⁻¹, Jbar.inv_mem (Jbar.inv_mem g'.2)⟩ : Jbar) = g' :=
      Subtype.ext (inv_inv g'.val)
    rw [e]

theorem jOrbit_code
    (r : ℕ) :
    jOrbit (qS r) = MulAction.orbit (Subgroup.closure (censusGen '' {m | m < 2})) (vecW r) :=
  jOrbit_eq_orbit (qS_mem r)

theorem mem_jOrbit_self (y : Sbp) : psiS y ∈ jOrbit y :=
  ⟨1, Jbar.op.one_mem, by rw [inv_one, one_mul, mul_one]⟩

theorem jOrbit_eq_of_mem
    {y z : Sbp} (hy : y ∈ Qs) (hz : z ∈ Qs) (h : psiS z ∈ jOrbit y) :
    jOrbit z = jOrbit y := by
  rw [jOrbit_eq_orbit hy] at h
  rw [jOrbit_eq_orbit hy, jOrbit_eq_orbit hz]
  exact MulAction.orbit_eq_iff.2 h

theorem jOrbit_eq_range
    {y : Sbp} (hy : y ∈ Qs) :
    jOrbit y = Set.range fun k : Kstab (phi0 (coordOf rStar)) => wAct _ k (psiS y) := by
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, (psiS_conj hg hy).symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ := jbarToKv_surjective k
    refine ⟨op (g'.val⁻¹), Jbar.inv_mem g'.2, ?_⟩
    rw [psiS_conj (g := op (g'.val⁻¹)) (Jbar.inv_mem g'.2) hy]
    have e : (⟨(op (g'.val⁻¹)).unop⁻¹, Jbar.inv_mem (Jbar.inv_mem g'.2)⟩ : Jbar) = g' :=
      Subtype.ext (inv_inv g'.val)
    rw [e]

@[expose] def censusValid (v : ℕ) : Bool := decide (0 < v) && decide (v < 2 ^ 22)

theorem vecW_zero : vecW 0 = 0 := by rw [vecW, qS_zero, psiS_one]

theorem vecW_ne_zero
    {v : ℕ} (h : censusValid v = true) : vecW v ≠ 0 := by
  simp only [censusValid, Bool.and_eq_true, decide_eq_true_eq] at h
  intro e
  rw [← vecW_zero] at e
  have := vecW_injOn h.2 (show (0 : ℕ) < 2 ^ 22 by norm_num) e
  omega

theorem census_inj
    (a b : ℕ) (ha : censusValid a = true) (hb : censusValid b = true)
    (h : vecW a = vecW b) : a = b := by
  simp only [censusValid, Bool.and_eq_true, decide_eq_true_eq] at ha hb
  exact vecW_injOn ha.2 hb.2 h

theorem census_hact :
    ∀ m < 2, ∀ a, censusValid a = true →
    vecW (censusAct m a) = censusGen m • vecW a := fun _ hm a _ => vecW_censusAct hm a

theorem censusOK_parts :
    (∀ r ∈ censusRecs, OrbitList censusAct 2 censusValid r.1 r.2) ∧
    (censusRecs.map (·.2)).sum = 2 ^ 22 - 1 ∧ chainLt (censusRecs.map (·.1)) = true :=
  ⟨census_orbitLists, by simp [censusRecs], by simp [censusRecs, chainLt]⟩

theorem census_facts
    {r : ℕ × ℕ} (hr : r ∈ censusRecs) :
    censusValid r.1 = true ∧ (jOrbit (qS r.1)).ncard = r.2 ∧
    ∀ w ∈ jOrbit (qS r.1), ∃ n, censusValid n = true ∧ r.1 ≤ n ∧ w = vecW n := by
  obtain ⟨pts, -, hval, horb, hnc, hroot⟩ := orbit_of_orbitList (censusOK_parts.1 r hr)
    census_hact census_inj
  rw [jOrbit_code]
  refine ⟨hroot, hnc, fun w hw => ?_⟩
  rw [horb] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨p, (hval p hp).1, (hval p hp).2, rfl⟩

theorem exists_vecW
    (w : WS) : ∃ n < 2 ^ 22, vecW n = w := by
  obtain ⟨e, he⟩ := psiBar_surjective (Multiplicative.ofAdd w)
  have hm : op e.1 ∈ Qs := e.2
  obtain ⟨n, -, hn⟩ := exists_qS hm
  refine ⟨n % 2 ^ 22, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [vecW, psiS_qS_congr (bvec_mod n), hn, psiS_of_mem hm]
  rw [show (⟨(op e.1).unop, hm⟩ : Ebar) = e from Subtype.ext rfl, he, toAdd_ofAdd]

@[expose] noncomputable def censusList : List (Set WS) :=
  (censusRecs.map (·.1)).map fun n => jOrbit (qS n)

theorem censusList_eq : censusList =
    [jOrbit (qS 1), jOrbit (qS 3), jOrbit (qS 7), jOrbit (qS 17), jOrbit (qS 19)] := rfl

theorem censusList_disjoint :
    censusList.Pairwise Disjoint := by
  have h := orbits_pairwise_disjoint (Subgroup.closure (censusGen '' {m | m < 2}))
    (dec := vecW) (valid := censusValid) census_inj (reps := censusRecs.map (·.1))
    (fun n hn => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
      obtain ⟨h1, -, h3⟩ := census_facts hr
      exact ⟨h1, fun x hx => h3 x (by rw [jOrbit_code]; exact hx)⟩)
    ((chainLt_iff _).1 censusOK_parts.2.2)
  rw [censusList]
  convert h using 2
  funext n
  exact jOrbit_code n

theorem censusList_sum :
    (censusList.map Set.ncard).sum = 2 ^ 22 - 1 := by
  rw [← censusOK_parts.2.1, censusList, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  exact (census_facts hr).2.1

theorem ncard_valid : {n | censusValid n = true}.ncard = 2 ^ 22 - 1 := by
  have e : {n | censusValid n = true} = ↑(Finset.Ioo 0 (2 ^ 22)) := by
    ext n
    simp [censusValid]
  rw [e, Set.ncard_coe_finset, Nat.card_Ioo, Nat.sub_zero]

instance finite_WS :
    Finite WS :=
  Finite.of_surjective (fun n : Fin (2 ^ 22) => vecW n) fun w => by
    obtain ⟨n, hn, h⟩ := exists_vecW w
    exact ⟨⟨n, hn⟩, h⟩

theorem ncard_validImg :
    (vecW '' {n | censusValid n = true}).ncard = 2 ^ 22 - 1 := by
  rw [Set.InjOn.ncard_image (s := {n | censusValid n = true})
    (fun a ha b hb e => census_inj a b ha hb e), ncard_valid]

theorem census_cover
    {w : WS} (hw : w ≠ 0) : ∃ r ∈ censusRecs, w ∈ jOrbit (qS r.1) := by
  obtain ⟨n, hn, rfl⟩ := exists_vecW w
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hw vecW_zero
  have hmem : vecW n ∈ vecW '' {n | censusValid n = true} :=
    ⟨n, by simp only [censusValid, Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq]; omega,
      rfl⟩
  have h := subset_biUnion_of_ncard (Set.toFinite _) censusList (fun o _ => Set.toFinite o)
    (fun o ho => by
      rw [censusList, List.map_map, List.mem_map] at ho
      obtain ⟨r, hr, rfl⟩ := ho
      intro x hx
      obtain ⟨m, hm, -, rfl⟩ := (census_facts hr).2.2 x hx
      exact ⟨m, hm, rfl⟩) censusList_disjoint
    (by rw [censusList_sum, ncard_validImg]) hmem
  simp only [Set.mem_iUnion] at h
  obtain ⟨o, ho, hwo⟩ := h
  rw [censusList, List.map_map, List.mem_map] at ho
  obtain ⟨r, hr, rfl⟩ := ho
  exact ⟨r, hr, hwo⟩

theorem ne_zero_of_mem_census
    {w : WS} {r : ℕ × ℕ} (hr : r ∈ censusRecs)
    (h : w ∈ jOrbit (qS r.1)) : w ≠ 0 := by
  obtain ⟨n, hn, -, rfl⟩ := (census_facts hr).2.2 w h
  exact vecW_ne_zero hn

theorem squaresOK_parts :
    qmul gArr 1 1 = 0 ∧ qmul gArr 3 3 = 0 ∧ qmul gArr 7 7 = 0 ∧ qmul gArr 17 17 = 2 ^ 22 ∧
      qmul gArr 19 19 = 2 ^ 22 := by
  have h := squaresOK_eq_true
  simp only [squaresOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem psiS_inv {e : Sbp} (he : e ∈ Qs) : psiS e⁻¹ = psiS e := by
  have h := psiS_mul (Qs.inv_mem he) he
  rw [inv_mul_cancel, psiS_one] at h
  rw [eq_neg_of_add_eq_zero_left h.symm, ZModModule.neg_eq_self]

theorem psiS_conj_Qs {e y : Sbp} (he : e ∈ Qs) (hy : y ∈ Qs) : psiS (e⁻¹ * y * e) = psiS y := by
  rw [psiS_mul (Qs.mul_mem (Qs.inv_mem he) hy) he, psiS_mul (Qs.inv_mem he) hy, psiS_inv he,
    add_comm (psiS e), add_assoc, ZModModule.add_self, add_zero]

theorem sq_mem {z : Sbp} (hz : z ∈ Qs) : z * z = 1 ∨ z * z = xs := by
  rcases eq_of_psiS_eq (Qs.mul_mem hz hz) Qs.one_mem
      (by rw [psiS_mul hz hz, psiS_one, ZModModule.add_self]) with h | h
  · exact .inl h
  · exact .inr (by rw [h, mul_one])

theorem xs_mul_sq {u : Sbp} (hu : u ∈ Qs) : xs * u * (xs * u) = u * u := by
  calc xs * u * (xs * u) = xs * (u * xs) * u := by group
    _ = xs * (xs * u) * u := by rw [xs_comm hu]
    _ = u * u := by rw [← mul_assoc, xs_mul_self, one_mul]

theorem sq_eq_of_mem_jOrbit
    {y z : Sbp} (hy : y ∈ Qs) (hz : z ∈ Qs) (h : psiS y ∈ jOrbit z) :
    y * y = z * z := by
  obtain ⟨g, hg, hyg⟩ := h
  have hc : g⁻¹ * (z * z) * g = z * z := by
    rcases sq_mem hz with h1 | h1 <;> rw [h1]
    · group
    · exact conj_xs hg
  have hu := conj_mem_Qs hg hz
  have hsq : g⁻¹ * z * g * (g⁻¹ * z * g) = z * z := by
    rw [← hc]
    group
  rcases eq_of_psiS_eq hy hu hyg with h2 | h2
  · rw [h2, hsq]
  · rw [h2, xs_mul_sq hu, hsq]

theorem sq_qS_one
    {r : ℕ} (hr : r = 1 ∨ r = 3 ∨ r = 7) : qS r * qS r = 1 := by
  rw [qS_mul]
  rcases hr with rfl | rfl | rfl
  · rw [squaresOK_parts.1, qS_zero]
  · rw [squaresOK_parts.2.1, qS_zero]
  · rw [squaresOK_parts.2.2.1, qS_zero]

theorem sq_qS_x
    {r : ℕ} (hr : r = 17 ∨ r = 19) : qS r * qS r = xs := by
  rw [qS_mul]
  rcases hr with rfl | rfl
  · rw [squaresOK_parts.2.2.2.1, qS_two_pow_22]
  · rw [squaresOK_parts.2.2.2.2, qS_two_pow_22]

theorem eq_one_or_xs_of_comm {c : Sbp} (hc : c ∈ Qs) (hcomm : ∀ e ∈ Qs, e * c = c * e) :
    c = 1 ∨ c = xs := by
  have hz : c.unop ∈ Subgroup.zpowers xbar := by
    rw [← centralizer_Ebar]
    refine ⟨Ebar_le_Jbar hc, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have e := congrArg unop (hcomm (op y) hy)
    rw [unop_mul, unop_mul, unop_op] at e
    exact e.symm
  rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar).1 hz with h1 | h1
  · exact .inl (unop_injective h1)
  · exact .inr (unop_injective h1)

theorem exists_flip
    {y : Sbp} (hy : y ∈ Qs) (h0 : psiS y ≠ 0) : ∃ e ∈ Qs, e⁻¹ * y * e = xs * y := by
  by_contra hne'
  have hne : ∀ e ∈ Qs, e⁻¹ * y * e ≠ xs * y := fun e he h => hne' ⟨e, he, h⟩
  have hcomm : ∀ e ∈ Qs, e * y = y * e := by
    intro e he
    rcases eq_of_psiS_eq (Qs.mul_mem (Qs.mul_mem (Qs.inv_mem he) hy) he) hy
      (psiS_conj_Qs he hy) with h | h
    · calc e * y = e * (e⁻¹ * y * e) := by rw [h]
        _ = y * e := by group
    · exact absurd h (hne e he)
  rcases eq_one_or_xs_of_comm hy hcomm with rfl | rfl
  · exact h0 psiS_one
  · exact h0 psiS_xs

@[expose] def jClass (t : Sbp) : Set Sbp := {u | ∃ g ∈ Jbar.op, u = g⁻¹ * t * g}

theorem mem_jClass_self (t : Sbp) : t ∈ jClass t := ⟨1, Jbar.op.one_mem, by group⟩

theorem jClass_eq_of_mem {u t : Sbp} (h : u ∈ jClass t) : jClass u = jClass t := by
  obtain ⟨g, hg, rfl⟩ := h
  ext v
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g * k, Jbar.op.mul_mem hg hk, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g⁻¹ * k, Jbar.op.mul_mem (Jbar.op.inv_mem hg) hk, by group⟩

theorem jClass_disjoint
    {a b : Sbp} (h : (jClass a).ncard ≠ (jClass b).ncard) :
    Disjoint (jClass a) (jClass b) :=
  Set.disjoint_left.2 fun _ ha hb => h (by rw [← jClass_eq_of_mem ha, ← jClass_eq_of_mem hb])

theorem jClass_xs : jClass xs = {xs} := by
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact conj_xs hg
  · rintro rfl
    exact mem_jClass_self xs

theorem jClass_eq_fiber
    {y : Sbp} (hy : y ∈ Qs) (h0 : psiS y ≠ 0) :
    jClass y = {u | u ∈ Qs ∧ psiS u ∈ jOrbit y} := by
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨conj_mem_Qs hg hy, g, hg, rfl⟩
  · rintro ⟨hu, g, hg, hpg⟩
    rcases eq_of_psiS_eq hu (conj_mem_Qs hg hy) hpg with rfl | rfl
    · exact ⟨g, hg, rfl⟩
    · obtain ⟨e, he, hey⟩ := exists_flip hy h0
      refine ⟨e * g, Jbar.op.mul_mem (Ebar_le_Jbar he) hg, ?_⟩
      calc xs * (g⁻¹ * y * g) = g⁻¹ * xs * g * (g⁻¹ * y * g) := by rw [conj_xs hg]
        _ = g⁻¹ * (xs * y) * g := by group
        _ = g⁻¹ * (e⁻¹ * y * e) * g := by rw [hey]
        _ = (e * g)⁻¹ * y * (e * g) := by group

@[expose] def codesIn (O : Set WS) : Set ℕ := {m | m < 2 ^ 22 ∧ vecW m ∈ O}

theorem codesIn_finite
    (O : Set WS) : (codesIn O).Finite :=
  (Set.finite_Iio (2 ^ 22)).subset fun _ hm => hm.1

theorem ncard_codesIn
    (O : Set WS) : (codesIn O).ncard = O.ncard := by
  have e : O = vecW '' codesIn O := by
    ext w
    constructor
    · intro hw
      obtain ⟨n, hn, rfl⟩ := exists_vecW w
      exact ⟨n, ⟨hn, hw⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact hn.2
  conv_rhs => rw [e]
  rw [Set.InjOn.ncard_image (vecW_injOn.mono fun _ hm => hm.1)]

theorem psiS_qS_add {m : ℕ} (hm : m < 2 ^ 22) : psiS (qS (m + 2 ^ 22)) = vecW m := by
  rw [vecW]
  refine psiS_qS_congr ?_
  rw [← bvec_mod (m + 2 ^ 22), Nat.add_mod_right, Nat.mod_eq_of_lt hm]

theorem fiber_eq
    (O : Set WS) :
    {u | u ∈ Qs ∧ psiS u ∈ O} = qS '' (codesIn O ∪ (· + 2 ^ 22) '' codesIn O) := by
  ext u
  constructor
  · rintro ⟨hu, hO⟩
    obtain ⟨n, hn, rfl⟩ := exists_qS hu
    by_cases hlt : n < 2 ^ 22
    · exact ⟨n, .inl ⟨hlt, hO⟩, rfl⟩
    · refine ⟨n, .inr ⟨n - 2 ^ 22, ⟨by omega, ?_⟩, Nat.sub_add_cancel (by omega)⟩, rfl⟩
      rw [← psiS_qS_add (by omega), Nat.sub_add_cancel (by omega)]
      exact hO
  · rintro ⟨n, hn | ⟨m, hm, rfl⟩, rfl⟩
    · exact ⟨qS_mem n, hn.2⟩
    · exact ⟨qS_mem _, by rw [psiS_qS_add hm.1]; exact hm.2⟩

theorem ncard_fiber
    (O : Set WS) : {u | u ∈ Qs ∧ psiS u ∈ O}.ncard = 2 * O.ncard := by
  have hsub : codesIn O ∪ (· + 2 ^ 22) '' codesIn O ⊆ Set.Iio (2 ^ 23) := by
    rintro n (hn | ⟨m, hm, rfl⟩)
    · exact lt_trans hn.1 (by norm_num)
    · show m + 2 ^ 22 < 2 ^ 23
      have := hm.1
      omega
  have hdisj : Disjoint (codesIn O) ((· + 2 ^ 22) '' codesIn O) := by
    rw [Set.disjoint_left]
    rintro n hn ⟨m, -, rfl⟩
    have : m + 2 ^ 22 < 2 ^ 22 := hn.1
    omega
  rw [fiber_eq, Set.InjOn.ncard_image (qS_injOn.mono hsub),
    Set.ncard_union_eq hdisj (codesIn_finite O) ((codesIn_finite O).image _),
    Set.ncard_image_of_injective _ (add_left_injective _), ncard_codesIn]
  ring

end CFSG.Monster.B.CTIB
