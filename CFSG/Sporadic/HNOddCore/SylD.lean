module

public import CFSG.Sporadic.HNOddCore.SylC
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

open scoped Pointwise in
theorem exists_conj_mem_of_index {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) {e : G} (he : e ^ 2 = 1) :
    ∃ g : G, g * e * g⁻¹ ∈ P := by
  by_cases h1 : e = 1
  · exact ⟨1, by rw [h1, mul_one, inv_one, mul_one]; exact P.one_mem⟩
  have hord : orderOf e = 2 := orderOf_eq_prime he h1
  have hE : IsPGroup 2 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hP.toSylow hidx)
  refine ⟨g, ?_⟩
  have h2 : MulAut.conj g • e ∈ MulAut.conj g • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul e _ _ (hQ (Subgroup.mem_zpowers e))
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h2
  exact h2

theorem fix_of_conj_fix {G α : Type*} [Group G] [MulAction G α] {a b : G} {p : α}
    (h : (b⁻¹ * a * b) • p = p) : a • (b • p) = b • p := by
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at h
  exact h

theorem exists_conj_RV_of_fix
    {y : RH} {p : X} (hp : y • p = p) : ∃ g : RH, g * y * g⁻¹ ∈ RV := by
  obtain ⟨g, hg⟩ := exists_smul_zero p.val p.isLt
  have hx : p = jR g • x0 := by
    apply Fin.ext
    rw [jR_smul]
    exact hg.symm
  refine ⟨(jR g)⁻¹, ?_⟩
  rw [MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, ← hx, hp, hx, inv_smul_smul]

theorem mem_zpowers_t4C
    {z : C4} (hz : z ∈ Subgroup.zpowers t4C) : z = 1 ∨ z = t4C := by
  obtain ⟨k, rfl⟩ := hz
  show t4C ^ k = 1 ∨ t4C ^ k = t4C
  rw [← zpow_mod_orderOf, orderOf_t4C]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem t4C_comm
    (x : C4) : Commute x t4C := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_centralizer_singleton_iff.1 x.2

theorem t4C_sq :
    t4C ^ 2 = 1 := by
  rw [← orderOf_t4C]
  exact pow_orderOf_eq_one t4C

theorem sub_mul_sq {G : Type*} [Group G] {H : Subgroup G} {a b : H} (h : Commute a b)
    (hb : b ^ 2 = 1) : (a * b) ^ 2 = a ^ 2 := by
  rw [h.mul_pow, hb, mul_one]

theorem sub_mul_eq_left {G : Type*} [Group G] {H : Subgroup G} {a b : H} (h : a * b = a) :
    b = 1 :=
  mul_eq_left.1 h

theorem sub_eq_of_inv_mul {G : Type*} [Group G] {H : Subgroup G} {a b : H} (h : a⁻¹ * b = 1) :
    b = a :=
  (inv_mul_eq_one.1 h).symm

theorem sub_eq_mul_of_inv_mul {G : Type*} [Group G] {H : Subgroup G} {a b c : H}
    (h : a⁻¹ * b = c) : b = a * c :=
  inv_mul_eq_iff_eq_mul.1 h

theorem sub_of_one_mul {G : Type*} [Group G] {H : Subgroup G} {a : H} (h : 1 * a = 1) : a = 1 := by
  rwa [one_mul] at h

theorem sub_orderOf_four {G : Type*} [Group G] {H : Subgroup G} {y t : H} (h2 : y ^ 2 = t)
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) : orderOf y = 4 := by
  have h4 : y ^ 2 ^ (1 + 1) = 1 := by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h2, ht]
  have hn : ¬ y ^ 2 ^ 1 = 1 := by rw [pow_one, h2]; exact ht1
  exact orderOf_eq_prime_pow hn h4

theorem mul_t4C_sq
    (x : C4) : (x * t4C) ^ 2 = x ^ 2 := sub_mul_sq (t4C_comm x) t4C_sq

abbrev Pc :
    Subgroup C4 := Subgroup.closure (Set.range (fun i : Fin 14 => gensC i) ∪ {t4C})

theorem gensC_mem_Pc
    (i : ℕ) : gensC i ∈ Pc := by
  by_cases hi : i < 14
  · exact Subgroup.subset_closure (Or.inl ⟨⟨i, hi⟩, rfl⟩)
  · have e : gensC i = 1 := by
      rw [gensC, getElem!_neg _ i (by rw [p_parts.2.2.1]; omega)]
      exact wordVal_nil _
    rw [e]
    exact Pc.one_mem

theorem t4C_mem_Pc :
    t4C ∈ Pc := Subgroup.subset_closure (Or.inr rfl)

theorem liftCF_mem :
    ∀ f r, liftCF f r ∈ Pc
  | 0, _ => Pc.one_mem
  | f + 1, r => by
    unfold liftCF
    split_ifs
    · exact Pc.one_mem
    · exact Pc.mul_mem (gensC_mem_Pc _) (liftCF_mem f _)

theorem liftC_mem
    (r : ℕ) : liftC r ∈ Pc := liftCF_mem r r

theorem map_Pc :
    Pc.map rho4 = Pbar := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | h)
    · show rho4 (gensC i) ∈ Pbar
      rw [← pbarPerm_eq i.2]
      exact pbarPerm_mem i.2
    · rw [Set.mem_singleton_iff] at h
      subst h
      show rho4 t4C ∈ Pbar
      rw [MonoidHom.mem_ker.1 t4C_mem_ker]
      exact Pbar.one_mem
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨gensC i, gensC_mem_Pc i, (pbarPerm_eq i.2).symm⟩

theorem ker_le_Pc :
    rho4.ker ≤ Pc := by
  rw [ker_rho4, Subgroup.zpowers_le]
  exact t4C_mem_Pc

theorem card_Pc :
    Nat.card Pc = 32768 := by
  have h := card_ker_mul_card_map rho4 ker_le_Pc
  rw [map_Pc, card_Pbar, ker_rho4, Nat.card_zpowers, orderOf_t4C] at h
  exact h.symm.trans (by norm_num)

abbrev PR :
    Subgroup RH := Pc.map C4.subtype

theorem card_PR :
    Nat.card PR = 32768 := by
  rw [Subgroup.card_map_of_injective C4.subtype_injective, card_Pc]

theorem card_RH :
    Nat.card RH = 546061824000000 := by
  have h := card_of_split (C := ⊤) (K := ⊤) fun r =>
    ⟨fun _ => (exists_jR_or r).imp (fun ⟨g, hg⟩ => ⟨g, Subgroup.mem_top g, hg⟩)
      (fun ⟨g, hg⟩ => ⟨g, Subgroup.mem_top g, hg⟩), fun _ => Subgroup.mem_top r⟩
  rw [Subgroup.card_top, Subgroup.card_top, card_JH] at h
  exact h.trans (by norm_num)

theorem index_PR :
    PR.index = 16664484375 := by
  have h := PR.card_mul_index
  rw [card_PR, card_RH] at h
  generalize PR.index = x at h ⊢
  omega

theorem PR_isPGroup :
    IsPGroup 2 PR := IsPGroup.of_card (n := 15) (card_PR.trans (by norm_num))

theorem PR_not_dvd :
    ¬ 2 ∣ PR.index := by
  rw [index_PR]
  norm_num

theorem wit_parts :
    pReps.size = 29 ∧ InvData.witRep.size = 39 ∧ InvData.witKer.size = 39 ∧
    InvData.nonRep.size = 9 ∧
    (∀ c < 29, ∀ e < 2, InvData.nonRep.contains pReps[c]! = true ∨ (pReps[c]! = 0 ∧ e = 0) ∨
      ∃ w < 39, InvData.witRep[w]! = pReps[c]! ∧ InvData.witKer[w]! = e) ∧
    (List.range 29).countP (fun c => InvData.nonRep.contains pReps[c]!) = 9 ∧
    (∀ w < 39, pReps.contains InvData.witRep[w]! = true ∧
      InvData.nonRep.contains InvData.witRep[w]! = false ∧ InvData.witKer[w]! < 2 ∧
      ¬ (InvData.witRep[w]! = 0 ∧ InvData.witKer[w]! = 0)) ∧
    (∀ w < 39, ∀ w' < 39, InvData.witRep[w]! = InvData.witRep[w']! →
      InvData.witKer[w]! = InvData.witKer[w']! → w = w') := by
  have h := wit_cert
  unfold witCoverChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, fun c hc e he => ?_, h6, fun w hw => ?_, fun w hw w' hw' hr hk => ?_⟩
  · have := allBelowN_spec (allBelowN_spec h5 hc) he
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      rw [Bool.not_eq_true', ← Bool.not_eq_true, allBelowN_iff] at h
      push Not at h
      obtain ⟨w, hw, hne⟩ := h
      exact ⟨w, hw, by simpa using hne⟩
  · have := allBelowN_spec h7 hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    refine ⟨h1, h2, h3, ?_⟩
    rintro ⟨ha, hb⟩
    rcases h4 with h4 | h4
    · exact h4 ha
    · exact h4 hb
  · have := allBelowN_spec (allBelowN_spec h8 hw) hw'
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at this
    rcases this with h | h | h
    · exact h
    · exact absurd hr h
    · exact absurd hk h

theorem lift_eq
    {r : ℕ} (hr : r < 16384) {y : C4} (hy : rho4 y = ePerm r) :
    y = liftC r ∨ y = liftC r * t4C := by
  have hz : (liftC r)⁻¹ * y ∈ rho4.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, ePerm_eq hr, inv_mul_cancel]
  rw [ker_rho4] at hz
  rcases mem_zpowers_t4C hz with h | h
  · exact Or.inl (sub_eq_of_inv_mul h)
  · exact Or.inr (sub_eq_mul_of_inv_mul h)

theorem liftC_sq_val
    (r : ℕ) (p : X) :
    ((((liftC r ^ 2 : C4) : RH) • p : X) : ℕ) = evalLift gTabs (pinvs hnsData.n gTabs)
      InvData.parRecs r (evalLift gTabs (pinvs hnsData.n gTabs) InvData.parRecs r p) := by
  rw [pow_two, Subgroup.coe_mul, mul_smul, liftC_smul, liftC_smul]

theorem t4_smul_val
    (p : X) : ((((t4C : C4) : RH) • p : X) : ℕ) = t4Tab[(p : ℕ)]! := by
  rw [prep_t4 p, ← permR_jR, permR_apply]
  rfl

theorem nonRep_sq
    {r : ℕ} (h : InvData.nonRep.contains r = true) : liftC r ^ 2 ≠ 1 := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  obtain ⟨p, hp, hne⟩ := lift_parts'.2.2.2.2.2.1 i hi
  rw [getElem!_pos _ i hi, hie] at hne
  intro h1
  apply hne
  have := liftC_sq_val r ⟨p, hp⟩
  rw [h1, Subgroup.coe_one, one_smul] at this
  exact this.symm

theorem liftC_sq_mem
    {r : ℕ} (hr : r < 16384) (h2 : ePerm r ^ 2 = 1) :
    liftC r ^ 2 = 1 ∨ liftC r ^ 2 = t4C := by
  have h : liftC r ^ 2 ∈ rho4.ker := by rw [MonoidHom.mem_ker, map_pow, ← ePerm_eq hr, h2]
  rw [ker_rho4] at h
  exact mem_zpowers_t4C h

theorem rep_sq
    {c : ℕ} (hc : c < 29) (h : InvData.nonRep.contains pReps[c]! = false) :
    liftC pReps[c]! ^ 2 = 1 := by
  rcases liftC_sq_mem (rep_lt hc) (repPerm_sq hc) with h1 | h1
  · exact h1
  · exfalso
    rcases lift_parts'.2.2.2.2.2.2 c hc with h' | ⟨p, hp, hne, hfix⟩
    · rw [h] at h'
      exact Bool.false_ne_true h'
    · apply hne
      have := liftC_sq_val pReps[c]! ⟨p, hp⟩
      rw [h1, t4_smul_val] at this
      exact this.trans hfix

theorem nonRep_orderOf
    {c : ℕ} (hc : c < 29) (h : InvData.nonRep.contains pReps[c]! = true)
    {y : C4} (hy : rho4 y = repPerm c) : orderOf y = 4 := by
  have h2 : y ^ 2 = t4C := by
    have hsq : y ^ 2 = (liftC pReps[c]!) ^ 2 := by
      rcases lift_eq (rep_lt hc) hy with rfl | rfl
      · rfl
      · exact mul_t4C_sq _
    rcases liftC_sq_mem (rep_lt hc) (repPerm_sq hc) with h1 | h1
    · exact absurd h1 (nonRep_sq h)
    · rw [hsq, h1]
  exact sub_orderOf_four h2 t4C_sq t4C_ne_one

@[expose] def witElt
    (w : ℕ) : C4 :=
  if InvData.witKer[w]! = 1 then liftC InvData.witRep[w]! * t4C else liftC InvData.witRep[w]!

theorem witElt_fix
    {w : ℕ} (hw : w < 39) : ∃ p : X, ((witElt w : C4) : RH) • p = p := by
  obtain ⟨hlt, he⟩ := lift_parts'.2.2.2.2.1 w hw
  refine ⟨⟨_, hlt⟩, Fin.ext ?_⟩
  unfold witElt
  split_ifs with h
  · rw [ite_eq_left h] at he
    rw [Subgroup.coe_mul, mul_smul, liftC_smul, t4_smul_val]
    exact he
  · rw [ite_eq_right h] at he
    rw [liftC_smul]
    exact he

theorem witElt_mem
    (w : ℕ) : witElt w ∈ Pc := by
  unfold witElt
  split_ifs
  · exact Pc.mul_mem (liftC_mem _) t4C_mem_Pc
  · exact liftC_mem _

theorem wit_rep
    {w : ℕ} (hw : w < 39) : ∃ c < 29, pReps[c]! = InvData.witRep[w]! := by
  have h := (wit_parts.2.2.2.2.2.2.1 w hw).1
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at h
  obtain ⟨c, hc, hce⟩ := h
  refine ⟨c, by rw [← wit_parts.1]; exact hc, ?_⟩
  rw [getElem!_pos _ c hc, hce]

theorem rho4_witElt
    (w : ℕ) : rho4 (witElt w) = rho4 (liftC InvData.witRep[w]!) := by
  unfold witElt
  split_ifs
  · rw [map_mul, MonoidHom.mem_ker.1 t4C_mem_ker, mul_one]
  · rfl

theorem witElt_sq
    {w : ℕ} (hw : w < 39) : witElt w ^ 2 = 1 := by
  obtain ⟨c, hc, hce⟩ := wit_rep hw
  have h := rep_sq hc (by rw [hce]; exact (wit_parts.2.2.2.2.2.2.1 w hw).2.1)
  rw [hce] at h
  unfold witElt
  split_ifs
  · rw [mul_t4C_sq, h]
  · exact h

theorem ePerm_zero :
    ePerm 0 = 1 := by rw [ePerm_eq (by norm_num), liftC_zero, map_one]

theorem witElt_ne_one
    {w : ℕ} (hw : w < 39) : witElt w ≠ 1 := by
  obtain ⟨c, hc, hce⟩ := wit_rep hw
  obtain ⟨-, -, hk, h00⟩ := wit_parts.2.2.2.2.2.2.1 w hw
  intro h1
  have hρ := congrArg rho4 h1
  rw [rho4_witElt, map_one, ← ePerm_eq (hce ▸ rep_lt hc), ← ePerm_zero] at hρ
  have hr0 := ePerm_injective (hce ▸ rep_lt hc) (by norm_num) hρ
  unfold witElt at h1
  rw [hr0, liftC_zero] at h1
  split_ifs at h1 with h
  · exact t4C_ne_one (sub_of_one_mul h1)
  · exact h00 ⟨hr0, by omega⟩

theorem witElt_rho
    {w : ℕ} (hw : w < 39) : ∃ c : Fin 29, rho4 (witElt w) = repPerm c := by
  obtain ⟨c, hc, hce⟩ := wit_rep hw
  refine ⟨⟨c, hc⟩, ?_⟩
  rw [rho4_witElt, ← hce, ← ePerm_eq (rep_lt hc)]
  rfl

theorem lift_witness
    {c : ℕ} (hc : c < 29) {u : C4} (hu : rho4 u = repPerm c) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) : ∃ w < 39, u = witElt w := by
  have hcov := wit_parts.2.2.2.2.1 c hc
  rcases lift_eq (rep_lt hc) hu with rfl | rfl
  · rcases hcov 0 (by norm_num) with h | ⟨h0, -⟩ | ⟨w, hw, hr, hk⟩
    · exact absurd hu2 (nonRep_sq h)
    · rw [h0, liftC_zero] at hu1
      exact absurd rfl hu1
    · refine ⟨w, hw, ?_⟩
      unfold witElt
      rw [ite_eq_right (by omega), hr]
  · rcases hcov 1 (by norm_num) with h | ⟨-, h0⟩ | ⟨w, hw, hr, hk⟩
    · rw [mul_t4C_sq] at hu2
      exact absurd hu2 (nonRep_sq h)
    · exact absurd h0 (by norm_num)
    · refine ⟨w, hw, ?_⟩
      unfold witElt
      rw [ite_eq_left hk, hr]

theorem witElt_injective
    {w w' : ℕ} (hw : w < 39) (hw' : w' < 39) (h : witElt w = witElt w') :
    w = w' := by
  obtain ⟨c, hc, hce⟩ := wit_rep hw
  obtain ⟨c', hc', hce'⟩ := wit_rep hw'
  have hρ := congrArg rho4 h
  rw [rho4_witElt, rho4_witElt, ← ePerm_eq (hce ▸ rep_lt hc),
    ← ePerm_eq (hce' ▸ rep_lt hc')] at hρ
  have hr := ePerm_injective (hce ▸ rep_lt hc) (hce' ▸ rep_lt hc') hρ
  refine wit_parts.2.2.2.2.2.2.2 w hw w' hw' hr ?_
  have hk := (wit_parts.2.2.2.2.2.2.1 w hw).2.2.1
  have hk' := (wit_parts.2.2.2.2.2.2.1 w' hw').2.2.1
  unfold witElt at h
  rw [hr] at h
  split_ifs at h with h1 h2 h2
  · rw [h1, h2]
  · exact absurd (sub_mul_eq_left h) t4C_ne_one
  · exact absurd (sub_mul_eq_left h.symm) t4C_ne_one
  · omega

abbrev InvLift :
    Type := {u : C4 // u ∈ Pc ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧ ∃ c : Fin 29, rho4 u = repPerm c}

@[expose] def witLift
    (w : Fin 39) : InvLift :=
  ⟨witElt w, witElt_mem w, witElt_sq w.2, witElt_ne_one w.2, witElt_rho w.2⟩

theorem witLift_bijective :
    Function.Bijective witLift := by
  refine ⟨fun w w' h => Fin.ext (witElt_injective w.2 w'.2 (congrArg Subtype.val h)), ?_⟩
  rintro ⟨u, -, hu2, hu1, c, hc⟩
  obtain ⟨w, hw, rfl⟩ := lift_witness c.2 hc hu2 hu1
  exact ⟨⟨w, hw⟩, rfl⟩

theorem card_invLift :
    Nat.card InvLift = 39 := by
  rw [← Nat.card_eq_of_bijective witLift witLift_bijective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem exists_witness
    {y : C4} (hy : y ∈ Pc) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    ∃ x ∈ Pc, ∃ w < 39, x⁻¹ * y * x = witElt w := by
  have hρy : rho4 y ∈ Pbar := by
    rw [← map_Pc]
    exact ⟨y, hy, rfl⟩
  have hρ2 : rho4 y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  obtain ⟨c, ⟨yb, hyb, hybe⟩, -⟩ := classes_Pbar _ hρy hρ2
  obtain ⟨x, hx, rfl⟩ : yb ∈ Pc.map rho4 := by
    rw [map_Pc]
    exact hyb
  refine ⟨x, hx, ?_⟩
  have hu : rho4 (x⁻¹ * y * x) = repPerm c := by
    rw [map_mul, map_mul, map_inv, ← hybe]
    group
  have hu2 : (x⁻¹ * y * x) ^ 2 = 1 := by
    rw [show (x⁻¹ * y * x) ^ 2 = x⁻¹ * y ^ 2 * x by rw [pow_two, pow_two]; group, hy2]
    group
  have hu1 : x⁻¹ * y * x ≠ 1 := by
    intro h
    apply hy1
    rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, h]
    group
  exact lift_witness c.2 hu hu2 hu1

theorem exists_fix_of_mem_Pc
    {u : C4} (hu : u ∈ Pc) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ q : X, (u : RH) • q = q := by
  obtain ⟨x, -, w, hw, hxw⟩ := exists_witness hu hu2 hu1
  obtain ⟨p, hp⟩ := witElt_fix hw
  rw [← hxw, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hp
  exact ⟨_, fix_of_conj_fix hp⟩

theorem exists_fix_R
    {y : RH} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : ∃ q : X, y • q = q := by
  obtain ⟨g, u, hu, hue⟩ := exists_conj_mem_of_index PR_isPGroup PR_not_dvd hy2
  have hu' : (u : RH) = g * y * g⁻¹ := hue
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hu', Subgroup.coe_one, conj_pow, hy2, mul_one, mul_inv_cancel]
  have hu1 : u ≠ 1 := by
    intro h
    apply hy1
    rw [h, Subgroup.coe_one] at hu'
    rw [show y = g⁻¹ * (g * y * g⁻¹) * g by group, ← hu']
    group
  obtain ⟨q, hq⟩ := exists_fix_of_mem_Pc hu hu2 hu1
  rw [hu'] at hq
  exact ⟨g⁻¹ • q, fix_of_conj_fix (by rw [inv_inv]; exact hq)⟩

theorem exists_conj_RV
    {y : RH} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : ∃ g : RH, g * y * g⁻¹ ∈ RV := by
  obtain ⟨q, hq⟩ := exists_fix_R hy2 hy1
  exact exists_conj_RV_of_fix hq

end CFSG.Sporadic.HNOddCore
