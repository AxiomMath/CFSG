module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManySection
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyLarge
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyIndex
public import CFSG.Timmesfeld.Bridge.RootStructWTIModule

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootMany

variable {G : Type} [Group G] {D : Set G} [Finite G] (C : ThinGateCounter G D) {q : ℕ}
  (K : ThinGateCount G D q 2 2) {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
  (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)

include C K ha in
theorem two_le_q : 2 ≤ q := by
  have hD := C.hyp.root
  rw [← K.card_rootGroup a ha]
  refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => hD.ne_one ha ?_
  rw [← Subgroup.mem_bot, ← h]
  exact rootSet_subset_rootGroup D a (mem_rootSet_self ha)

include C K ha in
theorem three_le_ncard_rootLines : 3 ≤ (rootLines D a).ncard := by
  have hq := two_le_q C K ha
  have := K.ncard_rootLines a ha
  have : 4 ≤ q ^ 2 := by nlinarith
  omega

include C K ha hd had hadD hdT in
theorem exists_l2 : ∃ m : ℕ, 2 ≤ m ∧ 2 ^ m = q ^ 2 ∧ nCore D a ≤ lineGroup D a d ∧
    ∃ f : lineGroup D a d →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m),
      Function.Surjective f ∧ f.ker = (nCore D a).subgroupOf (lineGroup D a d) := by
  have hLS := lineSetting_of_counter C
  have hq := two_le_q C K ha
  obtain ⟨m, -, hmcard, hMR, -, ⟨f, hf, hker⟩, -⟩ :=
    rootLinesL2Step G D hLS a ha d hd had hadD hdT (three_le_ncard_rootLines C K ha)
  have hqm : 2 ^ m = q ^ 2 := by have := K.ncard_rootLines a ha; omega
  refine ⟨m, ?_, hqm, hMR, f, hf, hker⟩
  by_contra hm
  have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 4 ≤ q ^ 2 := by nlinarith
  omega

omit [Finite G] in
include C ha hd had hadD hdT in
theorem exists_point : ∃ x ∈ D, Commute a x ∧ a * x ∈ D ∧
    x ∉ rootGroup D a ⊔ rootGroup D d := by
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨L₁, hL₁, hL₁T⟩ := hLS.exists_ne_mem_rootLines ha hT
  obtain ⟨x, hx, hax, haxD, hxT, rfl⟩ := hL₁
  exact ⟨x, hx, hax, haxD, fun h' =>
    hL₁T (hLS.sup_rootGroup_eq_of_mem_sup ha hx hd hax hxT had hadD hdT h')⟩

include C K ha hd had hadD hdT in
theorem card_nCore_eq : Nat.card (nCore D a) = q ^ 3 * Nat.card ↥(nCore D a ⊓ nCore D d) := by
  have hLS := lineSetting_of_counter C
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  obtain ⟨y, hy, hdy, hdyD, hyT⟩ := exists_point C hd ha had.symm hdaD haT
  have h1 := hLS.card_nCore_inf_eq hd ha had.symm hdaD haT hy hdy hdyD hyT
  rw [K.ncard_rootLines d hd, lineN₀_comm, lineN₀] at h1
  have h2 := le_card_nCore_inf_centralizer C K ha hd had hadD hdT
  have h3 := card_le_mul_card_inf_of_le ha hd (nCore_le_transv C ha hd had)
  rw [K.card_rootGroup a ha] at h3
  have e : q ^ 2 + 1 - 1 = q ^ 2 := by omega
  rw [e] at h1
  rw [h1] at h2 h3
  have := le_antisymm h3 h2
  rw [this]
  ring

omit [Finite G] in
@[expose] def nCenter (D : Set G) (a : G) : Subgroup G :=
  nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)

omit [Finite G] in
theorem mem_nCenter {z : G} :
    z ∈ nCenter D a ↔ z ∈ nCore D a ∧ ∀ m ∈ nCore D a, Commute z m := by
  simp only [nCenter, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun m hm => (h2 m hm).symm⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun m hm => (h2 m hm).symm⟩⟩

section Sec

include C K ha hd had hadD hdT

omit [Finite G] K ha hd had hadD hdT in
theorem conj_mem_nCore_of_mem_lineGroup {r : G} (hr : r ∈ lineGroup D a d) {m : G}
    (hm : m ∈ nCore D a) : r * m * r⁻¹ ∈ nCore D a :=
  conj_mem_nCore C.hyp.isClass
    (Subgroup.mem_centralizer_singleton_iff.1 (lineGroup_le_centralizer D a d hr)) hm

omit [Finite G] K ha hd had hadD hdT in
theorem conj_mem_rootGroup_of_mem_lineGroup {r : G} (hr : r ∈ lineGroup D a d) {α : G}
    (hα : α ∈ rootGroup D a) : r * α * r⁻¹ ∈ rootGroup D a :=
  (Subgroup.mem_normalizer_iff.1 ((lineSetting_of_counter C).lineGroup_le_normalizer d hr) α).1
    hα

omit [Finite G] K ha hd had hadD hdT in
theorem conj_mem_nCenter_of_mem_lineGroup {r : G} (hr : r ∈ lineGroup D a d) {z : G}
    (hz : z ∈ nCenter D a) : r * z * r⁻¹ ∈ nCenter D a := by
  rw [mem_nCenter] at hz ⊢
  refine ⟨conj_mem_nCore_of_mem_lineGroup C hr hz.1, fun m hm => ?_⟩
  have hm' : r⁻¹ * m * r⁻¹⁻¹ ∈ nCore D a :=
    conj_mem_nCore_of_mem_lineGroup C (inv_mem hr) hm
  have h := (hz.2 _ hm').map (MulAut.conj r)
  simp only [MulAut.conj_apply] at h
  convert h using 1
  group

omit [Finite G] K hadD hdT in
theorem rootGroup_le_nCore' : rootGroup D a ≤ nCore D a :=
  le_sup_left.trans ((lineSetting_of_counter C).sup_rootGroup_le_nCore ha hd had)

omit [Finite G] K hadD hdT in
theorem rootGroup_le_nCenter : rootGroup D a ≤ nCenter D a := fun _ hα =>
  mem_nCenter.2 ⟨rootGroup_le_nCore' C ha hd had hα, fun _ hm =>
    (commute_of_mem_nCore_of_mem_rootGroup hm hα).symm⟩

theorem secHyp_nCore :
    SecHyp (lineGroup D a d) (nCore D a) (nCore D a) (rootGroup D a) where
  le := rootGroup_le_nCore' C ha hd had
  le_R := (exists_l2 C K ha hd had hadD hdT).choose_spec.2.2.1
  conj_E := fun _ hr _ hm => conj_mem_nCore_of_mem_lineGroup C hr hm
  conj_A := fun _ hr _ hα => conj_mem_rootGroup_of_mem_lineGroup C hr hα
  comm := fun x hx y hy => nCoreCommutatorInRoot_of_hyp C.hyp C.closure a ha x hx y hy
  sq := fun _ hx => mul_self_mem_rootGroup_of_mem_nCore C.hyp C.closure ha hx
  ker := fun k hk e he => nCoreCommutatorInRoot_of_hyp C.hyp C.closure a ha k hk e he

theorem secHyp_nCenter :
    SecHyp (lineGroup D a d) (nCore D a) (nCenter D a) (rootGroup D a) where
  le := rootGroup_le_nCenter C ha hd had
  le_R := fun _ hz => (secHyp_nCore C K ha hd had hadD hdT).le_R (mem_nCenter.1 hz).1
  conj_E := fun _ hr _ hz => conj_mem_nCenter_of_mem_lineGroup C hr hz
  conj_A := fun _ hr _ hα => conj_mem_rootGroup_of_mem_lineGroup C hr hα
  comm := fun x hx y hy => by
    rw [(mem_nCenter.1 hx).2 y (mem_nCenter.1 hy).1, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  sq := fun x hx => mul_self_mem_rootGroup_of_mem_nCore C.hyp C.closure ha (mem_nCenter.1 hx).1
  ker := fun k hk e he => by
    rw [((mem_nCenter.1 he).2 k hk).symm, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem secHyp_nCore_nCenter :
    SecHyp (lineGroup D a d) (nCore D a) (nCore D a) (nCenter D a) where
  le := fun _ hz => (mem_nCenter.1 hz).1
  le_R := (secHyp_nCore C K ha hd had hadD hdT).le_R
  conj_E := (secHyp_nCore C K ha hd had hadD hdT).conj_E
  conj_A := fun _ hr _ hz => conj_mem_nCenter_of_mem_lineGroup C hr hz
  comm := fun x hx y hy => rootGroup_le_nCenter C ha hd had
    ((secHyp_nCore C K ha hd had hadD hdT).comm x hx y hy)
  sq := fun x hx => rootGroup_le_nCenter C ha hd had
    ((secHyp_nCore C K ha hd had hadD hdT).sq x hx)
  ker := fun k hk e he => rootGroup_le_nCenter C ha hd had
    ((secHyp_nCore C K ha hd had hadD hdT).ker k hk e he)

omit K in
theorem card_mul_card_nCenter_le {x : G} (hx : x ∈ D) (hax : Commute a x)
    (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) :
    Nat.card (rootGroup D x) * Nat.card (nCenter D a) ≤ Nat.card (nCore D a) := by
  have hLS := lineSetting_of_counter C
  have hdM : d ∈ nCore D a :=
    hLS.sup_rootGroup_le_nCore ha hd had (right_mem_line hd)
  have hAx : rootGroup D x ≤ nCore D a := hLS.rootGroup_le_nCore ha hax
  have hbot := hLS.rootGroup_inf_centralizer_eq_bot ha hd had hadD hdT hx hax hxT
  have hinter : ∀ g ∈ rootGroup D x, g ∈ nCenter D a → g = 1 := by
    intro g hg hgZ
    have hgd : g ∈ Subgroup.centralizer {d} :=
      Subgroup.mem_centralizer_singleton_iff.2 ((mem_nCenter.1 hgZ).2 d hdM).eq
    have : g ∈ rootGroup D x ⊓ Subgroup.centralizer {d} := ⟨hg, hgd⟩
    rwa [hbot, Subgroup.mem_bot] at this
  let φ : ↥(rootGroup D x) × ↥(nCenter D a) → ↥(nCore D a) :=
    fun p => ⟨p.1 * p.2, mul_mem (hAx p.1.2) (mem_nCenter.1 p.2.2).1⟩
  have hφ : Function.Injective φ := by
    rintro ⟨g, z⟩ ⟨g', z'⟩ h
    have h' : (g : G) * z = g' * z' := congrArg Subtype.val h
    have e1 : (g' : G)⁻¹ * g = z' * (z : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have h1 := hinter _ (mul_mem (inv_mem g'.2) g.2) (by rw [e1]; exact mul_mem z'.2 (inv_mem z.2))
    rw [inv_mul_eq_one] at h1
    have h2 : (z : G) = z' := by
      rw [h1] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective φ hφ

theorem comm_mem_rootGroup_of_mem_nCenter (hM : Nat.card (nCore D a) < q ^ 6) {z : G}
    (hz : z ∈ nCenter D a) {r : G} (hr : r ∈ lineGroup D a d) :
    r * z * r⁻¹ * z⁻¹ ∈ rootGroup D a := by
  by_contra hre
  obtain ⟨m, hm, hqm, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have h1 := (secHyp_nCenter C K ha hd had hadD hdT).sq_mul_card_le f hf hker hm hF hr hz hre
  rw [hqm, K.card_rootGroup a ha] at h1
  obtain ⟨x, hx, hax, -, hxT⟩ := exists_point C ha hd had hadD hdT
  have h2 := card_mul_card_nCenter_le C ha hd had hadD hdT hx hax hxT
  rw [K.card_rootGroup x hx] at h2
  have : q ^ 6 ≤ Nat.card (nCore D a) :=
    calc q ^ 6 = q * ((q ^ 2) ^ 2 * q) := by ring
      _ ≤ q * Nat.card (nCenter D a) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card (nCore D a) := h2
  omega

theorem commute_of_odd (hM : Nat.card (nCore D a) < q ^ 6) {z : G} (hz : z ∈ nCenter D a)
    {g : G} (hg : g ∈ lineGroup D a d) (hodd : Odd (orderOf g)) : Commute g z := by
  have hLS := lineSetting_of_counter C
  obtain ⟨α, hαdef⟩ : ∃ α, α = g * z * g⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hα : α ∈ rootGroup D a := by
    rw [hαdef]
    exact comm_mem_rootGroup_of_mem_nCenter C K ha hd had hadD hdT hM hz hg
  have hgα : Commute g α := hLS.commute_of_mem_lineGroup ha hd had hadD hdT hg hα
  have hconj : g * z * g⁻¹ = α * z := by rw [hαdef]; group
  have key : ∀ k : ℕ, g ^ k * z * (g ^ k)⁻¹ = α ^ k * z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g ^ (k + 1) * z * (g ^ (k + 1))⁻¹ = g * (g ^ k * z * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * (α ^ k * z) * g⁻¹ := by rw [ih]
        _ = (g * α ^ k * g⁻¹) * (g * z * g⁻¹) := by group
        _ = α ^ k * (g * z * g⁻¹) := by rw [(hgα.pow_right k).eq, mul_inv_cancel_right]
        _ = α ^ (k + 1) * z := by rw [hconj, pow_succ, mul_assoc]
  have h1 := key (orderOf g)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
  have hα2 : α * α = 1 := mul_self_eq_one_of_mem_rootGroup C.hyp.root ha hα
  obtain ⟨j, hj⟩ := hodd
  have hα1 : α = 1 := by
    have : α ^ (2 * j + 1) = α := by rw [pow_succ, pow_mul, sq, hα2, one_pow, one_mul]
    rw [← hj, h1] at this
    exact this.symm
  rw [hα1] at hconj
  rw [one_mul] at hconj
  exact (mul_inv_eq_iff_eq_mul.1 hconj)

theorem card_nCenter_lt (hM : Nat.card (nCore D a) < q ^ 6) :
    Nat.card (nCenter D a) < q ^ 2 := by
  obtain ⟨m, hm, hqm, -, f, hf, hker⟩ := exists_l2 C K ha hd had hadD hdT
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨r, hr, e, he, hre⟩ : ∃ r ∈ lineGroup D a d, ∃ e ∈ nCore D a,
      r * e * r⁻¹ * e⁻¹ ∉ nCenter D a := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, c, hc, hxc⟩ := exists_conj_mul_inv_not_mem C ha hd had hadD hdT
      (three_le_ncard_rootLines C K ha)
    exact hxc ((secHyp_nCore C K ha hd had hadD hdT).comm_mem f hf hker hm hF h
      (fun r hr z hz => comm_mem_rootGroup_of_mem_nCenter C K ha hd had hadD hdT hM hz hr) hx hc)
  have h1 := (secHyp_nCore_nCenter C K ha hd had hadD hdT).sq_mul_card_le f hf hker hm hF hr he
    hre
  rw [hqm] at h1
  by_contra h2
  push Not at h2
  have : q ^ 6 ≤ Nat.card (nCore D a) :=
    calc q ^ 6 = (q ^ 2) ^ 2 * q ^ 2 := by ring
      _ ≤ (q ^ 2) ^ 2 * Nat.card (nCenter D a) := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (nCore D a) := h1
  omega

end Sec

end RootMany

end CFSG.Timmesfeld.Bridge
