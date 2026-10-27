module

public import CFSG.Quasithin.Recognition.M12AscGlobal
public import CFSG.Quasithin.Recognition.M12AscHFacts

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

structure AscModel (z : G) where
  φ : ↥(ascH z) ≃* ascHModel
  hz : (φ ⟨z, z_mem_ascH z⟩ : Equiv.Perm (Fin 12)) = ascHImg 0 * ascHImg 0

open CFSG.GH74.M12 (Asc03Hyp)

theorem asc_z_sq (hyp : Asc03Hyp G z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [hyp.orderTwo, pow_two] at this

theorem asc_z_ne_one (hyp : Asc03Hyp G z) : z ≠ 1 := by
  intro h
  have := hyp.orderTwo
  rw [h, orderOf_one] at this
  omega

theorem asc_conj_sq (hyp : Asc03Hyp G z) (g : G) : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
  calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [asc_z_sq hyp]; group

theorem asc_conj_ne_one (hyp : Asc03Hyp G z) (g : G) : g * z * g⁻¹ ≠ 1 := by
  intro h1
  apply asc_z_ne_one hyp
  have := congrArg (fun w => g⁻¹ * w * g) h1
  simpa [mul_assoc] using this

namespace AscModel

variable (m : AscModel z)

include m

open Classical in
noncomputable def tb (g : G) : List (Fin 12) :=
  if h : g ∈ ascH z then tabOf (m.φ ⟨g, h⟩ : Equiv.Perm (Fin 12)) else []

theorem tb_of_mem {g : G} (h : g ∈ ascH z) :
    m.tb g = tabOf (m.φ ⟨g, h⟩ : Equiv.Perm (Fin 12)) := by simp [tb, h]

theorem tb_mem {g : G} (h : g ∈ ascH z) : m.tb g ∈ ascHTabs := by
  rw [m.tb_of_mem h]
  exact (mem_ascHModel_iff _).1 (m.φ ⟨g, h⟩).2

theorem tb_mul {g g' : G} (h : g ∈ ascH z) (h' : g' ∈ ascH z) :
    m.tb (g * g') = tmul (m.tb g) (m.tb g') := by
  rw [m.tb_of_mem (mul_mem h h'), m.tb_of_mem h, m.tb_of_mem h', ← tabOf_mul']
  congr 1
  exact congrArg (fun x : ascHModel => (x : Equiv.Perm (Fin 12)))
    (m.φ.map_mul (⟨g, h⟩ : ↥(ascH z)) ⟨g', h'⟩)

theorem tb_one : m.tb 1 = tid := by
  rw [m.tb_of_mem (one_mem _)]
  have : m.φ (⟨1, one_mem _⟩ : ↥(ascH z)) = 1 := m.φ.map_one
  rw [show (⟨1, one_mem _⟩ : ↥(ascH z)) = 1 from rfl, m.φ.map_one]
  exact tabOf_one'

theorem tb_inj {g g' : G} (h : g ∈ ascH z) (h' : g' ∈ ascH z) (e : m.tb g = m.tb g') : g = g' := by
  rw [m.tb_of_mem h, m.tb_of_mem h'] at e
  have := m.φ.injective (Subtype.ext (tabOf_injective e))
  exact congrArg Subtype.val this

theorem exists_tb {t : List (Fin 12)} (ht : t ∈ ascHTabs) :
    ∃ g : G, g ∈ ascH z ∧ m.tb g = t := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  have hmem : ascHEval p.1 ∈ ascHModel := by
    rw [mem_ascHModel_iff, ascHData_ok p hp]
    exact ht
  refine ⟨((m.φ.symm ⟨ascHEval p.1, hmem⟩ : ↥(ascH z)) : G), (m.φ.symm _).2, ?_⟩
  rw [m.tb_of_mem (m.φ.symm _).2]
  simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  exact ascHData_ok p hp

theorem tb_z : m.tb z = zTab := by
  rw [m.tb_of_mem (z_mem_ascH z), m.hz, ← zTab_eval]

theorem mul_self_eq_one_iff {g : G} (h : g ∈ ascH z) :
    g * g = 1 ↔ tmul (m.tb g) (m.tb g) = tid := by
  rw [← m.tb_mul h h, ← m.tb_one]
  exact ⟨fun e => by rw [e], fun e => m.tb_inj (mul_mem h h) (one_mem _) e⟩

theorem comm_iff {g g' : G} (h : g ∈ ascH z) (h' : g' ∈ ascH z) :
    g * g' = g' * g ↔ tmul (m.tb g) (m.tb g') = tmul (m.tb g') (m.tb g) := by
  rw [← m.tb_mul h h', ← m.tb_mul h' h]
  exact ⟨fun e => by rw [e], fun e => m.tb_inj (mul_mem h h') (mul_mem h' h) e⟩

theorem eq_one_iff {g : G} (h : g ∈ ascH z) : g = 1 ↔ m.tb g = tid := by
  rw [← m.tb_one]
  exact ⟨fun e => by rw [e], fun e => m.tb_inj h (one_mem _) e⟩

theorem eq_z_iff {g : G} (h : g ∈ ascH z) : g = z ↔ m.tb g = zTab := by
  rw [← m.tb_z]
  exact ⟨fun e => by rw [e], fun e => m.tb_inj h (z_mem_ascH z) e⟩

theorem tmul_eq_iff {g g' k k' : G} (hg : g ∈ ascH z) (hg' : g' ∈ ascH z) (hk : k ∈ ascH z)
    (hk' : k' ∈ ascH z) :
    g * g' = k * k' ↔ tmul (m.tb g) (m.tb g') = tmul (m.tb k) (m.tb k') := by
  rw [← m.tb_mul hg hg', ← m.tb_mul hk hk']
  exact ⟨fun e => by rw [e], fun e => m.tb_inj (mul_mem hg hg') (mul_mem hk hk') e⟩

def subOf (L : List (List (Fin 12))) (hsub : ∀ t ∈ L, t ∈ ascHTabs) (h1 : tid ∈ L)
    (hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L) (hinv : ∀ t ∈ L, ∃ s ∈ L, tmul t s = tid) :
    Subgroup G where
  carrier := {g | g ∈ ascH z ∧ m.tb g ∈ L}
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [m.tb_mul ha.1 hb.1]; exact hmul _ ha.2 _ hb.2⟩
  one_mem' := ⟨one_mem _, by rw [m.tb_one]; exact h1⟩
  inv_mem' := fun {a} ha => by
    refine ⟨inv_mem ha.1, ?_⟩
    obtain ⟨s, hs, hs1⟩ := hinv _ ha.2
    obtain ⟨g', hg', hgs⟩ := m.exists_tb (hsub s hs)
    have h1 : a * g' = 1 := by
      rw [m.eq_one_iff (mul_mem ha.1 hg'), m.tb_mul ha.1 hg', hgs]
      exact hs1
    have h2 : g' = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [← h2, hgs]
    exact hs

theorem mem_subOf_iff {L : List (List (Fin 12))} {hsub : ∀ t ∈ L, t ∈ ascHTabs} {h1 : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ t ∈ L, ∃ s ∈ L, tmul t s = tid} {g : G} :
    g ∈ m.subOf L hsub h1 hmul hinv ↔ g ∈ ascH z ∧ m.tb g ∈ L := Iff.rfl

theorem card_subOf {L : List (List (Fin 12))} {hsub : ∀ t ∈ L, t ∈ ascHTabs} {h1 : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ t ∈ L, ∃ s ∈ L, tmul t s = tid}
    (hnd : L.Nodup) : Nat.card ↥(m.subOf L hsub h1 hmul hinv) = L.length := by
  have h : Nat.card ↥(m.subOf L hsub h1 hmul hinv) = Nat.card {t // t ∈ L} := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨m.tb g.1, g.2.2⟩) ⟨?_, ?_⟩)
    · intro g g' e
      exact Subtype.ext (m.tb_inj g.2.1 g'.2.1 (congrArg Subtype.val e))
    · rintro ⟨t, ht⟩
      obtain ⟨g, hg, hgt⟩ := m.exists_tb (hsub t ht)
      exact ⟨⟨g, hg, by rw [hgt]; exact ht⟩, Subtype.ext hgt⟩
  have h2 : Nat.card {t // t ∈ L} = Nat.card ↥L.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight (by simp))
  rw [h, h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

def qSub : Subgroup G :=
  m.subOf qTabs qTabs_sub tid_mem_q qTabs_mul qTabs_inv

def fSub : Subgroup G :=
  m.subOf FTabs (fun t ht => qTabs_sub t (FTabs_sub t ht)) tid_mem_F FTabs_mul
    (fun t ht => ⟨t, ht, (FTabs_elab t ht t ht).1⟩)

def tSub : Subgroup G :=
  m.subOf tTabs tTabs_sub tid_mem_t tTabs_mul tTabs_inv

theorem mem_fSub_iff {g : G} : g ∈ m.fSub ↔ g ∈ ascH z ∧ m.tb g ∈ FTabs := Iff.rfl
theorem card_qSub : Nat.card ↥m.qSub = 32 := by
  rw [qSub, m.card_subOf qTabs_nodup, qTabs_length]
theorem card_fSub : Nat.card ↥m.fSub = 8 := by
  rw [fSub, m.card_subOf FTabs_nodup, FTabs_length]
theorem card_tSub : Nat.card ↥m.tSub = 64 := by
  rw [tSub, m.card_subOf tTabs_nodup, tTabs_length]

theorem qSub_le_ascH : m.qSub ≤ ascH z := fun _ hg => hg.1
theorem fSub_le_qSub : m.fSub ≤ m.qSub := fun _ hg =>
  ⟨hg.1, FTabs_sub _ hg.2⟩

theorem ascQ_eq_qSub [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) : ascQ z = m.qSub := by
  symm
  set Nq : Subgroup ↥(ascH z) := m.qSub.subgroupOf (ascH z) with hNq
  have hcardNq : Nat.card ↥Nq = 32 := by
    rw [← m.card_qSub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.qSub_le_ascH).toEquiv
  have hnormal : Nq.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNq, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨q', hq', hq'e⟩ := qTabs_normal (m.tb g.1) (m.tb_mem g.2) _ hn.2
    obtain ⟨k, hk, hkq⟩ := m.exists_tb (qTabs_sub _ hq')
    have hkq' : k ∈ m.qSub := ⟨hk, by rw [hkq]; exact hq'⟩
    have hgn : g.1 * n.1 = k * g.1 := by
      rw [m.tmul_eq_iff g.2 n.2 hk g.2, hkq]
      exact hq'e
    have : (g * n * g⁻¹ : ↥(ascH z)).1 = k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc g.1 * n.1 * (g.1)⁻¹ = (g.1 * n.1) * (g.1)⁻¹ := rfl
        _ = k * g.1 * (g.1)⁻¹ := by rw [hgn]
        _ = k := by group
    rw [this]
    exact hkq'
  have hp : IsPGroup 2 ↥Nq := by
    rw [IsPGroup.iff_card, hcardNq]
    exact ⟨5, by norm_num⟩
  have hle : Nq ≤ CFSG.pCore 2 ↥(ascH z) := le_sSup ⟨hnormal, hp⟩
  have hsub : m.qSub ≤ ascQ z := by
    intro g hg
    rw [mem_ascQ_iff]
    exact ⟨hg.1, hle (by rw [hNq, Subgroup.mem_subgroupOf]; exact hg)⟩
  have hcard : Nat.card ↥(ascQ z) = 32 := by
    unfold ascQ
    rw [← hyp.card_core]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥(ascH z))
      (ascH z).subtype (ascH z).subtype_injective).toEquiv).symm
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, m.card_qSub])

theorem mem_ascQ_iff_tb [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) {g : G} :
    g ∈ ascQ z ↔ g ∈ ascH z ∧ m.tb g ∈ qTabs := by
  rw [m.ascQ_eq_qSub hyp]; rfl

theorem conj_tb_mem {L : List (List (Fin 12))} (hL : ∀ t ∈ L, t ∈ ascHTabs)
    (hn : ∀ h ∈ ascHTabs, ∀ q ∈ L, ∃ q' ∈ L, tmul h q = tmul q' h)
    {h f : G} (hh : h ∈ ascH z) (hf : f ∈ ascH z) (hfL : m.tb f ∈ L) :
    ∃ k : G, k ∈ ascH z ∧ m.tb k ∈ L ∧ h * f = k * h := by
  obtain ⟨q', hq', hq'e⟩ := hn _ (m.tb_mem hh) _ hfL
  obtain ⟨k, hk, hkq⟩ := m.exists_tb (hL q' hq')
  exact ⟨k, hk, by rw [hkq]; exact hq',
    (m.tmul_eq_iff hh hf hk hh).2 (by rw [hkq]; exact hq'e)⟩

theorem fSub_normal {h f : G} (hh : h ∈ ascH z) (hf : f ∈ m.fSub) : h * f * h⁻¹ ∈ m.fSub := by
  obtain ⟨k, hk, hkF, hkf⟩ := m.conj_tb_mem (fun t ht => qTabs_sub t (FTabs_sub t ht))
    FTabs_normal hh hf.1 hf.2
  have : h * f * h⁻¹ = k := by rw [hkf]; group
  rw [this]
  exact ⟨hk, hkF⟩

theorem qSub_normal {h f : G} (hh : h ∈ ascH z) (hf : f ∈ m.qSub) : h * f * h⁻¹ ∈ m.qSub := by
  obtain ⟨k, hk, hkF, hkf⟩ := m.conj_tb_mem qTabs_sub qTabs_normal hh hf.1 hf.2
  have : h * f * h⁻¹ = k := by rw [hkf]; group
  rw [this]
  exact ⟨hk, hkF⟩

theorem fSub_elab {x y : G} (hx : x ∈ m.fSub) (hy : y ∈ m.fSub) : x * x = 1 ∧ x * y = y * x := by
  have := FTabs_elab _ hx.2 _ hy.2
  exact ⟨(m.mul_self_eq_one_iff hx.1).2 this.1, (m.comm_iff hx.1 hy.1).2 this.2⟩

theorem z_mem_fSub : z ∈ m.fSub := ⟨z_mem_ascH z, by rw [m.tb_z]; exact zTab_mem_F⟩

theorem le_fSub_of_centralizes {g : G} (hg : ∀ f ∈ m.fSub, g * f = f * g) : g ∈ m.fSub := by
  have hgH : g ∈ ascH z := Subgroup.mem_centralizer_singleton_iff.2 (hg z m.z_mem_fSub)
  refine ⟨hgH, CH_F _ (m.tb_mem hgH) fun f hf => ?_⟩
  obtain ⟨f', hf', hff'⟩ := m.exists_tb (qTabs_sub f (FTabs_sub f hf))
  have hfF : f' ∈ m.fSub := ⟨hf', by rw [hff']; exact hf⟩
  rw [← hff']
  exact (m.comm_iff hgH hf').1 (hg f' hfF)

theorem fSub_orbit {s s' : G} (hs : s ∈ m.fSub) (hs1 : s ≠ 1) (hsz : s ≠ z) (hs' : s' ∈ m.fSub)
    (hs1' : s' ≠ 1) (hsz' : s' ≠ z) : ∃ h : G, h ∈ ascH z ∧ h * s = s' * h := by
  have := F_orbit _ hs.2 (fun e => hs1 ((m.eq_one_iff hs.1).2 e))
    (fun e => hsz ((m.eq_z_iff hs.1).2 e)) _ hs'.2 (fun e => hs1' ((m.eq_one_iff hs'.1).2 e))
    (fun e => hsz' ((m.eq_z_iff hs'.1).2 e))
  obtain ⟨t, ht, hte⟩ := this
  obtain ⟨h, hh, hht⟩ := m.exists_tb ht
  exact ⟨h, hh, (m.tmul_eq_iff hh hs.1 hs'.1 hh).2 (by rw [hht]; exact hte)⟩

theorem qSub_outF_orbit {s s' : G} (hs : s ∈ m.qSub) (hsF : s ∉ m.fSub) (hs2 : s * s = 1)
    (hs' : s' ∈ m.qSub) (hsF' : s' ∉ m.fSub) (hs2' : s' * s' = 1) :
    ∃ h : G, h ∈ ascH z ∧ h * s = s' * h := by
  have := O12_orbit _ hs.2 (fun e => hsF ⟨hs.1, e⟩) ((m.mul_self_eq_one_iff hs.1).1 hs2) _ hs'.2
    (fun e => hsF' ⟨hs'.1, e⟩) ((m.mul_self_eq_one_iff hs'.1).1 hs2')
  obtain ⟨t, ht, hte⟩ := this
  obtain ⟨h, hh, hht⟩ := m.exists_tb ht
  exact ⟨h, hh, (m.tmul_eq_iff hh hs.1 hs'.1 hh).2 (by rw [hht]; exact hte)⟩

theorem outInv_orbit_G [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) {v w : G} (hv : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hv2 : v * v = 1) (hw : w ∈ ascH z) (hwQ : w ∉ ascQ z) (hw2 : w * w = 1) :
    ∃ h : G, h ∈ ascH z ∧ h * v = w * h := by
  rw [m.mem_ascQ_iff_tb hyp] at hvQ hwQ
  have := outInv_orbit _ (m.tb_mem hv) (fun e => hvQ ⟨hv, e⟩) ((m.mul_self_eq_one_iff hv).1 hv2)
    _ (m.tb_mem hw) (fun e => hwQ ⟨hw, e⟩) ((m.mul_self_eq_one_iff hw).1 hw2)
  obtain ⟨t, ht, hte⟩ := this
  obtain ⟨h, hh, hht⟩ := m.exists_tb ht
  exact ⟨h, hh, (m.tmul_eq_iff hh hv hw hh).2 (by rw [hht]; exact hte)⟩

theorem exists_inv_Q_notF :
    ∃ t : G, t ∈ m.qSub ∧ t ∉ m.fSub ∧ t * t = 1 := by
  obtain ⟨t, ht, htF, hts⟩ := O12_exists
  obtain ⟨v, hv, hvt⟩ := m.exists_tb (qTabs_sub t ht)
  refine ⟨v, ⟨hv, by rw [hvt]; exact ht⟩, fun h => htF (by rw [← hvt]; exact h.2),
    (m.mul_self_eq_one_iff hv).2 (by rw [hvt]; exact hts)⟩

theorem mem_fSub_of_commute [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) {v s : G} (hv : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hv2 : v * v = 1) (hs : s ∈ ascQ z) (hs1 : s ≠ 1) (hsz : s ≠ z)
    (hs2 : s * s = 1) (hc : v * s = s * v) : s ∈ m.fSub := by
  rw [m.mem_ascQ_iff_tb hyp] at hvQ hs
  have := commuting_involution_mem_F _ (m.tb_mem hv) (fun e => hvQ ⟨hv, e⟩)
    ((m.mul_self_eq_one_iff hv).1 hv2) _ hs.2 (fun e => hs1 ((m.eq_one_iff hs.1).2 e))
    (fun e => hsz ((m.eq_z_iff hs.1).2 e)) ((m.mul_self_eq_one_iff hs.1).1 hs2)
    ((m.comm_iff hv hs.1).1 hc)
  exact ⟨hs.1, this⟩

theorem coset_of_involutions_outside_F [Finite G] (hyp : CFSG.GH74.M12.Asc03Hyp G z) {s y y' : G}
    (hs : s ∈ m.fSub) (hs1 : s ≠ 1) (hsz : s ≠ z)
    (hy : y ∈ ascQ z) (hyF : y ∉ m.fSub) (hy2 : y * y = 1) (hys : y * s = s * y)
    (hy' : y' ∈ ascQ z) (hyF' : y' ∉ m.fSub) (hy2' : y' * y' = 1) (hys' : y' * s = s * y') :
    y * y' = 1 ∨ y * y' = z ∨ y * y' = s ∨ y * y' = z * s := by
  rw [m.mem_ascQ_iff_tb hyp] at hy hy'
  have := involutions_outside_F_one_coset _ hs.2 (fun e => hs1 ((m.eq_one_iff hs.1).2 e))
    (fun e => hsz ((m.eq_z_iff hs.1).2 e)) _ hy.2 (fun e => hyF ⟨hy.1, e⟩)
    ((m.mul_self_eq_one_iff hy.1).1 hy2) ((m.comm_iff hy.1 hs.1).1 hys)
    _ hy'.2 (fun e => hyF' ⟨hy'.1, e⟩) ((m.mul_self_eq_one_iff hy'.1).1 hy2')
    ((m.comm_iff hy'.1 hs.1).1 hys')
  have hyy : y * y' ∈ ascH z := mul_mem hy.1 hy'.1
  rcases this with h | h | h | h
  · left; exact (m.eq_one_iff hyy).2 (by rw [m.tb_mul hy.1 hy'.1]; exact h)
  · right; left; exact (m.eq_z_iff hyy).2 (by rw [m.tb_mul hy.1 hy'.1]; exact h)
  · right; right; left
    exact m.tb_inj hyy hs.1 (by rw [m.tb_mul hy.1 hy'.1]; exact h)
  · right; right; right
    exact m.tb_inj hyy (mul_mem (z_mem_ascH z) hs.1)
      (by rw [m.tb_mul hy.1 hy'.1, m.tb_mul (z_mem_ascH z) hs.1, m.tb_z]; exact h)

theorem conj_mem_fSub [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) : g * z * g⁻¹ ∈ m.fSub := by
  obtain ⟨-, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := config_of_conj hyp hgz hsQ
  have hv₀2 : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀
    rwa [hv₀o, pow_two] at this
  obtain ⟨q, hq, hqv⟩ := Subgroup.mem_map.1 hv₀.2
  have hqH : q ∈ ascH z := ascQ_le_ascH z hq
  have hqz : q * z = z * q := Subgroup.mem_centralizer_singleton_iff.1 hqH
  have hv₀def : v₀ = g * q * g⁻¹ := by
    rw [← hqv]
    simp [MulAut.conj_apply]
  have hcomm : v₀ * (g * z * g⁻¹) = (g * z * g⁻¹) * v₀ := by
    rw [hv₀def]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  exact m.mem_fSub_of_commute hyp hv₀.1 hv₀Q hv₀2 hsQ (asc_conj_ne_one hyp g) hgz
    (asc_conj_sq hyp g) hcomm

theorem conj_mem_Q_iff [Finite G] (hyp : Asc03Hyp G z) {s : G} (hsQ : s ∈ ascQ z) (hs1 : s ≠ 1) :
    (∃ g : G, g * z * g⁻¹ = s) ↔ s ∈ m.fSub := by
  constructor
  · rintro ⟨g, rfl⟩
    by_cases h : g * z * g⁻¹ = z
    · rw [h]; exact m.z_mem_fSub
    · exact m.conj_mem_fSub hyp h hsQ
  · intro hsF
    by_cases hsz : s = z
    · exact ⟨1, by simp [hsz]⟩
    · obtain ⟨g₀, hg₀z, q, hqP, hq⟩ := hyp.not_weakly_closed
      have hs₀Q : g₀ * z * g₀⁻¹ ∈ ascQ z := by
        rw [← hq]
        exact (mem_ascQ_iff z _).2 ⟨q.2, hqP⟩
      have hs₀F := m.conj_mem_fSub hyp hg₀z hs₀Q
      obtain ⟨h, hh, hhs⟩ := m.fSub_orbit hs₀F (asc_conj_ne_one hyp g₀) hg₀z hsF hs1 hsz
      refine ⟨h * g₀, ?_⟩
      calc h * g₀ * z * (h * g₀)⁻¹ = h * (g₀ * z * g₀⁻¹) * h⁻¹ := by group
        _ = s := by rw [hhs]; group

omit m in
theorem z_mem_ascQ (hyp : Asc03Hyp G z) : z ∈ ascQ z := (extraspecialAt_ascQ hyp).mem

theorem fSub_le_ascQ [Finite G] (hyp : Asc03Hyp G z) : m.fSub ≤ ascQ z := by
  rw [m.ascQ_eq_qSub hyp]
  exact m.fSub_le_qSub

theorem exists_E_not_conj_fSub [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z)
    (hEF : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≠ m.fSub) :
    ∃ e ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom, g⁻¹ * e * g ∉ m.fSub := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hE8, -⟩ := config_of_conj hyp hgz hsQ
  have hle : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≤ m.fSub := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]; exact one_mem _
    · have hf := hno e he
      have hf1 : g⁻¹ * e * g ≠ 1 := by
        intro h
        apply he1
        have := congrArg (fun w => g * w * g⁻¹) h
        simpa [mul_assoc] using this
      obtain ⟨x, hx⟩ := (m.conj_mem_Q_iff hyp (m.fSub_le_ascQ hyp hf) hf1).2 hf
      refine (m.conj_mem_Q_iff hyp he.1 he1).1 ⟨g * x, ?_⟩
      calc g * x * z * (g * x)⁻¹ = g * (x * z * x⁻¹) * g⁻¹ := by group
        _ = e := by rw [hx]; group
  exact hEF (Subgroup.eq_of_le_of_card_ge hle (by rw [hE8, m.card_fSub]))

theorem outer_involution_conj_z [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z)
    (hEF : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≠ m.fSub) {v : G}
    (hv : v ∈ ascH z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom) (hv2 : v * v = 1)
    (hvQ : v ∉ ascQ z) : ∃ x : G, x * z * x⁻¹ = v := by
  obtain ⟨hzQ, hE8, helem, -⟩ := config_of_conj hyp hgz hsQ
  obtain ⟨e, he, heF⟩ := m.exists_E_not_conj_fSub hyp hgz hsQ hEF
  have hgz' : g⁻¹ * z * g⁻¹⁻¹ ≠ z := by
    intro h
    apply hgz
    rw [inv_inv] at h
    have := congrArg (fun w => g * w * g⁻¹) h
    simpa [mul_assoc] using this.symm
  have hs'Q : g⁻¹ * z * g⁻¹⁻¹ ∈ ascQ z := by rwa [inv_inv]
  have hs'F : g⁻¹ * z * g ∈ m.fSub := by
    have := m.conj_mem_fSub hyp hgz' hs'Q
    rwa [inv_inv] at this
  have hs'1 : g⁻¹ * z * g ≠ 1 := by
    have := asc_conj_ne_one hyp g⁻¹
    rwa [inv_inv] at this
  have hs'z : g⁻¹ * z * g ≠ z := by
    intro h
    apply hgz
    have := congrArg (fun w => g * w * g⁻¹) h
    simpa [mul_assoc] using this.symm
  have hjQ : g⁻¹ * v * g ∈ ascQ z := (mem_map_conj_iff _ g v).1 hv.2
  have hj2 : g⁻¹ * v * g * (g⁻¹ * v * g) = 1 := by
    calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hv2]; group
  have hvz : v * z = z * v := Subgroup.mem_centralizer_singleton_iff.1 hv.1
  have hjs' : g⁻¹ * v * g * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * v * g) := by
    calc g⁻¹ * v * g * (g⁻¹ * z * g) = g⁻¹ * (v * z) * g := by group
      _ = g⁻¹ * (z * v) * g := by rw [hvz]
      _ = (g⁻¹ * z * g) * (g⁻¹ * v * g) := by group
  have hzE : z ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom :=
    ⟨z_mem_ascQ hyp, (mem_map_conj_iff _ g z).2 hzQ⟩
  have hsE : g * z * g⁻¹ ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
    refine ⟨hsQ, (mem_map_conj_iff _ g _).2 ?_⟩
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact z_mem_ascQ hyp
  have hjF : g⁻¹ * v * g ∈ m.fSub := by
    by_contra hjF
    have hy'Q : g⁻¹ * e * g ∈ ascQ z := (mem_map_conj_iff _ g e).1 he.2
    have hy'2 : g⁻¹ * e * g * (g⁻¹ * e * g) = 1 := by
      calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
        _ = 1 := by rw [(helem e he).1]; group
    have hez : e * z = z * e := (helem e he).2 z hzE
    have hy's' : g⁻¹ * e * g * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * e * g) := by
      calc g⁻¹ * e * g * (g⁻¹ * z * g) = g⁻¹ * (e * z) * g := by group
        _ = g⁻¹ * (z * e) * g := by rw [hez]
        _ = (g⁻¹ * z * g) * (g⁻¹ * e * g) := by group
    have hcos := m.coset_of_involutions_outside_F hyp hs'F hs'1 hs'z hjQ hjF hj2 hjs' hy'Q heF
      hy'2 hy's'
    have hve : v * e ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
      have hvee : v * e = g * (g⁻¹ * v * g * (g⁻¹ * e * g)) * g⁻¹ := by group
      rw [hvee]
      rcases hcos with h | h | h | h <;> rw [h]
      · simp
      · simpa using hsE
      · rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]; exact hzE
      · rw [show g * (z * (g⁻¹ * z * g)) * g⁻¹ = (g * z * g⁻¹) * z by group]
        exact mul_mem hsE hzE
    have hvE : v ∈ ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
      have := mul_mem hve (inv_mem he)
      simpa using this
    exact hvQ hvE.1
  have hj1 : g⁻¹ * v * g ≠ 1 := by
    intro h
    apply hvQ
    have : v = 1 := by
      have := congrArg (fun w => g * w * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this]; exact one_mem _
  obtain ⟨x, hx⟩ := (m.conj_mem_Q_iff hyp hjQ hj1).2 hjF
  refine ⟨g * x, ?_⟩
  calc g * x * z * (g * x)⁻¹ = g * (x * z * x⁻¹) * g⁻¹ := by group
    _ = v := by rw [hx]; group

omit m in
theorem card_ascH (hyp : Asc03Hyp G z) : Nat.card ↥(ascH z) = 192 := by
  obtain ⟨e⟩ := hyp.quotient_S3
  have h1 : Nat.card (↥(ascH z) ⧸ CFSG.pCore 2 ↥(ascH z)) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have h2 := (CFSG.pCore 2 ↥(ascH z)).card_eq_card_quotient_mul_card_subgroup
  rw [h1, hyp.card_core] at h2
  omega

theorem tSub_le_ascH : m.tSub ≤ ascH z := fun _ hg => hg.1

theorem z_mem_tSub : z ∈ m.tSub := ⟨z_mem_ascH z, by rw [m.tb_z]; exact zTab_mem_t⟩

theorem isPGroup_tSub : IsPGroup 2 ↥m.tSub :=
  IsPGroup.of_card (n := 6) (by rw [m.card_tSub]; norm_num)

theorem eq_one_or_z_of_central_tSub {c : G} (hc : c ∈ m.tSub) (hcc : ∀ t ∈ m.tSub, c * t = t * c) :
    c = 1 ∨ c = z := by
  have := tTabs_center _ hc.2 (fun t' ht' => by
    obtain ⟨t, ht, htt⟩ := m.exists_tb (tTabs_sub t' ht')
    have htT : t ∈ m.tSub := ⟨ht, by rw [htt]; exact ht'⟩
    rw [← htt]
    exact (m.comm_iff hc.1 ht).1 (hcc t htT))
  rcases this with h | h
  · left; exact (m.eq_one_iff hc.1).2 h
  · right; exact (m.eq_z_iff hc.1).2 h

theorem le_tSub_of_isPGroup [Finite G] (hyp : Asc03Hyp G z) {S : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hTS : m.tSub ≤ S) : S ≤ m.tSub := by
  by_contra hne
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  set T' : Subgroup ↥S := m.tSub.subgroupOf S with hT'
  have hlt : T' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    intro g hg
    have : (⟨g, hg⟩ : ↥S) ∈ T' := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.1 this)
  obtain ⟨⟨n, hnS⟩, hnN, hnT⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent T' hlt)
  have hnT' : n ∉ m.tSub := fun h => hnT (Subgroup.mem_subgroupOf.2 h)
  have hnorm : ∀ t ∈ m.tSub, n * t * n⁻¹ ∈ m.tSub := by
    intro t ht
    have h1 : (⟨t, hTS ht⟩ : ↥S) ∈ T' := Subgroup.mem_subgroupOf.2 ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hnN _).1 h1
    exact Subgroup.mem_subgroupOf.1 h2
  have hnorm' : ∀ t ∈ m.tSub, n⁻¹ * t * n ∈ m.tSub := by
    intro t ht
    have h1 : (⟨t, hTS ht⟩ : ↥S) ∈ T' := Subgroup.mem_subgroupOf.2 ht
    have h2 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) _).1 h1
    have := Subgroup.mem_subgroupOf.1 h2
    simpa using this
  have hzc : n * z * n⁻¹ = z := by
    have hzT : n * z * n⁻¹ ∈ m.tSub := hnorm z m.z_mem_tSub
    have hcen : ∀ t ∈ m.tSub, (n * z * n⁻¹) * t = t * (n * z * n⁻¹) := by
      intro t ht
      have h1 : n⁻¹ * t * n ∈ m.tSub := hnorm' t ht
      have h2 : z * (n⁻¹ * t * n) = (n⁻¹ * t * n) * z :=
        (Subgroup.mem_centralizer_singleton_iff.1 (m.tSub_le_ascH h1)).symm
      calc n * z * n⁻¹ * t = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by rw [h2]
        _ = t * (n * z * n⁻¹) := by group
    rcases m.eq_one_or_z_of_central_tSub hzT hcen with h | h
    · exact absurd h (by
        intro h1
        apply asc_z_ne_one hyp
        have := congrArg (fun w => n⁻¹ * w * n) h1
        simpa [mul_assoc] using this)
    · exact h
  have hnH : n ∈ ascH z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun w => w * n) hzc
    simpa [mul_assoc] using this
  set A : Subgroup G := m.tSub ⊔ Subgroup.zpowers n with hA
  have hAS : A ≤ S := sup_le hTS (by rw [Subgroup.zpowers_le]; exact hnS)
  have hAH : A ≤ ascH z := sup_le m.tSub_le_ascH (by rw [Subgroup.zpowers_le]; exact hnH)
  have hAp : IsPGroup 2 ↥A := hS.to_le hAS
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hAp
  have hdvd : Nat.card ↥A ∣ 192 := by
    rw [← card_ascH hyp]
    exact Subgroup.card_dvd_of_le hAH
  have hk6 : k ≤ 6 := by
    by_contra hk7
    push Not at hk7
    have : 2 ^ 7 ∣ 192 := (pow_dvd_pow 2 hk7).trans (hk ▸ hdvd)
    norm_num at this
  have hcardA : Nat.card ↥A ≤ 64 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
      _ = 64 := by norm_num
  have hTA : m.tSub ≤ A := le_sup_left
  have heq : m.tSub = A := Subgroup.eq_of_le_of_card_ge hTA (by rw [m.card_tSub]; exact hcardA)
  apply hnT'
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)

@[expose] noncomputable def tSylow [Finite G] (hyp : Asc03Hyp G z) : Sylow 2 G where
  toSubgroup := m.tSub
  isPGroup' := m.isPGroup_tSub
  is_maximal' := fun hQ hle => le_antisymm (m.le_tSub_of_isPGroup hyp hQ hle) hle

theorem coe_tSylow [Finite G] (hyp : Asc03Hyp G z) : (m.tSylow hyp : Subgroup G) = m.tSub := rfl

theorem involution_conj_z_or_t [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z)
    (hEF : ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom ≠ m.fSub) {t : G}
    (ht : t ∈ m.qSub) (htF : t ∉ m.fSub) (ht2 : t * t = 1) {x : G} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : (∃ c : G, c * z * c⁻¹ = x) ∨ (∃ c : G, c * t * c⁻¹ = x) := by
  have hxp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    rw [orderOf_eq_prime (by rwa [pow_two]) hx1]
    simp
  obtain ⟨S, hxS⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G (m.tSylow hyp) S
  have hxmem : x ∈ ((c • m.tSylow hyp : Sylow 2 G) : Subgroup G) := by
    rw [hc]; exact hxS (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, coe_tSylow] at hxmem
  obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.1 hxmem
  have hyx' : c * y * c⁻¹ = x := by simpa [MulAut.conj_apply] using hyx
  have hyH : y ∈ ascH z := m.tSub_le_ascH hyT
  have hy2 : y * y = 1 := by
    have h1 : c⁻¹ * (x * x) * c = y * y := by rw [← hyx']; group
    rw [← h1, hx2]; group
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [← hyx', h]; group
  by_cases hyQ : y ∈ ascQ z
  · have hyQ' : y ∈ m.qSub := by rwa [m.ascQ_eq_qSub hyp] at hyQ
    by_cases hyF : y ∈ m.fSub
    · left
      obtain ⟨d, hd⟩ := (m.conj_mem_Q_iff hyp hyQ hy1).2 hyF
      exact ⟨c * d, by calc c * d * z * (c * d)⁻¹ = c * (d * z * d⁻¹) * c⁻¹ := by group
                          _ = x := by rw [hd, hyx']⟩
    · right
      obtain ⟨h, hh, hht⟩ := m.qSub_outF_orbit ht htF ht2 hyQ' hyF hy2
      refine ⟨c * h, ?_⟩
      calc c * h * t * (c * h)⁻¹ = c * (h * t * h⁻¹) * c⁻¹ := by group
        _ = x := by rw [hht]; simpa using hyx'
  · left
    obtain ⟨v₀, hv₀, hv₀o, hv₀Q⟩ := (config_of_conj hyp hgz hsQ).2.2.2.2
    have hv₀2 : v₀ * v₀ = 1 := by
      have := pow_orderOf_eq_one v₀
      rwa [hv₀o, pow_two] at this
    obtain ⟨x₀, hx₀⟩ := m.outer_involution_conj_z hyp hgz hsQ hEF hv₀ hv₀2 hv₀Q
    obtain ⟨h, hh, hhv⟩ := m.outInv_orbit_G hyp hv₀.1 hv₀Q hv₀2 hyH hyQ hy2
    refine ⟨c * h * x₀, ?_⟩
    calc c * h * x₀ * z * (c * h * x₀)⁻¹ = c * (h * (x₀ * z * x₀⁻¹) * h⁻¹) * c⁻¹ := by group
      _ = x := by rw [hx₀, hhv]; simpa using hyx'

end AscModel

end CFSG.Quasithin
