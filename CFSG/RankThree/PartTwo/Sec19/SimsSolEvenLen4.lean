module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCentral
public import CFSG.CGT.PushingUpLit.SolK.FourTheta

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

section Bar

variable {n : ℕ}

@[expose] def indVec (I : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ I then 1 else 0

@[expose] noncomputable def barInd (I : Finset (Fin n)) : permBar n := (indVec I : permBar n)

theorem vecWt_indVec (I : Finset (Fin n)) : vecWt (indVec I) = I.card := by
  unfold vecWt
  congr 1
  ext i
  simp [indVec]

theorem barLen_barInd (I : Finset (Fin n)) : barLen (barInd I) = min I.card (n - I.card) := by
  rw [barInd, barLen_mk, vecWt_indVec]

theorem barAct_barInd (σ : Perm (Fin n)) (I : Finset (Fin n)) :
    barAct σ (barInd I) = barInd (I.image σ) := by
  rw [barInd, barAct_mk]
  congr 1
  funext i
  simp only [vecPerm_apply, indVec, Finset.mem_image]
  by_cases h : σ⁻¹ i ∈ I
  · rw [if_pos h, if_pos]
    exact ⟨σ⁻¹ i, h, by simp⟩
  · rw [if_neg h, if_neg]
    rintro ⟨a, ha, rfl⟩
    exact h (by simpa using ha)

private theorem zmod2_neg_add_eq_zero : ∀ a b : ZMod 2, -a + b = 0 → b = a := by decide
private theorem zmod2_neg_add_eq_one : ∀ a b : ZMod 2, -a + b = 1 → b = a + 1 := by decide
private theorem zmod2_aux3 : ∀ a b : ZMod 2, a = b → a ≠ b + 1 := by decide
private theorem zmod2_aux4 : ∀ a : ZMod 2, a = a + 1 + 1 := by decide

theorem bar_mk_eq_iff {x y : Fin n → ZMod 2} :
    (x : permBar n) = (y : permBar n) ↔ (∀ i, y i = x i) ∨ (∀ i, y i = x i + 1) := by
  rw [QuotientAddGroup.eq, mem_zmultiples_allOnes_iff]
  constructor
  · rintro (h | h)
    · left
      intro i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
      exact zmod2_neg_add_eq_zero _ _ this
    · right
      intro i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.neg_apply, allOnes] at this
      exact zmod2_neg_add_eq_one _ _ this
  · rintro (h | h)
    · left
      funext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      rw [h i]
      exact neg_add_cancel _
    · right
      funext i
      simp only [Pi.add_apply, Pi.neg_apply, allOnes]
      rw [h i]
      exact neg_add_cancel_left _ _

theorem bar_mk_ne_of_coords {x y : Fin n → ZMod 2} {i j : Fin n} (hi : x i ≠ y i)
    (hj : x j = y j) : (x : permBar n) ≠ (y : permBar n) := by
  intro h
  rcases bar_mk_eq_iff.1 h with h0 | h1
  · exact hi (h0 i).symm
  · exact zmod2_aux3 _ _ hj.symm (h1 j)

theorem indVec_compl (I : Finset (Fin n)) : indVec Iᶜ = indVec I + allOnes n := by
  funext i
  by_cases h : i ∈ I
  · simp only [indVec, Finset.mem_compl, h, not_true_eq_false, if_false, if_true, Pi.add_apply,
      allOnes]
    decide
  · simp [indVec, h, allOnes]

theorem barInd_compl (I : Finset (Fin n)) : barInd Iᶜ = barInd I := by
  unfold barInd
  rw [indVec_compl, QuotientAddGroup.mk_add]
  have : (allOnes n : permBar n) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  rw [this, add_zero]

theorem barInd_eq_barInd_iff {I J : Finset (Fin n)} :
    barInd I = barInd J ↔ I = J ∨ I = Jᶜ := by
  unfold barInd
  rw [bar_mk_eq_iff]
  constructor
  · rintro (h | h)
    · left
      ext i
      have := h i
      by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp_all [indVec]
    · right
      ext i
      have := h i
      by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp_all [indVec]
  · rintro (rfl | rfl)
    · left
      intro i
      rfl
    · right
      intro i
      have := congrFun (indVec_compl J) i
      simp only [Pi.add_apply, allOnes] at this
      rw [this]
      exact zmod2_aux4 _

theorem exists_supp_of_len (v : permBar n) :
    ∃ I : Finset (Fin n), I.card = barLen v ∧ v = barInd I := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  set I : Finset (Fin n) := Finset.univ.filter fun i => x i = 1 with hI
  have hx : (x : permBar n) = barInd I := by
    unfold barInd
    congr 1
    funext i
    simp only [indVec, hI, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod_two_cases' (x i) with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hwt : vecWt x = I.card := rfl
  rw [barLen_mk, hwt]
  by_cases hle : I.card ≤ n - I.card
  · refine ⟨I, ?_, hx⟩
    rw [min_eq_left hle]
  · refine ⟨Iᶜ, ?_, hx.trans (barInd_compl I).symm⟩
    rw [min_eq_right (by omega), Finset.card_compl, Fintype.card_fin]

theorem eq_of_barInd_eq {I J : Finset (Fin n)} (hI : 2 * I.card < n) (hJ : J.card = I.card)
    (h : barInd I = barInd J) : I = J := by
  rcases barInd_eq_barInd_iff.1 h with h1 | h1
  · exact h1
  · exfalso
    have := congrArg Finset.card h1
    rw [Finset.card_compl, Fintype.card_fin, hJ] at this
    omega

theorem card_image_perm (σ : Perm (Fin n)) (I : Finset (Fin n)) : (I.image σ).card = I.card :=
  Finset.card_image_of_injective _ σ.injective

theorem image_eq_iff_mem_setStab (σ : Perm (Fin n)) (I : Finset (Fin n)) :
    I.image σ = I ↔ σ ∈ setStab I := by
  rw [mem_setStab]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 hx
      rw [← σ.injective hax]
      exact ha
    · intro hx
      rw [← h]
      exact Finset.mem_image_of_mem σ hx
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact (h a).2 ha
    · intro hy
      refine Finset.mem_image.2 ⟨σ⁻¹ y, ?_, by simp⟩
      have := h (σ⁻¹ y)
      rw [perm_apply_inv_self] at this
      exact this.1 hy

theorem barAct_barInd_eq_self_iff {I : Finset (Fin n)} (hI : 2 * I.card < n) (σ : Perm (Fin n)) :
    barAct σ (barInd I) = barInd I ↔ σ ∈ setStab I := by
  rw [barAct_barInd, ← image_eq_iff_mem_setStab]
  constructor
  · intro h
    rcases barInd_eq_barInd_iff.1 h with h1 | h1
    · exact h1
    · exfalso
      have := congrArg Finset.card h1
      rw [Finset.card_compl, Fintype.card_fin, card_image_perm] at this
      omega
  · intro h
    rw [h]

theorem barInd_empty : barInd (∅ : Finset (Fin n)) = 0 := by
  unfold barInd
  have : indVec (∅ : Finset (Fin n)) = 0 := by
    funext i
    simp [indVec]
  rw [this]
  rfl

theorem eq_zero_of_barLen_eq_zero {v : permBar n} (h : barLen v = 0) : v = 0 := by
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len v
  rw [h, Finset.card_eq_zero] at hIc
  rw [hI, hIc, barInd_empty]

theorem even_vecWt_of_sum_eq_zero {x : Fin n → ZMod 2} (hx : ∑ i, x i = 0) : Even (vecWt x) := by
  have h2 : ∑ i, x i = (vecWt x : ZMod 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i = 1)]
    have h3 : ∑ i ∈ Finset.univ.filter (fun i => ¬ x i = 1), x i = 0 :=
      Finset.sum_eq_zero fun i hi => (zmod_two_eq_zero_iff_ne_one _).2 (Finset.mem_filter.1 hi).2
    rw [h3, add_zero]
    have h4 : ∑ i ∈ Finset.univ.filter (fun i => x i = 1), x i =
        ∑ i ∈ Finset.univ.filter (fun i => x i = 1), (1 : ZMod 2) :=
      Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2
    rw [h4]
    simp [vecWt]
  rw [hx] at h2
  exact (ZMod.natCast_eq_zero_iff_even).1 h2.symm

end Bar

section Group

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem Rc_mul_self (hR : Nat.card ↥(Rc X) ≤ 2) {r : G} (hr : r ∈ Rc X) : r * r = 1 := by
  by_cases h1 : r = 1
  · rw [h1, mul_one]
  · have hne : (⟨r, hr⟩ : ↥(Rc X)) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have hne' : (⟨r⁻¹, (Rc X).inv_mem hr⟩ : ↥(Rc X)) ≠ 1 := fun h =>
      h1 (inv_eq_one.1 (congrArg Subtype.val h))
    have := congrArg Subtype.val (eq_of_card_le_two hR hne hne')
    exact mul_eq_one_iff_eq_inv.2 this

namespace Cfg

variable (C : Cfg G M X n)

@[expose] def qB (_C : Cfg G M X n) : Subgroup G :=
  Subgroup.closure {q | q ∈ CFSG.Open.pCoreOf 2 M ∧ q * q = 1}

theorem mem_qB_iff
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) {q : G} :
    q ∈ C.qB ↔ q ∈ CFSG.Open.pCoreOf 2 M ∧ q * q = 1 := by
  constructor
  · intro hq
    induction hq using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨(CFSG.Open.pCoreOf 2 M).one_mem, mul_one 1⟩
    | mul x y _ _ hx hy =>
      refine ⟨(CFSG.Open.pCoreOf 2 M).mul_mem hx.1 hy.1, ?_⟩
      have hc := hQ x hx.1 y hy.1
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx.2, hy.2, one_mul]
    | inv x _ hx =>
      refine ⟨(CFSG.Open.pCoreOf 2 M).inv_mem hx.1, ?_⟩
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx.2, inv_one]
  · exact fun hq => Subgroup.subset_closure hq

theorem qB_le_Q : C.qB ≤ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.closure_le _).2 fun _ hq => hq.1

theorem blockU_le_qB
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) :
    blockU X ≤ C.qB := fun w hw =>
  (C.mem_qB_iff hQ).2 ⟨C.S.W_le_Q hw, by
    have := C.S.elemU.2 w hw
    rwa [pow_two] at this⟩

theorem Rc_le_qB
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q)
    (hR : Nat.card ↥(Rc X) ≤ 2) : Rc X ≤ C.qB := fun r hr =>
  (C.mem_qB_iff hQ).2 ⟨by
    rw [C.S.R_eq_inf] at hr
    exact (Subgroup.mem_inf.1 hr).1, Rc_mul_self hR hr⟩

theorem qB_normalized
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) {m b : G}
    (hm : m ∈ M) (hb : b ∈ C.qB) : m * b * m⁻¹ ∈ C.qB := by
  obtain ⟨hbQ, hb2⟩ := (C.mem_qB_iff hQ).1 hb
  refine (C.mem_qB_iff hQ).2 ⟨pCoreOf_normalized M hm hbQ, ?_⟩
  calc m * b * m⁻¹ * (m * b * m⁻¹) = m * (b * b) * m⁻¹ := by group
    _ = 1 := by rw [hb2]; group

theorem isElemAbelian_qB
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) :
    CFSG.Open.IsElemAbelian 2 C.qB := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · exact hQ _ ((C.mem_qB_iff hQ).1 a.2).1 _ ((C.mem_qB_iff hQ).1 b.2).1
  · rw [pow_two]
    exact ((C.mem_qB_iff hQ).1 hx).2

theorem normalizer_qB_eq (hR : Nat.card ↥(Rc X) ≤ 2) :
    Subgroup.normalizer ((C.qB : Subgroup G) : Set G) = M := by
  have hQ := C.Q_comm hR
  refine le_antisymm (C.normalizer_le_M_of_W_le (C.blockU_le_qB hQ) C.qB_le_Q) fun m hm => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => C.qB_normalized hQ hm hb, fun hb => ?_⟩
  have := C.qB_normalized hQ (M.inv_mem hm) hb
  simpa [mul_assoc] using this

theorem card_eq_card_inf_mul (hR : Nat.card ↥(Rc X) ≤ 2) {U : Subgroup G} (hUM : U ≤ M) :
    Nat.card U = Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) *
      Nat.card ↥((U.subgroupOf M).map C.θ) := by
  classical
  let U' : Subgroup ↥M := U.subgroupOf M
  let f : ↥U' →* Perm (Fin n) := C.θ.comp U'.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hU' : Nat.card ↥U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have hrange : Nat.card f.range = Nat.card ↥(U'.map C.θ) := by
    congr 2
    ext σ
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k.2, hk⟩, fun ⟨m, hm, hk⟩ => ⟨⟨m, hm⟩, hk⟩⟩
  have hker : Nat.card f.ker = Nat.card ↥(U ⊓ CFSG.Open.pCoreOf 2 M) := by
    refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨((k : ↥U') : ↥M).1, ?_⟩) ⟨?_, ?_⟩)
    · refine Subgroup.mem_inf.2 ⟨k.1.2, ?_⟩
      have hk1 : C.θ (k.1 : ↥M) = 1 := k.2
      rw [← C.K_eq_Q hR]
      exact C.mem_K.2 ⟨(k.1 : ↥M).2, hk1⟩
    · intro k k' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    · intro u
      have hu := u.2
      have huM : (u : G) ∈ M := hUM (Subgroup.mem_inf.1 hu).1
      obtain ⟨hg, hθ⟩ := C.mem_K.1 (C.Q_le_K (Subgroup.mem_inf.1 hu).2)
      exact ⟨⟨⟨⟨(u : G), huM⟩, (Subgroup.mem_inf.1 hu).1⟩, hθ⟩, rfl⟩
  rw [hker, hrange, hU'] at h1
  exact h1.symm

end Cfg

namespace Cfg.PiData

variable {C : Cfg G M X n} (D : C.PiData)

theorem card_eq_card_inf_R_mul {H : Subgroup G} (hHQ : H ≤ CFSG.Open.pCoreOf 2 M) :
    Nat.card H = Nat.card ↥(H ⊓ Rc X) *
      Nat.card ↥((H.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) := by
  classical
  let H' : Subgroup ↥(CFSG.Open.pCoreOf 2 M) := H.subgroupOf (CFSG.Open.pCoreOf 2 M)
  let f : ↥H' →* Multiplicative (permBar n) := D.piQ.comp H'.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hH' : Nat.card ↥H' = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv
  have hrange : Nat.card f.range = Nat.card ↥(H'.map D.piQ) := by
    congr 2
    ext σ
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k.2, hk⟩, fun ⟨m, hm, hk⟩ => ⟨⟨m, hm⟩, hk⟩⟩
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ Rc X) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun k => ⟨(((k : ↥H') : ↥(CFSG.Open.pCoreOf 2 M)) : G), ?_⟩) ⟨?_, ?_⟩)
    · refine Subgroup.mem_inf.2 ⟨k.1.2, ?_⟩
      exact (D.piQ_eq_one_iff _).1 k.2
    · intro k k' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    · intro u
      have hu := u.2
      have huQ : (u : G) ∈ CFSG.Open.pCoreOf 2 M := hHQ (Subgroup.mem_inf.1 hu).1
      exact ⟨⟨⟨⟨(u : G), huQ⟩, (Subgroup.mem_inf.1 hu).1⟩,
        (D.piQ_eq_one_iff ⟨(u : G), huQ⟩).2 (Subgroup.mem_inf.1 hu).2⟩, rfl⟩
  rw [hker, hrange, hH'] at h1
  exact h1.symm

theorem heart_mem_piQ_qB
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q)
    (u : altHeart n) :
    Multiplicative.ofAdd (heartToBar u) ∈
      (C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ := by
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
  have hwQ : (w : G) ∈ CFSG.Open.pCoreOf 2 M := C.S.W_le_Q w.2
  have hwB : (w : G) ∈ C.qB := C.blockU_le_qB hQ w.2
  refine Subgroup.mem_map.2 ⟨⟨(w : G), hwQ⟩, Subgroup.mem_subgroupOf.2 hwB, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [D.piQ_W w ⟨(w : G), hwQ⟩ rfl, hw]
  rfl

theorem card_qB (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) :
    Nat.card ↥C.qB = Nat.card ↥(Rc X) *
      Nat.card ↥((C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) := by
  have h := D.card_eq_card_inf_R_mul C.qB_le_Q
  rwa [inf_eq_right.2 (C.Rc_le_qB hQ hR)] at h

end Cfg.PiData

end Group

section Klein

variable {n : ℕ}

@[expose] noncomputable def klein4 (I : Finset (Fin n)) : Subgroup (Perm (Fin n)) :=
  ((alternatingGroup.kleinFour ↥I).map (alternatingGroup ↥I).subtype).map
    (Perm.ofSubtype : Perm ↥I →* Perm (Fin n))

theorem card_subtype_finset (I : Finset (Fin n)) : Nat.card ↥I = I.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem mem_klein4_iff {I : Finset (Fin n)} (hI : I.card = 4) {σ : Perm (Fin n)} :
    σ ∈ klein4 I ↔ σ ∈ altOn I ∧ σ * σ = 1 := by
  have hα4 : Nat.card ↥I = 4 := by rw [card_subtype_finset, hI]
  constructor
  · intro h
    obtain ⟨g', ⟨g, hg, rfl⟩, rfl⟩ := Subgroup.mem_map.1 h
    refine ⟨Subgroup.mem_map.2 ⟨g.1, g.2, rfl⟩, ?_⟩
    have h2 : g ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨g, hg⟩ : ↥(alternatingGroup.kleinFour ↥I))
      rw [alternatingGroup.exponent_kleinFour_of_card_eq_four hα4] at this
      simpa using congrArg Subtype.val this
    have h3 : (g.1 : Perm ↥I) * g.1 = 1 := by
      have := congrArg Subtype.val h2
      simpa [pow_two] using this
    show Perm.ofSubtype g.1 * Perm.ofSubtype g.1 = 1
    rw [← map_mul, h3, map_one]
  · rintro ⟨hA, hsq⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hA
    have hg2 : g * g = 1 := by
      apply Perm.ofSubtype_injective
      rw [map_mul, hsq, map_one]
    have hord : orderOf g ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have hct := alternatingGroup.mem_kleinFour_of_order_two_pow hα4 hg hord
    refine Subgroup.mem_map.2 ⟨g, Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩, rfl⟩
    rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four hα4]
    rcases hct with h0 | h0
    · left
      have : g = 1 := Perm.cycleType_eq_zero.1 h0
      subst this
      rfl
    · right
      exact h0

theorem klein4_le_altOn {I : Finset (Fin n)} (hI : I.card = 4) : klein4 I ≤ altOn I :=
  fun _ h => ((mem_klein4_iff hI).1 h).1

theorem card_klein4 {I : Finset (Fin n)} (hI : I.card = 4) : Nat.card ↥(klein4 I) = 4 := by
  have hα4 : Nat.card ↥I = 4 := by rw [card_subtype_finset, hI]
  unfold klein4
  rw [Subgroup.card_map_of_injective Perm.ofSubtype_injective,
    Subgroup.card_map_of_injective (alternatingGroup ↥I).subtype_injective,
    alternatingGroup.kleinFour_card_of_card_eq_four hα4]

theorem isPGroup_klein4 {I : Finset (Fin n)} (hI : I.card = 4) : IsPGroup 2 ↥(klein4 I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 2) ?_
  rw [card_klein4 hI]
  norm_num

theorem klein4_conj_mem {I : Finset (Fin n)} (hI : I.card = 4) {τ : Perm (Fin n)}
    (hτ : τ ∈ setStab I) {σ : Perm (Fin n)} (hσ : σ ∈ klein4 I) : τ * σ * τ⁻¹ ∈ klein4 I := by
  obtain ⟨hA, hsq⟩ := (mem_klein4_iff hI).1 hσ
  refine (mem_klein4_iff hI).2 ⟨?_, ?_⟩
  · rw [mem_altOn] at hA ⊢
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 : τ⁻¹ x ∉ I := by
        intro h
        apply hx
        have := (mem_setStab.1 hτ (τ⁻¹ x)).2 h
        rwa [perm_apply_inv_self] at this
      simp only [Perm.mul_apply]
      rw [hA.1 _ h1, perm_apply_inv_self]
    · simp [hA.2]
  · calc τ * σ * τ⁻¹ * (τ * σ * τ⁻¹) = τ * (σ * σ) * τ⁻¹ := by group
      _ = 1 := by rw [hsq]; group

theorem klein4_fourGroup {I : Finset (Fin n)} (hI : I.card = 4) : FourGroup I (klein4 I) where
  two := isPGroup_klein4 hI
  stab := (klein4_le_altOn hI).trans (altOn_le_setStab I)
  fix := fun σ hσ x hx => (mem_altOn.1 (klein4_le_altOn hI hσ)).1 x hx
  norm := fun τ hτ σ hσ => klein4_conj_mem hI (altOn_le_setStab I hτ) hσ

end Klein

section Numeric

@[expose] noncomputable def uvec {n : ℕ} (x y : Fin n) : permBar n :=
  ((Pi.single x (1 : ZMod 2) + Pi.single y (1 : ZMod 2) : Fin n → ZMod 2) : permBar n)

theorem heartToBar_pairEW_eq_uvec {n : ℕ} (x y : Fin n) :
    heartToBar (pairEW x y : altHeart n) = uvec x y := by
  rw [heartToBar_pairEW]
  unfold uvec
  rw [QuotientAddGroup.mk_add]

theorem barAct_uvec {n : ℕ} (σ : Perm (Fin n)) (x y : Fin n) :
    barAct σ (uvec x y) = uvec (σ x) (σ y) := by
  unfold uvec
  rw [barAct_mk, map_add, vecPerm_single, vecPerm_single]

private theorem zmod2_aux5 : ∀ a b c : ZMod 2, -(a + b) + (c + b) = a + c := by decide

theorem neg_uvec_add_uvec {n : ℕ} (x y p : Fin n) : -(uvec x p) + uvec y p = uvec x y := by
  unfold uvec
  rw [← QuotientAddGroup.mk_neg, ← QuotientAddGroup.mk_add]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.neg_apply]
  exact zmod2_aux5 _ _ _

theorem uvec_moved {σ : Perm (Fin 10)} {x y : Fin 10} (hxy : x ≠ y) (h1 : σ x ≠ x)
    (h2 : σ x ≠ y) : barAct σ (uvec x y) ≠ uvec x y := by
  rw [barAct_uvec]
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := exists_ne_four (by norm_num : 5 ≤ 10) (σ x) (σ y) x y
  have hσxy : σ x ≠ σ y := fun h => hxy (σ.injective h)
  unfold uvec
  refine bar_mk_ne_of_coords (i := σ x) (j := j) ?_ ?_
  · simp only [Pi.add_apply, Pi.single_apply, if_true, hσxy, h1, h2, if_false]
    decide
  · simp only [Pi.add_apply, Pi.single_apply, hj1, hj2, hj3, hj4, if_false]

theorem _root_.CFSG.CGT.PushingUpLit.SolK.FourGroup.barAct_uvec_ne {I : Finset (Fin 10)}
    {N : Subgroup (Perm (Fin 10))} (h : FourGroup I N) (hI : I.card = 4) {σ σ' : Perm (Fin 10)}
    (hσ : σ ∈ N) (hσ1 : σ ≠ 1) (hσ' : σ' ∈ N) (hσ'1 : σ' ≠ 1) (hne : σ ≠ σ') {a : Fin 10}
    (ha : a ∈ I) : barAct σ (uvec a (σ' a)) ≠ uvec a (σ' a) :=
  uvec_moved (fun h' => h.free hI hσ' hσ'1 a ha h'.symm) (h.free hI hσ hσ1 a ha)
    (h.apart hI hσ hσ' hne ha)

theorem card_mul_le_of_cosets {H : Type*} [Group H] {A Z : Subgroup H} [Finite H] (hZA : Z ≤ A)
    {ι : Type*} [Finite ι] (a : ι → H) (haA : ∀ i, a i ∈ A)
    (hdist : ∀ i j, i ≠ j → (a i)⁻¹ * a j ∉ Z) : Nat.card Z * Nat.card ι ≤ Nat.card A := by
  let f : ↥Z × ι → ↥A := fun zi => ⟨a zi.2 * (zi.1 : H), A.mul_mem (haA zi.2) (hZA zi.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨z, i⟩ ⟨z', j⟩ h
    have h1 : a i * (z : H) = a j * (z' : H) := congrArg Subtype.val h
    by_cases hij : i = j
    · subst hij
      have : (z : H) = z' := mul_left_cancel h1
      rw [Subtype.ext this]
    · exfalso
      apply hdist j i (Ne.symm hij)
      have : (a j)⁻¹ * a i = (z' : H) * (z : H)⁻¹ := by
        calc (a j)⁻¹ * a i = (a j)⁻¹ * (a i * (z : H)) * (z : H)⁻¹ := by group
          _ = (a j)⁻¹ * (a j * (z' : H)) * (z : H)⁻¹ := by rw [h1]
          _ = (z' : H) * (z : H)⁻¹ := by group
      rw [this]
      exact Z.mul_mem z'.2 (Z.inv_mem z.2)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem card_mul_succ_le {F : Subgroup (Perm (Fin 10))}
    {A Z : Subgroup (Multiplicative (permBar 10))}
    (hA : ∀ u : altHeart 10, Multiplicative.ofAdd (heartToBar u) ∈ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z)
    (T : Finset (Fin 10)) (p : Fin 10) (hp : p ∉ T)
    (hP : ∀ x ∈ T, ∃ σ ∈ F, σ x ≠ x ∧ σ x ≠ p)
    (hQ : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ σ ∈ F, σ x ≠ x ∧ σ x ≠ y) :
    Nat.card Z * (T.card + 1) ≤ Nat.card A := by
  classical
  let a : Option ↥T → Multiplicative (permBar 10) := fun i =>
    match i with
    | none => 1
    | some x => Multiplicative.ofAdd (uvec (x : Fin 10) p)
  have haA : ∀ i, a i ∈ A := by
    intro i
    cases i with
    | none => exact A.one_mem
    | some x =>
      have := hA (pairEW (x : Fin 10) p : altHeart 10)
      rwa [heartToBar_pairEW_eq_uvec] at this
  have hcard : Nat.card (Option ↥T) = T.card + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe]
  have key := card_mul_le_of_cosets hZA a haA (fun i j hij hmem => by
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some y =>
        obtain ⟨σ, hσ, h1, h2⟩ := hP y y.2
        have hy : (y : Fin 10) ≠ p := fun h => hp (h ▸ y.2)
        have e : Multiplicative.toAdd ((a none)⁻¹ * a (some y)) = uvec (y : Fin 10) p := by
          simp [a]
        have := hZ _ hmem σ hσ
        rw [e] at this
        exact uvec_moved hy h1 h2 this
    | some x =>
      cases j with
      | none =>
        obtain ⟨σ, hσ, h1, h2⟩ := hP x x.2
        have hx : (x : Fin 10) ≠ p := fun h => hp (h ▸ x.2)
        have e : Multiplicative.toAdd ((a (some x))⁻¹ * a none) = -(uvec (x : Fin 10) p) := by
          simp [a]
        have := hZ _ hmem σ hσ
        rw [e, map_neg] at this
        exact uvec_moved hx h1 h2 (neg_inj.1 this)
      | some y =>
        have hxy : (x : Fin 10) ≠ y := fun h => hij (by rw [Subtype.ext h])
        obtain ⟨σ, hσ, h1, h2⟩ := hQ x x.2 y y.2 hxy
        have e : Multiplicative.toAdd ((a (some x))⁻¹ * a (some y)) =
            uvec (x : Fin 10) (y : Fin 10) := by
          simp only [a, toAdd_mul, toAdd_inv, toAdd_ofAdd]
          exact neg_uvec_add_uvec _ _ _
        have := hZ _ hmem σ hσ
        rw [e] at this
        exact uvec_moved hxy h1 h2 this)
  rwa [hcard] at key

theorem card_mul_card_lt {I : Finset (Fin 10)} (hI : I.card = 4)
    {F : Subgroup (Perm (Fin 10))} (hFle : F ≤ klein4 I) (hF1 : F ≠ ⊥)
    {A Z : Subgroup (Multiplicative (permBar 10))}
    (hA : ∀ u : altHeart 10, Multiplicative.ofAdd (heartToBar u) ∈ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z) :
    Nat.card Z * Nat.card F < Nat.card A := by
  classical
  have hN := klein4_fourGroup hI
  have hFdvd : Nat.card F ∣ 4 := by
    have := Subgroup.card_dvd_of_le hFle
    rwa [card_klein4 hI] at this
  have hF1' : Nat.card F ≠ 1 := fun h => hF1 (Subgroup.card_eq_one.1 h)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hdiv : Nat.card F = 2 ∨ Nat.card F = 4 := by
    have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hFdvd
    have hpos : 0 < Nat.card F := Nat.card_pos
    interval_cases h : Nat.card F
    · exact absurd rfl hF1'
    · exact Or.inl rfl
    · exact absurd hFdvd (by norm_num)
    · exact Or.inr rfl
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := I) (t := (Finset.univ : Finset (Fin 10))) (by rw [hI]; simp)
  obtain ⟨σ, hσF, hσ1⟩ : ∃ σ ∈ F, σ ≠ 1 := by
    obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    exact ⟨σ, hσ, fun h => hσ1 (Subtype.ext h)⟩
  have hfree : ∀ q ∈ I, σ q ≠ q := hN.free hI (hFle hσF) hσ1
  have hσI : ∀ q ∈ I, σ q ∈ I := fun q hq => (mem_setStab.1 (hN.stab (hFle hσF)) q).2 hq
  have hσsq : σ * σ = 1 := ((mem_klein4_iff hI).1 (hFle hσF)).2
  have hσσ : ∀ q, σ (σ q) = q := fun q => by
    have := congrArg (fun f : Perm (Fin 10) => f q) hσsq
    simpa [Perm.mul_apply] using this
  rcases hdiv with h2 | h4
  ·
    obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨c, hcI, hc⟩ := exists_fourth hI {a, σ a} (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hca, hcσ⟩ := hc
    have hac : a ≠ c := Ne.symm hca
    have hcard : ({a, c} : Finset (Fin 10)).card = 2 := Finset.card_pair hac
    have hpT : p ∉ ({a, c} : Finset (Fin 10)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hp (h ▸ haI), fun h => hp (h ▸ hcI)⟩
    have key := card_mul_succ_le hA hZA hZ {a, c} p hpT
      (fun x hx => by
        have hxI : x ∈ I := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        exact ⟨σ, hσF, hfree x hxI, fun h => hp (h ▸ hσI x hxI)⟩)
      (fun x hx y hy hxy => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl
        · rcases hy with rfl | rfl
          · exact absurd rfl hxy
          · exact ⟨σ, hσF, hfree _ haI, fun h => hcσ h.symm⟩
        · rcases hy with rfl | rfl
          · refine ⟨σ, hσF, hfree _ hcI, fun h => hcσ ?_⟩
            have := congrArg σ h
            rw [hσσ] at this
            exact this
          · exact absurd rfl hxy)
    rw [hcard] at key
    rw [h2]
    omega
  ·
    have hFN : F = klein4 I := Subgroup.eq_of_le_of_card_ge hFle (by rw [card_klein4 hI, h4])
    have hN1 : klein4 I ≠ ⊥ := hFN ▸ hF1
    have key := card_mul_succ_le hA hZA hZ I p hp
      (fun x hx => ⟨σ, hσF, hfree x hx, fun h => hp (h ▸ hσI x hx)⟩)
      (fun x hx y hy hxy => by
        obtain ⟨z, hzI, hz⟩ := exists_fourth hI {x, y} (Finset.card_le_two.trans (by norm_num))
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        obtain ⟨τ, hτ, hτx⟩ := hN.transitive hI hN1 hx hzI
        exact ⟨τ, hFN ▸ hτ, by rw [hτx]; exact hz.1, by rw [hτx]; exact hz.2⟩)
    rw [hI] at key
    rw [h4]
    omega

end Numeric

section TOf

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem Q_le_TOf
    (hQ : ∀ q ∈ CFSG.Open.pCoreOf 2 M, ∀ q' ∈ CFSG.Open.pCoreOf 2 M, q * q' = q' * q) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) : CFSG.Open.pCoreOf 2 M ≤ TOf M x := by
  refine le_pCoreOf_of_normalized (fun q hq => Subgroup.mem_inf.2 ⟨pCoreOf_le_self M hq, ?_⟩)
    (fun k hk q hq => pCoreOf_normalized M (Subgroup.mem_inf.1 hk).1 hq) (isPGroup_pCoreOf' M)
  exact mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (hQ q hq x hx))

namespace Cfg

variable (C : Cfg G M X n)

@[expose] noncomputable def thetaN (x : G) : Subgroup (Perm (Fin n)) :=
  ((TOf M x).subgroupOf M).map C.θ

theorem mem_thetaN {x : G} {σ : Perm (Fin n)} :
    σ ∈ C.thetaN x ↔ ∃ t : ↥M, (t : G) ∈ TOf M x ∧ C.θ t = σ := by
  unfold thetaN
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩⟩

theorem isPGroup_thetaN (x : G) : IsPGroup 2 (C.thetaN x) := by
  have h2 : IsPGroup 2 ↥((TOf M x).subgroupOf M) :=
    (isPGroup_TOf M x).of_equiv (Subgroup.subgroupOfEquivOfLe (TOf_le_M M x)).symm
  exact h2.map C.θ

end Cfg

end TOf

theorem isElemAbelian_conjSubgroup {G : Type} [Group G] {H : Subgroup G}
    (h : CFSG.Open.IsElemAbelian 2 H) (g : G) :
    CFSG.Open.IsElemAbelian 2 (conjSubgroup g H) := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun y hy => ?_⟩
  · have h1 := congrArg Subtype.val (h.1.is_comm.comm ⟨g⁻¹ * a * g, mem_conjSubgroup.1 a.2⟩
      ⟨g⁻¹ * b * g, mem_conjSubgroup.1 b.2⟩)
    have h1' : (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) =
        (g⁻¹ * (b : G) * g) * (g⁻¹ * (a : G) * g) := h1
    calc (a : G) * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1']
      _ = b * a := by group
  · have h1 := h.2 _ (mem_conjSubgroup.1 hy)
    rw [pow_two] at h1 ⊢
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

section Len4

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10}

namespace Cfg.PiData

variable (D : C.PiData)

theorem altOn_le_theta_CMOf {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : 2 * I.card < 10) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
    {S : Finset (Fin 10)} (hS : S = I ∨ S = Iᶜ) :
    altOn S ≤ ((CMOf M x).subgroupOf M).map C.θ := by
  refine altOn_le_of_threeCycles S _ fun τ hτ hsupp => ?_
  have hτS : τ ∈ altOn S := mem_altOn.2 ⟨hsupp, hτ.sign⟩
  have hτst : τ ∈ setStab S := altOn_le_setStab S hτS
  have hτI : τ ∈ setStab I := by
    rcases hS with rfl | rfl
    · exact hτst
    · exact setStab_compl_le I hτst
  have hfix : barAct τ (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) =
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) := by
    rw [hπ]
    exact (barAct_barInd_eq_self_iff hI _).2 hτI
  obtain ⟨y, hyθ, hyc⟩ := D.exists_comm_lift ⟨x, hx⟩ hτ hfix
  have hyM : (y : G) ∈ M := C.S.le y.2
  refine Subgroup.mem_map.2 ⟨⟨(y : G), hyM⟩, ?_, hyθ⟩
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.2 ⟨hyM, mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 hyc)⟩

theorem theta_mem_setStab_of_mem_CMOf {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 10)} (hI : 2 * I.card < 10)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {k : ↥M} (hk : (k : G) ∈ CMOf M x) :
    C.θ k ∈ setStab I := by
  have hc : (k : G) * x * (k : G)⁻¹ = x := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
  have := D.piQ_conj k ⟨x, hx⟩ ⟨x, hx⟩ hc.symm
  rw [hπ] at this
  exact (barAct_barInd_eq_self_iff hI _).1 this.symm

theorem thetaN_le_setStab {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : 2 * I.card < 10) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    C.thetaN x ≤ setStab I := by
  intro σ hσ
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  exact D.theta_mem_setStab_of_mem_CMOf hx hI hπ (TOf_le_C M x htT)

theorem thetaN_normalized {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : 2 * I.card < 10) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
    {S : Finset (Fin 10)} (hS : S = I ∨ S = Iᶜ) :
    ∀ τ ∈ altOn S, ∀ σ ∈ C.thetaN x, τ * σ * τ⁻¹ ∈ C.thetaN x := by
  intro τ hτ σ hσ
  obtain ⟨c, hcC, hcθ⟩ := Subgroup.mem_map.1 (D.altOn_le_theta_CMOf hx hI hπ hS hτ)
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcmT : (c : G) * (t : G) * (c : G)⁻¹ ∈ TOf M x := normalized_TOf M x hcC' htT
  refine C.mem_thetaN.2 ⟨⟨(c : G) * t * (c : G)⁻¹, TOf_le_M M x hcmT⟩, hcmT, ?_⟩
  have : (⟨(c : G) * (t : G) * (c : G)⁻¹, TOf_le_M M x hcmT⟩ : ↥M) = c * t * c⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hcθ]

theorem thetaN_fix_compl {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : 2 * I.card < 10) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    ∀ σ ∈ C.thetaN x, ∀ y, y ∉ I → σ y = y := by
  have hNIc : C.thetaN x ≤ setStab Iᶜ := fun σ hσ y => by
    have := mem_setStab.1 (D.thetaN_le_setStab hx hI hπ hσ) y
    simp [this]
  have hfix := block_fixes (C.isPGroup_thetaN x) hNIc
    (D.thetaN_normalized hx hI hπ (Or.inr rfl))
    (by rw [Finset.card_compl, Fintype.card_fin]; omega)
  exact fun σ hσ y hy => hfix σ hσ y (Finset.mem_compl.2 hy)

theorem fourGroup_thetaN {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)}
    (hI : I.card = 4) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    FourGroup I (C.thetaN x) :=
  ⟨C.isPGroup_thetaN x, D.thetaN_le_setStab hx (by omega) hπ,
    D.thetaN_fix_compl hx (by omega) hπ, D.thetaN_normalized hx (by omega) hπ (Or.inl rfl)⟩

theorem klein4_le_thetaN (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : klein4 I ≤ C.thetaN x := by
  classical
  set Lam : Subgroup G := CMOf M x ⊓ ((klein4 I).comap C.θ).map M.subtype with hLam
  have hmemLam : ∀ g : G, g ∈ Lam ↔
      g ∈ CMOf M x ∧ ∃ hg : g ∈ M, C.θ ⟨g, hg⟩ ∈ klein4 I := by
    intro g
    rw [hLam, Subgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hLamC : Lam ≤ CMOf M x := inf_le_left
  have hnorm : ∀ k ∈ CMOf M x, ∀ u ∈ Lam, k * u * k⁻¹ ∈ Lam := by
    intro k hk u hu
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hkM : k ∈ M := (Subgroup.mem_inf.1 hk).1
    have hkuM : k * u * k⁻¹ ∈ M := M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM)
    refine (hmemLam _).2 ⟨(CMOf M x).mul_mem ((CMOf M x).mul_mem hk huC) ((CMOf M x).inv_mem hk),
      hkuM, ?_⟩
    have e : (⟨k * u * k⁻¹, hkuM⟩ : ↥M) = ⟨k, hkM⟩ * ⟨u, huM⟩ * ⟨k, hkM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact klein4_conj_mem hI
      (D.theta_mem_setStab_of_mem_CMOf hx (by omega) hπ (k := ⟨k, hkM⟩) hk) huθ
  have hLam2 : IsPGroup 2 Lam := by
    refine isPGroup_two_of_forall fun u hu => ?_
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hsq := ((mem_klein4_iff hI).1 huθ).2
    have hK : u * u ∈ C.K := by
      refine C.mem_K.2 ⟨M.mul_mem huM huM, ?_⟩
      have e : (⟨u * u, M.mul_mem huM huM⟩ : ↥M) = ⟨u, huM⟩ * ⟨u, huM⟩ := rfl
      rw [e, map_mul, hsq]
    rw [C.K_eq_Q hR] at hK
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf M hK
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hj
  have hLamT : Lam ≤ TOf M x := le_pCoreOf_of_normalized hLamC hnorm hLam2
  intro σ hσ
  have hσA : σ ∈ altOn I := klein4_le_altOn hI hσ
  obtain ⟨c, hcC, hcθ⟩ :=
    Subgroup.mem_map.1 (D.altOn_le_theta_CMOf hx (by omega) hπ (Or.inl rfl) hσA)
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcLam : (c : G) ∈ Lam := (hmemLam _).2 ⟨hcC', c.2, by
    show C.θ c ∈ klein4 I
    rw [hcθ]
    exact hσ⟩
  exact C.mem_thetaN.2 ⟨c, hLamT hcLam, hcθ⟩

theorem theta_TOf_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    ((TOf M x).subgroupOf M).map C.θ = klein4 I := by
  have hF := D.fourGroup_thetaN hx hI hπ
  have hle := D.klein4_le_thetaN hR hx hI hπ
  have hc4 := hF.card_le_four hI
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_klein4 hI]; exact hc4)).symm

theorem elem_le_of_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {E : Subgroup G} (hET : E ≤ TOf M x)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ↥E ≤ Nat.card ↥C.qB ∧ (Nat.card ↥E = Nat.card ↥C.qB → E = C.qB) := by
  classical
  have hQ := C.Q_comm hR
  have hEM : E ≤ M := hET.trans (TOf_le_M M x)
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← pow_two]; exact hE.2 e he
  have hcardE := C.card_eq_card_inf_mul hR hEM
  by_cases hbot : (E.subgroupOf M).map C.θ = ⊥
  ·
    rw [hbot, Subgroup.card_bot, mul_one] at hcardE
    have hEQ : E ⊓ CFSG.Open.pCoreOf 2 M = E :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ CFSG.Open.pCoreOf 2 M ≤ E) hcardE.le
    have hEle : E ≤ CFSG.Open.pCoreOf 2 M := hEQ ▸ inf_le_right
    have hEB : E ≤ C.qB := fun e he => (C.mem_qB_iff hQ).2 ⟨hEle he, hEsq e he⟩
    exact ⟨Subgroup.card_le_of_le hEB, fun h => Subgroup.eq_of_le_of_card_ge hEB h.symm.le⟩
  ·
    set F : Subgroup (Perm (Fin 10)) := (E.subgroupOf M).map C.θ with hF
    have hFN : F ≤ klein4 I := by
      rw [← D.theta_TOf_len_four hR hx hI hπ]
      exact Subgroup.map_mono (fun m hm => hET hm)
    have hqBQ : C.qB ≤ CFSG.Open.pCoreOf 2 M := C.qB_le_Q
    set A : Subgroup (Multiplicative (permBar 10)) :=
      (C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ with hA
    set Zg : Subgroup G := C.qB ⊓ Subgroup.centralizer (E : Set G) with hZg
    set Zp : Subgroup (Multiplicative (permBar 10)) :=
      (Zg.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ with hZp
    have hZgQ : Zg ≤ CFSG.Open.pCoreOf 2 M := inf_le_left.trans hqBQ
    have hAU : ∀ u : altHeart 10, Multiplicative.ofAdd (heartToBar u) ∈ A :=
      D.heart_mem_piQ_qB hQ
    have hZpA : Zp ≤ A := by
      rintro z ⟨q, hq, rfl⟩
      exact ⟨q, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1, rfl⟩
    have hZpfix : ∀ z ∈ Zp, ∀ σ ∈ F,
        barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z := by
      rintro z ⟨q, hq, rfl⟩ σ ⟨m, hm, rfl⟩
      have hqE : (q : G) ∈ Subgroup.centralizer (E : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).2
      have hmE : (m : G) ∈ E := hm
      have hc : (m : G) * (q : G) = (q : G) * (m : G) :=
        Subgroup.mem_centralizer_iff.1 hqE (m : G) hmE
      have := D.piQ_conj m q q (by rw [Subgroup.coe_inv, hc]; group)
      exact this.symm
    have hlt := card_mul_card_lt hI hFN hbot hAU hZpA hZpfix
    have hcardZ := D.card_eq_card_inf_R_mul hZgQ
    have hcardB := D.card_eq_card_inf_R_mul hqBQ
    have hRB : C.qB ⊓ Rc X = Rc X := inf_eq_right.2 (C.Rc_le_qB hQ hR)
    rw [hRB] at hcardB
    have hZR : Nat.card ↥(Zg ⊓ Rc X) ≤ Nat.card ↥(Rc X) := Subgroup.card_le_of_le inf_le_right
    have hEZ : E ⊓ CFSG.Open.pCoreOf 2 M ≤ Zg := by
      intro e he
      obtain ⟨heE, heQ⟩ := Subgroup.mem_inf.1 he
      refine Subgroup.mem_inf.2 ⟨(C.mem_qB_iff hQ).2 ⟨heQ, hEsq e heE⟩,
        Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨h, hh⟩ ⟨e, heE⟩)
    have hEZc : Nat.card ↥(E ⊓ CFSG.Open.pCoreOf 2 M) ≤ Nat.card Zg := Subgroup.card_le_of_le hEZ
    have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
    have hlt' : Nat.card ↥E < Nat.card ↥C.qB := by
      rw [hcardE, hcardB]
      calc Nat.card ↥(E ⊓ CFSG.Open.pCoreOf 2 M) * Nat.card F
          ≤ Nat.card Zg * Nat.card F := Nat.mul_le_mul_right _ hEZc
        _ = (Nat.card ↥(Zg ⊓ Rc X) * Nat.card Zp) * Nat.card F := by rw [hcardZ]
        _ ≤ (Nat.card ↥(Rc X) * Nat.card Zp) * Nat.card F :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hZR)
        _ = Nat.card ↥(Rc X) * (Nat.card Zp * Nat.card F) := by ring
        _ < Nat.card ↥(Rc X) * Nat.card A := Nat.mul_lt_mul_of_pos_left hlt hRpos
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

theorem conj_qB_eq_of_le_TOf_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : conjSubgroup g C.qB ≤ TOf M x) : conjSubgroup g C.qB = C.qB := by
  obtain ⟨-, hEq⟩ := D.elem_le_of_len_four hR hx hI hπ hg
    (isElemAbelian_conjSubgroup (C.isElemAbelian_qB (C.Q_comm hR)) g)
  exact hEq (Subgroup.card_map_of_injective (MulAut.conj g).injective)

theorem mem_M_of_conj_qB_le_TOf_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : conjSubgroup g C.qB ≤ TOf M x) : g ∈ M := by
  have h := D.conj_qB_eq_of_le_TOf_len_four hR hx hI hπ hg
  have hn : g⁻¹ ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have key := mem_conjSubgroup (g := g) (T := C.qB) (x := b)
    rw [h] at key
    simpa using key
  have := (C.normalizer_qB_eq hR).le hn
  simpa using M.inv_mem this

theorem normalizer_le_M_of_qB_le_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {P : Subgroup G} (hBP : C.qB ≤ P)
    (hPT : P ≤ TOf M x) : Subgroup.normalizer (P : Set G) ≤ M := by
  intro g hg
  refine D.mem_M_of_conj_qB_le_TOf_len_four hR hx hI hπ fun e he => ?_
  have he' : g⁻¹ * e * g ∈ C.qB := mem_conjSubgroup.1 he
  have h2 := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * e * g)).1 (hBP he')
  have : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
  rw [this] at h2
  exact hPT h2

theorem normalizer_TOf_le_M_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) ≤ M :=
  D.normalizer_le_M_of_qB_le_len_four hR hx hI hπ
    (C.qB_le_Q.trans (Q_le_TOf (C.Q_comm hR) hx)) le_rfl

end Cfg.PiData

end Len4

end CFSG.RankThree.PartTwo.Sec19.SolEven
