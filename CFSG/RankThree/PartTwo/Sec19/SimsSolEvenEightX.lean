module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightP
public import CFSG.LargeExtraspecial.S9FiveB

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

namespace Eight

section Klein

variable {d : ℕ}

theorem klein8_comm {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ τ : Perm (Fin d)} (hσ : σ ∈ klein8 I) (hτ : τ ∈ klein8 I) : σ * τ = τ * σ := by
  have h1 := klein8_mul_self hI hIc hσ
  have h2 := klein8_mul_self hI hIc hτ
  have h3 := klein8_mul_self hI hIc ((klein8 I).mul_mem hσ hτ)
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right h1
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h2
  have h4 : (σ * τ)⁻¹ = σ * τ := inv_eq_of_mul_eq_one_right h3
  rw [mul_inv_rev, hσi, hτi] at h4
  exact h4.symm

theorem barAct_ne_of_odd_on {J : Finset (Fin d)} (hJ : J.card = 4) {σ : Perm (Fin d)}
    (hσ : σ ∈ klein4 J) (hσ1 : σ ≠ 1) {y u : Fin d → ZMod 2} (hy : ∑ k ∈ J, y k = 1)
    (hu : ∀ a ∈ J, ∀ b ∈ J, u a = u b) :
    barAct σ (y : permBar d) ≠ ((y + u : Fin d → ZMod 2) : permBar d) := by
  intro heq
  rw [barAct_mk, eq_comm, bar_mk_eq_iff] at heq
  obtain ⟨i, hi⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨j, hj, hij⟩ := pair_sum_ne hJ hσ hσ1 hy hi
  apply hij
  have hinv := klein4_inv hJ hσ
  have hcst : ∀ k ∈ J, y (σ k) + y k = u i ∨ y (σ k) + y k = u i + 1 → True := fun _ _ _ => trivial
  clear hcst
  have key : ∀ t s : ZMod 2, ∀ c : ZMod 2, (s = t + c) → t + s = c := by decide
  have key1 : ∀ t s : ZMod 2, ∀ c : ZMod 2, (s = t + c + 1) → t + s = c + 1 := by decide
  rcases heq with h | h
  · have e1 := h i
    have e2 := h j
    simp only [vecPerm_apply, hinv, Pi.add_apply] at e1 e2
    rw [add_comm (y (σ i)), add_comm (y (σ j)), key _ _ _ e1, key _ _ _ e2, hu i hi j hj]
  · have e1 := h i
    have e2 := h j
    simp only [vecPerm_apply, hinv, Pi.add_apply] at e1 e2
    rw [add_comm (y (σ i)), add_comm (y (σ j)), key1 _ _ _ e1, key1 _ _ _ e2, hu i hi j hj]

end Klein

section Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 8} (D : C.PiData)

@[expose] noncomputable def Q0 (I : Finset (Fin 8)) : Subgroup G where
  carrier := {q | ∃ hq : q ∈ CFSG.Open.pCoreOf 2 M,
    Multiplicative.toAdd (D.piQ ⟨q, hq⟩) ∈ qbar0 I}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(CFSG.Open.pCoreOf 2 M).mul_mem ha hb, ?_⟩
    have : (⟨a * b, (CFSG.Open.pCoreOf 2 M).mul_mem ha hb⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    exact (qbar0 I).add_mem ha' hb'
  one_mem' := ⟨(CFSG.Open.pCoreOf 2 M).one_mem, by
    have : (⟨1, (CFSG.Open.pCoreOf 2 M).one_mem⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := rfl
    rw [this, map_one, toAdd_one]
    exact (qbar0 I).zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(CFSG.Open.pCoreOf 2 M).inv_mem ha, ?_⟩
    have : (⟨a⁻¹, (CFSG.Open.pCoreOf 2 M).inv_mem ha⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        (⟨a, ha⟩)⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    exact (qbar0 I).neg_mem ha'

theorem Q0_le_Q (I : Finset (Fin 8)) : Q0 D I ≤ CFSG.Open.pCoreOf 2 M := fun _ hq => hq.1

theorem x_mem_Q0 {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)}
    (hI : I.card = 4) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : x ∈ Q0 D I :=
  ⟨hx, hπ ▸ barInd_mem_qbar0 hI (card_compl_eight hI)⟩

theorem Q0_le_of_normalized (hrbot : Rc X = ⊥) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {Y : Subgroup G}
    (hYQ : Y ≤ CFSG.Open.pCoreOf 2 M) (hYn : ∀ k ∈ CMOf M x, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    {y₀ : G} (hy₀ : y₀ ∈ Y) (h1 : y₀ ≠ 1) (h2 : y₀ ≠ x) : Q0 D I ≤ Y := by
  classical
  set W : AddSubgroup (permBar 8) :=
    Subgroup.toAddSubgroup' ((Y.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) with hW
  have hmemW : ∀ w, w ∈ W ↔ ∃ y : ↥(CFSG.Open.pCoreOf 2 M), (y : G) ∈ Y ∧
      Multiplicative.toAdd (D.piQ y) = w := by
    intro w
    rw [hW, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyw⟩
      exact ⟨y, hy, by rw [hyw]; rfl⟩
    · rintro ⟨y, hy, hyw⟩
      exact ⟨y, hy, by rw [← hyw]; rfl⟩
  have hinv : ∀ m : ↥M, (m : G) ∈ CMOf M x → ∀ w ∈ W, barAct (C.θ m) w ∈ W := by
    intro m hm w hw
    obtain ⟨y, hyY, rfl⟩ := (hmemW w).1 hw
    have hyQ' : (m : G) * y * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M m.2 y.2
    exact (hmemW _).2 ⟨⟨_, hyQ'⟩, hYn _ hm _ hyY, D.piQ_conj m y ⟨_, hyQ'⟩ rfl⟩
  have h3 : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ τ : Perm (Fin 8), τ.IsThreeCycle →
      (∀ y, y ∉ J → τ y = y) → ∀ w ∈ W, barAct τ w ∈ W := by
    intro J hJ τ hτ hsupp w hw
    have hτJ : τ ∈ setStab J := fun y => by
      by_cases hy : y ∈ J
      · refine iff_of_true ?_ hy
        by_contra h
        have := hsupp (τ y) h
        rw [τ.injective this] at h
        exact h hy
      · rw [hsupp y hy]
    have hτI : τ ∈ setStab I := by
      rcases hJ with rfl | rfl
      · exact hτJ
      · exact setStab_compl_le I hτJ
    have hfix : barAct τ (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) =
        Multiplicative.toAdd (D.piQ ⟨x, hx⟩) := by
      rw [hπ]
      exact barAct_barInd_of_mem_setStab hτI
    obtain ⟨t, htθ, htc⟩ := D.exists_comm_lift ⟨x, hx⟩ hτ hfix
    have htM : (t : G) ∈ M := C.S.le t.2
    have h := hinv ⟨t, htM⟩ (Subgroup.mem_inf.2 ⟨htM,
      mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 htc)⟩) w hw
    rwa [htθ] at h
  obtain ⟨s, hsC, hsw⟩ := exists_swap D hrbot hx hI hπ
  have hinj := piQ_injective D hrbot
  have hw₀ : Multiplicative.toAdd (D.piQ ⟨y₀, hYQ hy₀⟩) ∈ W := (hmemW _).2 ⟨_, hy₀, rfl⟩
  have hne0 : Multiplicative.toAdd (D.piQ ⟨y₀, hYQ hy₀⟩) ≠ 0 := by
    intro h
    apply h1
    have h' : D.piQ ⟨y₀, hYQ hy₀⟩ = D.piQ 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective h
    exact congrArg Subtype.val (hinj h')
  have hneI : Multiplicative.toAdd (D.piQ ⟨y₀, hYQ hy₀⟩) ≠ barInd I := by
    intro h
    apply h2
    rw [← hπ] at h
    exact congrArg Subtype.val (hinj (Multiplicative.toAdd.injective h))
  have hle := qbar0_le_of_invariant hI h3 hsw (hinv s hsC) hw₀ hne0 hneI
  intro q hq
  obtain ⟨hqQ, hqq⟩ := hq
  obtain ⟨y, hyY, hyq⟩ := (hmemW _).1 (hle hqq)
  have hyeq : (y : G) = q := congrArg Subtype.val (hinj (Multiplicative.toAdd.injective hyq) :
    y = ⟨q, hqQ⟩)
  rw [← hyeq]
  exact hyY

theorem normalizer_le_M_of_Q0_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {Y : Subgroup G}
    (hYQ : Y ≤ CFSG.Open.pCoreOf 2 M) (hQ0Y : Q0 D I ≤ Y) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  have hIc := card_compl_eight hI
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  have hx1 : x ≠ 1 := x_ne_one D hx hI (by norm_num) hπ
  have hYne : Y ≠ ⊥ := by
    intro h
    have := hQ0Y (x_mem_Q0 D hx hI hπ)
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  have hO2 : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (Y : Set G)) ≤
      CFSG.Open.pCoreOf 2 M := by
    refine (pCoreOf_le_self _).trans ?_
    intro m hm
    obtain ⟨hmM, hmc⟩ := Subgroup.mem_inf.1 hm
    have hfix : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ a ∈ J, ∀ b ∈ J,
        barAct (C.θ ⟨m, hmM⟩) (uvec a b) = uvec a b := by
      intro J hJ a ha b hb
      obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a b
      have hqQ0 : (q : G) ∈ Q0 D I := ⟨q.2, by rw [hq]; exact uvec_mem_qbar0 hIe hIce hJ ha hb⟩
      have hqY := hQ0Y hqQ0
      have hc : (q : G) = m * q * m⁻¹ := by
        have := Subgroup.mem_centralizer_iff.1 hmc q hqY
        calc (q : G) = q * m * m⁻¹ := by group
          _ = m * q * m⁻¹ := by rw [this]
      have h := D.piQ_conj ⟨m, hmM⟩ q q hc
      rw [hq] at h
      exact h.symm
    have hθ1 := eq_one_of_fix_pairs hI hfix
    have hK : m ∈ C.K := C.mem_K.2 ⟨hmM, hθ1⟩
    rwa [C.K_eq_Q hR] at hK
  exact (C.centralizer_le_M hR hYQ hYne hO2).2

theorem mem_of_K_normalized (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M)
    {Y : Subgroup G} (hYQ : Y ≤ CFSG.Open.pCoreOf 2 M)
    (hYn : ∀ k ∈ CGOf x, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) : ∀ y ∈ Y, y = 1 ∨ y = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀, h1, h2⟩ := hcon
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  have hQ0 := Q0_le_of_normalized D hrbot hx hI hπ hYQ
    (fun k hk y hy => hYn k (Subgroup.mem_inf.1 hk).2 y hy) hy₀ h1 h2
  have hN := normalizer_le_M_of_Q0_le D hR hx hI hπ hYQ hQ0
  apply hKM
  intro k hk
  apply hN
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hYn k hk y hy, fun hy => ?_⟩
  have := hYn k⁻¹ ((CGOf x).inv_mem hk) _ hy
  simpa [mul_assoc] using this

@[expose] noncomputable def commSq (x : G) : Subgroup G :=
  Subgroup.closure ({c | ∃ p ∈ CFSG.Open.pCoreOf 2 (CGOf x),
    ∃ p' ∈ CFSG.Open.pCoreOf 2 (CGOf x), c = p * p' * p⁻¹ * p'⁻¹} ∪
    {c | ∃ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), c = p * p})

theorem commSq_normalized {x k : G} (hk : k ∈ CGOf x) {y : G} (hy : y ∈ commSq x) :
    k * y * k⁻¹ ∈ commSq x := by
  have hPn : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), k * p * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
    fun p hp => pCoreOf_normalized _ hk hp
  induction hy using Subgroup.closure_induction with
  | mem c hc =>
    rcases hc with ⟨p, hp, p', hp', rfl⟩ | ⟨p, hp, rfl⟩
    · refine Subgroup.subset_closure (Or.inl ⟨k * p * k⁻¹, hPn p hp, k * p' * k⁻¹, hPn p' hp', ?_⟩)
      group
    · refine Subgroup.subset_closure (Or.inr ⟨k * p * k⁻¹, hPn p hp, ?_⟩)
      group
  | one => simpa using (commSq x).one_mem
  | mul a b _ _ ha hb =>
    have : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [this]
    exact (commSq x).mul_mem ha hb
  | inv a _ ha =>
    have : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
    rw [this]
    exact (commSq x).inv_mem ha

theorem commSq_le_Q (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    commSq x ≤ CFSG.Open.pCoreOf 2 M := by
  have hIc := card_compl_eight hI
  have hPM := P_le_M D hR hx hI hπ
  have hθ : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), ∀ hpM : p ∈ M, C.θ ⟨p, hpM⟩ ∈ klein8 I :=
    fun p hp hpM => theta_P_le D hR hx hI hπ
      (Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩)
  have hK : ∀ g (hg : g ∈ M), C.θ ⟨g, hg⟩ = 1 → g ∈ CFSG.Open.pCoreOf 2 M := by
    intro g hg h
    have hK : g ∈ C.K := C.mem_K.2 ⟨hg, h⟩
    rwa [C.K_eq_Q hR] at hK
  refine (Subgroup.closure_le _).2 ?_
  rintro c (⟨p, hp, p', hp', rfl⟩ | ⟨p, hp, rfl⟩)
  · have hpM := hPM hp
    have hp'M := hPM hp'
    have hcM : p * p' * p⁻¹ * p'⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hpM hp'M) (M.inv_mem hpM)) (M.inv_mem hp'M)
    refine hK _ hcM ?_
    have e : (⟨p * p' * p⁻¹ * p'⁻¹, hcM⟩ : ↥M) =
        ⟨p, hpM⟩ * ⟨p', hp'M⟩ * ⟨p, hpM⟩⁻¹ * ⟨p', hp'M⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      klein8_comm hI hIc (hθ p hp hpM) (hθ p' hp' hp'M)]
    group
  · have hpM := hPM hp
    refine hK _ (M.mul_mem hpM hpM) ?_
    have e : (⟨p * p, M.mul_mem hpM hpM⟩ : ↥M) = ⟨p, hpM⟩ * ⟨p, hpM⟩ := rfl
    rw [e, map_mul]
    exact klein8_mul_self hI hIc (hθ p hp hpM)

theorem comm_mem_of_not_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) {p p' : G}
    (hp : p ∈ CFSG.Open.pCoreOf 2 (CGOf x)) (hp' : p' ∈ CFSG.Open.pCoreOf 2 (CGOf x)) :
    p * p' * p⁻¹ * p'⁻¹ = 1 ∨ p * p' * p⁻¹ * p'⁻¹ = x :=
  mem_of_K_normalized D hR hx hI hπ hKM (commSq_le_Q D hR hx hI hπ)
    (fun k hk y hy => commSq_normalized hk hy) _
    (Subgroup.subset_closure (Or.inl ⟨p, hp, p', hp', rfl⟩))

theorem sq_mem_of_not_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) {p : G}
    (hp : p ∈ CFSG.Open.pCoreOf 2 (CGOf x)) : p * p = 1 ∨ p * p = x :=
  mem_of_K_normalized D hR hx hI hπ hKM (commSq_le_Q D hR hx hI hπ)
    (fun k hk y hy => commSq_normalized hk hy) _
    (Subgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩))

theorem P_inf_Q_le_Q0 (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M ≤ Q0 D I := by
  classical
  have hIc := card_compl_eight hI
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  intro q hq
  obtain ⟨hqP, hqQ⟩ := Subgroup.mem_inf.1 hq
  refine ⟨hqQ, ?_⟩
  by_contra hq0
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (D.piQ ⟨q, hqQ⟩))
  rw [← hy, mem_qbar0_mk hIe hIce] at hq0
  obtain ⟨J, hJ, hodd⟩ : ∃ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) ∧ ∑ k ∈ J, y k = 1 := by
    have hcases : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
    by_cases h1 : ∑ i ∈ I, y i = 0
    · exact ⟨Iᶜ, Or.inr rfl, hcases _ fun h2 => hq0 ⟨h1, h2⟩⟩
    · exact ⟨I, Or.inl rfl, hcases _ h1⟩
  have hJc : J.card = 4 := by rcases hJ with rfl | rfl <;> assumption
  have hF := klein4_fourGroup hJc
  have hN1 : klein4 J ≠ ⊥ := by
    intro h
    have := card_klein4 hJc
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨σ, hσN, hσ1, -⟩ := hF.exists_ne hJc hN1 1
  have hσ8 : σ ∈ klein8 I := by
    rcases hJ with rfl | rfl
    · exact klein4_le_klein8 J hσN
    · exact klein4_compl_le_klein8 I hσN
  rw [← theta_P_eq D hR hx hI hπ hKM] at hσ8
  obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 hσ8
  have hpP : (pm : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := Subgroup.mem_subgroupOf.1 hpm
  have hc := comm_mem_of_not_le D hR hx hI hπ hKM hpP hqP
  have hpq : (pm : G) * q * (pm : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M pm.2 hqQ
  have hconj := D.piQ_conj pm ⟨q, hqQ⟩ ⟨(pm : G) * q * (pm : G)⁻¹, hpq⟩ rfl
  rw [hpmσ, ← hy] at hconj
  have hu : ∀ u : Fin 8 → ZMod 2, (u = 0 ∨ u = indVec I) → ∀ a ∈ J, ∀ b ∈ J, u a = u b := by
    rintro u (rfl | rfl) a ha b hb
    · rfl
    · rcases hJ with rfl | rfl
      · simp [indVec, ha, hb]
      · simp only [Finset.mem_compl] at ha hb
        simp [indVec, ha, hb]
  rcases hc with hc | hc
  · have e : (pm : G) * q * (pm : G)⁻¹ = q := by
      calc (pm : G) * q * (pm : G)⁻¹ = (pm * q * (pm : G)⁻¹ * q⁻¹) * q := by group
        _ = q := by rw [hc, one_mul]
    have h' : Multiplicative.toAdd (D.piQ ⟨(pm : G) * q * (pm : G)⁻¹, hpq⟩) =
        ((y + 0 : Fin 8 → ZMod 2) : permBar 8) := by
      rw [add_zero, hy]
      congr 2
      exact Subtype.ext e
    rw [h'] at hconj
    exact barAct_ne_of_odd_on hJc hσN hσ1 hodd (hu 0 (Or.inl rfl)) hconj.symm
  · have e : (pm : G) * q * (pm : G)⁻¹ = x * q := by
      calc (pm : G) * q * (pm : G)⁻¹ = (pm * q * (pm : G)⁻¹ * q⁻¹) * q := by group
        _ = x * q := by rw [hc]
    have h' : Multiplicative.toAdd (D.piQ ⟨(pm : G) * q * (pm : G)⁻¹, hpq⟩) =
        ((y + indVec I : Fin 8 → ZMod 2) : permBar 8) := by
      have e' : (⟨(pm : G) * q * (pm : G)⁻¹, hpq⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
          ⟨x, hx⟩ * ⟨q, hqQ⟩ := Subtype.ext e
      rw [e', map_mul, toAdd_mul, hπ, ← hy, QuotientAddGroup.mk_add, add_comm]
      rfl
    rw [h'] at hconj
    exact barAct_ne_of_odd_on hJc hσN hσ1 hodd (hu _ (Or.inr rfl)) hconj.symm

theorem Q0_le_P (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    Q0 D I ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  classical
  have hIc := card_compl_eight hI
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  have hinj := piQ_injective D hrbot
  set W : AddSubgroup (permBar 8) := Subgroup.toAddSubgroup'
    (((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) with hW
  have hmemW : ∀ w, w ∈ W ↔ ∃ y : ↥(CFSG.Open.pCoreOf 2 M),
      (y : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) ∧ Multiplicative.toAdd (D.piQ y) = w := by
    intro w
    rw [hW, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyw⟩
      exact ⟨y, hy, by rw [hyw]; rfl⟩
    · rintro ⟨y, hy, hyw⟩
      exact ⟨y, hy, by rw [← hyw]; rfl⟩
  have hpairs : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → ∀ a ∈ J, ∀ b ∈ J, uvec a b ∈ W := by
    intro J hJ a ha b hb
    by_cases hab : a = b
    · subst hab
      rw [uvec_self]
      exact W.zero_mem
    have hJc : J.card = 4 ∧ Jᶜ.card = 4 := by
      rcases hJ with rfl | rfl
      · exact ⟨hI, hIc⟩
      · rw [compl_compl]; exact ⟨hIc, hI⟩
    have hF := klein4_fourGroup hJc.1
    have hN1 : klein4 J ≠ ⊥ := by
      intro h
      have := card_klein4 hJc.1
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨σ, hσN, hσa⟩ := hF.transitive hJc.1 hN1 ha hb
    have hσ8 : σ ∈ klein8 I := by
      rcases hJ with rfl | rfl
      · exact klein4_le_klein8 J hσN
      · exact klein4_compl_le_klein8 I hσN
    rw [← theta_P_eq D hR hx hI hπ hKM] at hσ8
    obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 hσ8
    have hpP : (pm : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := Subgroup.mem_subgroupOf.1 hpm
    obtain ⟨e, heJ⟩ : Jᶜ.Nonempty := Finset.card_pos.1 (by omega)
    have hefix : σ e = e := hF.fix σ hσN e (Finset.mem_compl.1 heJ)
    obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a e
    have hqK : (q : G) ∈ CGOf x := H4b.Q_le_CGOf C hR hx q.2
    have hpq : (pm : G) * (q : G) * (pm : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      pCoreOf_normalized M pm.2 q.2
    have hconj := D.piQ_conj pm q ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩ rfl
    let cq : ↥(CFSG.Open.pCoreOf 2 M) := q⁻¹ * ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩
    have hπc : Multiplicative.toAdd (D.piQ cq) = uvec a b := by
      simp only [cq, map_mul, map_inv, toAdd_mul, toAdd_inv]
      rw [hconj, hpmσ, hq, barAct_uvec, hσa, hefix]
      exact neg_uvec_add_uvec a b e
    have hcP : (cq : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
      have e' : (cq : G) = ((q : G)⁻¹ * (pm : G) * (q : G)) * (pm : G)⁻¹ := by
        show (q : G)⁻¹ * ((pm : G) * (q : G) * (pm : G)⁻¹) = _
        group
      have h3 : (q : G)⁻¹ * (pm : G) * (q : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
        have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hpP
        simpa using this
      rw [e']
      exact (CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem h3
        ((CFSG.Open.pCoreOf 2 (CGOf x)).inv_mem hpP)
    exact (hmemW _).2 ⟨cq, hcP, hπc⟩
  have hle := qbar0_le_of_pairs hIe hIce (Finset.card_pos.1 (by omega))
    (Finset.card_pos.1 (by omega)) hpairs
  intro q hq
  obtain ⟨hqQ, hqq⟩ := hq
  obtain ⟨y, hyP, hyq⟩ := (hmemW _).1 (hle hqq)
  have hyeq : (y : G) = q := congrArg Subtype.val (hinj (Multiplicative.toAdd.injective hyq) :
    y = ⟨q, hqQ⟩)
  rw [← hyeq]
  exact hyP

theorem card_Q0 (hrbot : Rc X = ⊥) {I : Finset (Fin 8)} (hI : I.card = 4) :
    Nat.card ↥(Q0 D I) = 2 ^ 5 := by
  have hIc := card_compl_eight hI
  have hIe : Even I.card := by rw [hI]; decide
  have hIce : Even Iᶜ.card := by rw [hIc]; decide
  have h := D.card_eq_card_inf_R_mul (Q0_le_Q D I)
  have hR1 : Q0 D I ⊓ Rc X = ⊥ := by rw [hrbot, inf_bot_eq]
  rw [hR1, Subgroup.card_bot, one_mul, ← card_toAddSubgroup'] at h
  rw [h, ← card_qbar0 hI]
  congr 2
  ext w
  rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqw⟩
    obtain ⟨hqQ, hqq⟩ := Subgroup.mem_subgroupOf.1 hq
    have hw : w = Multiplicative.toAdd (D.piQ q) := by rw [hqw]; rfl
    rw [hw]
    exact hqq
  · intro hw
    obtain ⟨q, hq⟩ := exists_piQ_eq_of_heart D (qbar0_le_heart hIe hIce hw)
    refine ⟨q, Subgroup.mem_subgroupOf.2 ⟨q.2, ?_⟩, ?_⟩
    · rw [hq]
      exact hw
    · rw [← hq]
      rfl

theorem P_inf_Q_eq_Q0 (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊓ CFSG.Open.pCoreOf 2 M = Q0 D I :=
  le_antisymm (P_inf_Q_le_Q0 D hR hx hI hπ hKM)
    (le_inf (Q0_le_P D hR hx hI hπ hKM) (Q0_le_Q D I))

theorem card_P (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x)) = 2 ^ 9 := by
  have h := C.card_eq_card_inf_mul hR (P_le_M D hR hx hI hπ)
  rw [P_inf_Q_eq_Q0 D hR hx hI hπ hKM, theta_P_eq D hR hx hI hπ hKM,
    card_klein8 hI (card_compl_eight hI), card_Q0 D (rc_eq_bot D hR hx hI hπ hKM) hI] at h
  rw [h]
  norm_num

theorem center_P (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) {z : G}
    (hzP : z ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (hz : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * z = z * p) : z = 1 ∨ z = x := by
  have hzQ := center_P_le_Q D hR hx hI hπ hKM hzP hz
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  have hinj := piQ_injective D hrbot
  have hθP := theta_P_eq D hR hx hI hπ hKM
  have hfix : ∀ σ ∈ klein8 I, barAct σ (Multiplicative.toAdd (D.piQ ⟨z, hzQ⟩)) =
      Multiplicative.toAdd (D.piQ ⟨z, hzQ⟩) := by
    intro σ hσ
    rw [← hθP] at hσ
    obtain ⟨pm, hpm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hpP : (pm : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := Subgroup.mem_subgroupOf.1 hpm
    have hc : z = (pm : G) * z * (pm : G)⁻¹ := by
      calc z = z * pm * (pm : G)⁻¹ := by group
        _ = pm * z * (pm : G)⁻¹ := by rw [hz _ hpP]
    exact (D.piQ_conj pm ⟨z, hzQ⟩ ⟨z, hzQ⟩ hc).symm
  rcases eq_zero_or_barInd_of_fixed hI (fun σ hσ => hfix σ (klein4_le_klein8 I hσ))
    (fun σ hσ => hfix σ (klein4_compl_le_klein8 I hσ)) with h | h
  · left
    have h' : D.piQ ⟨z, hzQ⟩ = D.piQ 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective h
    exact congrArg Subtype.val (hinj h')
  · right
    rw [← hπ] at h
    exact congrArg Subtype.val (hinj (Multiplicative.toAdd.injective h))

theorem orderOf_x (hrbot : Rc X = ⊥) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : orderOf x = 2 := by
  have hx1 := x_ne_one D hx hI (by norm_num) hπ
  have hsq : x * x = 1 := by
    have h1 : D.piQ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, toAdd_mul, hπ, permBar_add_self, toAdd_one]
    have h2 := (D.piQ_eq_one_iff _).1 h1
    rw [hrbot, Subgroup.mem_bot] at h2
    exact h2
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hx1

theorem centralizer_le_M_or_extraspecial (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    CGOf x ≤ M ∨ (IsExtraspecialPGroup 2 ↥(CFSG.Open.pCoreOf 2 (CGOf x)) ∧
      Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf x)) = 2 ^ 9 ∧ orderOf x = 2) := by
  classical
  by_cases hKM : CGOf x ≤ M
  · exact Or.inl hKM
  right
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  have hord := orderOf_x D hrbot hx hI hπ
  have hcard := card_P D hR hx hI hπ hKM
  refine ⟨?_, hcard, hord⟩
  set P := CFSG.Open.pCoreOf 2 (CGOf x) with hP
  have hxP : x ∈ P := Q0_le_P D hR hx hI hπ hKM (x_mem_Q0 D hx hI hπ)
  set xP : ↥P := ⟨x, hxP⟩ with hxPdef
  have hxPc : ∀ p : ↥P, p * xP = xP * p := by
    intro p
    have hpK : (p : G) ∈ CGOf x := pCoreOf_le_self _ p.2
    have h := mem_centralizer_zpowers_iff.1 hpK
    exact Subtype.ext (by
      show (p : G) * x = x * p
      calc (p : G) * x = (p * x * (p : G)⁻¹) * p := by group
        _ = x * p := by rw [h])
  have hmemZ : ∀ a : ↥P, ((a : G) = 1 ∨ (a : G) = x) → a ∈ Subgroup.zpowers xP := by
    rintro a (h | h)
    · have : a = 1 := Subtype.ext h
      rw [this]
      exact (Subgroup.zpowers xP).one_mem
    · have : a = xP := Subtype.ext h
      rw [this]
      exact Subgroup.mem_zpowers xP
  refine LargeExtraspecial.S9.isExtraspecialPGroup_of_center (isPGroup_pCoreOf' _)
    (Z := Subgroup.zpowers xP) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_zpowers]
    have : orderOf xP = orderOf x := Subgroup.orderOf_mk x hxP
    rw [this, hord]
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.2 fun p => hxPc p
  · intro a b
    refine hmemZ _ ?_
    have := comm_mem_of_not_le D hR hx hI hπ hKM a.2 b.2
    simpa [commutatorElement_def] using this
  · intro a
    refine hmemZ _ ?_
    have := sq_mem_of_not_le D hR hx hI hπ hKM a.2
    simpa [pow_two] using this
  · intro a ha
    refine hmemZ _ (center_P D hR hx hI hπ hKM a.2 fun p hp => ?_)
    exact congrArg Subtype.val (ha ⟨p, hp⟩).symm
  · by_contra hall
    push Not at hall
    have hle : (⊤ : Subgroup ↥P) ≤ Subgroup.zpowers xP := fun a _ => hall a
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, Nat.card_zpowers, Subgroup.orderOf_mk x hxP, hord, hcard] at h1
    norm_num at h1

end Eight

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
