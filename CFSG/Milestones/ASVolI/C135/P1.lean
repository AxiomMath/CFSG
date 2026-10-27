module

public import CFSG.Milestones.ASVolI.C135.P2
public import CFSG.Milestones.ASVolI.C135.N1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_dualHom coe_slNat moduleAct_false_eq
  moduleAct_true_eq)
open scoped Matrix commutatorElement

variable {G : Type} [Group G]

theorem burnsideC135_centerOf_eq_map (P : Subgroup G) :
    centerOf P = (Subgroup.center ↥P).map P.subtype := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · intro hz
    refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2)
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z'.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨y, hy⟩)⟩

theorem burnsideC135_le_normalizer_of_conj {L W : Subgroup G}
    (h : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) : L ≤ Subgroup.normalizer (W : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h l hl w, fun hw => ?_⟩
  have := h l⁻¹ (L.inv_mem hl) _ hw
  simpa [mul_assoc] using this

section Case3

variable [Finite G] {L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

@[expose] def burnsideC135_proj (F : Type) [Field F] (i : Fin 2) :
    Multiplicative (Fin 2 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => Fin 3 → F) i)

theorem burnsideC135_comm_mem_U {Q : Subgroup G} {dual : Bool} {k : ℕ}
    (h2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α dual k) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) : x * y * x⁻¹ * y⁻¹ ∈ centerOf Q := by
  obtain ⟨-, -, β, -, hβk, -⟩ := h2
  have h1 : (⟨x, hx⟩ : ↥Q) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (β _) (β _)]
    group
  rw [hβk, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem burnsideC135_sq_mem_U {Q : Subgroup G} {dual : Bool} {k : ℕ}
    (h2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α dual k) {x : G} (hx : x ∈ Q) :
    x * x ∈ centerOf Q := by
  obtain ⟨-, -, β, -, hβk, -⟩ := h2
  have h1 : (⟨x, hx⟩ : ↥Q) * ⟨x, hx⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i j
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [hβk, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem burnsideC135_slNat_ker (hα : IsModO2Surj L α) : (slNat α).ker = CFSG.pCore 2 ↥L := by
  rw [← hα.2]
  ext l
  simp only [MonoidHom.mem_ker, slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem burnsideC135_dualSplit_of_case3 (hα : IsModO2Surj L α) {Q : Subgroup G}
    (h1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2) :
    ∃ (W₁ W₂ : Subgroup G) (βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F))
      (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)) (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)),
      burnsideC135_DSG Q L W₁ W₂ (slNat α) βU β₁ β₂ := by
  classical
  set U := centerOf Q with hU
  obtain ⟨hLU, -, β', hβ's, hβ'k, hβ'eq⟩ := h1
  obtain ⟨hLQ, hUQ, β, hβs, hβk, hβeq⟩ := h2
  let e1 : Multiplicative (Fin 1 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
    AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => Fin 3 → F) 0)
  have he1 : Function.Bijective e1 := by
    refine ⟨fun a b h => ?_, fun c => ⟨Multiplicative.ofAdd (fun _ => c), rfl⟩⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0]
    exact congrArg Multiplicative.toAdd h
  let βU : ↥U →* Multiplicative (Fin 3 → F) := e1.comp β'
  let K : Fin 2 → Subgroup (Multiplicative (Fin 2 → Fin 3 → F)) := fun i =>
    { carrier := {v | Multiplicative.toAdd v i = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [toAdd_mul, Pi.add_apply, ha, hb, add_zero]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [toAdd_inv, Pi.neg_apply, ha, neg_zero] }
  let W : Fin 2 → Subgroup G := fun i => ((K i).comap β).map Q.subtype
  have hmemW : ∀ i (g : G), g ∈ W i ↔ ∃ h : g ∈ Q, Multiplicative.toAdd (β ⟨g, h⟩) i = 0 := by
    intro i g
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h, hq⟩
      exact ⟨⟨g, h⟩, hq, rfl⟩
  have hWQ : ∀ i, W i ≤ Q := fun i g hg => ((hmemW i g).mp hg).1
  let βW : ∀ i : Fin 2, ↥(W i) →* Multiplicative (Fin 3 → F) := fun i =>
    (burnsideC135_proj F (1 - i)).comp (β.comp (Subgroup.inclusion (hWQ i)))
  have hβW : ∀ i (w : ↥(W i)), βW i w =
      Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨w, hWQ i w.2⟩) (1 - i)) := fun _ _ => rfl
  have hcoord : ∀ (i : Fin 2) (x : Fin 3 → F), ∃ q : ↥Q,
      Multiplicative.toAdd (β q) i = 0 ∧ Multiplicative.toAdd (β q) (1 - i) = x := by
    intro i x
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun j => if j = i then 0 else x))
    refine ⟨q, ?_, ?_⟩
    · rw [hq]; simp
    · rw [hq]
      have : (1 - i : Fin 2) ≠ i := by fin_cases i <;> decide
      simp [this]
  have hUW : ∀ i, U ≤ W i := by
    intro i u hu
    refine (hmemW i u).mpr ⟨hUQ hu, ?_⟩
    have h1 : (⟨u, hUQ hu⟩ : ↥Q) ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact hu
    rw [MonoidHom.mem_ker] at h1
    rw [h1]
    rfl
  have hker : ∀ (q : ↥Q), Multiplicative.toAdd (β q) 0 = 0 → Multiplicative.toAdd (β q) 1 = 0 →
      (q : G) ∈ U := by
    intro q h0 h1
    have h2 : q ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext j
      fin_cases j
      · exact h0
      · exact h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hconj : ∀ (l : ↥L) (q : ↥Q),
      Multiplicative.toAdd (β ⟨(l : G) * q * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp q.2⟩) =
      fun j => ((dualHom (slNat α l) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β q) j := by
    intro l q
    funext j
    rw [hβeq l q _ rfl j, moduleAct_true_eq]
  have hnorm : ∀ i, L ≤ Subgroup.normalizer (W i : Set G) := by
    intro i
    refine burnsideC135_le_normalizer_of_conj fun l hl w hw => ?_
    obtain ⟨hwQ, hw0⟩ := (hmemW i w).mp hw
    refine (hmemW i _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hLQ hl) _).mp hwQ, ?_⟩
    have := congrFun (hconj ⟨l, hl⟩ ⟨w, hwQ⟩) i
    rw [this, hw0, Matrix.mulVec_zero]
  refine ⟨W 1, W 0, βU, βW 1, βW 0, ?_⟩
  refine ⟨burnsideC135_slNat_surj hα.1, hLQ, hUW 1, hUW 0, hWQ 1, hWQ 0, ?_, ?_, hnorm 1, hnorm 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_antisymm (sup_le (hWQ 1) (hWQ 0)) fun q hq => ?_
    obtain ⟨q₁, hq₁1, hq₁0⟩ := hcoord 1 (Multiplicative.toAdd (β ⟨q, hq⟩) 0)
    have hq₁W : (q₁ : G) ∈ W 1 := (hmemW 1 q₁).mpr ⟨q₁.2, hq₁1⟩
    have hq₂W : (q₁ : G)⁻¹ * q ∈ W 0 := by
      refine (hmemW 0 _).mpr ⟨Q.mul_mem (Q.inv_mem q₁.2) hq, ?_⟩
      have e : (⟨(q₁ : G)⁻¹ * q, Q.mul_mem (Q.inv_mem q₁.2) hq⟩ : ↥Q) = q₁⁻¹ * ⟨q, hq⟩ := rfl
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
      have : (1 - 1 : Fin 2) = 0 := rfl
      rw [this] at hq₁0
      rw [hq₁0, neg_add_cancel]
    have e : q = (q₁ : G) * ((q₁ : G)⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq₁W) (Subgroup.mem_sup_right hq₂W)
  ·
    refine le_antisymm (fun g hg => ?_) (le_inf (hUW 1) (hUW 0))
    obtain ⟨hgQ, hg1⟩ := (hmemW 1 g).mp hg.1
    obtain ⟨hgQ', hg0⟩ := (hmemW 0 g).mp hg.2
    exact hker ⟨g, hgQ⟩ hg0 hg1
  ·
    exact he1.2.comp hβ's
  ·
    rw [MonoidHom.ker_comp_of_injective β' e1 he1.1, hβ'k, Subgroup.bot_subgroupOf]
  ·
    intro l u v huv
    show Multiplicative.toAdd (e1 (β' v)) = _
    have h := hβ'eq l u v huv 0
    rw [moduleAct_false_eq] at h
    exact h
  ·
    intro x
    obtain ⟨q, hq1, hq0⟩ := hcoord 1 x
    refine ⟨⟨q, (hmemW 1 q).mpr ⟨q.2, hq1⟩⟩, ?_⟩
    rw [hβW]
    apply Multiplicative.toAdd.injective
    exact hq0
  ·
    refine Subgroup.ext fun w => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβW]
    obtain ⟨hwQ, hw1⟩ := (hmemW 1 w).mp w.2
    constructor
    · intro h
      have h0 : Multiplicative.toAdd (β ⟨w, hWQ 1 w.2⟩) 0 = 0 :=
        congrArg Multiplicative.toAdd h
      exact hker _ h0 hw1
    · intro h
      have h1 : (⟨w, hWQ 1 w.2⟩ : ↥Q) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact h
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  ·
    intro l u v huv
    rw [hβW, hβW, toAdd_ofAdd, toAdd_ofAdd]
    have e : (⟨v, hWQ 1 v.2⟩ : ↥Q) = ⟨(l : G) * (u : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp (hWQ 1 u.2)⟩ := Subtype.ext huv
    rw [e, hconj l ⟨u, hWQ 1 u.2⟩, coe_dualHom]
  ·
    intro x
    obtain ⟨q, hq0, hq1⟩ := hcoord 0 x
    refine ⟨⟨q, (hmemW 0 q).mpr ⟨q.2, hq0⟩⟩, ?_⟩
    rw [hβW]
    apply Multiplicative.toAdd.injective
    exact hq1
  ·
    refine Subgroup.ext fun w => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβW]
    obtain ⟨hwQ, hw0⟩ := (hmemW 0 w).mp w.2
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (β ⟨w, hWQ 0 w.2⟩) 1 = 0 :=
        congrArg Multiplicative.toAdd h
      exact hker _ hw0 h1
    · intro h
      have h1 : (⟨w, hWQ 0 w.2⟩ : ↥Q) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact h
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  ·
    intro l u v huv
    rw [hβW, hβW, toAdd_ofAdd, toAdd_ofAdd]
    have e : (⟨v, hWQ 0 v.2⟩ : ↥Q) = ⟨(l : G) * (u : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp (hWQ 0 u.2)⟩ := Subtype.ext huv
    rw [e, hconj l ⟨u, hWQ 0 u.2⟩, coe_dualHom]

theorem burnsideC135_isSpecial (hα : IsModO2Surj L α) {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {Q : Subgroup G} (h1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2) :
    IsSpecial2Group (3 * n) (6 * n) ↥Q := by
  classical
  have hcomm := fun {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) => burnsideC135_comm_mem_U h2 hx hy
  have hsq := fun {x : G} (hx : x ∈ Q) => burnsideC135_sq_mem_U h2 hx
  have hmemZ : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q ↔ (z : G) ∈ centerOf Q := by
    intro z
    rw [burnsideC135_centerOf_eq_map, Subgroup.mem_map]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', hzz⟩
      have : z' = z := Subtype.ext hzz
      rwa [← this]
  obtain ⟨hLU, -, β', hβ's, hβ'k, hβ'eq⟩ := h1
  obtain ⟨hLQ, hUQ, β, hβs, hβk, hβeq⟩ := h2
  have hβ'inj : Function.Injective β' := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ'k, Subgroup.bot_subgroupOf]
  have hUcard : Nat.card ↥(centerOf Q) = Fintype.card F ^ 3 := by
    rw [Nat.card_congr ((Equiv.ofBijective _ ⟨hβ'inj, hβ's⟩).trans Multiplicative.toAdd),
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, pow_one]
  have hZcard : Nat.card (Subgroup.center ↥Q) = Nat.card ↥(centerOf Q) := by
    rw [burnsideC135_centerOf_eq_map, Subgroup.card_map_of_injective Q.subtype_injective]
  have hQcard : Nat.card ↥Q = Nat.card ↥(centerOf Q) * Fintype.card F ^ 6 := by
    have h := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top_of_surjective β hβs, Subgroup.card_top, hβk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv, Nat.card_eq_fintype_card
        (α := Multiplicative (Fin 2 → Fin 3 → F)), Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    rw [← h]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hZcard, hUcard, hF, ← pow_mul, mul_comm]
  ·
    refine le_antisymm ?_ ?_
    · rw [commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [hmemZ]
      show (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ centerOf Q
      exact hcomm a.2 b.2
    ·
      set C := ⁅Q, Q⁆ with hC
      have hCmap : (commutator ↥Q).map Q.subtype = C := by
        rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hCU : C ≤ centerOf Q := by
        rw [hC, Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact hcomm ha hb
      have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun l hl =>
        CFSG.Quasithin.A4.mem_normalizer_commutator (hLQ hl) (hLQ hl)
      have hCne : C ≠ ⊥ := by
        intro hC1
        have hab : ∀ x ∈ Q, x ∈ centerOf Q := by
          intro x hx
          refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
          have h3 : ⁅y, x⁆ ∈ C := Subgroup.commutator_mem_commutator hy hx
          rw [hC1, Subgroup.mem_bot, commutatorElement_def] at h3
          calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
            _ = x * y := by rw [h3, one_mul]
        obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun _ => Pi.single 0 1))
        have h4 : q ∈ β.ker := by
          rw [hβk, Subgroup.mem_subgroupOf]
          exact hab _ q.2
        rw [MonoidHom.mem_ker, hq] at h4
        have h5 := congrFun (congrFun (congrArg Multiplicative.toAdd h4) 0) 0
        simp at h5
      let Y : AddSubgroup (Fin 3 → F) :=
        { carrier := {x | ∃ u : ↥(centerOf Q), (u : G) ∈ C ∧ Multiplicative.toAdd (β' u) 0 = x}
          add_mem' := by
            rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
            exact ⟨u * v, C.mul_mem hu hv, by rw [map_mul, toAdd_mul, Pi.add_apply]⟩
          zero_mem' := ⟨1, C.one_mem, by rw [map_one]; rfl⟩
          neg_mem' := by
            rintro _ ⟨u, hu, rfl⟩
            exact ⟨u⁻¹, C.inv_mem hu, by rw [map_inv, toAdd_inv, Pi.neg_apply]⟩ }
      have hYinv : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (v : Fin 3 → F), v ∈ Y →
          (Matrix.SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ Y := by
        rintro i j hij b _ ⟨u, hu, rfl⟩
        obtain ⟨l, hl⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F
          (Matrix.SpecialLinearGroup.transvection hij b))
        have hmem : (l : G) * u * (l : G)⁻¹ ∈ centerOf Q :=
          (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp u.2
        refine ⟨⟨_, hmem⟩, (Subgroup.mem_normalizer_iff.mp (hLC l.2) _).mp hu, ?_⟩
        rw [hβ'eq l u ⟨_, hmem⟩ rfl 0, moduleAct_false_eq]
        congr 1
        simp only [slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hl,
          MulEquiv.symm_apply_apply]
      obtain ⟨c, hcC, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hCne (eq_bot_iff.mpr fun c hc => Subgroup.mem_bot.mpr (hcon c hc))
      have hcY : Multiplicative.toAdd (β' ⟨c, hCU hcC⟩) 0 ∈ Y := ⟨_, hcC, rfl⟩
      have hc0 : Multiplicative.toAdd (β' ⟨c, hCU hcC⟩) 0 ≠ 0 := by
        intro h0
        apply hc1
        have h3 : β' ⟨c, hCU hcC⟩ = 1 := by
          apply Multiplicative.toAdd.injective
          funext i
          rw [Subsingleton.elim i 0]
          exact h0
        have h4 := hβ'inj (h3.trans (map_one β').symm)
        exact congrArg Subtype.val h4
      have htop := CFSG.Quasithin.H13.Ch4.eq_top_of_transvection_invariant Y hYinv hcY hc0
      intro z hz
      rw [hmemZ] at hz
      have h3 : Multiplicative.toAdd (β' ⟨z, hz⟩) 0 ∈ Y := by rw [htop]; exact AddSubgroup.mem_top _
      obtain ⟨u, hu, hu'⟩ := h3
      have h4 : β' u = β' ⟨z, hz⟩ := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [Subsingleton.elim i 0]
        exact hu'
      have h5 : (u : G) = z := congrArg Subtype.val (hβ'inj h4)
      have h6 : (z : G) ∈ C := h5 ▸ hu
      rw [← hCmap] at h6
      obtain ⟨z', hz', hzz⟩ := h6
      have : z' = z := Subtype.ext hzz
      rwa [← this]
  ·
    refine MS93.isE2_of_card ?_ ?_ ?_
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemZ]
      show ((a * b)⁻¹ * (b * a) : ↥Q).1 ∈ centerOf Q
      have h3 := hcomm (Q.inv_mem b.2) (Q.inv_mem a.2)
      have e : ((a * b)⁻¹ * (b * a) : ↥Q).1 = (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ *
          ((a : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        group
      rw [e]
      exact h3
    · intro x
      induction x using QuotientGroup.induction_on with
      | H a =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one, QuotientGroup.eq, hmemZ]
      show ((a * a)⁻¹ * 1 : ↥Q).1 ∈ centerOf Q
      simp only [mul_one, Subgroup.coe_inv, Subgroup.coe_mul]
      exact (centerOf Q).inv_mem (hsq a.2)
    · have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)
      rw [hZcard, hQcard] at h3
      have hU0 : 0 < Nat.card ↥(centerOf Q) := Nat.card_pos
      have h4 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Fintype.card F ^ 6 := by
        have h5 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) * Nat.card ↥(centerOf Q) =
            Fintype.card F ^ 6 * Nat.card ↥(centerOf Q) := by
          rw [← h3, mul_comm]
        exact Nat.eq_of_mul_eq_mul_right hU0 h5
      rw [h4, hF, ← pow_mul, mul_comm]

end Case3

end CFSG.ASVolI

end
