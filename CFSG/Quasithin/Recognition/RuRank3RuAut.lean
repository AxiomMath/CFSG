module

public import CFSG.Quasithin.Recognition.RuRank3RuGraph
public import CFSG.Quasithin.Recognition.RuRank3RuAutData
public import CFSG.Quasithin.Recognition.RuRank3TitsClsMain
public import CFSG.Sporadic.Schreier.TitsGraphAut

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups

attribute [local instance] fact_prime_five'

@[expose] noncomputable def ruCommonS (u v : Fin 4060) : ℕ :=
  {w : Fin 4060 | w ∈ ruS ∧ ruAdj u w ∧ ruAdj v w}.ncard

theorem ruCommonS_apply {g : Equiv.Perm (Fin 4060)} (hS : ∀ x, g x ∈ ruS ↔ x ∈ ruS)
    (hadj : ∀ x y, ruAdj (g x) (g y) ↔ ruAdj x y) (u v : Fin 4060) :
    ruCommonS (g u) (g v) = ruCommonS u v := by
  unfold ruCommonS
  have e : {w : Fin 4060 | w ∈ ruS ∧ ruAdj (g u) w ∧ ruAdj (g v) w} =
      g '' {w | w ∈ ruS ∧ ruAdj u w ∧ ruAdj v w} := by
    ext w
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨g⁻¹ w, ⟨?_, ?_, ?_⟩, perm_apply_inv g w⟩
      · rw [← hS, perm_apply_inv]
        exact h1
      · rw [← hadj, perm_apply_inv]
        exact h2
      · rw [← hadj, perm_apply_inv]
        exact h3
    · rintro ⟨w', ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨(hS w').2 h1, (hadj u w').2 h2, (hadj v w').2 h3⟩
  rw [e, Set.ncard_image_of_injective _ g.injective]

theorem ruCount_facts (j : Fin 1755) :
    isInvA 4060 (ruTreeArr ruDArr[(j : ℕ)]!) (ruTI ruDArr[(j : ℕ)]!) = true ∧
    (ruCnt (ruTI ruDArr[(j : ℕ)]!) = 512 ↔ (j : ℕ) ∈ (titsNbr[0]!).toList) := by
  have h := allLt_spec ruCount_check j.2
  simp only [ruCountOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  rw [Array.mem_toList_iff, ← Array.contains_iff_mem, ← h.2, beq_iff_eq]
  rfl

theorem ruAdj_ruB_iff_row
    (j : Fin 1755) (x : Fin 4060) :
    ruRowA (ruTI ruDArr[(j : ℕ)]!) x = true ↔ ruAdj (ruB j) x := by
  have hv : ((ruB j : Fin 4060) : ℕ) = ruDArr[(j : ℕ)]! := ruB_val j
  exact ruRowA_spec (by rw [hv]; exact (ruCount_facts j).1) x

theorem ruInS_iff
    (z : Fin 4060) : ruInS z = true ↔ z ∈ ruS := by
  rw [ruInS, beq_iff_eq, mem_ruS_iff]

theorem ruCommonS_one
    (j : Fin 1755) : ruCommonS 1 (ruB j) = ruCnt (ruTI ruDArr[(j : ℕ)]!) := by
  unfold ruCommonS ruCnt
  rw [← ncard_setOf_fin]
  congr 1
  ext w
  show (w ∈ ruS ∧ ruAdj 1 w ∧ ruAdj (ruB j) w) ↔
    (ruInS w && ruRowA ruTI1 w && ruRowA (ruTI ruDArr[(j : ℕ)]!) w) = true
  rw [Bool.and_eq_true, Bool.and_eq_true, ruInS_iff, ruRowA_one, ruAdj_ruB_iff_row, and_assoc]

theorem adj_zero_iff_common
    (j : Fin 1755) :
    titsPointGraph.Adj 0 j ↔ ruCommonS 1 (ruB j) = 512 := by
  rw [adj_iff_mem_nbr, ruCommonS_one, (ruCount_facts j).2]
  rfl

theorem adj_iff_common
    (j j' : Fin 1755) :
    titsPointGraph.Adj j j' ↔ ruCommonS (ruB j) (ruB j') = 512 := by
  have := titsA_pretransitive
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq titsA j (0 : Fin 1755)
  have ha' : (a : Equiv.Perm (Fin 1755)) j = 0 := ha
  set r : ruR0 := ruR0Equiv.symm a with hr
  have hrB : ∀ i, (r : Equiv.Perm (Fin 4060)) (ruB i) = ruB ((a : Equiv.Perm (Fin 1755)) i) := by
    intro i
    rw [ruR0Equiv_ruB, hr, MulEquiv.apply_symm_apply]
  have hrP : (r : Equiv.Perm (Fin 4060)) ∈ ruP := ruR0_le_ruP r.2
  rw [← mem_titsGraphAut.1 (titsA_le_titsGraphAut a.2) j j', ha',
    ← ruCommonS_apply (ruR0_mem_ruS_iff r.2) (ruAdj_apply hrP), hrB, hrB, ha', ruB_zero]
  exact adj_zero_iff_common _

theorem ruW_facts {i : ℕ} (hi : i < 20) :
    ruW[i]! < 1755 ∧ isInvA 4060 (ruTreeArr ruDArr[ruW[i]!]!) ruWTI[i]! = true := by
  have h := allLt_spec ruFP_check.1 hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem ruRowA_W
    {i : ℕ} (hi : i < 20) (x : Fin 4060) :
    ruRowA ruWTI[i]! x = true ↔ ruAdj (ruB ⟨ruW[i]!, (ruW_facts hi).1⟩) x := by
  have hv : ((ruB ⟨ruW[i]!, (ruW_facts hi).1⟩ : Fin 4060) : ℕ) = ruDArr[ruW[i]!]! := ruB_val _
  exact ruRowA_spec (by rw [hv]; exact (ruW_facts hi).2) x

theorem ruFP_eq
    {x y : Fin 4060} (h : ∀ j, ruAdj (ruB j) x ↔ ruAdj (ruB j) y) :
    ruFP x = ruFP y := by
  unfold ruFP
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Bool.eq_iff_iff, ruRowA_W hi x, ruRowA_W hi y]
  exact h _

theorem ruFPArr_get (x : Fin 4060) : ruFPArr[(x : ℕ)]! = ruFP x :=
  getElem!_ofFn_nat _ x.2

theorem ruInS_of_mem
    {z : Fin 4060} (hz : z ∈ ruS) : ruInS z = true := (ruInS_iff z).2 hz

theorem eq_of_adj_ruB
    {s s' : Fin 4060} (hs : s ∈ ruS) (hs' : s' ∈ ruS)
    (h : ∀ j, ruAdj s (ruB j) ↔ ruAdj s' (ruB j)) : s = s' := by
  have hfp : ruFPArr[(s : ℕ)]! = ruFPArr[(s' : ℕ)]! := by
    rw [ruFPArr_get, ruFPArr_get]
    apply ruFP_eq
    intro j
    rw [ruAdj_comm, h, ruAdj_comm]
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have h1 := allLt_spec ruFP_check.2 s'.2
    rw [ruInS_of_mem hs', Bool.not_true, Bool.false_or] at h1
    have h2 := allLt_spec h1 hlt
    rw [ruInS_of_mem hs, Bool.not_true, Bool.false_or, bne_iff_ne] at h2
    exact h2 hfp.symm
  · have h1 := allLt_spec ruFP_check.2 s.2
    rw [ruInS_of_mem hs, Bool.not_true, Bool.false_or] at h1
    have h2 := allLt_spec h1 hlt
    rw [ruInS_of_mem hs', Bool.not_true, Bool.false_or, bne_iff_ne] at h2
    exact h2 hfp

theorem mem_ruP_of_adj
    {σ : Equiv.Perm (Fin 4060)}
    (hσ : ∀ x y, ruAdj (σ x) (σ y) ↔ ruAdj x y) : σ ∈ ruP := by
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ ruP, p 0 = σ 0 :=
    ⟨ruTreeElt (σ 0), ruTreeElt_mem _, ruTreeElt_apply_zero _⟩
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : Equiv.Perm (Fin 4060), σ₁ = p⁻¹ * σ := ⟨_, rfl⟩
  have hσ₁ : ∀ x y, ruAdj (σ₁ x) (σ₁ y) ↔ ruAdj x y := by
    intro x y
    rw [hσ₁def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ruAdj_apply (inv_mem hp), hσ]
  have hσ₁0 : σ₁ 0 = 0 := by
    rw [hσ₁def, Equiv.Perm.mul_apply, ← hp0, perm_inv_apply]
  have hD : ∀ x, σ₁ x ∈ Set.range ruB ↔ x ∈ Set.range ruB := by
    intro x
    rw [← ruAdj_zero_iff, ← ruAdj_zero_iff, ← hσ₁ 0 x, hσ₁0]
  have hS : ∀ x, σ₁ x ∈ ruS ↔ x ∈ ruS := by
    intro x
    have h0 : σ₁ x = 0 ↔ x = 0 := by
      constructor
      · intro h
        apply σ₁.injective
        rw [h, hσ₁0]
      · rintro rfl
        exact hσ₁0
    show (σ₁ x ≠ 0 ∧ σ₁ x ∉ Set.range ruB) ↔ (x ≠ 0 ∧ x ∉ Set.range ruB)
    rw [ne_eq, ne_eq, h0, hD]
  have hτB : ∀ j, ruB (ruResD ⟨σ₁, hD⟩ j) = σ₁ (ruB j) := fun j => ruB_ruResD _ j
  have hτA : ruResD ⟨σ₁, hD⟩ ∈ titsA := by
    rw [← titsGraphAut_eq, mem_titsGraphAut]
    intro j j'
    rw [adj_iff_common, adj_iff_common, hτB, hτB, ruCommonS_apply hS hσ₁]
  obtain ⟨r, hr⟩ : ∃ r : ruR0, ruR0Equiv r = ⟨_, hτA⟩ :=
    ⟨ruR0Equiv.symm ⟨_, hτA⟩, MulEquiv.apply_symm_apply _ _⟩
  have hrB : ∀ j, (r : Equiv.Perm (Fin 4060)) (ruB j) = σ₁ (ruB j) := by
    intro j
    rw [ruR0Equiv_ruB, hr]
    exact hτB j
  have hrP : (r : Equiv.Perm (Fin 4060)) ∈ ruP := ruR0_le_ruP r.2
  obtain ⟨σ₂, hσ₂def⟩ : ∃ σ₂ : Equiv.Perm (Fin 4060), σ₂ = (r : Equiv.Perm (Fin 4060))⁻¹ * σ₁ :=
    ⟨_, rfl⟩
  have hσ₂adj : ∀ x y, ruAdj (σ₂ x) (σ₂ y) ↔ ruAdj x y := by
    intro x y
    rw [hσ₂def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ruAdj_apply (inv_mem hrP), hσ₁]
  have hσ₂B : ∀ j, σ₂ (ruB j) = ruB j := by
    intro j
    rw [hσ₂def, Equiv.Perm.mul_apply, ← hrB, perm_inv_apply]
  have hσ₂0 : σ₂ 0 = 0 := by
    rw [hσ₂def, Equiv.Perm.mul_apply, hσ₁0]
    exact ruR0_apply_zero (inv_mem r.2)
  have hσ₂S : ∀ x, σ₂ x ∈ ruS ↔ x ∈ ruS := by
    intro x
    rw [hσ₂def, Equiv.Perm.mul_apply, ruR0_mem_ruS_iff (inv_mem r.2), hS]
  have hσ₂fix : ∀ x, σ₂ x = x := by
    intro x
    by_cases h0 : x = 0
    · rw [h0, hσ₂0]
    by_cases hx : x ∈ Set.range ruB
    · obtain ⟨j, rfl⟩ := hx
      exact hσ₂B j
    have hxS : x ∈ ruS := ⟨h0, hx⟩
    apply eq_of_adj_ruB ((hσ₂S x).2 hxS) hxS
    intro j
    have := hσ₂adj x (ruB j)
    rwa [hσ₂B] at this
  have hσ₂one : σ₂ = 1 := Equiv.ext hσ₂fix
  have e1 : σ₁ = (r : Equiv.Perm (Fin 4060)) * σ₂ := by
    rw [hσ₂def, mul_inv_cancel_left]
  have e2 : σ = p * σ₁ := by
    rw [hσ₁def, mul_inv_cancel_left]
  rw [e2, e1, hσ₂one, mul_one]
  exact mul_mem hp hrP

@[expose] noncomputable def titsK0Gen (i : ℕ) : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 titsK0Strong[i]!

theorem titsK0Gens_size : titsK0Gens.size = 3 := by simp [titsK0Gens]

theorem titsK0Gens_rep
    : ∀ k < titsK0Gens.size, Rep 1755 titsK0Gens[k]! (titsK0Gen k) := by
  intro k hk
  rw [titsK0Gens_size] at hk
  rw [titsK0Gens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact (rep_permOfArr (titsK0_strong_inv (by omega))).1

theorem genSubgroup_titsK0 : genSubgroup 1755 titsK0Gens.size titsK0Gen = titsK0 := by
  rw [titsK0Gens_size, titsK0_eq_closure]
  rfl

theorem orbit_titsK0 (x : Fin 1755) :
    MulAction.orbit titsK0 x = {y : Fin 1755 | titsK0Lab[(y : ℕ)]! = titsK0Lab[(x : ℕ)]!} := by
  rw [← genSubgroup_titsK0]
  exact orbit_eq_orbLab titsK0Gens_rep titsK0_orbit_check.1 x

theorem ncard_orbit_titsK0_zero
    : (MulAction.orbit titsK0 (0 : Fin 1755)).ncard = 975 := by
  rw [orbit_titsK0, ncard_labelClass]
  exact titsK0_orbit_check.2.1

theorem ncard_orbit_titsK0_lt
    {x : Fin 1755} (hx : x ∉ MulAction.orbit titsK0 (0 : Fin 1755)) :
    (MulAction.orbit titsK0 x).ncard < 975 := by
  rw [orbit_titsK0] at hx ⊢
  rw [ncard_labelClass]
  have := allLt_spec titsK0_orbit_check.2.2.1 x.2
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with h | h
  · exact absurd h hx
  · exact h

theorem ruAdj_g0_ruB_iff
    (j : Fin 1755) :
    ruAdj ruG0F (ruB j) ↔ j ∉ MulAction.orbit titsK0 (0 : Fin 1755) := by
  rw [← ruRowA_g0, ruB_val, orbit_titsK0]
  have := allLt_spec titsK0_orbit_check.2.2.2 j.2
  rw [beq_iff_eq] at this
  rw [← this, bne_iff_ne]
  rfl

@[expose] noncomputable def ruE0
    : Subgroup titsA :=
  (MulAction.stabilizer ruR0 ruG0F).map ruR0Equiv.toMonoidHom

theorem mem_stabilizer_ruR0_iff {s : Fin 4060} (r : ruR0) :
    r ∈ MulAction.stabilizer ruR0 s ↔ (r : Equiv.Perm (Fin 4060)) s = s := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]

theorem mem_ruE0_iff
    (r : ruR0) :
    ruR0Equiv r ∈ ruE0 ↔ (r : Equiv.Perm (Fin 4060)) ruG0F = ruG0F := by
  rw [← mem_stabilizer_ruR0_iff]
  constructor
  · rintro ⟨r', hr', e⟩
    have : r' = r := ruR0Equiv.injective e
    rw [← this]
    exact hr'
  · intro h
    exact ⟨r, h, rfl⟩

theorem card_stabilizer_g0
    : Nat.card (MulAction.stabilizer ruR0 ruG0F) = 15600 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer ruR0 ruG0F)
  rw [MulAction.index_stabilizer, orbit_ruR0_g0, ncard_ruS, card_ruR0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2304) (h.trans (by norm_num))

theorem card_ruE0
    : Nat.card ruE0 = 15600 := by
  rw [ruE0, ← card_stabilizer_g0]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ ruR0Equiv.injective).toEquiv).symm

theorem mem_ruE0_of_normalizes
    {a : titsA}
    (ha : ∀ k, k ∈ titsK0 ↔
      (a : Equiv.Perm (Fin 1755)) * k * (a : Equiv.Perm (Fin 1755))⁻¹ ∈ titsK0) :
    a ∈ ruE0 := by
  have himg : ∀ x : Fin 1755, (a : Equiv.Perm (Fin 1755)) '' MulAction.orbit titsK0 x =
      MulAction.orbit titsK0 ((a : Equiv.Perm (Fin 1755)) x) := by
    intro x
    ext y
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨⟨(a : Equiv.Perm (Fin 1755)) * k * (a : Equiv.Perm (Fin 1755))⁻¹,
        (ha k).1 k.2⟩, ?_⟩
      show ((a : Equiv.Perm (Fin 1755)) * k * (a : Equiv.Perm (Fin 1755))⁻¹)
        ((a : Equiv.Perm (Fin 1755)) x) = (a : Equiv.Perm (Fin 1755)) ((k : Equiv.Perm _) x)
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply]
    · rintro ⟨k, rfl⟩
      have hk : (a : Equiv.Perm (Fin 1755))⁻¹ * k * (a : Equiv.Perm (Fin 1755)) ∈ titsK0 := by
        rw [ha]
        have e : (a : Equiv.Perm (Fin 1755)) * ((a : Equiv.Perm (Fin 1755))⁻¹ *
            (k : Equiv.Perm (Fin 1755)) * (a : Equiv.Perm (Fin 1755))) *
            (a : Equiv.Perm (Fin 1755))⁻¹ = k := by group
        rw [e]
        exact k.2
      refine ⟨((a : Equiv.Perm (Fin 1755))⁻¹ * k * (a : Equiv.Perm (Fin 1755))) x,
        ⟨⟨_, hk⟩, rfl⟩, ?_⟩
      show (a : Equiv.Perm (Fin 1755)) (((a : Equiv.Perm (Fin 1755))⁻¹ * k *
        (a : Equiv.Perm (Fin 1755))) x) = (k : Equiv.Perm _) ((a : Equiv.Perm (Fin 1755)) x)
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_apply_inv]
  have hA0 : (a : Equiv.Perm (Fin 1755)) 0 ∈ MulAction.orbit titsK0 (0 : Fin 1755) := by
    by_contra hn
    have h1 := ncard_orbit_titsK0_lt hn
    rw [← himg, Set.ncard_image_of_injective _ (Equiv.injective _), ncard_orbit_titsK0_zero] at h1
    exact lt_irrefl _ h1
  have hAO : (a : Equiv.Perm (Fin 1755)) '' MulAction.orbit titsK0 (0 : Fin 1755) =
      MulAction.orbit titsK0 (0 : Fin 1755) := by
    rw [himg]
    exact MulAction.orbit_eq_iff.2 hA0
  have hAOiff : ∀ y, (a : Equiv.Perm (Fin 1755)) y ∈ MulAction.orbit titsK0 (0 : Fin 1755) ↔
      y ∈ MulAction.orbit titsK0 (0 : Fin 1755) := by
    intro y
    constructor
    · intro h
      rw [← hAO] at h
      obtain ⟨y', hy', e⟩ := h
      rwa [(a : Equiv.Perm (Fin 1755)).injective e] at hy'
    · intro h
      rw [← hAO]
      exact ⟨y, h, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ruR0, ruR0Equiv r = a := ⟨ruR0Equiv.symm a, MulEquiv.apply_symm_apply _ _⟩
  have hrB : ∀ j, (r : Equiv.Perm (Fin 4060)) (ruB j) = ruB ((a : Equiv.Perm (Fin 1755)) j) := by
    intro j
    rw [ruR0Equiv_ruB, hr]
  have hrS : (r : Equiv.Perm (Fin 4060)) ruG0F ∈ ruS := (ruR0_mem_ruS_iff r.2 _).2 ruG0F_mem_ruS
  have hfix : (r : Equiv.Perm (Fin 4060)) ruG0F = ruG0F := by
    apply eq_of_adj_ruB hrS ruG0F_mem_ruS
    intro j
    have h1 : ruAdj ((r : Equiv.Perm (Fin 4060)) ruG0F) (ruB j) ↔
        ruAdj ruG0F (ruB ((a : Equiv.Perm (Fin 1755))⁻¹ j)) := by
      rw [← ruAdj_apply (ruR0_le_ruP r.2) ruG0F (ruB ((a : Equiv.Perm (Fin 1755))⁻¹ j)), hrB,
        perm_apply_inv]
    rw [h1, ruAdj_g0_ruB_iff, ruAdj_g0_ruB_iff, ← hAOiff ((a : Equiv.Perm (Fin 1755))⁻¹ j),
      perm_apply_inv]
  rw [← hr]
  exact (mem_ruE0_iff r).2 hfix

theorem exists_stab_eq_of_card
    {H : Subgroup titsA} (hH : Nat.card H = 20480) :
    ∃ d ∈ Set.range ruB, ∀ r : ruR0, ruR0Equiv r ∈ H ↔ (r : Equiv.Perm (Fin 4060)) d = d := by
  obtain ⟨x, rfl⟩ := exists_eq_stabilizer_of_card hH
  refine ⟨ruB x, ⟨x, rfl⟩, fun r => ?_⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def, ruR0Equiv_ruB,
    ruB_injective.eq_iff]

theorem mem_map_conj_iff {G : Type*} [Group G] (K : Subgroup G) (g k : G) :
    k ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * k * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem exists_stab_eq_of_isL225Plus
    {H : Subgroup titsA} (hH : IsL225Plus H) :
    ∃ s ∈ ruS, ∀ r : ruR0, ruR0Equiv r ∈ H ↔ (r : Equiv.Perm (Fin 4060)) s = s := by
  obtain ⟨K, hKn, hK2, ⟨e⟩, -, -⟩ := hH
  set ι : H →* Equiv.Perm (Fin 1755) := titsA.subtype.comp H.subtype with hι
  have hιinj : Function.Injective ι := fun x y h =>
    H.subtype_injective (titsA.subtype_injective h)
  set K' : Subgroup (Equiv.Perm (Fin 1755)) := K.map ι with hK'
  have hK'A : K' ≤ titsA := by
    rintro _ ⟨x, -, rfl⟩
    exact ((x : titsA)).2
  have eK' : K' ≃* PSL(2, GaloisField 5 2) :=
    (Subgroup.equivMapOfInjective K ι hιinj).symm.trans e
  obtain ⟨g, hgA, hg⟩ := exists_conj_eq_titsK0 hK'A eK'
  have hcardK : Nat.card K = 7800 := (psl225_witnesses e).1
  have hcardH : Nat.card H = 15600 := by
    have := K.card_mul_index
    rw [hcardK, hK2] at this
    rw [← this]
  have hnormK' : ∀ h : H, ∀ k, k ∈ K' ↔ ι h * k * (ι h)⁻¹ ∈ K' := by
    intro h k
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨h * x * h⁻¹, hKn.conj_mem x hx h, by simp⟩
    · rintro ⟨x, hx, hxk⟩
      refine ⟨h⁻¹ * x * h, ?_, ?_⟩
      · have := hKn.conj_mem x hx h⁻¹
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, hxk, map_inv]
        group
  set γ : titsA := ⟨g, hgA⟩ with hγ
  have hconj : ∀ h : H, γ * (h : titsA) * γ⁻¹ ∈ ruE0 := by
    intro h
    apply mem_ruE0_of_normalizes
    intro k
    rw [← hg, mem_map_conj_iff, mem_map_conj_iff]
    have e1 : ((γ * (h : titsA) * γ⁻¹ : titsA) : Equiv.Perm (Fin 1755)) = g * ι h * g⁻¹ := rfl
    rw [e1, hnormK' h]
    have e2 : g⁻¹ * (g * ι h * g⁻¹ * k * (g * ι h * g⁻¹)⁻¹) * g =
        ι h * (g⁻¹ * k * g) * (ι h)⁻¹ := by group
    rw [e2]
  have hle : H.map (MulAut.conj γ).toMonoidHom ≤ ruE0 := by
    rintro _ ⟨h, hh, rfl⟩
    exact hconj ⟨h, hh⟩
  have hmap : H.map (MulAut.conj γ).toMonoidHom = ruE0 := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_ruE0, ← hcardH]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj γ).toMonoidHom
      (fun a b hab => (MulAut.conj γ).injective hab)).toEquiv).le
  have hHiff : ∀ x : titsA, x ∈ H ↔ γ * x * γ⁻¹ ∈ ruE0 := by
    intro x
    rw [← hmap, mem_map_conj_iff]
    have e : γ⁻¹ * (γ * x * γ⁻¹) * γ = x := by group
    rw [e]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ruR0, ruR0Equiv ρ = γ := ⟨ruR0Equiv.symm γ, MulEquiv.apply_symm_apply _ _⟩
  refine ⟨(ρ : Equiv.Perm (Fin 4060))⁻¹ ruG0F, (ruR0_mem_ruS_iff (inv_mem ρ.2) _).2 ruG0F_mem_ruS,
    fun r => ?_⟩
  rw [hHiff, ← hρ, ← map_inv, ← map_mul, ← map_mul, mem_ruE0_iff]
  show (ρ : Equiv.Perm (Fin 4060)) ((r : Equiv.Perm (Fin 4060))
    ((ρ : Equiv.Perm (Fin 4060))⁻¹ ruG0F)) = ruG0F ↔ _
  constructor
  · intro h
    apply (ρ : Equiv.Perm (Fin 4060)).injective
    rw [h, perm_apply_inv]
  · intro h
    rw [h, perm_apply_inv]

end CFSG.Quasithin.RuRank3
