module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.RonanH412

section Vocab

variable {G : Type*} [Group G]

@[expose] def powMaps (φ : G →* G) : Set (G → G) := {f | f = id ∨ f = φ ∨ f = φ ∘ φ}

@[expose] def ActsInv (acts : Set (G → G)) (U : Subgroup G) : Prop :=
  ∀ f ∈ acts, ∀ u ∈ U, f u ∈ U

@[expose] def ChiefFactor (acts : Set (G → G)) (X Y : Subgroup G) : Prop :=
  X < Y ∧ ActsInv acts X ∧ ActsInv acts Y ∧
    ∀ W : Subgroup G, X ≤ W → W ≤ Y → ActsInv acts W → W = X ∨ W = Y

@[expose] def HasChiefCount (acts : Set (G → G)) (U : Subgroup G) (c : ℕ) : Prop :=
  ∃ (k : ℕ) (S : ℕ → Subgroup G), S 0 = ⊥ ∧ S k = U ∧
    (∀ i < k, ChiefFactor acts (S i) (S (i + 1))) ∧
    Set.ncard {i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} = c

@[expose] def fixSub (φ : G →* G) (U : Subgroup G) : Subgroup G where
  carrier := {u | u ∈ U ∧ φ u = u}
  mul_mem' := fun ⟨hu, hu'⟩ ⟨hv, hv'⟩ => ⟨U.mul_mem hu hv, by rw [map_mul, hu', hv']⟩
  one_mem' := ⟨U.one_mem, map_one φ⟩
  inv_mem' := fun ⟨hu, hu'⟩ => ⟨U.inv_mem hu, by rw [map_inv, hu']⟩

theorem mem_fixSub {φ : G →* G} {U : Subgroup G} {u : G} :
    u ∈ fixSub φ U ↔ u ∈ U ∧ φ u = u := Iff.rfl

theorem fixSub_mono (φ : G →* G) {X Y : Subgroup G} (h : X ≤ Y) : fixSub φ X ≤ fixSub φ Y :=
  fun _ hu => ⟨h hu.1, hu.2⟩

theorem actsInv_powMaps_iff (φ : G →* G) (W : Subgroup G) :
    ActsInv (powMaps φ) W ↔ ∀ w ∈ W, φ w ∈ W := by
  constructor
  · intro h w hw
    exact h φ (Or.inr (Or.inl rfl)) w hw
  · intro h f hf w hw
    rcases hf with rfl | rfl | rfl
    · exact hw
    · exact h w hw
    · exact h _ (h w hw)

theorem hasChiefCount_extend {acts : Set (G → G)} {Y' Y : Subgroup G} {c : ℕ}
    (h : HasChiefCount acts Y' c) (hstep : ChiefFactor acts Y' Y) :
    (HasChiefCount acts Y (c + 1) ∧ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y') ∨
    (HasChiefCount acts Y c ∧ ¬ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y') := by
  obtain ⟨k, S, h0, hk, hS, hc⟩ := h
  let S' : ℕ → Subgroup G := fun i => if i ≤ k then S i else Y
  have hS'le : ∀ i ≤ k, S' i = S i := fun i hi => if_pos hi
  have hS'k1 : S' (k + 1) = Y := if_neg (by omega)
  have h0' : S' 0 = ⊥ := by rw [hS'le 0 (Nat.zero_le _), h0]
  have hchief : ∀ i < k + 1, ChiefFactor acts (S' i) (S' (i + 1)) := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · rw [hS'le i hi'.le, hS'le (i + 1) hi']
      exact hS i hi'
    · rw [hS'le i le_rfl, hS'k1, hk]
      exact hstep
  have hnew : {i : ℕ | i < k + 1 ∧ ∃ f ∈ acts, ∃ u ∈ S' (i + 1), f u * u⁻¹ ∉ S' i} =
      {i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} ∪
        {i : ℕ | i = k ∧ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y'} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨hi, hex⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · left
        rw [hS'le i hi'.le, hS'le (i + 1) hi'] at hex
        exact ⟨hi', hex⟩
      · right
        rw [hS'le i le_rfl, hS'k1, hk] at hex
        exact ⟨rfl, hex⟩
    · rintro (⟨hi, hex⟩ | ⟨rfl, hex⟩)
      · refine ⟨by omega, ?_⟩
        rw [hS'le i hi.le, hS'le (i + 1) hi]
        exact hex
      · refine ⟨by omega, ?_⟩
        rw [hS'le i le_rfl, hS'k1, hk]
        exact hex
  have hfin : ({i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i}).Finite :=
    (Set.finite_lt_nat k).subset fun i hi => hi.1
  by_cases hnc : ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y'
  · left
    refine ⟨⟨k + 1, S', h0', hS'k1, hchief, ?_⟩, hnc⟩
    rw [hnew]
    have hdisj : Disjoint {i : ℕ | i < k ∧ ∃ f ∈ acts, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i}
        {i : ℕ | i = k ∧ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y'} := by
      rw [Set.disjoint_left]
      rintro i ⟨hi, -⟩ ⟨rfl, -⟩
      exact lt_irrefl _ hi
    have hsing : {i : ℕ | i = k ∧ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y'} = {k} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, hnc⟩⟩
    rw [Set.ncard_union_eq hdisj hfin (by rw [hsing]; exact Set.finite_singleton _), hc, hsing,
      Set.ncard_singleton]
  · right
    refine ⟨⟨k + 1, S', h0', hS'k1, hchief, ?_⟩, hnc⟩
    rw [hnew]
    have hempty : {i : ℕ | i = k ∧ ∃ f ∈ acts, ∃ u ∈ Y, f u * u⁻¹ ∉ Y'} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hnc h.2
    rw [hempty, Set.union_empty, hc]

theorem hasChiefCount_map {A : Type*} [Group A] {ι : A →* G} (hι : Function.Injective ι)
    {ψ : A →* A} {φ : G →* G} (hcomm : ∀ a, ι (ψ a) = φ (ι a)) {c : ℕ}
    (h : HasChiefCount (powMaps ψ) ⊤ c) : HasChiefCount (powMaps φ) ι.range c := by
  obtain ⟨k, S, h0, hk, hS, hc⟩ := h
  refine ⟨k, fun i => (S i).map ι, by show (S 0).map ι = ⊥; rw [h0, Subgroup.map_bot],
    by show (S k).map ι = ι.range; rw [hk, MonoidHom.range_eq_map], fun i hi => ?_, ?_⟩
  · obtain ⟨hlt, hinv0, hinv1, hmax⟩ := hS i hi
    rw [actsInv_powMaps_iff] at hinv0 hinv1
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine lt_of_le_of_ne (Subgroup.map_mono hlt.le) fun heq => ?_
      have := congrArg (Subgroup.comap ι) heq
      rw [Subgroup.comap_map_eq_self_of_injective hι,
        Subgroup.comap_map_eq_self_of_injective hι] at this
      exact hlt.ne this
    · rw [actsInv_powMaps_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ψ a, hinv0 a ha, hcomm a⟩
    · rw [actsInv_powMaps_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ψ a, hinv1 a ha, hcomm a⟩
    · intro W hW0 hW1 hWinv
      rw [actsInv_powMaps_iff] at hWinv
      have hWc : W.comap ι ≥ S i := fun a ha => hW0 ⟨a, ha, rfl⟩
      have hWc' : W.comap ι ≤ S (i + 1) := by
        intro a ha
        obtain ⟨b, hb, hba⟩ := hW1 ha
        rwa [← hι hba]
      have hinvc : ∀ a ∈ W.comap ι, ψ a ∈ W.comap ι := by
        intro a ha
        have := hWinv _ ha
        show ι (ψ a) ∈ W
        rw [hcomm]
        exact this
      have hmax' := hmax (W.comap ι) hWc hWc' ((actsInv_powMaps_iff ψ _).2 hinvc)
      have hWle : W ≤ ι.range := fun x hx => by
        obtain ⟨b, hb, rfl⟩ := hW1 hx
        exact ⟨b, rfl⟩
      have hWeq : (W.comap ι).map ι = W := by
        rw [Subgroup.map_comap_eq]
        exact inf_eq_right.2 hWle
      rcases hmax' with h' | h'
      · left
        rw [← hWeq, h']
      · right
        rw [← hWeq, h']
  · have hset : {i : ℕ | i < k ∧ ∃ f ∈ powMaps φ, ∃ u ∈ (S (i + 1)).map ι, f u * u⁻¹ ∉ (S i).map ι} =
        {i : ℕ | i < k ∧ ∃ f ∈ powMaps ψ, ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} := by
      ext i
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨f, hf, _, ⟨a, ha, rfl⟩, hn⟩
        rcases hf with rfl | rfl | rfl
        · exact absurd (by simp) hn
        · refine ⟨ψ, Or.inr (Or.inl rfl), a, ha, fun hmem => hn ?_⟩
          refine ⟨ψ a * a⁻¹, hmem, ?_⟩
          rw [map_mul, map_inv, hcomm]
        · refine ⟨ψ ∘ ψ, Or.inr (Or.inr rfl), a, ha, fun hmem => hn ?_⟩
          refine ⟨(ψ ∘ ψ) a * a⁻¹, hmem, ?_⟩
          rw [map_mul, map_inv, Function.comp_apply, Function.comp_apply, hcomm, hcomm]
      · rintro ⟨g, hg, a, ha, hn⟩
        rcases hg with rfl | rfl | rfl
        · exact absurd (by simp) hn
        · refine ⟨φ, Or.inr (Or.inl rfl), ι a, ⟨a, ha, rfl⟩, fun hmem => hn ?_⟩
          obtain ⟨b, hb, hbe⟩ := hmem
          have : b = ψ a * a⁻¹ := hι (by rw [hbe, map_mul, map_inv, hcomm])
          rwa [this] at hb
        · refine ⟨φ ∘ φ, Or.inr (Or.inr rfl), ι a, ⟨a, ha, rfl⟩, fun hmem => hn ?_⟩
          obtain ⟨b, hb, hbe⟩ := hmem
          have : b = (ψ ∘ ψ) a * a⁻¹ :=
            hι (by rw [hbe, map_mul, map_inv, Function.comp_apply, Function.comp_apply, hcomm,
              hcomm])
          rwa [this] at hb
    rw [hset]
    exact hc

end Vocab

section Elem

variable {A : Type*} [CommGroup A]

@[expose] def adjA (hsq : ∀ a : A, a * a = 1) (X : Subgroup A) (u : A) : Subgroup A where
  carrier := {z | z ∈ X ∨ z * u ∈ X}
  mul_mem' := by
    have sc : ∀ a b : A, a * (a * b) = b := fun a b => by rw [← mul_assoc, hsq, one_mul]
    rintro z w (hz | hz) (hw | hw)
    · exact Or.inl (X.mul_mem hz hw)
    · right
      have e : z * w * u = z * (w * u) := mul_assoc _ _ _
      rw [e]
      exact X.mul_mem hz hw
    · right
      have e : z * w * u = (z * u) * w := by simp [mul_assoc, mul_comm, mul_left_comm]
      rw [e]
      exact X.mul_mem hz hw
    · left
      have e : z * w = (z * u) * (w * u) := by
        simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
      rw [e]
      exact X.mul_mem hz hw
  one_mem' := Or.inl X.one_mem
  inv_mem' := by
    rintro z (hz | hz)
    · exact Or.inl (X.inv_mem hz)
    · right
      have e : z⁻¹ * u = z * u := by rw [inv_eq_of_mul_eq_one_right (hsq z)]
      rw [e]
      exact hz

theorem le_adjA (hsq : ∀ a : A, a * a = 1) (X : Subgroup A) (u : A) : X ≤ adjA hsq X u :=
  fun _ hz => Or.inl hz

theorem self_mem_adjA (hsq : ∀ a : A, a * a = 1) (X : Subgroup A) (u : A) :
    u ∈ adjA hsq X u := Or.inr (by rw [hsq u]; exact X.one_mem)

theorem card_adjA (hsq : ∀ a : A, a * a = 1) {X : Subgroup A} {u : A} (huX : u ∉ X) :
    Nat.card ↥(adjA hsq X u) = 2 * Nat.card ↥X := by
  classical
  have hmem : ∀ x : ↥X, (x : A) * u ∈ adjA hsq X u := fun x =>
    Or.inr (by rw [mul_assoc, hsq u, mul_one]; exact x.2)
  let f : ↥X × Bool → ↥(adjA hsq X u) := fun p =>
    if p.2 then ⟨(p.1 : A) * u, hmem p.1⟩ else ⟨p.1, Or.inl p.1.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, a⟩ ⟨y, b⟩ hxy
      have h := congrArg Subtype.val hxy
      cases a <;> cases b <;> simp only [f, Bool.false_eq_true, ↓reduceIte] at h
      · exact Prod.ext (Subtype.ext h) rfl
      · exfalso
        apply huX
        have : u = (y : A)⁻¹ * x := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact X.mul_mem (X.inv_mem y.2) x.2
      · exfalso
        apply huX
        have : u = (x : A)⁻¹ * y := by rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact X.mul_mem (X.inv_mem x.2) y.2
      · exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
    · rintro ⟨z, hz | hz⟩
      · exact ⟨(⟨z, hz⟩, false), rfl⟩
      · refine ⟨(⟨z * u, hz⟩, true), Subtype.ext ?_⟩
        show z * u * u = z
        rw [mul_assoc, hsq u, mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  simp [mul_comm]

theorem chief_step (hsq : ∀ a : A, a * a = 1) {ψ : A →* A} (hψ : ∀ a, ψ (ψ (ψ a)) = a)
    {X Y : Subgroup A} (hXY : X < Y) (hXψ : ∀ x ∈ X, ψ x ∈ X) (hYψ : ∀ y ∈ Y, ψ y ∈ Y)
    (hmax : ∀ W : Subgroup A, X ≤ W → W ≤ Y → (∀ w ∈ W, ψ w ∈ W) → W = X ∨ W = Y) :
    ((∀ u ∈ Y, ψ u * u⁻¹ ∈ X) ∧ Nat.card ↥Y = 2 * Nat.card ↥X ∧
        Nat.card ↥(fixSub ψ Y) = 2 * Nat.card ↥(fixSub ψ X)) ∨
    ((∃ u ∈ Y, ψ u * u⁻¹ ∉ X) ∧ Nat.card ↥Y = 4 * Nat.card ↥X ∧
        Nat.card ↥(fixSub ψ Y) = Nat.card ↥(fixSub ψ X)) := by
  have sc : ∀ a b : A, a * (a * b) = b := fun a b => by rw [← mul_assoc, hsq, one_mul]
  have hinv : ∀ a : A, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hXY' : X ≤ Y := hXY.le
  obtain ⟨u, huY, huX⟩ := SetLike.exists_of_lt hXY
  have hvY : ψ u ∈ Y := hYψ u huY
  have hwY : ψ (ψ u) ∈ Y := hYψ _ hvY
  by_cases hc : ψ u * u ∈ X
  · left
    have hWψ : ∀ w ∈ adjA hsq X u, ψ w ∈ adjA hsq X u := by
      rintro w (hw | hw)
      · exact Or.inl (hXψ w hw)
      · refine Or.inr ?_
        have e : ψ w * u = ψ (w * u) * (ψ u * u) := by
          rw [map_mul]
          simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact X.mul_mem (hXψ _ hw) hc
    have hWY : adjA hsq X u ≤ Y := by
      rintro z (hz | hz)
      · exact hXY' hz
      · have e : z = (z * u) * u := by simp [mul_assoc, hsq]
        rw [e]
        exact Y.mul_mem (hXY' hz) huY
    have hWeq : adjA hsq X u = Y :=
      (hmax _ (le_adjA hsq X u) hWY hWψ).resolve_left fun h => huX (h ▸ self_mem_adjA hsq X u)
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [hinv]
      have hy' : y ∈ adjA hsq X u := by rw [hWeq]; exact hy
      rcases hy' with h | h
      · exact X.mul_mem (hXψ y h) h
      · have e : ψ y * y = ψ (y * u) * (y * u) * (ψ u * u) := by
          rw [map_mul]
          simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact X.mul_mem (X.mul_mem (hXψ _ h) h) hc
    · rw [← hWeq]
      exact card_adjA hsq huX
    · obtain ⟨u', hu'⟩ : ∃ u' : A, u' = u * ψ u * ψ (ψ u) := ⟨_, rfl⟩
      have hu'fix : ψ u' = u' := by
        rw [hu', map_mul, map_mul, hψ]
        simp [mul_assoc, mul_comm, mul_left_comm]
      have hu'Y : u' ∈ Y := by
        rw [hu']
        exact Y.mul_mem (Y.mul_mem huY hvY) hwY
      have hψψ : ψ (ψ u) * ψ u ∈ X := by
        have := hXψ _ hc
        rwa [map_mul] at this
      have h1 : ψ (ψ u) * u ∈ X := by
        have e : ψ (ψ u) * u = (ψ (ψ u) * ψ u) * (ψ u * u) := by
          simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact X.mul_mem hψψ hc
      have hu'u : u' * u ∈ X := by
        have e : u' * u = (ψ u * u) * (ψ (ψ u) * u) := by
          rw [hu']
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [e]
        exact X.mul_mem hc h1
      have hu'X : u' ∉ X := fun h => huX (by
        have e : u = u'⁻¹ * (u' * u) := by rw [inv_mul_cancel_left]
        rw [e]
        exact X.mul_mem (X.inv_mem h) hu'u)
      have hFeq : fixSub ψ Y = adjA hsq (fixSub ψ X) u' := by
        ext z
        constructor
        · rintro ⟨hzY, hzf⟩
          have hz' : z ∈ adjA hsq X u := by rw [hWeq]; exact hzY
          rcases hz' with hzX | hzu
          · exact Or.inl ⟨hzX, hzf⟩
          · refine Or.inr ?_
            have hzu' : z * u' ∈ X := by
              have e : z * u' = (z * u) * (ψ u * ψ (ψ u)) := by
                rw [hu']
                simp [mul_assoc]
              rw [e]
              refine X.mul_mem hzu ?_
              have : ψ (u * ψ u) ∈ X := hXψ _ (by rw [mul_comm]; exact hc)
              rwa [map_mul] at this
            refine ⟨hzu', ?_⟩
            rw [map_mul, hzf, hu'fix]
        · rintro (⟨hzX, hzf⟩ | ⟨hzu', hzf⟩)
          · exact ⟨hXY' hzX, hzf⟩
          · have e : z = (z * u') * u' := by simp [mul_assoc, hsq]
            refine ⟨?_, ?_⟩
            · rw [e]
              exact Y.mul_mem (hXY' hzu') hu'Y
            · calc ψ z = ψ ((z * u') * u') := by rw [← e]
                _ = ψ (z * u') * ψ u' := map_mul _ _ _
                _ = (z * u') * u' := by rw [hzf, hu'fix]
                _ = z := e.symm
      rw [hFeq]
      exact card_adjA hsq (fun h => hu'X h.1)
  · right
    obtain ⟨n, hn⟩ : ∃ n : A, n = u * ψ u * ψ (ψ u) := ⟨_, rfl⟩
    have hnfix : ψ n = n := by
      rw [hn, map_mul, map_mul, hψ]
      simp [mul_assoc, mul_comm, mul_left_comm]
    have hnY : n ∈ Y := by
      rw [hn]
      exact Y.mul_mem (Y.mul_mem huY hvY) hwY
    have hnX : n ∈ X := by
      have hW₁ψ : ∀ w ∈ adjA hsq X n, ψ w ∈ adjA hsq X n := by
        rintro w (hw | hw)
        · exact Or.inl (hXψ w hw)
        · refine Or.inr ?_
          have := hXψ _ hw
          rwa [map_mul, hnfix] at this
      have hW₁Y : adjA hsq X n ≤ Y := by
        rintro z (hz | hz)
        · exact hXY' hz
        · have e : z = (z * n) * n := by simp [mul_assoc, hsq]
          rw [e]
          exact Y.mul_mem (hXY' hz) hnY
      rcases hmax _ (le_adjA hsq X n) hW₁Y hW₁ψ with h | h
      · exact h ▸ self_mem_adjA hsq X n
      · exfalso
        have huW : u ∈ adjA hsq X n := by rw [h]; exact huY
        rcases huW with h1 | h1
        · exact huX h1
        · apply hc
          have hψun : ψ u * n ∈ X := by
            have := hXψ _ h1
            rwa [map_mul, hnfix] at this
          have e : ψ u * u = (ψ u * n) * (u * n) := by
            simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
          rw [e]
          exact X.mul_mem hψun h1
    have hww : ψ (ψ u) = n * u * ψ u := by
      rw [hn]
      simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
    have hW₂ψ : ∀ z ∈ adjA hsq (adjA hsq X u) (ψ u), ψ z ∈ adjA hsq (adjA hsq X u) (ψ u) := by
      rintro z ((hz | hz) | (hz | hz))
      · exact Or.inl (Or.inl (hXψ z hz))
      · refine Or.inr (Or.inl ?_)
        have := hXψ _ hz
        rwa [map_mul] at this
      · refine Or.inr (Or.inr ?_)
        have h1 : ψ z * ψ (ψ u) ∈ X := by
          have := hXψ _ hz
          rwa [map_mul] at this
        have e : ψ z * ψ u * u = n * (ψ z * ψ (ψ u)) := by
          rw [hww]
          simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact X.mul_mem hnX h1
      · refine Or.inl (Or.inr ?_)
        have h1 : ψ z * ψ (ψ u) * ψ u ∈ X := by
          have := hXψ _ hz
          rwa [map_mul, map_mul] at this
        have e : ψ z * u = n * (ψ z * ψ (ψ u) * ψ u) := by
          rw [hww]
          simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact X.mul_mem hnX h1
    have hW₂Y : adjA hsq (adjA hsq X u) (ψ u) ≤ Y := by
      rintro z ((hz | hz) | (hz | hz))
      · exact hXY' hz
      · have e : z = (z * u) * u := by simp [mul_assoc, hsq]
        rw [e]
        exact Y.mul_mem (hXY' hz) huY
      · have e : z = (z * ψ u) * ψ u := by simp [mul_assoc, hsq]
        rw [e]
        exact Y.mul_mem (hXY' hz) hvY
      · have e : z = (z * ψ u * u) * u * ψ u := by simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
        rw [e]
        exact Y.mul_mem (Y.mul_mem (hXY' hz) huY) hvY
    have huW₂ : u ∈ adjA hsq (adjA hsq X u) (ψ u) := Or.inl (self_mem_adjA hsq X u)
    have hW₂eq : adjA hsq (adjA hsq X u) (ψ u) = Y :=
      (hmax _ (fun z hz => Or.inl (Or.inl hz)) hW₂Y hW₂ψ).resolve_left fun h => huX (h ▸ huW₂)
    have hvnot : ψ u ∉ adjA hsq X u := fun h => by
      rcases h with h | h
      · apply huX
        have := hXψ _ (hXψ _ h)
        rwa [hψ] at this
      · exact hc h
    refine ⟨⟨u, huY, by rw [hinv]; exact hc⟩, ?_, ?_⟩
    · rw [← hW₂eq, card_adjA hsq hvnot, card_adjA hsq huX]
      omega
    · have hFle : fixSub ψ Y ≤ fixSub ψ X := by
        rintro y ⟨hyY, hyf⟩
        have hy' : y ∈ adjA hsq (adjA hsq X u) (ψ u) := by rw [hW₂eq]; exact hyY
        rcases hy' with (hy | hy) | (hy | hy)
        · exact ⟨hy, hyf⟩
        · exfalso
          apply hc
          have h1 : y * ψ u ∈ X := by
            have := hXψ _ hy
            rwa [map_mul, hyf] at this
          have e : ψ u * u = (y * ψ u) * (y * u) := by
            simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
          rw [e]
          exact X.mul_mem h1 hy
        · exfalso
          have h1 : y * ψ (ψ u) ∈ X := by
            have := hXψ _ hy
            rwa [map_mul, hyf] at this
          have h2 : n * u ∈ X := by
            have e : n * u = (y * ψ (ψ u)) * (y * ψ u) := by
              rw [hww]
              simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
            rw [e]
            exact X.mul_mem h1 hy
          apply huX
          have e : u = n⁻¹ * (n * u) := by rw [inv_mul_cancel_left]
          rw [e]
          exact X.mul_mem (X.inv_mem hnX) h2
        · exfalso
          have h1 : y * ψ (ψ u) * ψ u ∈ X := by
            have := hXψ _ hy
            rwa [map_mul, map_mul, hyf] at this
          have h2 : n * ψ u ∈ X := by
            have e : n * ψ u = (y * ψ (ψ u) * ψ u) * (y * ψ u * u) := by
              rw [hww]
              simp [mul_assoc, mul_comm, mul_left_comm, sc, hsq]
            rw [e]
            exact X.mul_mem h1 hy
          have h3 : ψ u ∈ X := by
            have e : ψ u = n⁻¹ * (n * ψ u) := by rw [inv_mul_cancel_left]
            rw [e]
            exact X.mul_mem (X.inv_mem hnX) h2
          apply huX
          have := hXψ _ (hXψ _ h3)
          rwa [hψ] at this
      rw [le_antisymm hFle (fixSub_mono ψ hXY')]

theorem central_all {ψ : A →* A} {Y' Y : Subgroup A} (hY'ψ : ∀ y ∈ Y', ψ y ∈ Y')
    (hcen : ∀ u ∈ Y, ψ u * u⁻¹ ∈ Y') : ∀ f ∈ powMaps ψ, ∀ u ∈ Y, f u * u⁻¹ ∈ Y' := by
  rintro f hf u hu
  rcases hf with rfl | rfl | rfl
  · simp [Y'.one_mem]
  · exact hcen u hu
  · have e : (ψ ∘ ψ) u * u⁻¹ = ψ (ψ u * u⁻¹) * (ψ u * u⁻¹) := by
      rw [Function.comp_apply, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    rw [e]
    exact Y'.mul_mem (hY'ψ _ (hcen u hu)) (hcen u hu)

theorem exists_series [Finite A] (hsq : ∀ a : A, a * a = 1) {ψ : A →* A}
    (hψ : ∀ a, ψ (ψ (ψ a)) = a) :
    ∀ n : ℕ, ∀ Y : Subgroup A, Nat.card ↥Y ≤ n → (∀ y ∈ Y, ψ y ∈ Y) →
      ∃ c : ℕ, Nat.card ↥Y = 4 ^ c * Nat.card ↥(fixSub ψ Y) ∧ HasChiefCount (powMaps ψ) Y c := by
  classical
  intro n
  induction n with
  | zero =>
    intro Y hY _
    exact absurd hY (by have := Nat.card_pos (α := ↥Y); omega)
  | succ n ih =>
    intro Y hYn hYψ
    by_cases hbot : Y = ⊥
    · subst hbot
      have hF : fixSub ψ (⊥ : Subgroup A) = ⊥ := by
        ext u
        simp only [mem_fixSub, Subgroup.mem_bot]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h, map_one]⟩⟩
      refine ⟨0, ?_, 0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), by simp⟩
      rw [hF]
      simp
    · have hex : ∃ d : ℕ, ∃ W : Subgroup A, W < Y ∧ (∀ w ∈ W, ψ w ∈ W) ∧
          Nat.card ↥Y - Nat.card ↥W = d :=
        ⟨_, ⊥, bot_lt_iff_ne_bot.2 hbot, fun w hw => by
          rw [Subgroup.mem_bot] at hw ⊢
          rw [hw, map_one], rfl⟩
      obtain ⟨Y', hlt, hY'ψ, hd⟩ := Nat.find_spec hex
      have hmax' : ∀ W : Subgroup A, Y' ≤ W → W ≤ Y → (∀ w ∈ W, ψ w ∈ W) → W = Y' ∨ W = Y := by
        intro W hY'W hWY hWψ
        by_cases hWY' : W = Y
        · exact Or.inr hWY'
        · left
          have hWlt : W < Y := lt_of_le_of_ne hWY hWY'
          have h1 := Nat.find_min' hex ⟨W, hWlt, hWψ, rfl⟩
          have hle1 : Nat.card ↥Y' ≤ Nat.card ↥Y := Subgroup.card_le_of_le hlt.le
          have hle2 : Nat.card ↥W ≤ Nat.card ↥Y := Subgroup.card_le_of_le hWY
          have hle3 : Nat.card ↥Y' ≤ Nat.card ↥W := Subgroup.card_le_of_le hY'W
          have heq : Nat.card ↥Y' = Nat.card ↥W := by omega
          exact (Subgroup.eq_of_le_of_card_ge hY'W heq.ge).symm
      have hlt_card : Nat.card ↥Y' < Nat.card ↥Y :=
        lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le)
          (fun h => hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.ge))
      obtain ⟨c', hc'card, hc'⟩ := ih Y' (by omega) hY'ψ
      have hstep : ChiefFactor (powMaps ψ) Y' Y :=
        ⟨hlt, (actsInv_powMaps_iff ψ _).2 hY'ψ, (actsInv_powMaps_iff ψ _).2 hYψ,
          fun W h1 h2 h3 => hmax' W h1 h2 ((actsInv_powMaps_iff ψ _).1 h3)⟩
      have hcs := chief_step hsq hψ hlt hY'ψ hYψ hmax'
      rcases hasChiefCount_extend hc' hstep with ⟨hcnt, hex'⟩ | ⟨hcnt, hnex⟩
      · rcases hcs with ⟨hcen, -, -⟩ | ⟨-, hcY, hcF⟩
        · exfalso
          obtain ⟨f, hf, u, hu, hn⟩ := hex'
          exact hn (central_all hY'ψ hcen f hf u hu)
        · refine ⟨c' + 1, ?_, hcnt⟩
          rw [hcY, hcF, hc'card, pow_succ]
          ring_nf
      · rcases hcs with ⟨-, hcY, hcF⟩ | ⟨⟨u, hu, hn⟩, -, -⟩
        · refine ⟨c', ?_, hcnt⟩
          rw [hcY, hcF, hc'card]
          ring_nf
        · exact absurd ⟨ψ, Or.inr (Or.inl rfl), u, hu, hn⟩ hnex

theorem exists_hasChiefCount [Finite A] (hsq : ∀ a : A, a * a = 1) {ψ : A →* A}
    (hψ : ∀ a, ψ (ψ (ψ a)) = a) (c : ℕ)
    (hc : Nat.card A = 4 ^ c * Nat.card ↥(fixSub ψ ⊤)) : HasChiefCount (powMaps ψ) ⊤ c := by
  obtain ⟨c₀, hc₀, hcnt⟩ := exists_series hsq hψ (Nat.card ↥(⊤ : Subgroup A)) ⊤ le_rfl
    (fun _ _ => Subgroup.mem_top _)
  rw [Subgroup.card_top] at hc₀
  have hF : 0 < Nat.card ↥(fixSub ψ ⊤) := Nat.card_pos
  have h : 4 ^ c₀ = 4 ^ c := Nat.eq_of_mul_eq_mul_right hF (hc₀.symm.trans hc)
  have : c₀ = c := Nat.pow_right_injective (by norm_num) h
  rwa [this] at hcnt

end Elem

end CFSG.Quasithin.RonanH412
