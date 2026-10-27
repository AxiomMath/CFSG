module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.Blueprint

variable {Q Q' : Type} [Group Q] [Group Q']

@[expose] def PerfSubnormalBot (C : Subgroup Q) : Prop :=
  ∀ Y : Subgroup Q, Y ≤ C → (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y →
    ¬ 3 ∣ Nat.card Y → Y = ⊥

@[expose] def B3Fix (C : Subgroup Q) : Prop :=
  ∀ Y R : Subgroup Q, Y ≤ C → (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y →
    ¬ 3 ∣ Nat.card Y → R ≤ Y → ∀ [(R.subgroupOf Y).Normal], Group.IsSolvable R →
    (∃ f, SuzukiModel (Y ⧸ R.subgroupOf Y) 2 f) → ⁅R, Y⁆ = ⊥

theorem threePrimeB3_of_b3Fix
    (h : ∀ β : MulAut Q, β ^ 3 = 1 → ∀ C : Subgroup Q, (∀ z, z ∈ C ↔ β z = z) → B3Fix C) :
    ThreePrimeB3 Q := by
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs hsz
  exact h β hβ C hC Y R hYC hsn hYp hY3 hRY hRs hsz

theorem b3Fix_of_perfSubnormalBot {C : Subgroup Q} (h : PerfSubnormalBot C) : B3Fix C := by
  intro Y R hYC hsn hYp hY3 hRY hRn hRs hsz
  have hY := h Y hYC hsn hYp hY3
  subst hY
  exact Subgroup.commutator_bot_right R

theorem b3Fix_of_card_dvd {C : Subgroup Q} {M : ℕ}
    (hCM : Nat.card C ∣ M) (h : ∀ a, 1 ≤ a → ¬ suzukiOrder a ∣ M) : B3Fix C := by
  intro Y R hYC hsn hYp hY3 hRY hRn hRs hsz
  exfalso
  obtain ⟨f, hf⟩ := hsz
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hf
  apply h a ha
  rw [← hcard]
  exact ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hYC)).trans hCM

theorem b3Fix_of_not_five_dvd {C : Subgroup Q}
    (h : ∀ Y : Subgroup Q, Y ≤ C → Group.IsPerfect Y → ¬ 5 ∣ Nat.card Y) : B3Fix C := by
  intro Y R hYC hsn hYp hY3 hRY hRn hRs hsz
  exfalso
  obtain ⟨f, hf⟩ := hsz
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hf
  apply h Y hYC hYp
  rw [card_eq_card_mul_card_quotient hRY, hcard]
  exact Dvd.dvd.mul_left (five_dvd_suzukiOrder a) _

theorem not_suzukiOrder_dvd_12096 {a : ℕ} (ha : 1 ≤ a) : ¬ suzukiOrder a ∣ 12096 := by
  intro h
  have haB := le_of_suzukiOrder_dvd (M := 12096) (B := 2) (by norm_num) (by norm_num) h
  interval_cases a <;> exact absurd h (by decide)

theorem b3Fix_of_map (e : Q ≃* Q') {C : Subgroup Q} (h : B3Fix (C.map e.toMonoidHom)) :
    B3Fix C := by
  intro Y R hYC hsn hYp hY3 hRY hRn hRs hsz
  set f : Q →* Q' := e.toMonoidHom with hf
  have hRn' : ((R.map f).subgroupOf (Y.map f)).Normal := by
    rw [← map_subgroupOf_subgroupMap]
    exact hRn.map _ (e.subgroupMap Y).surjective
  have hsn' : ((Y.map f).subgroupOf (C.map f)).IsSubnormal := by
    rw [← map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  have hYp' : Group.IsPerfect (Y.map f) := Group.IsPerfect.map f
  have hY3' : ¬ 3 ∣ Nat.card (Y.map f) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hRs' : Group.IsSolvable (R.map f) :=
    Group.isSolvable_of_surjective (f := (e.subgroupMap R).toMonoidHom)
      (e.subgroupMap R).surjective
  have hsz' : ∃ f', SuzukiModel ((Y.map f) ⧸ (R.map f).subgroupOf (Y.map f)) 2 f' := by
    obtain ⟨n, hn⟩ := hsz
    obtain ⟨h2, a, ha, K, _, _, hn', hK, ⟨eK⟩⟩ := hn
    refine ⟨n, h2, a, ha, K, inferInstance, inferInstance, hn', hK, ⟨?_⟩⟩
    exact (QuotientGroup.congr (R.subgroupOf Y) ((R.map f).subgroupOf (Y.map f))
      (e.subgroupMap Y) (map_subgroupOf_subgroupMap e R Y)).symm.trans eK
  have key := @h (Y.map f) (R.map f) (Subgroup.map_mono hYC) hsn' hYp' hY3'
    (Subgroup.map_mono hRY) hRn' hRs' hsz'
  rw [← Subgroup.map_commutator] at key
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp key

theorem perfSubnormalBot_of_map (e : Q ≃* Q') {C : Subgroup Q}
    (h : PerfSubnormalBot (C.map e.toMonoidHom)) : PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  set f : Q →* Q' := e.toMonoidHom with hf
  have hsn' : ((Y.map f).subgroupOf (C.map f)).IsSubnormal := by
    rw [← map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  have hYp' : Group.IsPerfect (Y.map f) := Group.IsPerfect.map f
  have hY3' : ¬ 3 ∣ Nat.card (Y.map f) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp
    (h (Y.map f) (Subgroup.map_mono hYC) hsn' hYp' hY3')

theorem perfSubnormalBot_centralizer_of_conj (z g : Q)
    (hz : PerfSubnormalBot (Subgroup.centralizer ({g * z * g⁻¹} : Set Q))) :
    PerfSubnormalBot (Subgroup.centralizer ({z} : Set Q)) := by
  refine perfSubnormalBot_of_map (MulAut.conj g) ?_
  convert hz using 1
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : x * z = z * x := hx
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have h1 : y * (g * z * g⁻¹) = g * z * g⁻¹ * y := hy
    show g⁻¹ * y * g * z = z * (g⁻¹ * y * g)
    calc g⁻¹ * y * g * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * y) * g := by rw [h1]
      _ = z * (g⁻¹ * y * g) := by group

theorem pow_three_eq_one_of_conj_pow_three {M : Type*} [Group M] (hM : Subgroup.center M = ⊥)
    {z : M} (h : (MulAut.conj z) ^ 3 = 1) : z ^ 3 = 1 := by
  have h2 : z ^ 3 ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut M => φ y)
      (show MulAut.conj (z ^ 3) = 1 by rw [map_pow]; exact h)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * z ^ 3 = z ^ 3 * y * (z ^ 3)⁻¹ * z ^ 3 := by rw [this]
      _ = z ^ 3 * y := by group
  rwa [hM, Subgroup.mem_bot] at h2

theorem fixed_conj_eq_centralizer {M : Type*} [Group M] {z : M} {C : Subgroup M}
    (hC : ∀ y, y ∈ C ↔ (MulAut.conj z) y = y) : C = Subgroup.centralizer ({z} : Set M) := by
  ext y
  rw [hC y, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * z = z * y * z⁻¹ * z := by rw [h]
      _ = z * y := by group
  · intro h
    calc z * y * z⁻¹ = y * z * z⁻¹ := by rw [h]
      _ = y := by group

theorem conj_mul_conj_inv_apply {M : Type*} [Group M] (k : M) (Φ : MulAut M) (x : M) :
    (MulAut.conj k * Φ * (MulAut.conj k)⁻¹) x = k * Φ (k⁻¹ * x * k) * k⁻¹ := by
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem ringChar_eq_of_card_pow {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ f) : ringChar F = p := by
  have : Fintype F := Fintype.ofFinite F
  haveI : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  exact ringChar.eq F p

theorem le_of_isPerfect_of_commutators {C N Y : Subgroup Q} (hYC : Y ≤ C)
    (hYp : Group.IsPerfect Y) (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) : Y ≤ N := by
  have h1 : ⁅Y, Y⁆ = Y := Subgroup.commutator_eq_self
  calc Y = ⁅Y, Y⁆ := h1.symm
    _ ≤ N := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact hcomm g₁ (hYC hg₁) g₂ (hYC hg₂)

theorem isSubnormal_subgroupOf_of_le {C N Y : Subgroup Q} (hNC : N ≤ C)
    (h : (Y.subgroupOf C).IsSubnormal) : (Y.subgroupOf N).IsSubnormal := by
  have := h.comap (Subgroup.inclusion hNC)
  convert this using 1
  ext ⟨n, hn⟩
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_comap]

theorem isSubnormal_eq_top_or_le_center {N : Type*} [Group N] (hN : CFSG.IsQuasisimple N)
    {H : Subgroup N} (h : H.IsSubnormal) : H = ⊤ ∨ H ≤ Subgroup.center N := by
  induction h with
  | top => exact Or.inl rfl
  | step H K hHK hK hHn ih =>
    rcases ih with rfl | hKc
    · have hn : H.Normal :=
        ⟨fun n hn g => (Subgroup.normal_subgroupOf_iff hHK).mp hHn n g hn (Subgroup.mem_top g)⟩
      exact CFSG.LocalCores.quasisimple_normal_subgroups hN hn
    · exact Or.inr (hHK.trans hKc)

theorem eq_or_commute_of_isSubnormal {N : Subgroup Q} (hNq : CFSG.IsQuasisimple N)
    {Y : Subgroup Q} (hYN : Y ≤ N) (hsn : (Y.subgroupOf N).IsSubnormal) :
    Y = N ∨ ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y := by
  rcases isSubnormal_eq_top_or_le_center hNq hsn with h | h
  · left
    exact le_antisymm hYN (Subgroup.subgroupOf_eq_top.mp h)
  · right
    intro y hy n hn
    have h1 : (⟨y, hYN hy⟩ : N) ∈ Subgroup.center N := h (show (⟨y, hYN hy⟩ : N) ∈
      Y.subgroupOf N from hy)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨n, hn⟩)).symm

theorem three_dvd_card_of_exists {M : Type*} [Group M] {Y : Subgroup M}
    (hx : ∃ x ∈ Y, x ≠ 1 ∧ x ^ 3 = 1) : 3 ∣ Nat.card Y := by
  obtain ⟨x, hxY, hx1, hx3⟩ := hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (⟨x, hxY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have h1 : (⟨x, hxY⟩ : Y) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  exact (orderOf_eq_prime h3 h1) ▸ orderOf_dvd_natCard (⟨x, hxY⟩ : Y)

theorem eq_one_of_pow_three_eq_one_of_not_three_dvd {M : Type*} [Group M] {Y : Subgroup M}
    (hY3 : ¬ 3 ∣ Nat.card Y) {y : M} (hy : y ∈ Y) (hy3 : y ^ 3 = 1) : y = 1 := by
  by_contra hne
  exact hY3 (three_dvd_card_of_exists ⟨y, hy, hne, hy3⟩)

theorem perfSubnormalBot_of_commutators_le_quasisimple {C N : Subgroup Q} (hNC : N ≤ C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) (hNq : CFSG.IsQuasisimple N)
    (hx : ∃ x ∈ N, x ≠ 1 ∧ x ^ 3 = 1) : PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  have hYN := le_of_isPerfect_of_commutators hYC hYp hcomm
  have hsnN := isSubnormal_subgroupOf_of_le hNC hsn
  rcases eq_or_commute_of_isSubnormal hNq hYN hsnN with rfl | hcen
  · exact absurd (three_dvd_card_of_exists hx) hY3
  · exact eq_bot_of_isPerfect_of_isSolvable hYp
      (Group.isSolvable_of_comm fun a b => Subtype.ext (hcen a a.2 b (hYN b.2)))

theorem perfSubnormalBot_of_commutators_le_glTwo {C S : Subgroup Q}
    {K : Type} [Field K] [Finite K]
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ S) (ι : S →* GL (Fin 2) K)
    (hι : Function.Injective ι) : PerfSubnormalBot C := by
  intro Y hYC _ hYp hY3
  have hYS := le_of_isPerfect_of_commutators hYC hYp hcomm
  set ι' : Y →* GL (Fin 2) K := ι.comp (Subgroup.inclusion hYS) with hι'
  have hι'inj : Function.Injective ι' :=
    hι.comp (Subgroup.inclusion_injective hYS)
  have hperf : Group.IsPerfect ι'.range := Group.IsPerfect.range ι'
  have hcard : Nat.card ι'.range = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hι'inj).toEquiv).symm
  have hbot := eq_bot_of_isPerfect_of_glTwo ι'.range hperf (by rwa [hcard])
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hmem : ι' ⟨y, hy⟩ ∈ ι'.range := ⟨⟨y, hy⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have := hι'inj (hmem.trans (map_one ι').symm)
  exact congrArg Subtype.val this

theorem perfSubnormalBot_of_isSimpleGroup {C : Subgroup Q} (hC : IsSimpleGroup C)
    (hx : ∃ x ∈ C, x ≠ 1 ∧ x ^ 3 = 1) : PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  rcases hsn.eq_bot_or_top_of_isSimpleGroup hC with h0 | h0
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hYC] at h0
    exact h0
  · exact absurd (three_dvd_card_of_exists (by rwa [le_antisymm hYC
      (Subgroup.subgroupOf_eq_top.mp h0)])) hY3

theorem perfSubnormalBot_of_isSolvable {C : Subgroup Q} (hC : Group.IsSolvable C) :
    PerfSubnormalBot C := by
  intro Y hYC _ hYp _
  have hYs : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hYC) (Subgroup.inclusion_injective hYC)
  exact eq_bot_of_isPerfect_of_isSolvable hYp hYs

@[expose] def PerfSubnormalBotGrp (D : Type*) [Group D] : Prop :=
  ∀ Y : Subgroup D, Y.IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → Y = ⊥

theorem perfSubnormalBot_of_grp {C : Subgroup Q} (h : PerfSubnormalBotGrp C) :
    PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  have e : Y.subgroupOf C ≃* Y := Subgroup.subgroupOfEquivOfLe hYC
  have hp : Group.IsPerfect (Y.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card (Y.subgroupOf C) = Nat.card Y := Nat.card_congr e.toEquiv
  have h0 := h (Y.subgroupOf C) hsn hp (by rwa [hcard])
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hYC] at h0
  exact h0

theorem perfSubnormalBotGrp_of_mulEquiv {D D' : Type*} [Group D] [Group D'] (e : D ≃* D')
    (h : PerfSubnormalBotGrp D') : PerfSubnormalBotGrp D := by
  intro Y hsn hYp hY3
  have hsn' : (Y.map e.toMonoidHom).IsSubnormal := hsn.map e.surjective
  have hYp' : Group.IsPerfect (Y.map e.toMonoidHom) := Group.IsPerfect.map e.toMonoidHom
  have hY3' : ¬ 3 ∣ Nat.card (Y.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp (h _ hsn' hYp' hY3')

theorem perfSubnormalBotGrp_of_isSimpleGroup {D : Type*} [Group D] (hD : IsSimpleGroup D)
    (hx : ∃ x : D, x ≠ 1 ∧ x ^ 3 = 1) : PerfSubnormalBotGrp D := by
  intro Y hsn _ hY3
  rcases hsn.eq_bot_or_top_of_isSimpleGroup hD with h0 | h0
  · exact h0
  · obtain ⟨x, hx1, hx3⟩ := hx
    have hxY : x ∈ Y := by rw [h0]; exact Subgroup.mem_top x
    exact absurd (three_dvd_card_of_exists (Y := Y) ⟨x, hxY, hx1, hx3⟩) hY3

theorem perfSubnormalBot_of_commutators_le_grp {C N : Subgroup Q} (hNC : N ≤ C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ N) (hN : PerfSubnormalBotGrp N) :
    PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  have hYN := le_of_isPerfect_of_commutators hYC hYp hcomm
  have hsnN := isSubnormal_subgroupOf_of_le hNC hsn
  have e : Y.subgroupOf N ≃* Y := Subgroup.subgroupOfEquivOfLe hYN
  have hp : Group.IsPerfect (Y.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card (Y.subgroupOf N) = Nat.card Y := Nat.card_congr e.toEquiv
  have h0 := hN (Y.subgroupOf N) hsnN hp (by rwa [hcard])
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hYN] at h0
  exact h0

theorem eq_bot_of_isPerfect_of_isSolvable' {M : Type*} [Group M] {Y : Subgroup M}
    (hYp : Group.IsPerfect Y) (hYs : Group.IsSolvable Y) : Y = ⊥ := by
  by_contra hY
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
  exact Group.IsPerfect.not_isSolvable Y hYs

theorem perfSubnormalBotGrp_of_isQuasisimple {D : Type*} [Group D] (hD : CFSG.IsQuasisimple D)
    (hx : ∃ x : D, x ≠ 1 ∧ x ^ 3 = 1) : PerfSubnormalBotGrp D := by
  intro Y hsn hYp hY3
  rcases isSubnormal_eq_top_or_le_center hD hsn with h0 | h0
  · obtain ⟨x, hx1, hx3⟩ := hx
    have hxY : x ∈ Y := by rw [h0]; exact Subgroup.mem_top x
    exact absurd (three_dvd_card_of_exists (Y := Y) ⟨x, hxY, hx1, hx3⟩) hY3
  · exact eq_bot_of_isPerfect_of_isSolvable' hYp
      (Group.isSolvable_of_comm fun a b => Subtype.ext (by
        exact (Subgroup.mem_center_iff.mp (h0 a.2) b).symm))

theorem perfSubnormalBot_of_le_grp {C N : Subgroup Q} (hNC : N ≤ C)
    (hle : ∀ Y : Subgroup Q, Y ≤ C → Group.IsPerfect Y → Y ≤ N) (hN : PerfSubnormalBotGrp N) :
    PerfSubnormalBot C := by
  intro Y hYC hsn hYp hY3
  have hYN := hle Y hYC hYp
  have hsnN := isSubnormal_subgroupOf_of_le hNC hsn
  have e : Y.subgroupOf N ≃* Y := Subgroup.subgroupOfEquivOfLe hYN
  have hp : Group.IsPerfect (Y.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card (Y.subgroupOf N) = Nat.card Y := Nat.card_congr e.toEquiv
  have h0 := hN (Y.subgroupOf N) hsnN hp (by rwa [hcard])
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hYN] at h0
  exact h0

theorem map_conj_fixed_eq {M : Type*} [Group M] {Φ β : MulAut M} (k : M)
    (hβ : β = MulAut.conj k * Φ * (MulAut.conj k)⁻¹) {C R : Subgroup M}
    (hC : ∀ z, z ∈ C ↔ β z = z) (hR : ∀ y, y ∈ R ↔ Φ y = y) :
    C.map (MulAut.conj k⁻¹ : M ≃* M).toMonoidHom = R := by
  ext y
  rw [Subgroup.mem_map, hR y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := (hC x).mp hx
    rw [hβ, conj_mul_conj_inv_apply] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc Φ (k⁻¹ * x * k) = k⁻¹ * (k * Φ (k⁻¹ * x * k) * k⁻¹) * k := by group
      _ = k⁻¹ * x * k := by rw [h1]
  · intro hy
    refine ⟨k * y * k⁻¹, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [hC, hβ, conj_mul_conj_inv_apply]
    have : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [this, hy]

theorem two_pow_mod_three_of_even {f : ℕ} (h : Even f) : 2 ^ f % 3 = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul, pow_mul]
  simp [Nat.pow_mod]

theorem two_pow_mod_three_of_odd {f : ℕ} (h : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_succ, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

theorem not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem three_dvd_sq_sub_one {n : ℕ} (hn : ¬ 3 ∣ n) : 3 ∣ n ^ 2 - 1 := by
  have h1 : n ^ 2 % 3 = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  omega

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
