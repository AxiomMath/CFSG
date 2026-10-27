module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Gen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

section Basic

variable {X H : Type} [Group X] [Group H]

structure OutProps (Φ : X →* H) (ψ : H) (α : MulAut X) : Prop where
  inj : Function.Injective Φ
  act : ∀ x, ψ * Φ x * ψ⁻¹ = Φ (α x)
  cen : ∀ h : H, (∀ x, h * Φ x * h⁻¹ = Φ x) → h = 1
  gen : ∀ h : H, ∃ (g : X) (s : ℕ), h = Φ g * ψ ^ s
  outer : ∀ (s : ℕ) (g : X), α ^ s = MulAut.conj g → α ^ s = 1

variable {Φ : X →* H} {ψ : H} {α : MulAut X}

theorem OutProps.act_pow (P : OutProps Φ ψ α) (s : ℕ) (x : X) :
    ψ ^ s * Φ x * (ψ ^ s)⁻¹ = Φ ((α ^ s) x) := by
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    have e : ψ ^ (s + 1) * Φ x * (ψ ^ (s + 1))⁻¹ = ψ ^ s * (ψ * Φ x * ψ⁻¹) * (ψ ^ s)⁻¹ := by
      rw [pow_succ, _root_.mul_inv_rev]
      group
    rw [e, P.act, ih, pow_succ, MulAut.mul_apply]

theorem OutProps.range_normal (P : OutProps Φ ψ α) : Φ.range.Normal := by
  refine ⟨fun n hn h => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨g, s, rfl⟩ := P.gen h
  refine ⟨g * (α ^ s) x * g⁻¹, ?_⟩
  have e : Φ g * ψ ^ s * Φ x * (Φ g * ψ ^ s)⁻¹ =
      Φ g * (ψ ^ s * Φ x * (ψ ^ s)⁻¹) * (Φ g)⁻¹ := by
    rw [_root_.mul_inv_rev]
    group
  rw [e, P.act_pow, map_mul, map_mul, map_inv]

theorem OutProps.pow_eq_one_iff (P : OutProps Φ ψ α) (s : ℕ) : ψ ^ s = 1 ↔ α ^ s = 1 := by
  constructor
  · intro h
    refine MulEquiv.ext fun x => P.inj ?_
    rw [← P.act_pow s x, h]
    simp
  · intro h
    apply P.cen
    intro x
    rw [P.act_pow, h]
    simp

theorem OutProps.eq_one_of_mem_range (P : OutProps Φ ψ α) {s : ℕ} (h : ψ ^ s ∈ Φ.range) :
    ψ ^ s = 1 := by
  obtain ⟨g, hg⟩ := h
  have hc : α ^ s = MulAut.conj g := by
    refine MulEquiv.ext fun x => P.inj ?_
    rw [← P.act_pow s x, ← hg]
    simp [MulAut.conj_apply]
  exact (P.pow_eq_one_iff s).2 (P.outer s g hc)

theorem mem_zpowers_iff_nat [Finite H] (ψ x : H) :
    x ∈ Subgroup.zpowers ψ ↔ ∃ s : ℕ, ψ ^ s = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨s, -, hs⟩
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s % orderOf ψ, Nat.mod_lt _ (orderOf_pos ψ), by rw [pow_mod_orderOf, hs]⟩

theorem OutProps.inf_zpowers_eq_bot [Finite H] (P : OutProps Φ ψ α) :
    Φ.range ⊓ Subgroup.zpowers ψ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxr, hxz⟩
  obtain ⟨s, rfl⟩ := (mem_zpowers_iff_nat ψ x).mp hxz
  rw [Subgroup.mem_bot]
  exact P.eq_one_of_mem_range hxr

theorem OutProps.sup_eq_top (P : OutProps Φ ψ α) : Subgroup.zpowers ψ ⊔ Φ.range = ⊤ := by
  rw [eq_top_iff]
  intro h _
  obtain ⟨g, s, rfl⟩ := P.gen h
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨g, rfl⟩)
    (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) s))

theorem OutProps.card_eq [Finite H] (P : OutProps Φ ψ α) :
    Nat.card H = Nat.card X * orderOf ψ := by
  have hnorm := P.range_normal
  have h1 := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf
    (A := Subgroup.zpowers ψ) (B := Φ.range) Subgroup.le_normalizer_of_normal
  rw [inf_comm, P.inf_zpowers_eq_bot, Subgroup.card_bot, mul_one, P.sup_eq_top,
    Subgroup.card_top, Nat.card_zpowers] at h1
  rw [h1, mul_comm]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective P.inj).toEquiv).symm

theorem OutProps.commutator_mem_range (P : OutProps Φ ψ α) (a b : H) :
    a * b * a⁻¹ * b⁻¹ ∈ Φ.range := by
  have : Φ.range.Normal := P.range_normal
  obtain ⟨g, s, rfl⟩ := P.gen a
  obtain ⟨h, t, rfl⟩ := P.gen b
  have e1 : ∀ x : X, ((Φ x : H) : H ⧸ Φ.range) = 1 := fun x =>
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, e1, one_mul]
  group

theorem OutProps.perfectCore_eq_inf_range (P : OutProps Φ ψ α) (N : Subgroup H) :
    perfectCore N = perfectCore (N ⊓ Φ.range) := by
  apply le_antisymm
  · have hle : derivedSeriesOf N 1 ≤ N ⊓ Φ.range := by
      rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ⟨?_, ?_⟩
      · exact N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
      · exact P.commutator_mem_range a b
    have key : ∀ k, derivedSeriesOf N (1 + k) ≤ derivedSeriesOf (N ⊓ Φ.range) k := by
      intro k
      induction k with
      | zero => exact hle
      | succ k ih =>
        rw [← add_assoc, derivedSeriesOf_succ, derivedSeriesOf_succ]
        exact Subgroup.commutator_mono ih ih
    exact le_iInf fun k => (perfectCore_le_derivedSeriesOf N (1 + k)).trans (key k)
  · exact perfectCore_mono inf_le_left

end Basic

section TwoPart

variable {H : Type} [Group H]

@[expose] noncomputable def twoExp (ψ : H) : ℕ := (orderOf ψ).factorization 2

@[expose] noncomputable def oddPart (ψ : H) : ℕ := orderOf ψ / 2 ^ twoExp ψ

@[expose] noncomputable def psi2 (ψ : H) : H := ψ ^ oddPart ψ

omit [Group H] in
theorem twoExp_mul_oddPart (ψ : H) [Group H] : 2 ^ twoExp ψ * oddPart ψ = orderOf ψ :=
  Nat.ordProj_mul_ordCompl_eq_self (orderOf ψ) 2

theorem oddPart_odd [Finite H] (ψ : H) : Odd (oddPart ψ) :=
  Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos ψ).ne')

theorem oddPart_pos [Finite H] (ψ : H) : 0 < oddPart ψ := (oddPart_odd ψ).pos

theorem orderOf_psi2 [Finite H] (ψ : H) : orderOf (psi2 ψ) = 2 ^ twoExp ψ := by
  unfold psi2
  have hd : oddPart ψ ∣ orderOf ψ := ⟨2 ^ twoExp ψ, by rw [← twoExp_mul_oddPart ψ, mul_comm]⟩
  rw [orderOf_pow_of_dvd (oddPart_pos ψ).ne' hd]
  conv_lhs => rw [← twoExp_mul_oddPart ψ]
  exact Nat.mul_div_cancel _ (oddPart_pos ψ)

theorem twoExp_pos [Finite H] {ψ : H} (he : Even (orderOf ψ)) : 1 ≤ twoExp ψ := by
  by_contra h
  have h0 : twoExp ψ = 0 := by omega
  have := twoExp_mul_oddPart ψ
  rw [h0, pow_zero, one_mul] at this
  rw [← this] at he
  exact (Nat.not_even_iff_odd.mpr (oddPart_odd ψ)) he

theorem psi2_pow_eq (ψ : H) (s : ℕ) : psi2 ψ ^ s = ψ ^ (oddPart ψ * s) := by
  unfold psi2
  rw [pow_mul]

theorem psi2_pow_two_exp [Finite H] (ψ : H) : psi2 ψ ^ (2 ^ twoExp ψ) = 1 := by
  rw [← orderOf_psi2 ψ]
  exact pow_orderOf_eq_one _

theorem zpowers_psi2_le_zpowers (ψ : H) : Subgroup.zpowers (psi2 ψ) ≤ Subgroup.zpowers ψ := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) _

end TwoPart

section TGroup

variable {X H : Type} [Group X] [Group H] [Finite H] {Φ : X →* H} {ψ : H} {α : MulAut X}

omit [Finite H] in
theorem OutProps.pow_mem_normalizer_map (P : OutProps Φ ψ α) {V : Subgroup X}
    (hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ V ↔ x ∈ V) (s : ℕ) :
    ψ ^ s ∈ Subgroup.normalizer ((V.map Φ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [P.act_pow]
    exact ⟨_, (hV _ v).mpr hv, rfl⟩
  · intro hy
    have hy1 : ψ ^ s * y * (ψ ^ s)⁻¹ ∈ Φ.range := by
      obtain ⟨v, -, hv⟩ := hy
      exact ⟨v, hv⟩
    have hy2 : y ∈ Φ.range := by
      have hnorm := P.range_normal
      have := hnorm.conj_mem _ hy1 (ψ ^ s)⁻¹
      simpa [mul_assoc] using this
    obtain ⟨z, rfl⟩ := hy2
    rw [P.act_pow] at hy
    obtain ⟨v, hv, hvz⟩ := hy
    have := P.inj hvz
    refine ⟨z, ?_, rfl⟩
    have hv' : (α ^ s) z ∈ V := this ▸ hv
    exact (hV _ z).mp hv'

omit [Finite H] in
theorem OutProps.psi2_mem_normalizer_map (P : OutProps Φ ψ α) {V : Subgroup X}
    (hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ V ↔ x ∈ V) :
    psi2 ψ ∈ Subgroup.normalizer ((V.map Φ : Subgroup H) : Set H) :=
  P.pow_mem_normalizer_map hV _

@[expose] noncomputable def spT (Φ : X →* H) (ψ : H) (U : Subgroup X) : Subgroup H :=
  U.map Φ ⊔ Subgroup.zpowers (psi2 ψ)

omit [Finite H] in
theorem OutProps.zpowers_psi2_le_normalizer (P : OutProps Φ ψ α) {V : Subgroup X}
    (hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ V ↔ x ∈ V) :
    Subgroup.zpowers (psi2 ψ) ≤ Subgroup.normalizer ((V.map Φ : Subgroup H) : Set H) := by
  rw [Subgroup.zpowers_le]
  exact P.psi2_mem_normalizer_map hV

theorem OutProps.mem_spT_iff (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) {y : H} :
    y ∈ spT Φ ψ U ↔ ∃ u ∈ U, ∃ s : ℕ, y = Φ u * psi2 ψ ^ s := by
  unfold spT
  constructor
  · intro hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (P.zpowers_psi2_le_normalizer hU)] at hy
    obtain ⟨_, ⟨u, hu, rfl⟩, z, hz, rfl⟩ := hy
    obtain ⟨s, rfl⟩ := (mem_zpowers_iff_nat (psi2 ψ) z).mp hz
    exact ⟨u, hu, s, rfl⟩
  · rintro ⟨u, hu, s, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨u, hu, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) s))

omit [Finite H] in
theorem OutProps.psi2_pow_mem_range_iff (P : OutProps Φ ψ α) (s : ℕ) :
    psi2 ψ ^ s ∈ Φ.range ↔ psi2 ψ ^ s = 1 := by
  constructor
  · intro h
    rw [psi2_pow_eq] at h ⊢
    exact P.eq_one_of_mem_range h
  · intro h
    rw [h]
    exact Φ.range.one_mem

theorem OutProps.spT_inf_range (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) :
    spT Φ ψ U ⊓ Φ.range = U.map Φ := by
  apply le_antisymm
  · rintro y ⟨hyT, hyR⟩
    obtain ⟨u, hu, s, rfl⟩ := (P.mem_spT_iff hU).mp hyT
    have h1 : psi2 ψ ^ s ∈ Φ.range := by
      obtain ⟨g, hg⟩ := hyR
      refine ⟨u⁻¹ * g, ?_⟩
      rw [map_mul, map_inv, hg]
      group
    rw [(P.psi2_pow_mem_range_iff s).mp h1, mul_one]
    exact ⟨u, hu, rfl⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_sup_left hy
    · obtain ⟨u, -, rfl⟩ := hy
      exact ⟨u, rfl⟩

theorem OutProps.zpowers_psi2_inf (P : OutProps Φ ψ α) (V : Subgroup X) :
    Subgroup.zpowers (psi2 ψ) ⊓ V.map Φ = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy1, v, -, hv⟩
  have h2 : y ∈ Subgroup.zpowers ψ ⊓ Φ.range :=
    ⟨zpowers_psi2_le_zpowers ψ hy1, ⟨v, hv⟩⟩
  rw [inf_comm, P.inf_zpowers_eq_bot] at h2
  exact h2

theorem OutProps.card_spT (P : OutProps Φ ψ α) {V : Subgroup X}
    (hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ V ↔ x ∈ V) :
    Nat.card (spT Φ ψ V) = Nat.card V * 2 ^ twoExp ψ := by
  have h := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf
    (A := Subgroup.zpowers (psi2 ψ)) (B := V.map Φ) (P.zpowers_psi2_le_normalizer hV)
  rw [P.zpowers_psi2_inf V, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_psi2] at h
  unfold spT
  rw [sup_comm, h, mul_comm,
    Nat.card_congr (Subgroup.equivMapOfInjective V Φ P.inj).toEquiv.symm]

theorem OutProps.isSylowTwoOf_spT [Finite X] (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) (hUS : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (spT Φ ψ U) ⊤ := by
  have hpA : IsPGroup 2 (Subgroup.zpowers (psi2 ψ)) := by
    refine IsPGroup.of_card (n := twoExp ψ) ?_
    rw [Nat.card_zpowers, orderOf_psi2]
  have hpB : IsPGroup 2 (U.map Φ) := hUS.2.1.map Φ
  have hp : IsPGroup 2 (spT Φ ψ U) := by
    unfold spT
    rw [sup_comm]
    exact CFSG.QuasithinUnique.Lin2.isPGroup_sup_of_le_normalizer
      (P.zpowers_psi2_le_normalizer hU) hpA hpB
  refine isSylowTwoOf_of_card_eq le_top hp ?_
  rw [P.card_spT hU, hUS.card_eq]
  unfold twoPart
  rw [Subgroup.card_top, Subgroup.card_top, P.card_eq,
    Nat.factorization_mul Nat.card_pos.ne' (orderOf_pos ψ).ne']
  simp only [Finsupp.add_apply, pow_add]
  rfl

end TGroup

end CFSG.Quasithin.H13.F431.G2.OutK
