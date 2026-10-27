module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Setup
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Gen

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

universe u

section Core

variable {Mb : Type u} [Group Mb]

structure F431SpOutCore (T S : Subgroup Mb) (f : Mb) (N1 N2 : Subgroup Mb) (I : Finset Mb) :
    Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ N1
  T_le₂ : T ≤ N2
  Q_abel : ∀ j, ∀ x ∈ spQ N1 N2 j, ∀ y ∈ spQ N1 N2 j, x * y = y * x
  Q_card : Nat.card (spQ N1 N2 1) = Nat.card (spQ N1 N2 0)
  A_eq : ∀ A : Subgroup Mb, A ≤ T → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    Nat.card A = Nat.card (spQ N1 N2 0) → A = spQ N1 N2 0 ∨ A = spQ N1 N2 1
  S_le : S ≤ T
  S_norm : T ≤ Subgroup.normalizer (S : Set Mb)
  cyc : ∃ t₀ : Mb, T = S ⊔ Subgroup.zpowers t₀
  I_center : ∀ i ∈ I, i ∈ centerOf T
  I_le_S : ∀ i ∈ I, i ∈ S
  order_two : ∀ i ∈ I, orderOf i = 2
  rep : ∀ x ∈ S, orderOf x = 2 → ∃! i, i ∈ I ∧ IsConj i x
  fusion : ∀ x ∈ S, orderOf x = 2 → ∃ i ∈ I,
    (∃ m ∈ N1, m * x * m⁻¹ = i) ∨ (∃ m ∈ N2, m * x * m⁻¹ = i)
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f ^ 2 = 1
  f_not_central : f ∉ centerOf T
  Z_sq : ∀ j, ∀ x ∈ spZ N1 N2 j, x ^ 2 = 1
  Z_cls : ∀ j, ∀ x ∈ spZ N1 N2 j, ∀ y ∈ centerOf S, IsConj x y → y ∈ spZ N1 N2 j
  W_le : spWf T f ≤ centerOf S
  Sylow_Tf : ∀ j, IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ spN N1 N2 j)

theorem F431SpOutCore.toOut {T S : Subgroup Mb} {f : Mb} {N1 N2 : Subgroup Mb} {I : Finset Mb}
    (C : F431SpOutCore T S f N1 N2 I)
    (hW : ∃ j, ∃ x ∈ spWf T f, x ∈ spZ N1 N2 j ∧ x ≠ 1) : F431SpOut T S f N1 N2 I where
  sylow := C.sylow
  T_le₁ := C.T_le₁
  T_le₂ := C.T_le₂
  Q_abel := C.Q_abel
  Q_card := C.Q_card
  A_eq := C.A_eq
  S_le := C.S_le
  S_norm := C.S_norm
  cyc := C.cyc
  I_center := C.I_center
  I_le_S := C.I_le_S
  order_two := C.order_two
  rep := C.rep
  fusion := C.fusion
  f_mem := C.f_mem
  f_not := C.f_not
  f_sq := C.f_sq
  f_not_central := C.f_not_central
  Z_sq := C.Z_sq
  Z_cls := C.Z_cls
  W_le := C.W_le
  W_ne := hW
  Sylow_Tf := C.Sylow_Tf

end Core

namespace SpOut2

section TwoPart

variable {H : Type u} [Group H] [Finite H]

@[expose] noncomputable def twoExp (ψ : H) : ℕ := (orderOf ψ).factorization 2

@[expose] noncomputable def oddPart (ψ : H) : ℕ := orderOf ψ / 2 ^ twoExp ψ

@[expose] noncomputable def psi2 (ψ : H) : H := ψ ^ oddPart ψ

omit [Finite H] in
theorem twoExp_mul_oddPart (ψ : H) : 2 ^ twoExp ψ * oddPart ψ = orderOf ψ :=
  Nat.ordProj_mul_ordCompl_eq_self (orderOf ψ) 2

theorem oddPart_odd (ψ : H) : Odd (oddPart ψ) :=
  Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos ψ).ne')

theorem oddPart_pos (ψ : H) : 0 < oddPart ψ := (oddPart_odd ψ).pos

theorem orderOf_psi2 (ψ : H) : orderOf (psi2 ψ) = 2 ^ twoExp ψ := by
  unfold psi2
  have hd : oddPart ψ ∣ orderOf ψ := ⟨2 ^ twoExp ψ, by rw [← twoExp_mul_oddPart ψ, mul_comm]⟩
  rw [orderOf_pow_of_dvd (oddPart_pos ψ).ne' hd]
  conv_lhs => rw [← twoExp_mul_oddPart ψ]
  exact Nat.mul_div_cancel _ (oddPart_pos ψ)

theorem twoExp_pos {ψ : H} (he : Even (orderOf ψ)) : 1 ≤ twoExp ψ := by
  by_contra h
  have h0 : twoExp ψ = 0 := by omega
  have := twoExp_mul_oddPart ψ
  rw [h0, pow_zero, one_mul] at this
  rw [← this] at he
  exact (Nat.not_even_iff_odd.mpr (oddPart_odd ψ)) he

omit [Finite H] in
theorem psi2_pow_eq (ψ : H) (s : ℕ) : psi2 ψ ^ s = ψ ^ (oddPart ψ * s) := by
  unfold psi2
  rw [pow_mul]

theorem psi2_pow_two_exp (ψ : H) : psi2 ψ ^ (2 ^ twoExp ψ) = 1 := by
  rw [← orderOf_psi2 ψ]
  exact pow_orderOf_eq_one _

end TwoPart

section TGroup

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H] [Finite H]
  {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}

omit [Finite H] in
theorem OutProps.act_psi2_pow (P : OutProps Φ ψ k₀) (s : ℕ) (x : antiSp F) :
    psi2 ψ ^ s * Φ x * (psi2 ψ ^ s)⁻¹ =
      Φ ((frobAut F ^ (k₀ * (oddPart ψ * s))) x) := by
  rw [psi2_pow_eq]
  exact P.act_pow _ x

omit [Finite H] in
theorem OutProps.pow_mem_normalizer_map (P : OutProps Φ ψ k₀) {V : Subgroup (antiSp F)}
    (hV : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ V ↔ x ∈ V) (s : ℕ) :
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
    have hv' : (frobAut F ^ (k₀ * s)) z ∈ V := this ▸ hv
    exact (hV _ z).mp hv'

omit [Finite H] in
theorem OutProps.psi2_mem_normalizer_map (P : OutProps Φ ψ k₀) {V : Subgroup (antiSp F)}
    (hV : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ V ↔ x ∈ V) :
    psi2 ψ ∈ Subgroup.normalizer ((V.map Φ : Subgroup H) : Set H) :=
  P.pow_mem_normalizer_map hV _

@[expose] noncomputable def spT (Φ : antiSp F →* H) (ψ : H) (U : Subgroup (antiSp F)) :
    Subgroup H :=
  U.map Φ ⊔ Subgroup.zpowers (psi2 ψ)

omit [Finite H] in
theorem OutProps.zpowers_psi2_le_normalizer (P : OutProps Φ ψ k₀) {V : Subgroup (antiSp F)}
    (hV : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ V ↔ x ∈ V) :
    Subgroup.zpowers (psi2 ψ) ≤ Subgroup.normalizer ((V.map Φ : Subgroup H) : Set H) := by
  rw [Subgroup.zpowers_le]
  exact P.psi2_mem_normalizer_map hV

theorem OutProps.mem_spT_iff (P : OutProps Φ ψ k₀) {U : Subgroup (antiSp F)}
    (hU : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ U ↔ x ∈ U) {y : H} :
    y ∈ spT Φ ψ U ↔ ∃ u ∈ U, ∃ s : ℕ, y = Φ u * psi2 ψ ^ s := by
  unfold spT
  constructor
  · intro hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (P.zpowers_psi2_le_normalizer hU)] at hy
    obtain ⟨_, ⟨u, hu, rfl⟩, z, hz, rfl⟩ := hy
    obtain ⟨s, rfl⟩ := (OutProps.mem_zpowers_iff (psi2 ψ) z).mp hz
    exact ⟨u, hu, s, rfl⟩
  · rintro ⟨u, hu, s, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨u, hu, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) s))

omit [Finite H] in
theorem OutProps.psi2_pow_mem_range_iff {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (s : ℕ) : psi2 ψ ^ s ∈ Φ.range ↔ psi2 ψ ^ s = 1 := by
  constructor
  · intro h
    rw [psi2_pow_eq] at h ⊢
    exact P.eq_one_of_mem_range hn hF h
  · intro h
    rw [h]
    exact Φ.range.one_mem

theorem OutProps.spT_inf_range {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {U : Subgroup (antiSp F)}
    (hU : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ U ↔ x ∈ U) :
    spT Φ ψ U ⊓ Φ.range = U.map Φ := by
  apply le_antisymm
  · rintro y ⟨hyT, hyR⟩
    obtain ⟨u, hu, s, rfl⟩ := (P.mem_spT_iff hU).mp hyT
    have h1 : psi2 ψ ^ s ∈ Φ.range := by
      obtain ⟨g, hg⟩ := hyR
      refine ⟨u⁻¹ * g, ?_⟩
      rw [map_mul, map_inv, hg]
      group
    rw [(P.psi2_pow_mem_range_iff hn hF s).mp h1, mul_one]
    exact ⟨u, hu, rfl⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_sup_left hy
    · obtain ⟨u, -, rfl⟩ := hy
      exact ⟨u, rfl⟩

end TGroup

section Sylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H] [Finite H]
  {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}

omit [Finite H] in
theorem zpowers_psi2_le_zpowers (ψ : H) : Subgroup.zpowers (psi2 ψ) ≤ Subgroup.zpowers ψ := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) _

theorem OutProps.zpowers_psi2_inf {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (V : Subgroup (antiSp F)) :
    Subgroup.zpowers (psi2 ψ) ⊓ V.map Φ = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy1, v, -, hv⟩
  have h2 : y ∈ Subgroup.zpowers ψ ⊓ Φ.range :=
    ⟨zpowers_psi2_le_zpowers ψ hy1, ⟨v, hv⟩⟩
  rw [inf_comm, P.inf_zpowers_eq_bot hn hF] at h2
  exact h2

theorem OutProps.card_spT {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {V : Subgroup (antiSp F)}
    (hV : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ V ↔ x ∈ V) :
    Nat.card (spT Φ ψ V) = Nat.card V * 2 ^ twoExp ψ := by
  have h := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf
    (A := Subgroup.zpowers (psi2 ψ)) (B := V.map Φ) (P.zpowers_psi2_le_normalizer hV)
  rw [P.zpowers_psi2_inf hn hF V, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    orderOf_psi2] at h
  unfold spT
  rw [sup_comm, h, mul_comm,
    Nat.card_congr (Subgroup.equivMapOfInjective V Φ P.inj).toEquiv.symm]

theorem OutProps.isSylowTwoOf_spT {n : ℕ} (P : OutProps Φ ψ k₀) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {U : Subgroup (antiSp F)}
    (hU : ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ U ↔ x ∈ U)
    (hUS : IsSylowTwoOf U ⊤) : IsSylowTwoOf (spT Φ ψ U) ⊤ := by
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
  rw [P.card_spT hn hF hU, hUS.card_eq]
  unfold twoPart
  rw [Subgroup.card_top, Subgroup.card_top, P.card_eq hn hF,
    Nat.factorization_mul Nat.card_pos.ne' (orderOf_pos ψ).ne']
  simp only [Finsupp.add_apply, pow_add]
  rfl

end Sylow

section Index

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
theorem exists_card_eq_inf_mul (Inn : Subgroup H) [Inn.Normal] (M : Subgroup H) :
    ∃ k : ℕ, k ∣ Inn.index ∧ Nat.card M = Nat.card (M ⊓ Inn : Subgroup H) * k := by
  refine ⟨Inn.relIndex M, Subgroup.relIndex_dvd_index_of_normal Inn M, ?_⟩
  have h := Subgroup.card_mul_index ((M ⊓ Inn).subgroupOf M)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ Inn ≤ M)).toEquiv] at h
  have e : ((M ⊓ Inn).subgroupOf M).index = Inn.relIndex M := Subgroup.inf_relIndex_left M Inn
  rw [e] at h
  exact h.symm

end Index

section PCore

variable {X : Type*} {H : Type*} [Group X] [Group H] [Finite H]

theorem mem_of_map_mem_pCoreOf (Φ : X →* H) (hΦ : Function.Injective Φ) {R : Subgroup X}
    (hcore : pCoreOf 2 (Subgroup.normalizer (R : Set X)) = R) {z : X}
    (hz : z ∈ Subgroup.normalizer (R : Set X))
    (hzQ : Φ z ∈ pCoreOf 2 (Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H))) : z ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := Subgroup.normalizer ((R.map Φ : Subgroup H) : Set H) with hN
  set V : Subgroup X := (pCoreOf 2 N).comap Φ ⊓ Subgroup.normalizer (R : Set X) with hV
  have hVconj : ∀ n ∈ Subgroup.normalizer (R : Set X), ∀ y ∈ V, n * y * n⁻¹ ∈ V := by
    intro n hn y hy
    refine ⟨?_, ?_⟩
    · show Φ (n * y * n⁻¹) ∈ pCoreOf 2 N
      rw [map_mul, map_mul, map_inv]
      exact pCoreOf_conj_mem (map_mem_normalizer_map Φ hn) hy.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hy.2) (Subgroup.inv_mem _ hn)
  have hnormal : (V.subgroupOf (Subgroup.normalizer (R : Set X))).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hVconj n hn y hy, fun hy => ?_⟩
    have := hVconj n⁻¹ (Subgroup.inv_mem _ hn) _ hy
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 V := by
    have h1 : V.map Φ ≤ pCoreOf 2 N := by
      rintro _ ⟨v, hv, rfl⟩
      exact hv.1
    have h2 : IsPGroup 2 (V.map Φ) := (pCoreOf_isPGroup 2 N).to_le h1
    exact h2.of_equiv (Subgroup.equivMapOfInjective V Φ hΦ).symm
  have hle := le_pCoreOf 2 (inf_le_right : V ≤ Subgroup.normalizer (R : Set X)) hnormal hp
  rw [hcore] at hle
  exact hle ⟨hzQ, hz⟩

end PCore

section Perfect

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H]
  {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}

theorem OutProps.commutator_mem_range (P : OutProps Φ ψ k₀) (a b : H) :
    a * b * a⁻¹ * b⁻¹ ∈ Φ.range := by
  have : Φ.range.Normal := P.range_normal
  obtain ⟨g, s, rfl⟩ := P.gen a
  obtain ⟨h, t, rfl⟩ := P.gen b
  have e1 : ∀ x : antiSp F, ((Φ x : H) : H ⧸ Φ.range) = 1 := fun x =>
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, e1, one_mul]
  group

theorem OutProps.perfectCore_eq_inf_range (P : OutProps Φ ψ k₀) (N : Subgroup H) :
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

end Perfect

section Stable

variable {X : Type*} [Group X]

theorem normalizer_stable {θ : MulAut X} {R : Subgroup X} (hR : ∀ x, θ x ∈ R ↔ x ∈ R) (x : X) :
    θ x ∈ Subgroup.normalizer (R : Set X) ↔ x ∈ Subgroup.normalizer (R : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    have := h (θ g)
    rw [hR, show θ x * θ g * (θ x)⁻¹ = θ (x * g * x⁻¹) by simp, hR] at this
    exact this
  · intro h g
    obtain ⟨g', rfl⟩ := θ.surjective g
    rw [hR, show θ x * θ g' * (θ x)⁻¹ = θ (x * g' * x⁻¹) by simp, hR]
    exact h g'

end Stable

end SpOut2

end CFSG.Quasithin.H13.F431
