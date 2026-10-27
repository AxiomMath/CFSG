module

public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.A5.SzPair

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure CompFacts (T K : Subgroup G) : Prop where
  syl : IsSylowTwoOf (T ⊓ K) K
  center : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1
  inner : ∀ s ∈ T, s ∈ Subgroup.normalizer (K : Set G) →
    ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹
  comm : ∀ x ∈ T ⊓ K, x ^ 2 = 1 → ∀ y ∈ T ⊓ K, x * y = y * x
  two : ∃ x ∈ T ⊓ K, ∃ y ∈ T ⊓ K, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y

structure PairFacts (T K K₁ : Subgroup G) : Prop where
  ne : K ≠ K₁
  comm : ∀ x ∈ K, ∀ y ∈ K₁, x * y = y * x
  swap : ∀ s ∈ T, s ∉ Subgroup.normalizer (K : Set G) → ∀ x, x ∈ K ↔ s * x * s⁻¹ ∈ K₁
  swap₁ : ∀ s ∈ T, s ∉ Subgroup.normalizer (K₁ : Set G) → ∀ x, x ∈ K₁ ↔ s * x * s⁻¹ ∈ K

theorem omegaOne_le (T K : Subgroup G) : omegaOneOf (T ⊓ K) ≤ T ⊓ K :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem conj_mem_of_mem_normalizer {K : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ K) : g * x * g⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem conj_inv_mem_of_mem_normalizer {K : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ K) : g⁻¹ * x * g ∈ K := by
  have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hg) hx
  rwa [inv_inv] at this

namespace CompFacts

variable {T K : Subgroup G}

theorem omegaOne_comm (h : CompFacts T K) {u : G} (hu : u ∈ omegaOneOf (T ⊓ K)) {y : G}
    (hy : y ∈ T ⊓ K) : u * y = y * u := by
  have hle : omegaOneOf (T ⊓ K) ≤ Subgroup.centralizer ({y} : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h.comm x hx.1 hx.2 y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

theorem omegaOne_elemAb (h : CompFacts T K) : IsElemAbelian 2 (omegaOneOf (T ⊓ K)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (h.omegaOne_comm a.2 (omegaOne_le T K b.2))⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    have hc : x * y = y * x := h.omegaOne_comm hx (omegaOne_le T K hy)
    rw [(Commute.mul_pow hc 2), hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

theorem two_lt_card (h : CompFacts T K) [Finite G] : 2 < Nat.card (omegaOneOf (T ⊓ K)) := by
  obtain ⟨x, hx, y, hy, hx2, hy2, hx1, hy1, hxy⟩ := h.two
  have h3 : ({1, x, y} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
  have hsub : ({1, x, y} : Set G) ⊆ (omegaOneOf (T ⊓ K) : Set G) := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, hx2⟩
    · exact Subgroup.subset_closure ⟨hy, hy2⟩
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3] at h4
  have h5 : Nat.card (omegaOneOf (T ⊓ K)) = (omegaOneOf (T ⊓ K) : Set G).ncard :=
    Nat.card_coe_set_eq _
  omega

theorem exists_inner_mem (h : CompFacts T K) [Finite G] (hT : IsPGroup 2 T) {s : G} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ T ⊓ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
  obtain ⟨k, hkK, hk⟩ := h.inner s hs hsN
  have hk' : ∀ x ∈ K, s⁻¹ * x * s = k⁻¹ * x * k := by
    intro x hx
    have := hk _ (conj_inv_mem_of_mem_normalizer hsN hx)
    rw [show s * (s⁻¹ * x * s) * s⁻¹ = x by group] at this
    calc s⁻¹ * x * s = k⁻¹ * (k * (s⁻¹ * x * s) * k⁻¹) * k := by group
      _ = k⁻¹ * x * k := by rw [← this]
  have hkN : k ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hk x hx.2]
      exact ⟨T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs), conj_mem_of_mem_normalizer hsN hx.2⟩
    · intro hx
      have hxK : k * x * k⁻¹ ∈ K := hx.2
      have e := hk' _ hxK
      rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group] at e
      rw [← e]
      exact ⟨T.mul_mem (T.mul_mem (T.inv_mem hs) hx.1) hs, conj_inv_mem_of_mem_normalizer hsN hxK⟩
  obtain ⟨m, hm⟩ := hT ⟨s, hs⟩
  have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hkpow : ∀ j : ℕ, ∀ x ∈ K, s ^ j * x * (s ^ j)⁻¹ = k ^ j * x * (k ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      calc s ^ (j + 1) * x * (s ^ (j + 1))⁻¹ = s ^ j * (s * x * s⁻¹) * (s ^ j)⁻¹ := by
            rw [pow_succ]; group
        _ = k ^ j * (s * x * s⁻¹) * (k ^ j)⁻¹ := ih _ (conj_mem_of_mem_normalizer hsN hx)
        _ = k ^ j * (k * x * k⁻¹) * (k ^ j)⁻¹ := by rw [hk x hx]
        _ = k ^ (j + 1) * x * (k ^ (j + 1))⁻¹ := by rw [pow_succ]; group
  have hk2 : k ^ 2 ^ m = 1 := by
    refine h.center _ (K.pow_mem hkK _) fun y hy => ?_
    have := hkpow (2 ^ m) y hy
    rw [hsm, one_mul, inv_one, mul_one] at this
    calc k ^ 2 ^ m * y = k ^ 2 ^ m * y * (k ^ 2 ^ m)⁻¹ * k ^ 2 ^ m := by group
      _ = y * k ^ 2 ^ m := by rw [← this]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨m, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk2, one_zpow]
  have hP : IsPGroup 2 ↥((T ⊓ K) ⊔ Subgroup.zpowers k) :=
    h.syl.2.1.to_sup_of_normal_left' hkp ((Subgroup.zpowers_le).2 hkN)
  have heq := h.syl.eq_of_le le_sup_left (sup_le inf_le_right ((Subgroup.zpowers_le).2 hkK)) hP
  have hmem : k ∈ (T ⊓ K) ⊔ Subgroup.zpowers k := Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  rw [heq] at hmem
  exact ⟨k, hmem, hk⟩

theorem conj_omegaOne (h : CompFacts T K) [Finite G] (hT : IsPGroup 2 T) {s : G} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) {u : G} (hu : u ∈ omegaOneOf (T ⊓ K)) :
    s * u * s⁻¹ = u := by
  obtain ⟨k, hk, hkK⟩ := h.exists_inner_mem hT hs hsN
  rw [hkK u (omegaOne_le T K hu).2, ← h.omegaOne_comm hu hk]
  group

theorem exists_inner_omegaOne (h : CompFacts T K) [Finite G] (hT : IsPGroup 2 T) {s : G}
    (hs : s ∈ T) (hsN : s ∈ Subgroup.normalizer (K : Set G)) (hs2 : s ^ 2 = 1) :
    ∃ k ∈ omegaOneOf (T ⊓ K), ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
  obtain ⟨k, hk, hkK⟩ := h.exists_inner_mem hT hs hsN
  refine ⟨k, Subgroup.subset_closure ⟨hk, ?_⟩, hkK⟩
  refine h.center _ (K.pow_mem hk.2 2) fun y hy => ?_
  have h1 := hkK y hy
  have h2 := hkK _ (conj_mem_of_mem_normalizer hsN hy)
  have h3 : s * (s * y * s⁻¹) * s⁻¹ = y := by
    calc s * (s * y * s⁻¹) * s⁻¹ = s ^ 2 * y * (s ^ 2)⁻¹ := by rw [pow_two]; group
      _ = y := by rw [hs2]; group
  rw [h3, h1, show k * (k * y * k⁻¹) * k⁻¹ = k ^ 2 * y * (k ^ 2)⁻¹ by rw [pow_two]; group] at h2
  calc k ^ 2 * y = k ^ 2 * y * (k ^ 2)⁻¹ * k ^ 2 := by group
    _ = y * k ^ 2 := by rw [← h2]

end CompFacts

namespace PairFacts

variable {T K K₁ : Subgroup G}

theorem symm (h : PairFacts T K K₁) : PairFacts T K₁ K where
  ne := h.ne.symm
  comm := fun x hx y hy => (h.comm y hy x hx).symm
  swap := h.swap₁
  swap₁ := h.swap

theorem mem_normalizer₁ (h : PairFacts T K K₁) {s : G} (hs : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) : s ∈ Subgroup.normalizer (K₁ : Set G) := by
  by_contra hsN₁
  apply h.ne
  ext x
  rw [h.swap₁ s hs hsN₁ x]
  exact Subgroup.mem_normalizer_iff.mp hsN x

theorem mul_mem_normalizer (h : PairFacts T K K₁) {a b : G} (ha : a ∈ T)
    (haN : a ∉ Subgroup.normalizer (K : Set G)) (hb : b ∈ T)
    (hbN : b ∉ Subgroup.normalizer (K : Set G)) : a * b ∈ Subgroup.normalizer (K : Set G) := by
  have haN₁ : a ∉ Subgroup.normalizer (K₁ : Set G) := fun h' => haN (h.symm.mem_normalizer₁ ha h')
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [h.swap b hb hbN x, h.swap₁ a ha haN₁]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem eq_one_of_mem (h : PairFacts T K K₁) (hK : CompFacts T K) {x : G} (hx : x ∈ K)
    (hx₁ : x ∈ K₁) : x = 1 :=
  hK.center x hx fun y hy => (h.comm y hy x hx₁).symm

theorem comm_of_mem_centralizer (h : PairFacts T K K₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {a : G} (haA : a ∈ A)
    (haN : a ∉ Subgroup.normalizer (K : Set G)) {d : G} (hdA : d ∈ A)
    (hdK : d ∈ Subgroup.centralizer (K : Set G)) {y : G} (hy : y ∈ K₁) : d * y = y * d := by
  have hx : a⁻¹ * y * a ∈ K := by
    rw [h.swap a (hAT haA) haN]
    simpa [mul_assoc] using hy
  have h1 : a⁻¹ * y * a * d = d * (a⁻¹ * y * a) := Subgroup.mem_centralizer_iff.mp hdK _ hx
  have h2 : d * a = a * d := hAc d hdA a haA
  calc d * y = d * a * (a⁻¹ * y * a) * a⁻¹ := by group
    _ = a * (d * (a⁻¹ * y * a)) * a⁻¹ := by rw [h2]; group
    _ = a * (a⁻¹ * y * a * d) * a⁻¹ := by rw [h1]
    _ = y * (a * d * a⁻¹) := by group
    _ = y * d := by rw [← h2]; group

end PairFacts

variable {T K K₁ : Subgroup G}

theorem omegaOne_commute (h : PairFacts T K K₁) (u : ↥(omegaOneOf (T ⊓ K)))
    (w : ↥(omegaOneOf (T ⊓ K₁))) :
    Commute ((omegaOneOf (T ⊓ K)).subtype u) ((omegaOneOf (T ⊓ K₁)).subtype w) :=
  h.comm _ (omegaOne_le T K u.2).2 _ (omegaOne_le T K₁ w.2).2

@[expose] noncomputable def vZero (h : PairFacts T K K₁) : Subgroup G :=
  ((omegaOneOf (T ⊓ K)).subtype.noncommCoprod (omegaOneOf (T ⊓ K₁)).subtype
    (omegaOne_commute h)).range

theorem mem_vZero (h : PairFacts T K K₁) {v : G} :
    v ∈ vZero h ↔ ∃ u ∈ omegaOneOf (T ⊓ K), ∃ w ∈ omegaOneOf (T ⊓ K₁), u * w = v := by
  constructor
  · rintro ⟨⟨u, w⟩, rfl⟩
    exact ⟨u, u.2, w, w.2, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

theorem vZero_le (h : PairFacts T K K₁) : vZero h ≤ T := by
  rintro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_vZero h).1 hv
  exact T.mul_mem (omegaOne_le T K hu).1 (omegaOne_le T K₁ hw).1

theorem vZero_elemAb (h : PairFacts T K K₁) (hK : CompFacts T K) (hK₁ : CompFacts T K₁) :
    IsElemAbelian 2 (vZero h) := by
  have hA := hK.omegaOne_elemAb
  have hB := hK₁.omegaOne_elemAb
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨u, hu, w, hw, hv⟩ := (mem_vZero h).1 a.2
    obtain ⟨u', hu', w', hw', hv'⟩ := (mem_vZero h).1 b.2
    show (a : G) * b = b * a
    rw [← hv, ← hv']
    have h1 : u * u' = u' * u := congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    have h2 : w * w' = w' * w := congrArg Subtype.val (hB.1.is_comm.comm ⟨w, hw⟩ ⟨w', hw'⟩)
    have h3 : w * u' = u' * w := (h.comm _ (omegaOne_le T K hu').2 _ (omegaOne_le T K₁ hw).2).symm
    have h4 : w' * u = u * w' := (h.comm _ (omegaOne_le T K hu).2 _ (omegaOne_le T K₁ hw').2).symm
    calc u * w * (u' * w') = u * (w * u') * w' := by group
      _ = u * (u' * w) * w' := by rw [h3]
      _ = (u * u') * (w * w') := by group
      _ = (u' * u) * (w' * w) := by rw [h1, h2]
      _ = u' * (u * w') * w := by group
      _ = u' * (w' * u) * w := by rw [h4]
      _ = u' * w' * (u * w) := by group
  · intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := (mem_vZero h).1 hv
    have h3 : u * w = w * u := h.comm _ (omegaOne_le T K hu).2 _ (omegaOne_le T K₁ hw).2
    rw [Commute.mul_pow h3 2, hA.2 u hu, hB.2 w hw, one_mul]

theorem mem_centralizer_vZero (h : PairFacts T K K₁) {s : G}
    (h₁ : ∀ u ∈ omegaOneOf (T ⊓ K), s * u * s⁻¹ = u)
    (h₂ : ∀ w ∈ omegaOneOf (T ⊓ K₁), s * w * s⁻¹ = w) :
    s ∈ Subgroup.centralizer (vZero h : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_vZero h).1 hv
  have e1 := h₁ u hu
  have e2 := h₂ w hw
  calc u * w * s = (s * u * s⁻¹) * (s * w * s⁻¹) * s := by rw [e1, e2]
    _ = s * (u * w) := by group

section Counting

variable [Finite G]

theorem card_le_two_mul (h : PairFacts T K K₁) {A : Subgroup G} (hAT : A ≤ T) {a : G}
    (haA : a ∈ A) (haN : a ∉ Subgroup.normalizer (K : Set G)) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set G)) := by
  classical
  let f : ↥A → ↥(A ⊓ Subgroup.normalizer (K : Set G)) × Bool := fun b =>
    if hb : (b : G) ∈ Subgroup.normalizer (K : Set G) then (⟨b, b.2, hb⟩, true)
    else (⟨a * b, A.mul_mem haA b.2, h.mul_mem_normalizer (hAT haA) haN (hAT b.2) hb⟩, false)
  have hf : Function.Injective f := by
    intro b b' hbb
    by_cases hb : (b : G) ∈ Subgroup.normalizer (K : Set G) <;>
      by_cases hb' : (b' : G) ∈ Subgroup.normalizer (K : Set G)
    · simp only [f, hb, hb', dite_true, Prod.mk.injEq] at hbb
      exact Subtype.ext
        (congrArg (fun x : ↥(A ⊓ Subgroup.normalizer (K : Set G)) => (x : G)) hbb.1)
    · simp [f, hb, hb'] at hbb
    · simp [f, hb, hb'] at hbb
    · simp only [f, hb, hb', dite_false, Prod.mk.injEq] at hbb
      exact Subtype.ext (mul_left_cancel
        (congrArg (fun x : ↥(A ⊓ Subgroup.normalizer (K : Set G)) => (x : G)) hbb.1))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

theorem card_inf_normalizer_le (hK : CompFacts T K) (hT : IsPGroup 2 T) {A : Subgroup G}
    (hAT : A ≤ T) (hAe : IsElemAbelian 2 A) :
    Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set G)) ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card (omegaOneOf (T ⊓ K)) := by
  set A₁ := A ⊓ Subgroup.normalizer (K : Set G) with hA₁
  let φ : ↥A₁ →* MulAut ↥K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_right : A₁ ≤ _))
  let ψ : ↥(omegaOneOf (T ⊓ K)) →* MulAut ↥K :=
    MulAut.conj.comp (Subgroup.inclusion ((omegaOne_le T K).trans inf_le_right))
  have hφ : ∀ (b : ↥A₁) (x : ↥K), ((φ b x : ↥K) : G) = b * x * (b : G)⁻¹ := fun _ _ => rfl
  have hψ : ∀ (u : ↥(omegaOneOf (T ⊓ K))) (x : ↥K), ((ψ u x : ↥K) : G) = u * x * (u : G)⁻¹ :=
    fun _ _ => rfl
  have hrange : φ.range ≤ ψ.range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk, hkK⟩ := hK.exists_inner_omegaOne hT (hAT b.2.1) b.2.2 (hAe.2 _ b.2.1)
    refine ⟨⟨k, hk⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hψ, hφ, hkK x x.2]
  have hcent : ∀ b : ↥φ.ker, ((b : ↥A₁) : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp b.2) ⟨x, hx⟩)
    rw [hφ] at h1
    calc x * ((b : ↥A₁) : G) = ((b : ↥A₁) : G) * x * ((b : ↥A₁) : G)⁻¹ * (b : ↥A₁) := by
          rw [h1]; rfl
      _ = (b : ↥A₁) * x := by group
  have hker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun b => ⟨(b : ↥A₁), Subgroup.mem_inf.mpr ⟨(b : ↥A₁).2.1, hcent b⟩⟩) ?_
    intro b b' hbb
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : ↥(A ⊓ Subgroup.centralizer (K : Set G)) => (x : G)) hbb))
  have hcard : Nat.card ↥A₁ = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hψc : Nat.card ψ.range ≤ Nat.card (omegaOneOf (T ⊓ K)) :=
    Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective
  rw [hcard]
  exact Nat.mul_le_mul hker ((Subgroup.card_le_of_le hrange).trans hψc)

omit [Finite G] in
theorem exists_big (h : PairFacts T K K₁) (hK : CompFacts T K) (hK₁ : CompFacts T K₁)
    {A : Subgroup G} (hAT : A ≤ T) (hAe : IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (haN : a ∉ Subgroup.normalizer (K : Set G)) :
    ∃ B : Subgroup G, B ≤ T ∧ IsElemAbelian 2 B ∧
      Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card (omegaOneOf (T ⊓ K)) *
        Nat.card (omegaOneOf (T ⊓ K₁)) ≤ Nat.card B := by
  set D := A ⊓ Subgroup.centralizer (K : Set G) with hD
  set U := omegaOneOf (T ⊓ K) with hU
  set W := omegaOneOf (T ⊓ K₁) with hW
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hUe := hK.omegaOne_elemAb
  have hWe := hK₁.omegaOne_elemAb
  have hUK : ∀ u ∈ U, u ∈ K := fun u hu => (omegaOne_le T K hu).2
  have hWK : ∀ w ∈ W, w ∈ K₁ := fun w hw => (omegaOne_le T K₁ hw).2
  have hDU : ∀ (d : ↥D) (u : ↥U), Commute (D.subtype d) (U.subtype u) := fun d u =>
    (Subgroup.mem_centralizer_iff.mp d.2.2 _ (hUK _ u.2)).symm
  have hDK₁ : ∀ d ∈ D, ∀ y ∈ K₁, d * y = y * d := fun d hd y hy =>
    h.comm_of_mem_centralizer hAT hAc haA haN hd.1 hd.2 hy
  have hDW : ∀ d ∈ D, ∀ w ∈ W, d * w = w * d := fun d hd w hw => hDK₁ d hd w (hWK w hw)
  let f₁ : ↥D × ↥U →* G := D.subtype.noncommCoprod U.subtype hDU
  have hf₁ : ∀ p : ↥D × ↥U, f₁ p = (p.1 : G) * p.2 := fun _ => rfl
  have hf₁W : ∀ (p : ↥D × ↥U) (w : ↥W), Commute (f₁ p) (W.subtype w) := by
    intro p w
    show f₁ p * w = w * f₁ p
    rw [hf₁]
    have h1 := hDW _ p.1.2 _ w.2
    have h2 := h.comm _ (hUK _ p.2.2) _ (hWK _ w.2)
    calc (p.1 : G) * p.2 * w = p.1 * (p.2 * w) := by group
      _ = p.1 * (w * p.2) := by rw [h2]
      _ = (p.1 * w) * p.2 := by group
      _ = (w * p.1) * p.2 := by rw [h1]
      _ = w * (p.1 * p.2) := by group
  let f : (↥D × ↥U) × ↥W →* G := f₁.noncommCoprod W.subtype hf₁W
  have hf : ∀ q : (↥D × ↥U) × ↥W, f q = (q.1.1 : G) * q.1.2 * q.2 := fun _ => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, u⟩, w⟩ h1
    rw [hf] at h1
    have hd : (d : G) = (u * w : G)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact h1
    have hu1 : (u : G) = 1 := by
      refine hK.center _ (hUK _ u.2) fun y hy => ?_
      have hdy : y * (d : G) = d * y := Subgroup.mem_centralizer_iff.mp d.2.2 y hy
      rw [hd] at hdy
      have huw : ((u : G) * w) * y = y * ((u : G) * w) := by
        calc ((u : G) * w) * y = ((u : G) * w) * (y * ((u : G) * w)⁻¹) * ((u : G) * w) := by
              group
          _ = ((u : G) * w) * (((u : G) * w)⁻¹ * y) * ((u : G) * w) := by rw [hdy]
          _ = y * ((u : G) * w) := by group
      have hwy : (w : G) * y = y * w := (h.comm y hy _ (hWK _ w.2)).symm
      calc (u : G) * y = (u : G) * (y * w) * (w : G)⁻¹ := by group
        _ = (u : G) * (w * y) * (w : G)⁻¹ := by rw [hwy]
        _ = ((u : G) * w) * y * (w : G)⁻¹ := by group
        _ = y * ((u : G) * w) * (w : G)⁻¹ := by rw [huw]
        _ = y * u := by group
    have hw1 : (w : G) = 1 := by
      refine hK₁.center _ (hWK _ w.2) fun y hy => ?_
      have hdy := hDK₁ _ d.2 _ hy
      rw [hd, hu1, one_mul] at hdy
      calc (w : G) * y = (w : G) * (y * (w : G)⁻¹) * w := by group
        _ = (w : G) * ((w : G)⁻¹ * y) * w := by rw [hdy]
        _ = y * w := by group
    have hd1 : (d : G) = 1 := by rw [hd, hu1, hw1, mul_one, inv_one]
    ext <;> simp [hd1, hu1, hw1]
  have hcomm : ∀ q r : (↥D × ↥U) × ↥W, q * r = r * q := by
    rintro ⟨⟨d, u⟩, w⟩ ⟨⟨d', u'⟩, w'⟩
    have h1 : d * d' = d' * d := Subtype.ext (hAc _ d.2.1 _ d'.2.1)
    have h2 : u * u' = u' * u := hUe.1.is_comm.comm u u'
    have h3 : w * w' = w' * w := hWe.1.is_comm.comm w w'
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact h1
    · exact h2
    · exact h3
  have hsq : ∀ q : (↥D × ↥U) × ↥W, q ^ 2 = 1 := by
    rintro ⟨⟨d, u⟩, w⟩
    have h1 : d ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ d.2.1)
    have h2 : u ^ 2 = 1 := Subtype.ext (by simpa using hUe.2 _ u.2)
    have h3 : w ^ 2 = 1 := Subtype.ext (by simpa using hWe.2 _ w.2)
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact h1
    · exact h2
    · exact h3
  refine ⟨f.range, ?_, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨⟨⟨d, u⟩, w⟩, rfl⟩
    rw [hf]
    exact T.mul_mem (T.mul_mem (hAT d.2.1) (omegaOne_le T K u.2).1) (omegaOne_le T K₁ w.2).1
  · obtain ⟨q, hq⟩ := x.2
    obtain ⟨r, hr⟩ := y.2
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hq, ← hr, ← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨q, rfl⟩
    rw [← map_pow, hsq, map_one]
  · rw [← Nat.card_congr (f.ofInjective hfinj).toEquiv, Nat.card_prod, Nat.card_prod]

theorem le_normalizer (h : PairFacts T K K₁) (hK : CompFacts T K) (hK₁ : CompFacts T K₁)
    (hT : IsPGroup 2 T) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  intro a haA
  by_contra haN
  have h1 := card_le_two_mul h hA.1 haA haN
  have h2 := card_inf_normalizer_le hK hT hA.1 hA.2.1
  obtain ⟨B, hBT, hBe, hB⟩ := exists_big h hK hK₁ hA.1 hA.2.1 haA haN
  have h3 := hA.2.2 B hBT hBe
  have h4 := hK₁.two_lt_card
  have h5 : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  have h6 : 0 < Nat.card (omegaOneOf (T ⊓ K)) := Nat.card_pos
  have h7 := Nat.mul_le_mul_left
    (Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card (omegaOneOf (T ⊓ K))) h4
  have h8 := Nat.mul_pos h5 h6
  generalize Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card (omegaOneOf (T ⊓ K)) =
    x at *
  generalize x * Nat.card (omegaOneOf (T ⊓ K₁)) = y at *
  omega

theorem thompsonJ_le (h : PairFacts T K K₁) (hK : CompFacts T K) (hK₁ : CompFacts T K₁)
    (hT : IsPGroup 2 T) : thompsonJ T ≤ T ⊓ Subgroup.centralizer (vZero h : Set G) := by
  refine iSup₂_le fun A hA => le_inf hA.1 fun s hs => ?_
  have hsN := le_normalizer h hK hK₁ hT hA hs
  have hsN₁ := le_normalizer h.symm hK₁ hK hT hA hs
  exact mem_centralizer_vZero h (fun u hu => hK.conj_omegaOne hT (hA.1 hs) hsN hu)
    (fun w hw => hK₁.conj_omegaOne hT (hA.1 hs) hsN₁ hw)

end Counting

theorem conj_mem_omegaOne {P : Subgroup G} {g u : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    (hu : u ∈ omegaOneOf P) : g * u * g⁻¹ ∈ omegaOneOf P := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨conj_mem_of_mem_normalizer hg hx.1, ?_⟩
    rw [show (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, hx.2]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

section Baum

variable [Finite G]

theorem conj_mem_centralizer_vZero (h : PairFacts T K K₁) (hK : CompFacts T K)
    (hK₁ : CompFacts T K₁) (hT : IsPGroup 2 T) {b : G} (hbK : b ∈ K)
    (hbN : b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) {c : G}
    (hc : c ∈ T ⊓ Subgroup.centralizer (vZero h : Set G)) :
    b * c * b⁻¹ ∈ T ⊓ Subgroup.centralizer (vZero h : Set G) := by
  obtain ⟨hcT, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := by
    by_contra hcN
    obtain ⟨x, hx, -, -, hx2, -, hx1, -, -⟩ := hK.two
    have hxV : x ∈ vZero h :=
      (mem_vZero h).2 ⟨x, Subgroup.subset_closure ⟨hx, hx2⟩, 1, Subgroup.one_mem _, mul_one x⟩
    have h1 : c * x * c⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_iff.mp hcC x hxV]
      group
    have h2 : c * x * c⁻¹ ∈ K₁ := (h.swap c hcT hcN x).mp hx.2
    rw [h1] at h2
    exact hx1 (h.eq_one_of_mem hK hx.2 h2)
  have hcN₁ := h.mem_normalizer₁ hcT hcN
  obtain ⟨k, hk, hkK⟩ := hK.exists_inner_mem hT hcT hcN
  obtain ⟨k₁, hk₁, hk₁K⟩ := hK₁.exists_inner_mem hT hcT hcN₁
  set d := (k * k₁)⁻¹ * c with hd
  have hdK : d ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have e1 := hkK x hx
    have e2 : k₁ * x = x * k₁ := (h.comm x hx k₁ hk₁.2).symm
    have e3 : x * k₁⁻¹ = k₁⁻¹ * x := by
      calc x * k₁⁻¹ = k₁⁻¹ * (k₁ * x) * k₁⁻¹ := by group
        _ = k₁⁻¹ * (x * k₁) * k₁⁻¹ := by rw [e2]
        _ = k₁⁻¹ * x := by group
    calc x * d = x * k₁⁻¹ * k⁻¹ * c := by rw [hd, mul_inv_rev]; group
      _ = k₁⁻¹ * x * k⁻¹ * c := by rw [e3]
      _ = k₁⁻¹ * k⁻¹ * (k * x * k⁻¹) * c := by group
      _ = k₁⁻¹ * k⁻¹ * (c * x * c⁻¹) * c := by rw [e1]
      _ = d * x := by rw [hd, mul_inv_rev]; group
  have hbk₁ : b * k₁ = k₁ * b := h.comm b hbK k₁ hk₁.2
  have hbd : b * d = d * b := Subgroup.mem_centralizer_iff.mp hdK b hbK
  have hceq : b * c * b⁻¹ = (b * k * b⁻¹) * k₁ * d := by
    have hc' : c = k * k₁ * d := by rw [hd]; group
    have e1 : b * k₁ * b⁻¹ = k₁ := by rw [hbk₁]; group
    have e2 : b * d * b⁻¹ = d := by rw [hbd]; group
    rw [hc']
    calc b * (k * k₁ * d) * b⁻¹ = (b * k * b⁻¹) * (b * k₁ * b⁻¹) * (b * d * b⁻¹) := by group
      _ = (b * k * b⁻¹) * k₁ * d := by rw [e1, e2]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [hceq]
    have hbk : b * k * b⁻¹ ∈ T ⊓ K := conj_mem_of_mem_normalizer hbN hk
    have hdT : d ∈ T := by
      rw [hd]
      exact T.mul_mem (T.inv_mem (T.mul_mem hk.1 hk₁.1)) hcT
    exact T.mul_mem (T.mul_mem hbk.1 hk₁.1) hdT
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := (mem_vZero h).1 hv
    have hbw : b⁻¹ * w = w * b⁻¹ := h.comm _ (K.inv_mem hbK) _ (omegaOne_le T K₁ hw).2
    have hu' : b⁻¹ * u * b ∈ omegaOneOf (T ⊓ K) := by
      have := conj_mem_omegaOne (Subgroup.inv_mem _ hbN) hu
      rwa [inv_inv] at this
    have hv' : b⁻¹ * (u * w) * b ∈ vZero h := by
      refine (mem_vZero h).2 ⟨b⁻¹ * u * b, hu', w, hw, ?_⟩
      calc b⁻¹ * u * b * w = b⁻¹ * u * (b * w * b⁻¹) * b := by group
        _ = b⁻¹ * u * w * b := by
          rw [show b * w * b⁻¹ = w by
            calc b * w * b⁻¹ = b * (w * b⁻¹) := by group
              _ = b * (b⁻¹ * w) := by rw [hbw]
              _ = w := by group]
        _ = b⁻¹ * (u * w) * b := by group
    have e := Subgroup.mem_centralizer_iff.mp hcC _ hv'
    calc u * w * (b * c * b⁻¹) = b * (b⁻¹ * (u * w) * b * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * (u * w) * b)) * b⁻¹ := by rw [e]
      _ = b * c * b⁻¹ * (u * w) := by group

theorem mem_normalizer_centralizer_vZero (h : PairFacts T K K₁) (hK : CompFacts T K)
    (hK₁ : CompFacts T K₁) (hT : IsPGroup 2 T) {b : G} (hbK : b ∈ K)
    (hbN : b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    b ∈ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (vZero h : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_centralizer_vZero h hK hK₁ hT hbK hbN
  · intro hc
    have := conj_mem_centralizer_vZero h hK hK₁ hT (K.inv_mem hbK) (Subgroup.inv_mem _ hbN) hc
    simpa [mul_assoc] using this

theorem mem_normalizer_baum (h : PairFacts T K K₁) (hK : CompFacts T K) (hK₁ : CompFacts T K₁)
    (hT : IsPGroup 2 T) {b : G} (hbK : b ∈ K)
    (hbN : b ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    b ∈ Subgroup.normalizer (baum T : Set G) := by
  rw [baum_eq_baum_centralizer (vZero_elemAb h hK hK₁) (vZero_le h) (thompsonJ_le h hK hK₁ hT)]
  exact normalizer_le_normalizer_baum _ (mem_normalizer_centralizer_vZero h hK hK₁ hT hbK hbN)

end Baum

end CFSG.Quasithin.H13.A5.SzPair
