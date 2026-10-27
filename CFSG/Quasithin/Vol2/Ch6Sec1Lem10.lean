module

public import CFSG.Quasithin.Vol2.Ch6Hyperplane
public import CFSG.Quasithin.Background.E6Thirteen
public import CFSG.Quasithin.Vol2.Ch6Offender

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section NatData

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ}

namespace NatL2Data

variable (D : NatL2Data L V n)

@[expose] def addSub (U : Subgroup G) : AddSubgroup (Fin 2 → D.K) where
  carrier := {y | ((D.E.symm (Multiplicative.ofAdd y) : ↥V) : G) ∈ U}
  zero_mem' := by
    show ((D.E.symm (Multiplicative.ofAdd 0) : ↥V) : G) ∈ U
    rw [ofAdd_zero, map_one, OneMemClass.coe_one]
    exact U.one_mem
  add_mem' := by
    intro y y' hy hy'
    show ((D.E.symm (Multiplicative.ofAdd (y + y')) : ↥V) : G) ∈ U
    rw [ofAdd_add, map_mul, Subgroup.coe_mul]
    exact U.mul_mem hy hy'
  neg_mem' := by
    intro y hy
    show ((D.E.symm (Multiplicative.ofAdd (-y)) : ↥V) : G) ∈ U
    rw [ofAdd_neg, map_inv, InvMemClass.coe_inv]
    exact U.inv_mem hy

theorem mem_addSub {U : Subgroup G} {y : Fin 2 → D.K} :
    y ∈ D.addSub U ↔ ((D.E.symm (Multiplicative.ofAdd y) : ↥V) : G) ∈ U := Iff.rfl

theorem toAdd_mem_addSub {U : Subgroup G} (x : ↥V) :
    Multiplicative.toAdd (D.E x) ∈ D.addSub U ↔ (x : G) ∈ U := by
  rw [mem_addSub, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem card_addSub {U : Subgroup G} (hUV : U ≤ V) : Nat.card (D.addSub U) = Nat.card U :=
  Nat.card_congr
    { toFun := fun y => ⟨_, y.2⟩
      invFun := fun x => ⟨Multiplicative.toAdd (D.E ⟨x, hUV x.2⟩), (D.toAdd_mem_addSub _).mpr x.2⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

theorem index_addSub [Finite G] {U : Subgroup G} (hUV : U ≤ V) :
    (D.addSub U).index = U.relIndex V := by
  have h1 := AddSubgroup.card_mul_index (D.addSub U)
  have h2 := Subgroup.card_mul_index (U.subgroupOf V)
  have h3 : Nat.card (Fin 2 → D.K) = Nat.card V :=
    (Nat.card_congr (D.E.toEquiv.trans Multiplicative.toAdd)).symm
  have h4 : Nat.card (U.subgroupOf V) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  rw [D.card_addSub hUV] at h1
  rw [h4] at h2
  have hpos : 0 < Nat.card U := Nat.card_pos
  have : Nat.card U * (D.addSub U).index = Nat.card U * U.relIndex V := by
    rw [h1, h3, ← h2]
    rfl
  exact Nat.eq_of_mul_eq_mul_left hpos this

@[expose] def subOf (H : AddSubgroup (Fin 2 → D.K)) : Subgroup G :=
  ((AddSubgroup.toSubgroup H).comap D.E.toMonoidHom).map V.subtype

theorem mem_subOf {H : AddSubgroup (Fin 2 → D.K)} {x : G} :
    x ∈ D.subOf H ↔ ∃ hx : x ∈ V, Multiplicative.toAdd (D.E ⟨x, hx⟩) ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxH⟩
    exact ⟨⟨x, hx⟩, hxH, rfl⟩

theorem subOf_le (H : AddSubgroup (Fin 2 → D.K)) : D.subOf H ≤ V :=
  fun _ hx => (D.mem_subOf.mp hx).1

theorem addSub_subOf (H : AddSubgroup (Fin 2 → D.K)) : D.addSub (D.subOf H) = H := by
  ext y
  rw [mem_addSub, mem_subOf]
  constructor
  · rintro ⟨hx, hxH⟩
    simpa using hxH
  · intro hy
    exact ⟨(D.E.symm (Multiplicative.ofAdd y)).2, by simpa using hy⟩

theorem relIndex_subOf [Finite G] (H : AddSubgroup (Fin 2 → D.K)) :
    (D.subOf H).relIndex V = H.index := by
  rw [← D.index_addSub (D.subOf_le H), D.addSub_subOf]

end NatL2Data

end NatData

theorem le_rkIdx_of_card_le {W : Type*} [Group W] [Finite W] {k m : ℕ}
    (hW : Nat.card W = 2 ^ k) (S : Subgroup W) (hS : Nat.card S * 2 ^ m ≤ 2 ^ k) :
    m ≤ rkIdx S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.index_mul_card S
  rw [hW] at h1
  have hdvd : S.index ∣ 2 ^ k := Dvd.intro _ h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h2 : 2 ^ m ≤ 2 ^ j := by
    rw [hj] at h1
    have : Nat.card S * 2 ^ m ≤ Nat.card S * 2 ^ j := by
      calc Nat.card S * 2 ^ m ≤ 2 ^ k := hS
        _ = 2 ^ j * Nat.card S := h1.symm
        _ = Nat.card S * 2 ^ j := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hpos
  unfold rkIdx
  rw [hj, padicValNat.prime_pow]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem rkIdx_eq_of_card {W : Type*} [Group W] [Finite W] {k m : ℕ}
    (hW : Nat.card W = 2 ^ k) (S : Subgroup W) (hS : Nat.card S * 2 ^ m = 2 ^ k) :
    rkIdx S = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.index_mul_card S
  rw [hW, ← hS] at h1
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h2 : S.index = 2 ^ m := by
    have : Nat.card S * S.index = Nat.card S * 2 ^ m := by rw [mul_comm, h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  unfold rkIdx
  rw [h2, padicValNat.prime_pow]

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem card_mul_relIndex_of_le {U V : Subgroup G} (hUV : U ≤ V) :
    Nat.card U * U.relIndex V = Nat.card V := by
  have h := Subgroup.card_mul_index (U.subgroupOf V)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv] at h

namespace Hyp611Nat

theorem exists_hyperplane_normalized (h : Hyp611Nat G T M L V n) :
    ∃ U₀ : Subgroup G, U₀ ≤ V ∧ U₀.relIndex V = 2 ∧ T ≤ Subgroup.normalizer (U₀ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := h.data with hD
  have hTN : ∀ t : ↥T, (t : G) ∈ Subgroup.normalizer (V : Set G) :=
    fun t => h.toHyp611.T_le_normalizer t.2
  let X := {H : AddSubgroup (Fin 2 → D.K) // H.index = 2}
  have : Finite (AddSubgroup (Fin 2 → D.K)) :=
    Finite.of_injective (fun H : AddSubgroup (Fin 2 → D.K) => (H : Set (Fin 2 → D.K)))
      SetLike.coe_injective
  let f : ↥T → (Fin 2 → D.K) ≃+ (Fin 2 → D.K) := fun t => D.conj ⟨t, hTN t⟩
  have hf1 : ∀ w, f 1 w = w := fun w =>
    D.conj_eq_of_mem_centralizer ⟨((1 : ↥T) : G), hTN 1⟩ (Subgroup.one_mem _) w
  have hfmul : ∀ s t w, f (s * t) w = f s (f t w) := fun s t w =>
    D.conj_mul ⟨(s : G), hTN s⟩ ⟨(t : G), hTN t⟩ w
  have hidx : ∀ (t : ↥T) (H : AddSubgroup (Fin 2 → D.K)),
      (H.map (f t).toAddMonoidHom).index = H.index := fun t H =>
    AddSubgroup.index_map_of_bijective (f := (f t).toAddMonoidHom) (f t).bijective H
  let act : MulAction ↥T X :=
    { smul := fun t H => ⟨H.1.map (f t).toAddMonoidHom, (hidx t H.1).trans H.2⟩
      one_smul := fun H => by
        apply Subtype.ext
        ext w
        change w ∈ H.1.map (f 1).toAddMonoidHom ↔ w ∈ H.1
        simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom, hf1]
        exact ⟨fun ⟨z, hz, e⟩ => e ▸ hz, fun hw => ⟨w, hw, rfl⟩⟩
      mul_smul := fun s t H => by
        apply Subtype.ext
        ext w
        change w ∈ H.1.map (f (s * t)).toAddMonoidHom ↔
          w ∈ (H.1.map (f t).toAddMonoidHom).map (f s).toAddMonoidHom
        simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom, hfmul]
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨f t z, ⟨z, hz, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨z, hz, rfl⟩ }
  have hX : ¬ 2 ∣ Nat.card X := odd_card_hyperplanes h.two_dvd_card_K
  obtain ⟨H₀, hH₀⟩ := h.sylow.1.nonempty_fixed_point_of_prime_not_dvd_card X hX
  have hfix : ∀ t : ↥T, ∀ w, w ∈ H₀.1 ↔ f t w ∈ H₀.1 := by
    intro t w
    have hmap : H₀.1.map (f t).toAddMonoidHom = H₀.1 := congrArg Subtype.val (hH₀ t)
    constructor
    · intro hw
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    · intro hw
      rw [← hmap] at hw
      obtain ⟨z, hz, e⟩ := hw
      have hzw : z = w := (f t).injective e
      rw [← hzw]
      exact hz
  refine ⟨D.subOf H₀.1, D.subOf_le H₀.1, by rw [D.relIndex_subOf, H₀.2], fun t ht => ?_⟩
  have htN := hTN ⟨t, ht⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [D.mem_subOf, D.mem_subOf]
  have key : ∀ (hx : x ∈ V) (hx' : t * x * t⁻¹ ∈ V),
      f ⟨t, ht⟩ (Multiplicative.toAdd (D.E ⟨x, hx⟩)) =
        Multiplicative.toAdd (D.E ⟨t * x * t⁻¹, hx'⟩) := by
    intro hx hx'
    have e : conjAct V ⟨t, htN⟩ ⟨x, hx⟩ = ⟨t * x * t⁻¹, hx'⟩ :=
      Subtype.ext (by rw [conjAct_apply_coe])
    change D.conj ⟨t, htN⟩ _ = _
    rw [D.conj_apply, e]
  constructor
  · rintro ⟨hx, hxH⟩
    have hx' : t * x * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp htN x).mp hx
    refine ⟨hx', ?_⟩
    rw [← key hx hx']
    exact (hfix ⟨t, ht⟩ _).mp hxH
  · rintro ⟨hx', hxH⟩
    have hx : x ∈ V := (Subgroup.mem_normalizer_iff.mp htN x).mpr hx'
    refine ⟨hx, (hfix ⟨t, ht⟩ _).mpr ?_⟩
    rw [key hx hx']
    exact hxH

theorem exists_conj_hyperplane (h : Hyp611Nat G T M L V n) {U U₀ : Subgroup G} (hUV : U ≤ V)
    (hU₀V : U₀ ≤ V) (hU : U.relIndex V = 2) (hU₀ : U₀.relIndex V = 2) :
    ∃ l ∈ L, U = conjSubgroup U₀ l := by
  set D := h.data with hD
  obtain ⟨A, hA⟩ := exists_sl2_hyperplane h.two_dvd_card_K (H := D.addSub U₀) (H' := D.addSub U)
    (by rw [D.index_addSub hU₀V, hU₀]) (by rw [D.index_addSub hUV, hU])
  obtain ⟨l, hl⟩ := D.rho_surjective A
  refine ⟨l, l.2, ?_⟩
  have hlN : (l : G) ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer l.2
  have key : ∀ (x : G) (hx : x ∈ V) (hx' : (l : G) * x * (l : G)⁻¹ ∈ V),
      (A : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd (D.E ⟨x, hx⟩)) =
        Multiplicative.toAdd (D.E ⟨(l : G) * x * (l : G)⁻¹, hx'⟩) := by
    intro x hx hx'
    have e : conjAct V ⟨l, hlN⟩ ⟨x, hx⟩ = ⟨(l : G) * x * (l : G)⁻¹, hx'⟩ :=
      Subtype.ext (by rw [conjAct_apply_coe])
    rw [← hl, ← D.conj_eq_rho, D.conj_apply, e]
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hx
    have hxV := hUV hx
    have hx' : (l : G) * x * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlN x).mp hxV
    have h1 := (hA (Multiplicative.toAdd (D.E ⟨x, hxV⟩))).mp ((D.toAdd_mem_addSub _).mpr hx)
    rw [key x hxV hx', D.toAdd_mem_addSub] at h1
    exact h1
  · intro hx
    have hx' : (l : G) * x * (l : G)⁻¹ ∈ V := hU₀V hx
    have hxV : x ∈ V := (Subgroup.mem_normalizer_iff.mp hlN x).mpr hx'
    refine (D.toAdd_mem_addSub ⟨x, hxV⟩).mp ((hA _).mpr ?_)
    rw [key x hxV hx', D.toAdd_mem_addSub]
    exact hx

omit [Finite G] in
theorem twoPrimeResidual_le_self (X : Subgroup G) : twoPrimeResidual X ≤ X :=
  iInf₂_le X ⟨le_rfl, Subgroup.le_normalizer, by simp⟩

theorem two_le_rParam (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) :
    (2 : ℕ∞) ≤ rParam V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := h.hypE61 h432
  obtain ⟨U₀, hU₀V, hU₀, hTU₀⟩ := h.exists_hyperplane_normalized
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have hU₀card : Nat.card U₀ * 2 = 2 ^ n * 2 ^ n := by
    have := card_mul_relIndex_of_le hU₀V
    rw [hU₀, hVcard] at this
    exact this
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hU₀1 : U₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hU₀card
    nlinarith
  have hCM : M ⊓ Subgroup.centralizer (U₀ : Set G) ≤ M ⊓ Subgroup.centralizer (V : Set G) := by
    rintro m ⟨hmM, hmC⟩
    refine ⟨hmM, ?_⟩
    by_contra hmV
    have hmN : m ∈ Subgroup.normalizer (V : Set G) :=
      (h.normalizer_le hU₀1 hU₀V ⟨hmM, Subgroup.centralizer_le_normalizer _ hmC⟩).2
    have hle := h.data.card_fixed_le_two_pow ⟨m, hmN⟩ (h.normal hmM) hmV
    have hsub : U₀ ≤ V ⊓ Subgroup.centralizer ({m} : Set G) := fun u hu =>
      ⟨hU₀V hu, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hmC u hu).symm⟩
    have := (Subgroup.card_le_of_le hsub).trans hle
    nlinarith
  have hres : twoPrimeResidual (M ⊓ Subgroup.centralizer (U₀ : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := (twoPrimeResidual_le_self _).trans hCM
  have hCU₀M := E6.e6_13 h311 hE hU₀V hU₀1 hres hTU₀
  have hCU₀N : Subgroup.centralizer (U₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun c hc => (h.normalizer_le hU₀1 hU₀V ⟨hCU₀M hc, Subgroup.centralizer_le_normalizer _ hc⟩).2
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hCU⟩ := hU
  have hrel : U.relIndex V ∣ 2 ^ (n + n) := by
    rw [pow_add, ← hVcard]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
  have hm : mQuot V U = j := by
    unfold mQuot
    rw [hj, padicValNat.prime_pow]
  rw [hm]
  by_contra hlt
  push Not at hlt
  have hj2 : j < 2 := by exact_mod_cast hlt
  interval_cases j
  ·
    have hVU : V ≤ U := Subgroup.relIndex_eq_one.mp (by rw [hj]; rfl)
    have hUV' : U = V := le_antisymm hUV hVU
    rw [hUV'] at hCU
    exact hCU (Subgroup.centralizer_le_normalizer _)
  · obtain ⟨l, hlL, hUl⟩ := h.exists_conj_hyperplane hUV hU₀V (by rw [hj]; rfl) hU₀
    apply hCU
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer hlL
    rw [hUl, ← E3.conjSubgroup_centralizer]
    calc conjSubgroup (Subgroup.centralizer (U₀ : Set G)) l ≤
        conjSubgroup (Subgroup.normalizer (V : Set G)) l := E3.conjSubgroup_mono_left l hCU₀N
      _ = Subgroup.normalizer (V : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hlN)

theorem card_ZS (h : Hyp611Nat G T M L V n) : Nat.card (ch6ZS T L V) = 2 ^ n := by
  classical
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi₀
  rw [← h.data.card]
  symm
  refine Nat.card_congr
    { toFun := fun c => ⟨(h.data.E.symm (Multiplicative.ofAdd (c • v)) : G),
        (h.mem_ZS_iff_line hv hle _).mpr ⟨c, by simp⟩⟩
      invFun := fun z => Multiplicative.toAdd (h.data.E ⟨z, z.2.1⟩) i₀ / v i₀
      left_inv := fun c => by
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd, Pi.smul_apply,
          smul_eq_mul]
        rw [mul_div_assoc, div_self hi₀, mul_one]
      right_inv := fun z => by
        obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, z.2.1⟩).mp z.2
        apply Subtype.ext
        simp only
        rw [hc]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_div_assoc, div_self hi₀, mul_one, ← hc]
        simp }

theorem card_fixV_zpowers_le (hV : IsElemAbelian 2 V) (g : Subgroup.normalizer (V : Set G)) :
    Nat.card (fixV (Subgroup.zpowers (convI hV g))) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer ({(g : G)} : Set G)) := by
  refine Nat.card_le_card_of_injective (fun w => ⟨w.1.val, w.1.val_mem, ?_⟩) ?_
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    have h1 := w.2 (convI hV g) (Subgroup.mem_zpowers _)
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    calc (g : G) * w.1.val = ((g : G) * w.1.val * (g : G)⁻¹) * g := by group
      _ = w.1.val * g := by rw [h2]
  · intro w w' hww'
    have h1 := congrArg Subtype.val hww'
    exact Subtype.ext (IntMod.val_injective h1)

theorem mParam_autI (h : Hyp611Nat G T M L V n) (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hLX : L ≤ X) (hXM : X ⊓ Subgroup.normalizer (V : Set G) ≤ M) :
    mParam (autI hV X) = n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : Nat.card (IntMod V hV) = 2 ^ (n + n) := by
    rw [pow_add]
    exact h.natural.card_eq
  have hlow : ∀ t ∈ autI hV X, t ≠ 1 → n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht ht1
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).mp ht
    have hgV : (g : G) ∉ Subgroup.centralizer (V : Set G) := fun hc =>
      ht1 ((convI_eq_one_iff hV g).mpr hc)
    have h1 := (card_fixV_zpowers_le hV g).trans
      (h.data.card_fixed_le_two_pow g (h.normal (hXM ⟨hgX, g.2⟩)) hgV)
    refine le_rkIdx_of_card_le hW _ ?_
    rw [pow_add]
    exact Nat.mul_le_mul_right _ h1
  obtain ⟨⟨A, hA⟩, hA1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.rhoTL_ne_bot
  have hA1' : A ≠ 1 := fun h0 => hA1 (Subtype.ext h0)
  obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hA
  have hℓTL : (ℓ : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hℓ
  set m : Subgroup.normalizer (V : Set G) := ⟨ℓ, h.data.le_normalizer ℓ.2⟩ with hm
  set t₀ := convI hV m with ht₀
  have ht₀X : t₀ ∈ autI hV X := convI_mem_autI hV (hLX ℓ.2) _
  have ht₀1 : t₀ ≠ 1 := by
    intro h0
    apply hA1'
    have hc := (convI_eq_one_iff hV m).mp h0
    exact (h.data.mem_ker_rho_iff ℓ).mpr hc
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hAv : h.data.rho ℓ ∈ sl2Stab v := hle (Subgroup.mem_map.mpr ⟨ℓ, hℓ, rfl⟩)
  have hA2 : h.data.rho ℓ ^ 2 = 1 := by
    obtain ⟨B, hB⟩ := exists_sl2_mulVec_single v hv
    obtain ⟨b, hb⟩ := (mem_sl2Stab_iff hB _).mp hAv
    rw [hb]
    have hX2 : sl2X b * sl2X b = (1 : Matrix.SpecialLinearGroup (Fin 2) h.data.K) := by
      have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      change !![1, b; 0, 1] * !![1, b; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) h.data.K)
      rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      simp [CharTwo.add_self_eq_zero]
    rw [pow_two, show B * sl2X b * B⁻¹ * (B * sl2X b * B⁻¹) = B * (sl2X b * sl2X b) * B⁻¹ by
      group, hX2, mul_one, mul_inv_cancel]
  have ht₀2 : t₀ ^ 2 = 1 := by
    rw [ht₀, ← map_pow]
    apply (convI_eq_one_iff hV _).mpr
    have : ℓ ^ 2 ∈ h.data.rho.ker := by rw [MonoidHom.mem_ker, map_pow, hA2]
    have hc := (h.data.mem_ker_rho_iff (ℓ ^ 2)).mp this
    simpa [hm] using hc
  have hord : orderOf t₀ = 2 := orderOf_eq_prime ht₀2 ht₀1
  have hcard : Nat.card (fixV (Subgroup.zpowers t₀)) = 2 ^ n := by
    apply le_antisymm
    · exact (card_fixV_zpowers_le hV m).trans
        (h.data.card_fixed_le_two_pow m (h.normal (h.L_le ℓ.2))
          fun hc => ht₀1 ((convI_eq_one_iff hV m).mpr hc))
    · rw [← h.card_ZS]
      refine Nat.card_le_card_of_injective (fun z => ⟨IntMod.mk hV ⟨z, z.2.1⟩, ?_⟩) ?_
      · intro x hx
        have hstab : Subgroup.zpowers t₀ ≤
            MulAction.stabilizer (MulAut (IntMod V hV)) (IntMod.mk hV ⟨z, z.2.1⟩) := by
          rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
          apply IntMod.val_injective
          change (convI hV m (IntMod.mk hV ⟨z, z.2.1⟩)).val = (z : G)
          rw [convI_apply_val]
          have hc := Subgroup.mem_centralizer_iff.mp z.2.2 (ℓ : G) hℓTL
          change (ℓ : G) * z * (ℓ : G)⁻¹ = z
          rw [hc]
          group
        exact hstab hx
      · intro z z' hzz'
        apply Subtype.ext
        have := congrArg (fun w => IntMod.val (Subtype.val w)) hzz'
        exact this
  have hrk : rkIdx (fixV (Subgroup.zpowers t₀)) = n :=
    rkIdx_eq_of_card hW _ (by rw [hcard, pow_add])
  apply le_antisymm
  ·
    have hzp : IsPGroup 2 (Subgroup.zpowers t₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hne : Subgroup.zpowers t₀ ≠ ⊥ := fun h0 => ht₀1 (Subgroup.zpowers_eq_bot.mp h0)
    rw [← hrk]
    exact mParam_le_rkIdx_fixV (Subgroup.zpowers_le.mpr ht₀X) hzp hne
  ·
    unfold mParam
    split_ifs with hev
    · refine le_csInf ⟨_, t₀, ht₀X, hord, rfl⟩ ?_
      rintro k ⟨t, ht, hto, rfl⟩
      exact hlow t ht (fun h1 => by rw [h1, orderOf_one] at hto; exact absurd hto (by norm_num))
    · unfold rk
      rw [hW, padicValNat.prime_pow]
      omega

theorem mQuot_conj_eq (h : Hyp611Nat G T M L V n) (hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n)
    {g : G} (hgN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G))
    (hgC : ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G)) :
    mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.toHyp611.isElemAbelian
  set P := conjSubgroup V g with hP
  have hPe : IsElemAbelian 2 P := E3.isElemAbelian_conjSubgroup hV g
  have hPcard : Nat.card P = 2 ^ (n + n) := by
    rw [hP, E3.card_conjSubgroup, pow_add]
    exact h.natural.card_eq
  have hrel : (P ⊓ Subgroup.centralizer (V : Set G)).relIndex P ∣ 2 ^ (n + n) := by
    rw [← hPcard]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
  have hm : mQuot P (P ⊓ Subgroup.centralizer (V : Set G)) = j := by
    unfold mQuot
    rw [hj, padicValNat.prime_pow]
  rw [hm]
  apply le_antisymm
  ·
    have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
      E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
        h.toHyp611.T_le_normalizer le_top
    obtain ⟨y, hyN, hyT⟩ := exists_conj_le_of_isSylowTwoOf hTsyl hgN
      (B2F.isPGroup_of_isElemAbelian hPe)
    set A := cjSub y P with hA
    have hAe : IsElemAbelian 2 A := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
      · have ha := mem_cjSub.mp a.2
        have hb := mem_cjSub.mp b.2
        have hab := B2F.isElemAbelian_comm hPe ha hb
        calc (a : G) * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [hab]
          _ = b * a := by group
      · have h2 := hPe.2 _ (mem_cjSub.mp ha)
        rw [pow_two] at h2 ⊢
        calc a * a = y * ((y⁻¹ * a * y) * (y⁻¹ * a * y)) * y⁻¹ := by group
          _ = 1 := by rw [h2]; group
    have hbound := h.card_le_two_pow_mul hyT hAe
    have hcardA : Nat.card A = Nat.card P := by
      rw [hA]
      exact Subgroup.card_map_of_injective (MulAut.conj y).injective
    have hcardAC : Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) := by
      refine Nat.card_le_card_of_injective (fun x => ⟨y⁻¹ * x * y, mem_cjSub.mp x.2.1, ?_⟩) ?_
      · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        have hw' : y * w * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
        have hc := Subgroup.mem_centralizer_iff.mp x.2.2 _ hw'
        calc w * (y⁻¹ * x * y) = y⁻¹ * ((y * w * y⁻¹) * x) * y := by group
          _ = y⁻¹ * (x * (y * w * y⁻¹)) * y := by rw [hc]
          _ = y⁻¹ * x * y * w := by group
      · intro x x' hxx'
        apply Subtype.ext
        have h1 := congrArg Subtype.val hxx'
        simp only at h1
        have h2 := congrArg (fun z => y * z * y⁻¹) h1
        simpa [mul_assoc] using h2
    have h1 := card_mul_relIndex_of_le (inf_le_left : P ⊓ Subgroup.centralizer (V : Set G) ≤ P)
    rw [hj] at h1
    have hpos : 0 < Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
    have h2 : Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ j ≤
        Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n := by
      calc Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ j = Nat.card P := h1
        _ = Nat.card A := hcardA.symm
        _ ≤ 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := hbound
        _ ≤ 2 ^ n * Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) :=
            Nat.mul_le_mul_left _ hcardAC
        _ = Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n := mul_comm _ _
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_left h2 hpos)
  ·
    by_contra hlt
    push Not at hlt
    have hB : P ⊓ Subgroup.centralizer (V : Set G) ≤ P ⊓ Subgroup.normalizer (V : Set G) :=
      inf_le_inf_left P (Subgroup.centralizer_le_normalizer _)
    have hlt' : mQuot P (P ⊓ Subgroup.centralizer (V : Set G)) < sParam hV := by
      rw [hm, hs hV]
      exact hlt
    have he := e3_7 hV hB hlt'
    apply hgC
    rw [← Subgroup.le_centralizer_iff]
    have hVB : V ≤ V ⊓ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (V : Set G) :
        Subgroup G) : Set G) :=
      le_inf le_rfl fun v hv => Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp hb.2 v hv).symm
    rw [he] at hVB
    exact hVB.trans inf_le_right

end Hyp611Nat

theorem stmt6_1_10 (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (hE63 : Ch6InE63) :
    Stmt6_1_10 := by
  intro G _ _ T M L V n h
  have hE := h.hypE61 h432
  have hm : ∀ hV : IsElemAbelian 2 V, mParam (autI hV M) = n := fun hV =>
    h.mParam_autI hV h.L_le inf_le_left
  have hmtop : ∀ hV : IsElemAbelian 2 V, mParam (autI hV ⊤) = n := fun hV =>
    h.mParam_autI hV le_top (inf_le_right.trans hE.normalizer_le)
  have hr : (n : ℕ∞) ≤ rParam V := by
    rcases eq_or_lt_of_le h.two_le with hn | hn
    · subst hn
      exact_mod_cast h.two_le_rParam h311 h432
    · have := (hE63 G T M V hE h.toHyp611.isElemAbelian
        (by rw [hm]; exact hn)).1
      rwa [hm] at this
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV => by
    unfold sParam
    rw [hmtop hV, min_eq_right hr]
    rfl
  exact ⟨hr, fun hV => ⟨hs hV, hm hV⟩, fun g hgN hgC => h.mQuot_conj_eq hs hgN hgC⟩

end CFSG.Quasithin.H13
